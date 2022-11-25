// Smt2 Code Generation - Function Declaration
//
//
// MIT License
//
// Copyright (c) 2021 Systopia Lab, Computer Science, University of British Columbia
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

//! Z3 Worker Thread

// std library imports
use std::collections::{HashMap, VecDeque};
use std::fs;
use std::num::NonZeroUsize;
use std::ops::Deref;
use std::path::PathBuf;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    mpsc::{self, Receiver, Sender, TryRecvError},
    Arc, Mutex,
};
use std::thread;
use std::time::Duration;

// own create imports
use super::query::{Z3Query, Z3Result, Z3Ticket};
use super::Z3Instance;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3 Worker -- A thread with a Z3 Instance
////////////////////////////////////////////////////////////////////////////////////////////////////

enum Z3Context {
    Query(Arc<Z3Query>),
    Result(Z3Result),
    None,
}

/// represents a Z3 worker thread
pub struct Z3Worker {
    /// the worker identifier
    id: usize,
    /// handle to the worker thread join handle
    thread: Option<thread::JoinHandle<()>>,

    context: Arc<Mutex<Z3Context>>,

    /// whether the worker is currently running
    running: Arc<AtomicBool>,

    /// reset
    reset: Arc<AtomicBool>,

    ///
    restart: Arc<AtomicBool>,
}

impl Z3Worker {
    pub fn new(
        id: usize,
        tasks: Arc<Mutex<VecDeque<(Z3Ticket, Z3Query)>>>,
        results: Sender<(Z3Ticket, Z3Result)>,
        logpath: Option<&PathBuf>,
    ) -> Self {
        Self::with_context(id, tasks, results, logpath, Arc::new(Z3Query::new()))
    }

    pub fn with_context(
        wid: usize,
        tasks: Arc<Mutex<VecDeque<(Z3Ticket, Z3Query)>>>,
        results: Sender<(Z3Ticket, Z3Result)>,
        logpath: Option<&PathBuf>,
        start_context: Arc<Z3Query>,
    ) -> Self {
        // create the running flag
        let running = Arc::new(AtomicBool::new(true));
        let running_clone = running.clone();

        let reset = Arc::new(AtomicBool::new(false));
        let reset_clone = reset.clone();

        let restart = Arc::new(AtomicBool::new(false));
        let restart_clone = reset.clone();

        let context = Arc::new(Mutex::new(Z3Context::None));
        let context_clone = context.clone();

        let mut logfile = if let Some(logpath) = logpath {
            // create the log directory if it does not exist
            fs::create_dir_all(logpath).expect("failed to create the log directory");
            Some(logpath.join(format!("z3-worker-{}-log.smt2", wid)))
        } else {
            None
        };

        // create the threads
        let thread = thread::Builder::new()
            .name(format!("z3-worker-{}", wid))
            .spawn(move || {

                let mut z3 = if let Some(logfile) = logfile {
                    Z3Instance::with_logfile(wid, logfile)
                } else {
                    Z3Instance::new(wid)
                };


                if !start_context.is_empty() {
                    if let Err(x) = z3.exec_shared(start_context.deref()) {
                        log::error!(target : "[Z3Worker]", "Z3 Worker {} failed to initialize with context: {:?}", wid, x);
                    }
                    running_clone.store(false, Ordering::Relaxed);
                }

                while running_clone.load(Ordering::Relaxed) {
                    // check if we need to do a reset
                    if reset_clone.load(Ordering::Relaxed) {
                        z3.reset().expect("resetting the Z3 instance failed");


                        let mut context = context_clone.as_ref().lock().unwrap();
                        if let Z3Context::Query(query) = &*context {
                            let res = z3.exec_shared(query.deref()).expect("executing the context failed");
                            *context = Z3Context::Result(res);
                        }
                        drop(context);

                        reset_clone.store(false, Ordering::Relaxed);
                        continue;
                    }

                    if restart_clone.load(Ordering::Relaxed) {
                        z3.restart();

                        let mut context = context_clone.as_ref().lock().unwrap();
                        if let Z3Context::Query(query) = &*context {
                            let res = z3.exec_shared(query.deref()).expect("executing the context failed");
                            *context = Z3Context::Result(res);
                        }
                        drop(context);

                        restart_clone.store(false, Ordering::Relaxed);
                        continue;
                    }

                    // see if we have a shared query
                    // match z3.exec_shared(query.deref()) {
                    //     Ok(result) => Z3ResultMsg::Result(id, result),
                    //     Err(_) => Z3ResultMsg::Error(id, None),
                    // }

                    // get a task
                    let mut task_q = tasks.lock().unwrap();
                    let mut task = task_q.pop_front();
                    drop(task_q); // drop the lock again

                    if let Some((ticket, mut query)) = task {
                        // run the query
                        query.timestamp("request");
                        let result = z3.exec(ticket, &mut query);
                        query.timestamp("smt");

                        match result {
                            Ok(mut result) => {
                                result.set_query(query);
                                results.send((ticket, result)).unwrap();
                            }
                            Err(x) => {
                                panic!("handle me: {:?}", x);
                            }
                        }
                    }
                }

                // finally terminate
                z3.terminate();
            })
            .unwrap();

        Self {
            id: wid,
            thread: Some(thread),
            context,
            running,
            reset,
            restart,
        }
    }

    // obtains the worker id
    pub fn id(&self) -> usize {
        self.id
    }

    /// stops the execution of the worker
    pub fn terminate(&mut self) {
        // set the termintation flag
        self.running.store(false, Ordering::Relaxed);
        if let Some(thread) = self.thread.take() {
            thread.join().expect("thread join failed");
        }
    }

    /// performs a reset of the z3 worker's Z3 instance
    pub fn reset(&mut self) {
        self.reset.store(true, Ordering::Relaxed);
        while self.reset.load(Ordering::Relaxed) {
            thread::yield_now();
        }
    }

    /// performs a restart of the z3 worker's Z3 instance
    pub fn restart(&mut self) {
        self.restart.store(true, Ordering::Relaxed);
        while self.restart.load(Ordering::Relaxed) {
            thread::yield_now();
        }
    }

    /// performs a restart of the z3 worker's Z3 instance
    pub fn restart_with_context(&mut self, ctx: Arc<Z3Query>) -> Option<Z3Result> {
        // set the context, so we can do the restart
        let mut context = self.context.as_ref().lock().unwrap();
        *context = Z3Context::Query(ctx);
        drop(context);

        // perform restart
        self.restart();

        None
    }

    /// performs a reset and initializes the z3 worker with the given contxt
    pub fn reset_with_context(&mut self, ctx: Arc<Z3Query>) -> Option<Z3Result> {
        // set the context, so we can do the restart
        let mut context = self.context.as_ref().lock().unwrap();
        *context = Z3Context::Query(ctx);
        drop(context);
        self.reset();
        // let mut context = self.context.lock().unwrap();
        // if let Z3Context::Result(res) = &*context {
        //     *context = Z3Context::None;
        //     Some(res.clone())
        // } else {
        //     *context = Z3Context::None;
        //     return None;
        // }
        None
    }
}

impl Drop for Z3Worker {
    fn drop(&mut self) {
        // println!("[z3-worker-{}] dropping...", self.id);
        self.terminate();
        // println!("[z3-worker-{}] dropped...", self.id);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3 Worker Pool -- A collection of Z3Workers to handle queries
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents a pool of Z3 worker threads
pub struct Z3WorkerPool {
    ///
    workers: Vec<Z3Worker>,

    /// the number of queries executed (statistics)
    stats_num_queries: usize,
    ///
    stats_cached: usize,
    ///
    query_cache: HashMap<Z3Query, Result<Z3Result, Vec<Z3Ticket>>>,
    /// tasks that haven't been dispatched to the client
    taskq: Arc<Mutex<VecDeque<(Z3Ticket, Z3Query)>>>,
    resultq: Receiver<(Z3Ticket, Z3Result)>,
    /// stored results that haven't been collected by the client
    results: HashMap<Z3Ticket, Z3Result>,
}

impl Z3WorkerPool {
    pub fn new(logpath: Option<Arc<PathBuf>>) -> Self {
        let parallelism = thread::available_parallelism()
            .unwrap_or(NonZeroUsize::new(1).unwrap())
            .get();
        Self::with_num_workers(parallelism, logpath)
    }

    pub fn with_num_workers(num_workers: usize, logpath: Option<Arc<PathBuf>>) -> Self {
        log::info!(
            target : "[Z3WorkerPool]", " initializing using {} workers, logpath {:?}",
            num_workers,
            logpath
        );

        let ctx = Z3Query::new();
        Self::with_num_workers_and_context(num_workers, logpath, ctx)
    }

    pub fn with_context(ctx: Z3Query, logpath: Option<Arc<PathBuf>>) -> Self {
        let parallelism = thread::available_parallelism()
            .unwrap_or(NonZeroUsize::new(1).unwrap())
            .get();

        Self::with_num_workers_and_context(parallelism, logpath, ctx)
    }

    pub fn with_num_workers_and_context(
        num_workers: usize,
        logpath: Option<Arc<PathBuf>>,
        ctx: Z3Query,
    ) -> Self {
        log::info!(
            target : "[Z3WorkerPool]", " initializing with context using {} workers, logpath {:?}",
            num_workers,
            logpath
        );

        // create the task and results
        let taskq = Arc::new(Mutex::new(VecDeque::<(Z3Ticket, Z3Query)>::new()));

        let (results_tx, resultq) = mpsc::channel::<(Z3Ticket, Z3Result)>();

        //
        let results = HashMap::new();

        // the query cache
        let query_cache = HashMap::new();

        let ctx = Arc::new(ctx);

        // create the workers
        let mut workers = Vec::with_capacity(num_workers);
        for i in 0..num_workers {
            let worker = if !ctx.is_empty() {
                Z3Worker::with_context(
                    i,
                    taskq.clone(),
                    results_tx.clone(),
                    logpath.as_ref().map(|h| h.as_ref()),
                    ctx.clone(),
                )
            } else {
                Z3Worker::new(
                    i,
                    taskq.clone(),
                    results_tx.clone(),
                    logpath.as_ref().map(|h| h.as_ref()),
                )
            };
            workers.push(worker);
        }

        Self {
            workers,
            resultq,
            taskq,
            results,
            query_cache,
            stats_cached: 0,
            stats_num_queries: 0,
        }
    }

    pub fn submit_query(&mut self, mut task: Z3Query) -> Result<Z3Ticket, Z3Query> {
        log::trace!(target : "[Z3WorkerPool]", " submitting query");
        // take the timestamp
        task.timestamp("submit");

        // get the ticket
        self.stats_num_queries += 1;
        let id = Z3Ticket(self.stats_num_queries);

        // see if we can the cached result
        match self.query_cache.get_mut(&task) {
            Some(Ok(r)) => {
                // we've already computed this query and it's results are ready
                log::debug!(target : "[Z3WorkerPool]", "not sending task, cached result for {}", id);
                self.results.insert(id, r.clone_with_query(task));
                self.stats_cached += 1;
            }
            Some(Err(v)) => {
                // we've submited but it's pending, push it back and continue
                log::trace!(target : "[Z3WorkerPool]", "not sending task, pending result for {}", id);
                v.push(id);
            }
            None => {
                log::trace!(target : "[Z3WorkerPool]", " sending task for {}", id);
                // we haven't seen this query before, add it to the cache
                self.query_cache
                    .insert(task.clone_without_timestamps(), Err(vec![id]));

                let mut taskq = self.taskq.lock().unwrap();
                taskq.push_back((id, task));
                drop(taskq);
            }
        }

        Ok(id)
    }

    fn drain_taskq(&mut self) {
        log::trace!(target : "[Z3WorkerPool]", "draining task queue");
        // XXX: that one here just makes sure there are no new tasks...
        let mut taskq = self.taskq.lock().unwrap();
        taskq.clear(); // just drop everything
    }

    fn drain_resultq(&mut self) {
        log::trace!(target : "[Z3WorkerPool]", "draining result queue");
        // XXX: that one here just makes sure there are no new tasks...

        let mut counter = 5;
        loop {
            match self.resultq.try_recv() {
                Ok((id, result)) => {
                    // nothing
                    let query = result.query();
                    let smtresult = result.result().to_string();

                    match self.query_cache.get_mut(query) {
                        Some(Ok(r)) => {
                            unreachable!("should not happen!");
                        }
                        Some(Err(v)) => {
                            for qid in v {
                                self.results.insert(*qid, result.clone());
                            }
                        }
                        None => {
                            unreachable!("should not happen!");
                        }
                    }

                    self.query_cache.insert(
                        query.clone_without_timestamps(),
                        Ok(Z3Result::new(smtresult)),
                    );
                }
                Err(TryRecvError::Empty) => {
                    if counter == 0 {
                        break;
                    }
                    counter -= 1;
                    break;
                }
                Err(TryRecvError::Disconnected) => {
                    return;
                }
            }
        }
    }

    pub fn wait_for_result(&mut self, id: Z3Ticket) -> Z3Result {
        loop {
            let res = self.get_result(id);
            if let Some(r) = res {
                return r;
            }
            // thread::yield_now();
            // thread::sleep(Duration::from_millis(5));
        }
    }

    pub fn get_result(&mut self, id: Z3Ticket) -> Option<Z3Result> {
        self.drain_resultq();
        self.results.remove(&id)
    }

    pub fn reset(&mut self) {
        log::info!(target : "[Z3WorkerPool]", "performing reset of worker pool");

        self.drain_taskq();
        for worker in self.workers.iter_mut() {
            worker.reset();
        }

        self.drain_resultq();
        self.results.clear();
        self.query_cache.clear();
    }

    pub fn reset_with_context(&mut self, ctx: Z3Query) {
        log::info!(target : "[Z3WorkerPool]", "performing reset of worker pool with context");

        let query = Arc::new(ctx);

        self.drain_taskq();
        for worker in self.workers.iter_mut() {
            worker.reset_with_context(query.clone());
        }
        self.drain_resultq();
        self.results.clear();
        self.query_cache.clear();
    }

    pub fn terminate(&mut self) {
        log::warn!(target : "[Z3WorkerPool]", "Terminating worker pool...");

        self.drain_taskq();
        for worker in self.workers.iter_mut() {
            worker.terminate();
        }
        self.drain_resultq();
        self.results.clear();
        self.query_cache.clear();

        log::warn!(target : "[Z3WorkerPool]", "terminated.");
    }

    pub fn num_workers(&self) -> usize {
        self.workers.len()
    }

    pub fn num_queries(&self) -> usize {
        self.stats_num_queries
    }

    pub fn num_cached_queries(&self) -> usize {
        self.stats_cached
    }
}
