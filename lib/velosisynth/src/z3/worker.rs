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
use std::collections::HashMap;
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

// own create imports
use super::query::{Z3Query, Z3Result, Z3Ticket, Z3TimeStamp};
use super::{TaskQ, Z3Instance, Z3TaskPriority};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3 Worker -- A thread with a Z3 Instance
////////////////////////////////////////////////////////////////////////////////////////////////////

enum Z3Context {
    Query(Arc<Z3Query>),
    Result(Z3Result),
    None,
}

/// represents a Z3 worker thread
#[repr(align(128))]
pub struct Z3Worker {
    /// the worker identifier
    id: usize,
    /// handle to the worker thread join handle
    thread: Option<thread::JoinHandle<usize>>,
    /// the context of the worker
    context: Arc<Mutex<Z3Context>>,
    /// whether the worker is currently running
    running: Arc<AtomicBool>,
    /// reset
    reset: Arc<AtomicBool>,
    /// whether to restart the current atomic bool
    restart: Arc<AtomicBool>,
}

impl Z3Worker {
    pub fn new(
        id: usize,
        tasks: TaskQ,
        results: Sender<(Z3Ticket, Z3Result)>,
        logpath: Option<&PathBuf>,
    ) -> Self {
        Self::with_context(id, tasks, results, logpath, Arc::new(Z3Query::new()))
    }

    pub fn with_context(
        wid: usize,
        tasks: TaskQ,
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

        let logfile = if let Some(logpath) = logpath {
            // create the log directory if it does not exist
            fs::create_dir_all(logpath).expect("failed to create the log directory");
            Some(logpath.join(format!("z3-worker-{wid}-log.smt2")))
        } else {
            None
        };

        // create the threads
        let thread = thread::Builder::new()
            .name(format!("z3-worker-{wid}"))
            .spawn(move || {

                let mut num_queries = 0;

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

                        // t_query_ms_clone.store(z3., Ordering::Relaxed);
                        // t_prepare_ms_clone

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

                    if let Some((ticket, mut query)) = tasks.pop() {
                        num_queries += 1;

                        // run the query
                        query.timestamp(Z3TimeStamp::Dispatch);
                        let result = z3.exec(ticket, &mut query);

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

                // return the number of queries
                num_queries
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
    pub fn terminate(&mut self) -> usize {
        // set the termintation flag
        self.running.store(false, Ordering::Relaxed);
        if let Some(thread) = self.thread.take() {
            thread.join().expect("thread join failed")
        } else {
            0
        }
    }

    /// performs a reset of the z3 worker's Z3 instance
    pub fn reset(&mut self) {
        self.do_reset();
        self.wait_reset_done();
    }

    fn do_reset(&mut self) {
        self.reset.store(true, Ordering::Relaxed);
    }

    ///
    pub fn wait_reset_done(&mut self) {
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
        self.do_reset();
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
    /// the workers of the worker pool
    workers: Vec<Z3Worker>,
    /// identifier for the next query
    next_query_id: usize,
    /// statistics about the queries executed on the worker pool
    stats: Z3WorkerPoolStats,
    /// a query cache for avoiding running the same query twice
    query_cache: HashMap<Z3Query, Result<Z3Result, Vec<Z3Ticket>>>,
    /// tasks that haven't been dispatched to the client
    taskq: TaskQ,
    /// the result queue
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
        let taskq = TaskQ::new();
        //let taskq = Arc::new(Mutex::new(VecDeque::<(Z3Ticket, Z3Query)>::new()));

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
            next_query_id: 0,
            resultq,
            taskq,
            results,
            query_cache,
            stats: Z3WorkerPoolStats::new(),
        }
    }

    pub fn submit_query(
        &mut self,
        mut task: Box<Z3Query>,
        priority: Z3TaskPriority,
    ) -> Result<Z3Ticket, Box<Z3Query>> {
        log::trace!(target : "[Z3WorkerPool]", " submitting query");
        // take the timestamp
        task.timestamp(Z3TimeStamp::Submit);

        // get the ticket
        self.next_query_id += 1;
        let id = Z3Ticket(self.next_query_id);

        // see if we can the cached result
        match self.query_cache.get_mut(&task) {
            Some(Ok(r)) => {
                // we've already computed this query and it's results are ready
                log::debug!(target : "[Z3WorkerPool]", "not sending task, cached result for {}", id);
                self.stats.add_cached(&task);
                self.results.insert(id, r.clone_with_query(task));
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
                self.taskq.push(priority, id, task);
            }
        }

        Ok(id)
    }

    fn drain_taskq(&mut self) {
        log::trace!(target : "[Z3WorkerPool]", "draining task queue");
        // XXX: that one here just makes sure there are no new tasks...
        self.taskq.drain();
    }

    fn drain_resultq(&mut self) {
        // log::trace!(target : "[Z3WorkerPool]", "draining result queue");
        // XXX: that one here just makes sure there are no new tasks...
        loop {
            match self.resultq.try_recv() {
                Ok((_id, mut result)) => {
                    // nothing
                    {
                        let query = result.query_mut();
                        query.timestamp(Z3TimeStamp::Done);
                    }
                    let query = result.query();
                    let smtresult = result.result().to_string();

                    // TODO: update stats!
                    self.stats.add_query(query);

                    match self.query_cache.get_mut(query) {
                        Some(Ok(_r)) => {
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

        for worker in self.workers.iter_mut() {
            worker.wait_reset_done();
        }
        self.drain_resultq();
        self.results.clear();
        self.query_cache.clear();
    }

    pub fn terminate(&mut self) {
        log::info!(target : "[Z3WorkerPool]", "Terminating worker pool...");

        self.drain_taskq();
        for worker in self.workers.iter_mut() {
            worker.terminate();
        }
        self.drain_resultq();
        self.results.clear();
        self.query_cache.clear();

        log::info!(target : "[Z3WorkerPool]", "terminated.");
    }

    pub fn num_workers(&self) -> usize {
        self.workers.len()
    }

    /// obtain the stats fo the worker pool
    pub fn stats(&self) -> &Z3WorkerPoolStats {
        &self.stats
    }

    /// reset the stats of the worker pool
    pub fn stats_reset(&mut self) {
        self.stats.reset();
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3 Worker Pool Stats
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Clone)]
pub struct Z3WorkerPoolStats {
    /// total number of queries run
    pub n_queries: u64,
    /// the number of cached queries
    pub n_cached: u64,
    /// total query creation time
    pub t_create_ms: u64,
    /// total queuing time
    pub t_queued_ms: u64,
    /// total time for formatting smtlib2
    pub t_prepare_ms: u64,
    /// total SMT time
    pub t_solver_ms: u64,
}

impl Z3WorkerPoolStats {
    pub fn new() -> Self {
        Self {
            n_queries: 0,
            n_cached: 0,
            t_create_ms: 0,
            t_queued_ms: 0,
            t_prepare_ms: 0,
            t_solver_ms: 0,
        }
    }

    pub fn reset(&mut self) {
        self.n_queries = 0;
        self.n_cached = 0;
        self.t_create_ms = 0;
        self.t_queued_ms = 0;
        self.t_prepare_ms = 0;
        self.t_solver_ms = 0;
    }

    fn update_times(&mut self, query: &Z3Query) {
        let mut timestamps = query.timestamps().iter();

        let t_start = if let Some((Z3TimeStamp::Create, t_start)) = timestamps.next() {
            t_start
        } else {
            return;
        };

        let t_submit = if let Some((Z3TimeStamp::Submit, t_submit)) = timestamps.next() {
            t_submit
        } else {
            return;
        };

        self.t_create_ms += t_submit.duration_since(*t_start).as_millis() as u64;

        let t_dispatch = if let Some((Z3TimeStamp::Dispatch, t_dispatch)) = timestamps.next() {
            t_dispatch
        } else {
            return;
        };

        self.t_queued_ms += t_dispatch.duration_since(*t_submit).as_millis() as u64;

        let _t_prepare = if let Some((Z3TimeStamp::FmtSmt, t_prepare)) = timestamps.next() {
            t_prepare
        } else {
            return;
        };

        let t_prepare = if let Some((Z3TimeStamp::SendCmd, t_prepare)) = timestamps.next() {
            t_prepare
        } else {
            return;
        };

        self.t_prepare_ms += t_prepare.duration_since(*t_dispatch).as_millis() as u64;
        let t_solver = if let Some((Z3TimeStamp::SolverDone, t_solver)) = timestamps.next() {
            t_solver
        } else {
            return;
        };

        self.t_solver_ms += t_solver.duration_since(*t_prepare).as_millis() as u64;
    }

    pub fn add_query(&mut self, query: &Z3Query) {
        self.n_queries += 1;
        self.update_times(query);
    }

    pub fn add_cached(&mut self, query: &Z3Query) {
        self.n_queries += 1;
        self.n_cached += 1;
        self.update_times(query);
    }
}

impl Default for Z3WorkerPoolStats {
    fn default() -> Self {
        Self::new()
    }
}
