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
use std::num::NonZeroUsize;
use std::ops::Deref;
use std::path::PathBuf;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    mpsc::{self, Receiver, Sender, TryRecvError},
    Arc,
};
use std::thread;
use std::time::Duration;

// own create imports
use super::instance::Z3Instance;
use super::query::{Z3Query, Z3Result, Z3Ticket};

/// Message type that is being sent to the worker thread
pub enum Z3QueryMsg {
    Query(Z3Ticket, Z3Query),
    SharedQuery(Z3Ticket, Arc<Z3Query>),
    Reset,
    Restart,
    Terminate,
}

pub enum Z3ResultMsg {
    Result(Z3Ticket, Z3Result),
    Error(Z3Ticket, Option<Z3Query>),
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3 Worker -- A thread with a Z3 Instance
////////////////////////////////////////////////////////////////////////////////////////////////////

/// represents a Z3 worker thread
pub struct Z3Worker {
    /// the worker identifier
    id: usize,
    /// handle to the worker thread join handle
    thread: Option<thread::JoinHandle<()>>,
    /// the task queue for sending new requests to the worker
    task_q: mpsc::Sender<Z3QueryMsg>,
    /// the result queue for completed tasks
    result_q: mpsc::Receiver<Z3ResultMsg>,
    /// the number of tasks in flight
    tasks_in_flight: usize,
    /// whether the worker is currently running
    running: Arc<AtomicBool>,
}

impl Z3Worker {
    pub fn new(id: usize, logpath: Option<&PathBuf>) -> Self {
        Self::with_context(id, logpath, Arc::new(Z3Query::new()))
    }

    pub fn with_context(wid: usize, logpath: Option<&PathBuf>, task: Arc<Z3Query>) -> Self {
        // create the running flag
        let running = Arc::new(AtomicBool::new(true));
        let running_clone = running.clone();

        // create the message channels
        let (task_tx, task_rx): (Sender<Z3QueryMsg>, Receiver<Z3QueryMsg>) = mpsc::channel();
        let (result_tx, result_rx): (Sender<Z3ResultMsg>, Receiver<Z3ResultMsg>) = mpsc::channel();

        let mut z3 = if let Some(logpath) = logpath {
            Z3Instance::with_logpath(wid, logpath)
        } else {
            Z3Instance::new(wid)
        };

        // create the threads
        let thread = thread::Builder::new()
            .name(format!("z3-worker-{}", wid))
            .spawn(move || {
                while running_clone.load(Ordering::Relaxed) {
                    let msg = task_rx.recv();
                    let result = match msg {
                        Ok(Z3QueryMsg::Query(id, mut query)) => {
                            query.timestamp("request");
                            let result = z3.exec(&mut query);
                            query.timestamp("smt");
                            match result {
                                Ok(mut result) => {
                                    result.set_query(query);
                                    Z3ResultMsg::Result(id, result)
                                }
                                Err(_) => Z3ResultMsg::Error(id, Some(query)),
                            }
                        }
                        Ok(Z3QueryMsg::SharedQuery(id, query)) => {
                            match z3.exec_shared(query.deref()) {
                                Ok(result) => Z3ResultMsg::Result(id, result),
                                Err(_) => Z3ResultMsg::Error(id, None),
                            }
                        }
                        Ok(Z3QueryMsg::Reset) => {
                            z3.reset().expect("resetting the Z3 instance failed");
                            continue;
                        }
                        Ok(Z3QueryMsg::Restart) => {
                            z3.restart();
                            continue;
                        }
                        Ok(Z3QueryMsg::Terminate) => {
                            // terminate the z3 instance
                            z3.terminate();
                            running_clone.store(false, Ordering::Relaxed);
                            break;
                        }
                        Err(_) => {
                            // channel closed, exit
                            running_clone.store(false, Ordering::Relaxed);
                            z3.terminate();
                            break;
                        }
                    };

                    let msg = result_tx.send(result);
                    if msg.is_err() {
                        running_clone.store(false, Ordering::Relaxed);
                        break;
                    }
                }
            })
            .unwrap();

        if !task.is_empty()
            && task_tx
                .send(Z3QueryMsg::SharedQuery(Z3Ticket(0), task))
                .is_err()
        {
            panic!("failed to send task to worker");
        }

        Self {
            id: wid,
            tasks_in_flight: 0,
            thread: Some(thread),
            task_q: task_tx,
            result_q: result_rx,
            running,
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
        if self.task_q.send(Z3QueryMsg::Terminate).is_err() {
            // println!("[z3-worker-{}] channel closed", self.id);
        }
        if let Some(thread) = self.thread.take() {
            thread.join().expect("thread join failed");
        }
    }

    /// performs a reset of the z3 worker
    pub fn reset(&mut self) {
        self.task_q
            .send(Z3QueryMsg::Reset)
            .expect("failed to send the reset message");
    }

    /// performs a reset and initializes the z3 worker with the given contxt
    pub fn reset_with_context(&mut self, ctx: Arc<Z3Query>) -> Option<Z3Result> {
        self.reset();
        self.exec_shared(ctx)
    }

    /// executes a task on the given worker
    pub fn exec_shared(&mut self, task: Arc<Z3Query>) -> Option<Z3Result> {
        if self.send_shared_query(task, Z3Ticket(0)).is_err() {
            return None;
        }
        self.recv_result().map(|e| e.1)
    }

    /// executes a task on the given worker
    pub fn exec(&mut self, task: Z3Query) -> Option<Z3Result> {
        if self.send_query(task, Z3Ticket(0)).is_err() {
            return None;
        }
        self.recv_result().map(|e| e.1)
    }

    /// whether or not the worker is busy
    pub fn is_busy(&self) -> bool {
        self.tasks_in_flight > 0
    }

    pub fn send_message(&mut self, msg: Z3QueryMsg) -> Result<(), Z3QueryMsg> {
        if self.running.load(Ordering::Relaxed) {
            let msg = self.task_q.send(msg);
            match msg {
                Ok(_) => {
                    self.tasks_in_flight += 1;
                    Ok(())
                }
                Err(t) => Err(t.0),
            }
        } else {
            Err(msg)
        }
    }

    /// sends a task to the worker
    pub fn send_shared_query(
        &mut self,
        task: Arc<Z3Query>,
        id: Z3Ticket,
    ) -> Result<Z3Ticket, Arc<Z3Query>> {
        if self.running.load(Ordering::Relaxed) {
            match self.send_message(Z3QueryMsg::SharedQuery(id, task)) {
                Ok(_) => Ok(id),
                Err(Z3QueryMsg::SharedQuery(_, task)) => Err(task),
                Err(_) => unreachable!(),
            }
        } else {
            Err(task)
        }
    }

    /// sends a task to the worker
    pub fn send_query(&mut self, task: Z3Query, id: Z3Ticket) -> Result<Z3Ticket, Z3Query> {
        if self.running.load(Ordering::Relaxed) {
            match self.send_message(Z3QueryMsg::Query(id, task)) {
                Ok(_) => Ok(id),
                Err(Z3QueryMsg::Query(_, task)) => Err(task),
                Err(_) => unreachable!(),
            }
        } else {
            Err(task)
        }
    }

    fn extract_result_msg(msg: Z3ResultMsg) -> Option<(Z3Ticket, Z3Result)> {
        match msg {
            Z3ResultMsg::Result(id, result) => Some((id, result)),
            _ => None,
        }
    }

    /// receives a result from the worker
    pub fn recv_result(&mut self) -> Option<(Z3Ticket, Z3Result)> {
        let msg = self.result_q.recv();
        match msg {
            Ok(result) => {
                self.tasks_in_flight -= 1;
                Self::extract_result_msg(result)
            }
            Err(_) => {
                if self.running.load(Ordering::Relaxed) {
                    panic!("Z3Worker::recv_result: disconnected while running");
                } else {
                    None
                }
            }
        }
    }

    /// receives a result from the worker
    pub fn try_recv_result(&mut self) -> Option<(Z3Ticket, Z3Result)> {
        let msg = self.result_q.try_recv();
        match msg {
            Ok(result) => {
                self.tasks_in_flight -= 1;
                Self::extract_result_msg(result)
            }
            Err(TryRecvError::Empty) => None,
            Err(_) => {
                if self.running.load(Ordering::Relaxed) {
                    panic!("Z3Worker::recv_result: disconnected while running");
                } else {
                    None
                }
            }
        }
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
    /// the number of queries executed (statistics)
    num_queries: usize,
    /// workers that are currently idle
    workers_idle: Vec<Z3Worker>,
    /// workers that are currently busy
    workers_busy: Vec<Z3Worker>,
    /// tasks that haven't been dispatched to the client
    taskq: VecDeque<(Z3Ticket, Z3Query)>,
    /// stored results that haven't been collected by the client
    results: HashMap<Z3Ticket, Z3Result>,
    ///
    query_cache: HashMap<Z3Query, Result<Z3Result, ()>>,
}

impl Z3WorkerPool {
    pub fn new(logpath: Option<&PathBuf>) -> Self {
        let parallelism = thread::available_parallelism()
            .unwrap_or(NonZeroUsize::new(1).unwrap())
            .get();
        Self::with_num_workers(parallelism, logpath)
    }

    pub fn with_num_workers(num_workers: usize, logpath: Option<&PathBuf>) -> Self {
        log::info!(
            target : "[Z3WorkerPool]", " initializing using {} workers, logpath {:?}",
            num_workers,
            logpath
        );

        let mut workers_idle = Vec::with_capacity(num_workers);
        for i in 1..=num_workers {
            workers_idle.push(Z3Worker::new(i, logpath));
        }
        Self {
            num_queries: 0,
            workers_idle,
            workers_busy: Vec::new(),
            taskq: VecDeque::new(),
            results: HashMap::new(),
            query_cache: HashMap::new(),
        }
    }

    pub fn with_context(ctx: Z3Query, logpath: Option<&PathBuf>) -> Self {
        let parallelism = thread::available_parallelism()
            .unwrap_or(NonZeroUsize::new(1).unwrap())
            .get();

        Self::with_num_workers_and_context(parallelism, logpath, ctx)
    }

    pub fn with_num_workers_and_context(
        num_workers: usize,
        logpath: Option<&PathBuf>,
        ctx: Z3Query,
    ) -> Self {
        log::info!(
            target : "[Z3WorkerPool]", " initializing with context using {} workers, logpath {:?}",
            num_workers,
            logpath
        );

        let ctx = Arc::new(ctx);
        let mut workers_idle = Vec::with_capacity(num_workers);
        for i in 0..num_workers {
            workers_idle.push(Z3Worker::with_context(i, logpath, ctx.clone()));
        }
        Self {
            num_queries: 0,
            workers_idle,
            workers_busy: Vec::with_capacity(num_workers),
            taskq: VecDeque::new(),
            results: HashMap::new(),
            query_cache: HashMap::new(),
        }
    }

    pub fn check_completed_tasks(&mut self) {
        let mut busy_workers = Vec::with_capacity(self.workers_busy.capacity());
        for mut w in self.workers_busy.drain(..) {
            if let Some((id, mut r)) = w.try_recv_result() {
                r.query_mut().timestamp("result");
                log::trace!(target : "[Z3WorkerPool]", " task {} is complete", id);

                // insert the cached result
                if r.has_query() {
                    let query = r.query();
                    let result = r.result().to_string();
                    self.query_cache
                        .insert(query.clone_without_program(), Ok(Z3Result::new(result)));
                }
                self.results.insert(id, r);
                self.workers_idle.push(w);
            } else {
                busy_workers.push(w);
            }
        }
        // update busy workers
        self.workers_busy = busy_workers;
    }

    fn maybe_check_completd_tasks(&mut self) {
        if 7 * self.workers_busy.len() > 8 * self.workers_idle.len() {
            self.check_completed_tasks();
        }
    }

    fn try_send_tasks(&mut self) {
        if self.taskq.is_empty() {
            log::trace!(target : "[Z3WorkerPool]", " no new tasks.");
            return;
        }

        while let Some(mut w) = self.workers_idle.pop() {
            if self.taskq.is_empty() {
                log::trace!(target : "[Z3WorkerPool]", " no more tasks to send.");
                self.workers_idle.push(w);
                return;
            }

            let (id, mut task) = self.taskq.pop_front().unwrap();
            task.timestamp("queue");

            // see if we can the cached result
            match self.query_cache.get(&task) {
                Some(Ok(r)) => {
                    // we've already computed this query and it's results are ready
                    log::info!(target : "[Z3WorkerPool]", " not sending task, cached result for {}", id);
                    self.results.insert(id, r.clone_with_query(task));
                    self.workers_idle.push(w);
                    continue;
                }
                Some(Err(_)) => {
                    // we've submited but it's pending, push it back and continue
                    log::info!(target : "[Z3WorkerPool]", " not sending task, pending result for {}", id);
                    self.taskq.push_back((id, task));
                    continue;
                }
                None => {
                    log::trace!(target : "[Z3WorkerPool]", " sending task for {}", id);
                    // we haven't seen this query before, add it to the cache
                    self.query_cache
                        .insert(task.clone_without_program(), Err(()));
                }
            }

            // send the query
            match w.send_query(task, id) {
                Ok(_) => {
                    self.workers_busy.push(w);
                }
                Err(t) => {
                    log::error!(target : "[Z3WorkerPool]", " sending task failed");
                    self.workers_idle.push(w);
                    self.taskq.push_back((id, t));
                }
            }
        }
    }

    pub fn submit_query(&mut self, mut task: Z3Query) -> Result<Z3Ticket, Z3Query> {
        log::trace!(target : "[Z3WorkerPool]", " submitting query");
        // take the timestamp
        task.timestamp("submit");
        self.maybe_check_completd_tasks();

        // get the ticket
        self.num_queries += 1;
        let id = Z3Ticket(self.num_queries);

        // add the task to the queue
        self.taskq.push_back((id, task));
        self.try_send_tasks();
        // no workers available, that's ok.
        Ok(id)
    }

    pub fn wait_for_completion(&mut self) {
        log::warn!(target : "[Z3WorkerPool]", " waiting for completion of all tasks");
        loop {
            self.check_completed_tasks();
            self.try_send_tasks();
            if self.workers_busy.is_empty() {
                break;
            }
            thread::sleep(Duration::from_millis(10));
        }
    }

    pub fn wait_for_result(&mut self, id: Z3Ticket) -> Z3Result {
        loop {
            let res = self.get_result(id);
            if let Some(r) = res {
                return r;
            }
            log::trace!(target : "[Z3WorkerPool]", " waiting for task {}", id);
            self.check_completed_tasks();
            self.try_send_tasks();
            thread::yield_now();
        }
    }

    pub fn get_result(&mut self, id: Z3Ticket) -> Option<Z3Result> {
        self.results.remove(&id)
    }

    pub fn reset(&mut self) {
        log::warn!(target : "[Z3WorkerPool]", " performing reset of worker pool");
        self.taskq.clear();
        self.results.clear();
        self.query_cache.clear();
        for w in self.workers_idle.iter_mut() {
            w.reset();
        }

        for w in self.workers_busy.iter_mut() {
            w.reset();
        }
    }

    pub fn reset_with_context(&mut self, ctx: Z3Query) {
        log::warn!(target : "[Z3WorkerPool]", " performing reset of worker pool with context");

        self.taskq.clear();
        self.results.clear();

        let ctx = Arc::new(ctx);
        for w in self.workers_idle.iter_mut() {
            w.reset_with_context(ctx.clone());
        }

        for w in self.workers_busy.iter_mut() {
            w.reset_with_context(ctx.clone());
        }

        self.query_cache.clear();
    }

    pub fn terminate(&mut self) {
        log::warn!(target : "[Z3WorkerPool]", " terminating worker pool");
        self.taskq.clear();
        self.results.clear();
        self.query_cache.clear();
        self.workers_idle.clear();
        self.workers_busy.clear();
    }
}
