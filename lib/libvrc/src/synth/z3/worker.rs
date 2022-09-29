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
use std::collections::VecDeque;
use std::num::NonZeroUsize;
use std::ops::Deref;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Receiver, Sender, TryRecvError};
use std::sync::Arc;
use std::thread;
use std::time::Duration;
//use std::collections::hash_map::DefaultHasher;
//use std::hash::Hasher
use std::collections::HashMap;
// use std::hash::Hash;

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

/// represents a worker thread
pub struct Z3Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
    task_q: mpsc::Sender<Z3QueryMsg>,
    result_q: mpsc::Receiver<Z3ResultMsg>,
    tasks_in_flight: usize,
    running: Arc<AtomicBool>,
}

impl Z3Worker {
    pub fn new(id: usize, logpath: Option<&PathBuf>) -> Self {
        Self::with_context(id, logpath, Arc::new(Z3Query::new()))
    }

    pub fn with_context(wid: usize, logpath: Option<&PathBuf>, task: Arc<Z3Query>) -> Self {
        // println!("[z3-worker-{}] creating new", wid);

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
                // println!("[z3-worker-{}] starting...", wid);
                while running_clone.load(Ordering::Relaxed) {
                    let msg = task_rx.recv();
                    let result = match msg {
                        Ok(Z3QueryMsg::Query(id, mut query)) => {
                            // println!("[z3-worker-{}] new query...", wid);
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
                            // println!("[z3-worker-{}] terminating Z3 instance...", wid);
                            // terminate the z3 instance
                            z3.terminate();
                            running_clone.store(false, Ordering::Relaxed);
                            break;
                        }
                        Err(_) => {
                            // channel closed, exit
                            // println!("[z3-worker-{}] channel closed...", wid);
                            running_clone.store(false, Ordering::Relaxed);
                            z3.terminate();
                            break;
                        }
                    };

                    // println!("[z3-worker-{}] sending result", wid);
                    let msg = result_tx.send(result);
                    if msg.is_err() {
                        // println!("[z3-worker-{}] channel closed exiting", wid);
                        running_clone.store(false, Ordering::Relaxed);
                        break;
                    }
                }
                // println!("[z3-worker-{}] exiting...", wid);
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

pub struct Z3WorkerPool {
    num_queries: usize,
    workers_idle: Vec<Z3Worker>,
    workers_busy: Vec<Z3Worker>,
    taskq: VecDeque<(Z3Ticket, Z3Query)>,
    results: HashMap<Z3Ticket, Z3Result>,
}

impl Z3WorkerPool {
    pub fn new(logpath: Option<&PathBuf>) -> Self {
        let parallelism = thread::available_parallelism()
            .unwrap_or(NonZeroUsize::new(1).unwrap())
            .get();
        Self::with_num_workers(parallelism, logpath)
    }

    pub fn with_num_workers(num_workers: usize, logpath: Option<&PathBuf>) -> Self {
        // println!("[z3-pool] initializing with {} workers", num_workers);

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
        // println!(
        //     "[z3-pool] initializing with {} workers, and context",
        //     num_workers
        // );

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
        }
    }

    pub fn check_completed_tasks(&mut self) {
        let mut busy_workers = Vec::with_capacity(self.workers_busy.capacity());
        for mut w in self.workers_busy.drain(..) {
            if let Some((id, mut r)) = w.try_recv_result() {
                r.query_mut().timestamp("result");
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
            return;
        }

        if let Some(mut w) = self.workers_idle.pop() {
            let (id, mut task) = self.taskq.pop_front().unwrap();
            task.timestamp("queue");
            match w.send_query(task, id) {
                Ok(_) => {
                    self.workers_busy.push(w);
                }
                Err(t) => {
                    self.workers_idle.push(w);
                    self.taskq.push_back((id, t));
                }
            }
        }
    }

    pub fn submit_query(&mut self, mut task: Z3Query) -> Result<Z3Ticket, Z3Query> {
        // use some hashing stuff to do caching of queries...
        // let mut s = DefaultHasher::new();
        // task.hash(&mut s);
        // let id = s.finish();

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
            self.check_completed_tasks();
            self.try_send_tasks();
            thread::yield_now();
        }
    }

    pub fn get_result(&mut self, id: Z3Ticket) -> Option<Z3Result> {
        self.results.remove(&id)
    }

    pub fn reset(&mut self) {
        self.taskq.clear();
        self.results.clear();
        for w in self.workers_idle.iter_mut() {
            w.reset();
        }

        for w in self.workers_busy.iter_mut() {
            w.reset();
        }
    }

    pub fn reset_with_context(&mut self, ctx: Z3Query) {
        self.taskq.clear();
        self.results.clear();

        let ctx = Arc::new(ctx);
        for w in self.workers_idle.iter_mut() {
            w.reset_with_context(ctx.clone());
        }

        for w in self.workers_busy.iter_mut() {
            w.reset_with_context(ctx.clone());
        }
    }

    pub fn terminate(&mut self) {
        self.taskq.clear();
        self.results.clear();
        self.workers_idle.clear();
        self.workers_busy.clear();
    }
}
