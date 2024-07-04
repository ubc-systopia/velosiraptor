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
use std::ops::{Deref, DerefMut};
use std::path::PathBuf;
use std::sync::{
    Arc,
};
use std::thread;



// own create imports
use super::query::{Z3Query, Z3Result, Z3Ticket, Z3TimeStamp};
use super::{TaskQ, Z3Instance, Z3TaskPriority, Z3Async};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3 Worker -- A thread with a Z3 Instance
////////////////////////////////////////////////////////////////////////////////////////////////////

/// represents a Z3 worker thread
#[repr(align(128))]
pub struct Z3Worker {
    /// the worker identifier
    id: usize,
    /// the solver instance we're using
    solver: Z3Instance,
    /// the current query that is being executed
    query: Option<(Box<Z3Query>, Z3Async)>,
    /// number of queries executed
    num_queries: usize,
    /// the context of the worker
    context: Option<Arc<Z3Query>>,
}

impl Z3Worker {
    pub fn new(
        id: usize,
        logpath: Option<&PathBuf>,
    ) -> Self {
        Self::with_context(id,  logpath, Arc::new(Z3Query::new()))
    }

    pub fn with_context(
        wid: usize,
        logpath: Option<&PathBuf>,
        context: Arc<Z3Query>,
    ) -> Self {
        let logfile = if let Some(logpath) = logpath {
            // create the log directory if it does not exist
            fs::create_dir_all(logpath).expect("failed to create the log directory");
            Some(logpath.join(format!("z3-worker-{wid}-log.smt2")))
        } else {
            None
        };

        let mut z3 = if let Some(logfile) = logfile {
            Z3Instance::with_logfile(wid, logfile)
        } else {
            Z3Instance::new(wid)
        };

        let context = if !context.is_empty() {
            if let Err(x) = z3.exec_shared(context.deref()) {
                log::error!(target : "[Z3Worker]", "Z3 Worker {} failed to initialize with context: {:?}", wid, x);
                panic!("failed to initialize Z3 worker with context")
            }
            Some(context)
        } else {
            None
        };

        Self {
            id: wid,
            solver: z3,
            query: None,
            context,
            num_queries: 0
        }
    }

    // obtains the worker id
    pub fn id(&self) -> usize {
        self.id
    }

    /// stops the execution of the worker
    pub fn terminate(&mut self) -> usize {
        self.solver.terminate();
        0
    }

    /// performs a reset of the z3 worker's Z3 instance
    pub fn reset(&mut self, _wait: bool) {
        self.solver.reset().expect("reset failed.");
        if let Some(ctx) = self.context.as_ref() {
            self.solver.exec_shared(ctx.deref()).expect("executing the context failed");
        }
        self.query = None;
    }

    ///
    pub fn wait_reset_done(&mut self) {
        // no-op
    }

    /// performs a restart of the z3 worker's Z3 instance
    pub fn restart(&mut self) {
        self.solver.restart();
        if let Some(ctx) = self.context.as_ref() {
            self.solver.exec_shared(ctx.deref()).expect("executing the context failed");
        }
        self.query = None;
    }

    /// performs a restart of the z3 worker's Z3 instance
    pub fn restart_with_context(&mut self, ctx: Arc<Z3Query>) -> Option<Z3Result> {
        self.solver.restart();
        self.solver.exec_shared(ctx.deref()).expect("executing the context failed");
        None
    }

    /// performs a reset and initializes the z3 worker with the given contxt
    pub fn reset_with_context(&mut self, ctx: Arc<Z3Query>) -> Option<Z3Result> {
        self.solver.reset().expect("reset failed.");
        self.solver.exec_shared(ctx.deref()).expect("executing the context failed");
        None
    }

    pub fn is_idle(&self) -> bool {
        self.query.is_none()
    }

    pub fn submit(&mut self, ticket: Z3Ticket, mut query: Box<Z3Query>) -> bool{
        log::trace!(target : "[Z3Worker]", "{} submitting query", self.id);
        match self.solver.exec_async(ticket, query.deref_mut()) {
            Ok(tok) => {
                self.query = Some((query, tok));
                true
            },
            Err(_err) => {
                panic!("failed to submit query");
                false
            }
        }
    }

    pub fn get_result(&mut self) -> Option<(Z3Ticket, Z3Result)> {
        if let Some((query, tok)) = self.query.take() {
            let ticket = tok.ticket;
            match self.solver.exec_done(tok) {
                Ok(mut result) => {
                    log::trace!(target : "[Z3Worker]", "{} obtaining result...", self.id);
                    self.num_queries += 1;
                    result.set_query(query);
                    Some((ticket, result))
                }
                Err(tok) => {
                    // log::trace!(target : "[Z3Worker]", "{} no result yet...", self.id);
                    self.query = Some((query, tok));
                    None
                }
            }
        } else {
            log::trace!(target : "[Z3Worker]", "{} worker was idle...", self.id);
            None
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
    /// workers that are currently busy w
    workers: Vec<Box<Z3Worker>>,
    queries_inflight: usize,

    /// identifier for the next query
    next_query_id: usize,
    /// statistics about the queries executed on the worker pool
    stats: Z3WorkerPoolStats,
    /// a query cache for avoiding running the same query twice
    query_cache: HashMap<Z3Query, Result<Z3Result, Vec<Z3Ticket>>>,
    /// whether or not the query cache is disabled
    opt_query_cache_disabled: bool,
    /// submitted tasks
    taskq: TaskQ,
    /// stored results that haven't been collected by the client
    results: HashMap<Z3Ticket, Z3Result>,
}

impl Z3WorkerPool {
    pub fn new(logpath: Option<Arc<PathBuf>>) -> Self {
        let parallelism = thread::available_parallelism()
            .unwrap_or(NonZeroUsize::new(1).unwrap())
            .get();

        let num_workers = if parallelism > 2 {
            parallelism - 1
        } else {
            1
        };

        Self::with_num_workers(num_workers, logpath)
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

        let ctx = Arc::new(ctx);

        // create the task and results
        let taskq = TaskQ::new(num_workers);
        let results = HashMap::new();

        // the query cache
        let query_cache = HashMap::new();

        let mut workers = Vec::with_capacity(num_workers);

        for i in 0..num_workers {
            let worker = if !ctx.is_empty() {
                Z3Worker::with_context(
                    i,
                    logpath.as_ref().map(|h| h.as_ref()),
                    ctx.clone(),
                )
            } else {
                Z3Worker::new(
                    i,
                    logpath.as_ref().map(|h| h.as_ref()),
                )
            };
            workers.push(Box::new(worker));
        }

        Self {
            workers,
            queries_inflight: 0,
            next_query_id: 0,
            taskq,
            results,
            query_cache,
            opt_query_cache_disabled: false,
            stats: Z3WorkerPoolStats::new(),
        }
    }

    pub fn disable_query_cache(&mut self, opt: bool) {
        self.opt_query_cache_disabled = opt;
    }

    fn process(&mut self, mut iter_max: usize) {
        log::trace!(target : "[Z3WorkerPool]", "processing queries...");
        while iter_max > 0 {
            // loop over the workers here
            for worker in self.workers.iter_mut() {
                if let Some((ticket, mut result)) = worker.get_result() {

                    {
                        let query = result.query_mut();
                        query.timestamp(Z3TimeStamp::Done);
                    }
                    let query = result.query();
                    let smtresult = result.result().to_string();

                    self.queries_inflight -= 1;
                    log::trace!(target : "[Z3WorkerPool]", "query done. in-flight: {}...", self.queries_inflight);
                    if self.opt_query_cache_disabled {
                        self.results.insert(ticket, result);
                    } else {
                        match self.query_cache.get_mut(query) {
                            Some(Ok(_r)) => {
                                // we already have a result, so we can just discard it here.
                            }
                            Some(Err(v)) => {
                                for qid in v {
                                    self.results.insert(*qid, result.clone());
                                }
                            }
                            None => {
                                // unreachable!("should not happen!");
                            }
                        }

                        self.query_cache.insert(
                            query.clone_without_timestamps(),
                            Ok(Z3Result::new(smtresult)),
                        );
                    }
                }

                if worker.is_idle() {
                    // the worker is idle now, submit another query
                    if let Some((ticket, query)) = self.taskq.pop(0) {
                        worker.submit(ticket, query);
                        self.queries_inflight += 1;
                        log::trace!(target : "[Z3WorkerPool]", "query submitted. in-flight: {}...", self.queries_inflight);
                    }
                }
            }

            if self.taskq.is_empty() {
                // log::error!(target : "[Z3WorkerPool]", "taskq is empty");
                break;
            }
            iter_max -= 1;
        }
    }

    fn do_push_query(&mut self, id: Z3Ticket, task: Box<Z3Query>, priority: Z3TaskPriority) {
        self.taskq.push(priority, id, task);
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

        if self.opt_query_cache_disabled {
            self.do_push_query(id, task, priority);
        } else {
            // see if we can the cached result
            match self.query_cache.get_mut(&task) {
                Some(Ok(r)) => {
                    // we've already computed this query and it's results are ready
                    log::debug!(target : "[Z3WorkerPool]", "not sending task, cached result for {}", id);
                    self.stats.add_cached(&task);
                    self.results.insert(id, r.clone_with_query(task));
                }
                Some(Err(v)) => {
                    // we've submitted but it's pending, push it back and continue
                    log::trace!(target : "[Z3WorkerPool]", "not sending task, pending result for {}", id);
                    self.stats.add_cached(&task);
                    v.push(id);
                }
                None => {
                    log::trace!(target : "[Z3WorkerPool]", " sending task for {}", id);
                    self.stats.add_query(&task);
                    // we haven't seen this query before, add it to the cache
                    self.query_cache
                        .insert(task.clone_without_timestamps(), Err(vec![id]));
                    self.do_push_query(id, task, priority);
                }
            }
        }

        self.process(1);

        Ok(id)
    }

    fn drain_taskq(&mut self) {
        log::trace!(target : "[Z3WorkerPool]", "draining task queue");
        // XXX: that one here just makes sure there are no new tasks...
        self.taskq.drain();
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
        log::trace!(target : "[Z3Worker]", "get result {} / {}", id, self.next_query_id);
        self.process(3);
        self.results.remove(&id)
    }

    pub fn reset(&mut self, wait: bool) {
        log::trace!(target : "[Z3WorkerPool]", "performing reset of worker pool");

        self.drain_taskq();
        for worker in self.workers.iter_mut() {
            worker.reset(wait);
        }

        self.results.clear();
        self.query_cache.clear();
    }

    pub fn reset_with_context(&mut self, ctx: Z3Query, wait: bool) {
        log::trace!(target : "[Z3WorkerPool]", "performing reset of worker pool with context");

        let query = Arc::new(ctx);

        self.drain_taskq();
        for worker in self.workers.iter_mut() {
            worker.reset_with_context(query.clone());
        }

        if wait {
            for worker in self.workers.iter_mut() {
                worker.wait_reset_done();
            }
        }

        self.results.clear();
        self.query_cache.clear();
    }

    pub fn terminate(&mut self) {
        log::info!(target : "[Z3WorkerPool]", "Terminating worker pool...");

        self.drain_taskq();
        for worker in self.workers.iter_mut() {
            worker.terminate();
        }
        self.results.clear();
        self.query_cache.clear();

        log::info!(target : "[Z3WorkerPool]", "terminated.");
    }

    pub fn restart(&mut self) {
        log::info!(target : "[Z3WorkerPool]", "Restarting worker pool...");

        self.drain_taskq();
        for worker in self.workers.iter_mut() {
            worker.restart();
        }
        self.results.clear();
        self.query_cache.clear();

        log::info!(target : "[Z3WorkerPool]", "restarted.");
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
