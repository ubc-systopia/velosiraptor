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

use crate::{Z3Query, Z3Ticket};
use std::collections::VecDeque;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc, Mutex,
};

type QueryQueue = VecDeque<(Z3Ticket, Box<Z3Query>)>;

#[derive(Clone)]
pub struct TaskQ {
    task_counts: [Arc<AtomicUsize>; 4],
    task_queues: [Arc<Mutex<QueryQueue>>; 4],
}

const TASKQ_CAPACITY: usize = 1024;

#[derive(Clone, Copy)]
pub enum Z3TaskPriority {
    High = 0,
    Medium = 1,
    Low = 2,
    Lowest = 3,
}

impl TaskQ {
    pub fn new() -> Self {
        Self {
            task_counts: [
                Arc::new(AtomicUsize::new(0)),
                Arc::new(AtomicUsize::new(0)),
                Arc::new(AtomicUsize::new(0)),
                Arc::new(AtomicUsize::new(0)),
            ],
            task_queues: [
                Arc::new(Mutex::new(VecDeque::with_capacity(TASKQ_CAPACITY))),
                Arc::new(Mutex::new(VecDeque::with_capacity(TASKQ_CAPACITY))),
                Arc::new(Mutex::new(VecDeque::with_capacity(TASKQ_CAPACITY))),
                Arc::new(Mutex::new(VecDeque::with_capacity(TASKQ_CAPACITY))),
            ],
        }
    }

    pub fn push(&self, priority: Z3TaskPriority, ticket: Z3Ticket, query: Box<Z3Query>) {
        self.task_queues[priority as usize]
            .lock()
            .unwrap()
            .push_back((ticket, query));
        self.task_counts[priority as usize].fetch_add(1, Ordering::SeqCst);
    }

    pub fn pop(&self) -> Option<(Z3Ticket, Box<Z3Query>)> {
        for i in 0..4 {
            if self.task_counts[i].load(Ordering::Relaxed) == 0 {
                continue;
            }
            if let Some((ticket, query)) = self.task_queues[i].lock().unwrap().pop_front() {
                self.task_counts[i].fetch_sub(1, Ordering::SeqCst);
                return Some((ticket, query));
            }
        }
        None
    }

    pub fn drain(&mut self) {
        for i in 0..4 {
            if let mut q = self.task_queues[i].lock().unwrap() {
                q.clear();
            }
            self.task_counts[i].store(0, Ordering::SeqCst);
        }
    }
}

impl Default for TaskQ {
    fn default() -> Self {
        Self::new()
    }
}
