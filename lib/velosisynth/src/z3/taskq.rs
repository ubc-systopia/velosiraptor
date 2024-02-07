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
use std::sync::Arc;

use crossbeam::queue::ArrayQueue;
use crossbeam::utils::CachePadded;

type QueryQueue = ArrayQueue<(Z3Ticket, Box<Z3Query>)>;

// type QueryQueue = VecDeque<(Z3Ticket, Box<Z3Query>)>;

const TASKQ_CAPACITY: usize = 1024;

const TASK_PRIO_MAX: usize = 4;

#[derive(Clone, Copy)]
pub struct Z3TaskPriority(usize);

impl Z3TaskPriority {
    pub fn new(prio: usize) -> Self {
        if prio >= TASK_PRIO_MAX {
            Self(TASK_PRIO_MAX - 1)
        } else {
            Self(prio)
        }
    }

    pub fn lowest() -> Self {
        Self::new(TASK_PRIO_MAX - 1)
    }

    pub fn is_lowest(&self) -> bool {
        self.0 == TASK_PRIO_MAX - 1
    }

    pub fn highest() -> Self {
        Self::new(0)
    }

    pub fn lower(&self) -> Self {
        if self.0 == TASK_PRIO_MAX - 1 {
            Self(self.0)
        } else {
            Self(self.0 + 1)
        }
    }

    pub fn higher(&self) -> Self {
        if self.0 == 0 {
            Self(self.0)
        } else {
            Self(self.0 - 1)
        }
    }

    pub fn as_usize(&self) -> usize {
        self.0
    }
}

impl std::fmt::Display for Z3TaskPriority {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Z3TaskPriority({})", self.0)
    }
}

#[derive(Clone)]
pub struct TaskQ {
    // task_counts: Arc<[CachePadded<AtomicUsize>; TASK_PRIO_MAX]>,
    task_queues: Arc<[CachePadded<QueryQueue>; TASK_PRIO_MAX]>,
}

impl TaskQ {
    pub fn new(_num_workers: usize) -> Self {
        let task_queues = (0..TASK_PRIO_MAX)
            .map(|_| CachePadded::new(QueryQueue::new(TASKQ_CAPACITY)))
            .collect::<Vec<_>>();

        Self {
            // task_counts: Arc::new([ARRAY_REPEAT_VALUE; TASK_PRIO_MAX ]),
            task_queues: Arc::new(task_queues.try_into().unwrap()),
        }
    }

    pub fn push(&self, priority: Z3TaskPriority, mut ticket: Z3Ticket, mut query: Box<Z3Query>) {
        loop {
            let target_priority = priority;
            if let Err((t, q)) = self.task_queues[target_priority.as_usize()].push((ticket, query))
            {
                let target_priority = priority.lower();
                if let Err((t, q)) = self.task_queues[target_priority.as_usize()].push((t, q)) {
                    ticket = t;
                    query = q;
                } else {
                    return;
                }
            } else {
                return;
            }
        }
    }

    pub fn pop(&self, _id: usize) -> Option<(Z3Ticket, Box<Z3Query>)> {
        for i in 0..TASK_PRIO_MAX {
            if let Some((ticket, query)) = self.task_queues[i].pop() {
                return Some((ticket, query));
            }
        }
        None
    }

    pub fn drain(&mut self) {
        for i in 0..TASK_PRIO_MAX {
            while !self.task_queues[i].is_empty() {
                _ = self.task_queues[i].pop();
            }

            // self.task_counts[i].store(0, Ordering::SeqCst);
        }
    }
}

impl Default for TaskQ {
    fn default() -> Self {
        Self::new(1)
    }
}
