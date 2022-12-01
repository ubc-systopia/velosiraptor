// Velosiraptor Code Generator
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

//! Rust Code Generation Backend

// https://doc.rust-lang.org/std/primitive.pointer.html#method.as_ref
// https://doc.rust-lang.org/alloc/boxed/struct.Box.html#method.into_raw
// https://doc.rust-lang.org/alloc/boxed/struct.Box.html#method.from_raw

// // in memory state
// #[repr(C)]
// struct Unit {
//     // for the in
//     field: Field,
// }

// struct PageTable {
//     entries: Box<[Unit; 512]>
//  }

// // register state
// struct Unit {
//     base: *mut ptr;
// }

// // special register state
// struct Unit {}

// // cpu register state
// struct Unit {}

// //

// impl Unit {
//     // for each field:
//     fn field_rd() {
//         readmem(dst, offet, value);
//         readmmio(dst, offset, value);

//         readreg(reg, value)
//     }

//     fn field_wr(&mut self, val : Field) {
//         writemem(dst, offet, value);

//         writemmio(dst, offset, value);

//         writereg(reg, value)
//     }

//     // maybe there are some "instructions"
//     fn instr() {

//     }
// }

// struct PageTableEntry {
//     pte: PteField,
// }

// struct PageTable {
//     pagetable : [PageTableEntry; 512]
// }
