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

//! State Synthesis Module: Rosette

// rosette language library imports
use rosettelang::{BVOp, FunctionDef, RExpr, RosetteFile};

// crate imports
use super::expr;
use crate::ast::{Method, Segment};

fn add_check_matchflags(rkt: &mut RosetteFile, m: &Method) {
    rkt.add_section(String::from("Correctness Property"));

    // add assumes clauses for va, pa, size, flags
    // w.r.t: sizes, alignments, etc.
    // those can come from the requires clauses from the map method

    let mut body = Vec::new();
    for c in &m.requires {
        body.push(RExpr::assume(expr::expr_to_rosette(c)))
    }

    let args = m
        .args
        .iter()
        .map(|a| RExpr::var(a.name.clone()))
        .collect::<Vec<RExpr>>();

    body.push(RExpr::letstart(
        vec![
            (
                String::from("st0"),
                RExpr::fncall(String::from("make-model"), vec![]),
            ),
            (
                String::from("st1"),
                RExpr::fncall(
                    String::from("ast-interpret"),
                    vec![
                        RExpr::fncall(String::from("impl"), args),
                        RExpr::var(String::from("st0")),
                    ],
                ),
            ),
        ],
        vec![RExpr::assert(RExpr::fncall(
            String::from("matchflags"),
            vec![
                RExpr::var(String::from("st1")),
                //RExpr::var(String::from("va")),
                RExpr::var(String::from("flgs")),
            ],
        ))],
    ));

    let mut args = vec![String::from("impl")];
    args.extend(m.args.iter().map(|a| a.name.clone()));

    let fdef = FunctionDef::new(String::from("ast-check-translate"), args, body);

    rkt.add_function_def(fdef);
    // add a let expr
    //     (let ([st (make-model)])
    //     ; evaluate the implementation, update the state
    //     (set! st (ast-interpret (impl st va pa size flags) st))

    //     ; now check if the translation is right
    //     (assert (bveq (translate st va 0) pa))
    //   )
}

fn add_check_translate(rkt: &mut RosetteFile, m: &Method) {
    rkt.add_section(String::from("Correctness Property"));

    // add assumes clauses for va, pa, size, flags
    // w.r.t: sizes, alignments, etc.
    // those can come from the requires clauses from the map method

    let mut body = Vec::new();
    for c in &m.requires {
        body.push(RExpr::assume(expr::expr_to_rosette(c)))
    }

    let args = m
        .args
        .iter()
        .map(|a| RExpr::var(a.name.clone()))
        .collect::<Vec<RExpr>>();

    body.push(RExpr::letstart(
        vec![
            (
                String::from("st0"),
                RExpr::fncall(String::from("make-model"), vec![]),
            ),
            (
                String::from("st1"),
                RExpr::fncall(
                    String::from("ast-interpret"),
                    vec![
                        RExpr::fncall(String::from("impl"), args),
                        RExpr::var(String::from("st0")),
                    ],
                ),
            ),
        ],
        vec![
            RExpr::assert(RExpr::bveq(
                RExpr::fncall(
                    String::from("translate"),
                    vec![
                        RExpr::var(String::from("st1")),
                        RExpr::var(String::from("va")),
                        //RExpr::var(String::from("flags")),
                    ],
                ),
                RExpr::var(String::from("pa")),
            )),
            RExpr::assert(RExpr::bveq(
                RExpr::fncall(
                    String::from("translate"),
                    vec![
                        RExpr::var(String::from("st1")),
                        RExpr::bvsub(
                            RExpr::bvadd(
                                RExpr::var(String::from("va")),
                                RExpr::var(String::from("sz")),
                            ),
                            RExpr::num(64, 1),
                        ),
                        // RExpr::var(String::from("flags")),
                    ],
                ),
                RExpr::bvsub(
                    RExpr::bvadd(
                        RExpr::var(String::from("pa")),
                        RExpr::var(String::from("sz")),
                    ),
                    RExpr::num(64, 1),
                ),
            )),
        ],
    ));

    let mut args = vec![String::from("impl")];
    args.extend(m.args.iter().map(|a| a.name.clone()));

    let fdef = FunctionDef::new(String::from("ast-check-translate"), args, body);

    rkt.add_function_def(fdef);
    // add a let expr
    //     (let ([st (make-model)])
    //     ; evaluate the implementation, update the state
    //     (set! st (ast-interpret (impl st va pa size flags) st))

    //     ; now check if the translation is right
    //     (assert (bveq (translate st va 0) pa))
    //   )
}

fn add_synthesis_def(rkt: &mut RosetteFile, inmax: u64, outmax: u64) {
    rkt.add_section(String::from("Solving / Synthesis"));

    rkt.add_subsection(String::from("Symbolic Variables"));
    // TODO: check the types here?
    rkt.add_new_symbolic_var(String::from("va"), String::from("int?"));
    rkt.add_expr(RExpr::constraint(String::from("va"), BVOp::BVGe, 0));
    rkt.add_expr(RExpr::constraint(String::from("va"), BVOp::BVLt, inmax));

    rkt.add_new_symbolic_var(String::from("pa"), String::from("int?"));
    rkt.add_expr(RExpr::constraint(String::from("pa"), BVOp::BVGe, 0));
    rkt.add_expr(RExpr::constraint(String::from("pa"), BVOp::BVLt, outmax));

    rkt.add_new_symbolic_var(String::from("size"), String::from("int?"));
    rkt.add_expr(RExpr::constraint(String::from("size"), BVOp::BVGe, 0));
    rkt.add_expr(RExpr::constraint(String::from("size"), BVOp::BVLt, outmax));

    rkt.add_new_symbolic_var(String::from("flags"), String::from("int?"));

    // // the map function
    // let fname = String::from("do-synth-one");
    // let args = vec![
    //     String::from("va"),
    //     String::from("size"),
    //     String::from("flags"),
    //     String::from("pa"),
    // ];
    // let body = vec![RExpr::fncall(
    //     String::from("ast-grammar"),
    //     vec![
    //         RExpr::var(String::from("va")),
    //         RExpr::var(String::from("size")),
    //         RExpr::var(String::from("flags")),
    //         RExpr::var(String::from("pa")),
    //         RExpr::param(String::from("depth")),
    //         RExpr::var(String::from("1")),
    //     ],
    // )];

    for i in 1..10 {
        rkt.add_raw(format!(
            "
; interprets the grammar
(define (do-synth-{i} va size flags pa)
  (ast-grammar va size flags pa #:depth {i})
)
; the solution with depth {i}
(define sol-{i}
  (synthesize
    #:forall (list va size flags pa)
    #:guarantee (ast-check-translate do-synth-{i} va size flags pa)
  )
)

; check if we have a success
(if (sat? sol-{i}) [
  (my-print-forms sol-{i})
  (exit)
]
(printf \"\")
)
",
            i = i
        ))
    }

    rkt.add_raw(String::from("(printf \"No solution found!\")"));

    // let mut fdef = FunctionDef::new(fname, args, body);
    // fdef.add_comment(String::from("interprets the grammar"));
    // rkt.add_function_def(fdef);

    // let body = RExpr::fncall(
    //     String::from("synthesize"),
    //     vec![
    //         RExpr::param(String::from("forall")),
    //         RExpr::fncall(
    //             String::from("list"),
    //             vec![
    //                 RExpr::var(String::from("va")),
    //                 RExpr::var(String::from("size")),
    //                 RExpr::var(String::from("flags")),
    //                 RExpr::var(String::from("pa")),
    //             ],
    //         ),
    //         RExpr::param(String::from("guarantee")),
    //         RExpr::fncall(
    //             String::from("ast-check-translate"),
    //             vec![
    //                 RExpr::var(String::from("do-synth")),
    //                 RExpr::var(String::from("va")),
    //                 RExpr::var(String::from("size")),
    //                 RExpr::var(String::from("flags")),
    //                 RExpr::var(String::from("pa")),
    //             ],
    //         ),
    //     ],
    // );
    // let vdef = VarDef::new(String::from("sol-one"), body);
    // rkt.add_var(vdef);
}

fn add_print_sol(rkt: &mut RosetteFile) {
    rkt.add_raw(String::from(
        "
; Pretty-prints the result of (generate-forms sol).
(define (my-print-forms sol)
  (for ([f (generate-forms sol)])
    (for ([e (syntax->list f)])
      (let ([s  (format \"~a\" (syntax->datum e))])
        (if (string-prefix? s \"(Seq\")
          (printf \"~a\n\" s)
          (printf \"\")
        )
      )
    )
  )
)
",
    ))
}

pub fn add_synthesis(rkt: &mut RosetteFile, part: &str, unit: &Segment, m: &Method) {
    if part == "matchflags" {
        add_check_matchflags(rkt, m);
    } else {
        add_check_translate(rkt, m);
    }
    add_print_sol(rkt);

    println!("\nadding synthesis for {}", part);
    add_synthesis_def(rkt, unit.vaddr_max(), unit.paddr_max());
}
