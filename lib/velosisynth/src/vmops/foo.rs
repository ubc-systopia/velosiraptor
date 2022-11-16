
    // fn add_check_for_precondition(
    //     &mut self,
    //     m_fn: &Method,
    //     progs: &mut Vec<Program>,
    // ) -> Vec<Z3Ticket> {
    //     for (_i, prog) in progs.drain(..).enumerate() {
    //         let (mut smt, symvars) = prog.to_smt2("map", m_fn.args.as_slice());

    //         let mut vars = vec![SortedVar::new(
    //             String::from("st!0"),
    //             String::from("Model_t"),
    //         )];
    //         for a in &m_fn.args {
    //             vars.push(SortedVar::new(
    //                 a.name.clone(),
    //                 types::type_to_smt2(&a.ptype),
    //             ));
    //         }

    //         let pre = Term::fn_apply(
    //             String::from("translate.assms"),
    //             vec![
    //                 Term::ident(String::from("st!0")),
    //                 Term::ident(String::from("va")),
    //             ],
    //         );

    //         let mut map_fn_args = vec![Term::ident(String::from("st!0"))];
    //         for v in m_fn.args.iter() {
    //             map_fn_args.push(Term::ident(v.name.clone()));
    //         }

    //         let check = Term::fn_apply(
    //             String::from("translate.pre"),
    //             vec![
    //                 Term::fn_apply(String::from("map"), map_fn_args),
    //                 Term::ident(String::from("va")),
    //             ],
    //         );

    //         let t = Term::forall(vars, pre.implies(check));

    //         smt.assert(t);
    //         smt.check_sat();

    //         symvars.add_get_values(&mut smt);

    //         let mut smtctx = Smt2Context::new();
    //         smtctx.subsection(String::from("Verification"));
    //         smtctx.level(smt);

    //         let mut query = Z3Query::from(smtctx);
    //         query.set_program(prog);

    //         match self.workerpool.submit_query(query) {
    //             Ok(t) => {
    //                 println!("Submitted query: {}", t);
    //             }
    //             Err(_e) => {
    //                 println!("Failed to submit query.");
    //             }
    //         }
    //     }
    //     Vec::new()
    // }

    // fn check_programs_translate(
    //     &mut self,
    //     m_fn: &Method,
    //     g_fn: &Method,
    //     mut progs: Vec<Program>,
    // ) -> Vec<Z3Ticket> {
    //     let mut tickets = Vec::new();
    //     for (_i, prog) in progs.drain(..).enumerate() {
    //         let (mut smt, symvars) = prog.to_smt2(&m_fn.name, m_fn.args.as_slice());

    //         let mut vars = vec![SortedVar::new(
    //             String::from("st!0"),
    //             String::from("Model_t"),
    //         )];

    //         for a in &m_fn.args {
    //             vars.push(SortedVar::new(
    //                 a.name.clone(),
    //                 types::type_to_smt2(&a.ptype),
    //             ));
    //         }

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in g_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }

    //         let pre1 = Term::fn_apply(format!("{}.assms", g_fn.name), assm_args);

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in m_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }
    //         let pre2 = Term::fn_apply(format!("{}.assms", m_fn.name), assm_args);

    //         let pre = Term::land(pre1, pre2);

    //         let mut fn_args = vec![Term::ident(String::from("st!0"))];
    //         for v in m_fn.args.iter() {
    //             fn_args.push(Term::ident(v.name.clone()));
    //         }

    //         let mut check_args = vec![Term::fn_apply(m_fn.name.clone(), fn_args)];
    //         for a in m_fn.args.iter() {
    //             check_args.push(Term::ident(a.name.clone()));
    //         }

    //         let check = Term::fn_apply(format!("{}.result.{}", g_fn.name, m_fn.name), check_args);

    //         let t = Term::forall(vars, pre.implies(check));

    //         smt.assert(t);
    //         smt.check_sat();

    //         symvars.add_get_values(&mut smt);

    //         let mut smtctx = Smt2Context::new();
    //         smtctx.subsection(String::from("Verification"));
    //         smtctx.level(smt);

    //         let mut query = Z3Query::from(smtctx);
    //         query.set_program(prog);

    //         let ticket = self
    //             .workerpool
    //             .submit_query(query)
    //             .expect("failed to submit query");

    //         tickets.push(ticket);
    //     }
    //     tickets
    // }

    // fn check_programs_matchflags(
    //     &mut self,
    //     m_fn: &Method,
    //     g_fn: &Method,
    //     mut progs: Vec<Program>,
    // ) -> Vec<Z3Ticket> {
    //     let mut tickets = Vec::new();
    //     for (_i, prog) in progs.drain(..).enumerate() {
    //         let (mut smt, symvars) = prog.to_smt2(&m_fn.name, m_fn.args.as_slice());

    //         let mut vars = vec![SortedVar::new(
    //             String::from("st!0"),
    //             String::from("Model_t"),
    //         )];

    //         for a in &m_fn.args {
    //             vars.push(SortedVar::new(
    //                 a.name.clone(),
    //                 types::type_to_smt2(&a.ptype),
    //             ));
    //         }

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in g_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }

    //         let pre1 = Term::fn_apply(format!("{}.assms", g_fn.name), assm_args);

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in m_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }
    //         let pre2 = Term::fn_apply(format!("{}.assms", m_fn.name), assm_args);

    //         let pre = Term::land(pre1, pre2);

    //         let mut fn_args = vec![Term::ident(String::from("st!0"))];
    //         for v in m_fn.args.iter() {
    //             fn_args.push(Term::ident(v.name.clone()));
    //         }

    //         let mut check_args = vec![Term::fn_apply(m_fn.name.clone(), fn_args)];
    //         for a in g_fn.args.iter() {
    //             check_args.push(Term::ident(a.name.clone()));
    //         }

    //         let check = Term::fn_apply(g_fn.name.to_string(), check_args);

    //         let t = Term::forall(vars, pre.implies(check));

    //         smt.assert(t);
    //         smt.check_sat();

    //         symvars.add_get_values(&mut smt);

    //         let mut smtctx = Smt2Context::new();
    //         smtctx.subsection(String::from("Verification"));
    //         smtctx.level(smt);

    //         let mut query = Z3Query::from(smtctx);
    //         query.set_program(prog);

    //         let ticket = self
    //             .workerpool
    //             .submit_query(query)
    //             .expect("failed to submit query");

    //         tickets.push(ticket);
    //     }
    //     tickets
    // }

    // fn check_programs_protect(
    //     &mut self,
    //     p_fn: &Method,
    //     f_fn: &Method,
    //     t_fn: &Method,
    //     mut progs: Vec<Program>,
    // ) -> Vec<Z3Ticket> {
    //     let mut tickets = Vec::new();
    //     for (_i, prog) in progs.drain(..).enumerate() {
    //         let (mut smt, symvars) = prog.to_smt2(&p_fn.name, p_fn.args.as_slice());

    //         let mut vars = vec![SortedVar::new(
    //             String::from("st!0"),
    //             String::from("Model_t"),
    //         )];

    //         for a in &p_fn.args {
    //             vars.push(SortedVar::new(
    //                 a.name.clone(),
    //                 types::type_to_smt2(&a.ptype),
    //             ));
    //         }

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in f_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }

    //         let pre1 = Term::fn_apply(format!("{}.assms", t_fn.name), assm_args);

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in f_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }
    //         let pre2 = Term::fn_apply(format!("{}.assms", f_fn.name), assm_args);

    //         let pre = Term::land(pre1, pre2);

    //         let mut fn_args = vec![Term::ident(String::from("st!0"))];
    //         for v in p_fn.args.iter() {
    //             fn_args.push(Term::ident(v.name.clone()));
    //         }

    //         let mut check_args = vec![Term::fn_apply(p_fn.name.clone(), fn_args)];
    //         for a in f_fn.args.iter() {
    //             check_args.push(Term::ident(a.name.clone()));
    //         }

    //         let mut fn_args = vec![Term::ident(String::from("st!0"))];

    //         //  ((st!0 Model_t) (st!1 Model_t) (va VAddr_t) (sz Size_t)) Bool
    //         for v in p_fn.args.iter() {
    //             fn_args.push(Term::ident(v.name.clone()));
    //         }
    //         let mut t_fn_check_args = vec![
    //             Term::ident(String::from("st!0")),
    //             Term::fn_apply(p_fn.name.clone(), fn_args),
    //         ];
    //         t_fn_check_args.push(Term::ident("va".to_string()));
    //         t_fn_check_args.push(Term::ident("sz".to_string()));

    //         // for a in t_fn.args.iter() {
    //         //     t_fn_check_args.push(Term::ident(a.name.clone()));
    //         // }

    //         let check = Term::land(
    //             Term::fn_apply(f_fn.name.to_string(), check_args),
    //             Term::fn_apply(format!("{}.result.protect", t_fn.name), t_fn_check_args),
    //         );

    //         let t = Term::forall(vars, pre.implies(check));

    //         smt.assert(t);
    //         smt.check_sat();

    //         symvars.add_get_values(&mut smt);

    //         let mut smtctx = Smt2Context::new();
    //         smtctx.subsection(String::from("Verification"));
    //         smtctx.level(smt);

    //         let mut query = Z3Query::from(smtctx);
    //         query.set_program(prog);

    //         let ticket = self
    //             .workerpool
    //             .submit_query(query)
    //             .expect("failed to submit query");

    //         tickets.push(ticket);
    //     }
    //     tickets
    // }

    // fn obtain_sat_results(&mut self, mut fn_tickets: Vec<Vec<Z3Ticket>>) -> Vec<Vec<Z3Result>> {
    //     let mut fn_results = Vec::new();
    //     for tickets in fn_tickets.drain(..) {
    //         let mut results = Vec::new();
    //         for t in tickets {
    //             let mut res = self.workerpool.wait_for_result(t);

    //             // res.print_timestamps();

    //             let output = res.result();

    //             let mut reslines = output.lines();
    //             if Some("sat") == reslines.next() {
    //                 if reslines.next().is_some() {
    //                     match resultparser::parse_result(&output[4..]) {
    //                         Ok(mut vars) => {
    //                             if !vars.is_empty() {
    //                                 // println!("rewriting the program: {:?}\n", vars);
    //                                 res.query_mut()
    //                                     .program_mut()
    //                                     .replace_symbolic_values(&mut vars);
    //                             }
    //                         }
    //                         Err(_e) => (),
    //                     }
    //                 }
    //                 results.push(res);
    //             }
    //         }
    //         if results.is_empty() {
    //             println!("no sat program");
    //         }
    //         fn_results.push(results);
    //     }
    //     fn_results
    // }
