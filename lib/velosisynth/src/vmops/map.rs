// Velosiraptor Synthesizer
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! Synthesis of Virtual Memory Operations: Map




fn add_synth_map_tasks(&mut self, unit: &mut Segment) -> Vec<Vec<Vec<Z3Ticket>>> {
    // get the map functions
    let m_fn = unit.get_method("map").unwrap();
    // get the translate function
    let t_fn = unit.get_method("translate").unwrap();
    // get the translate function
    let f_fn = unit.get_method("matchflags").unwrap();

    // --------------------------------------------------------------------------------------
    // Check whether the pre-conditions can be satisfied
    // --------------------------------------------------------------------------------------

    let t_start = Instant::now();
    self.check_precondition_satisfiability(m_fn, t_fn, f_fn);
    let now = Instant::now();
    let diff = now.saturating_duration_since(t_start);
    println!("map: precond satisfy, {:7}, us  ", diff.as_micros());

    // --------------------------------------------------------------------------------------
    // Translate: Add a query for each of the pre-conditions of the function
    // --------------------------------------------------------------------------------------

    let mut t_fn_tickets = Vec::new();

    for (i, pre) in t_fn
        .requires
        .iter()
        .filter(|p| p.has_state_references())
        .enumerate()
    {
        let state_syms = pre.get_state_references();

        let state_bits = unit.state.referenced_field_bits(&state_syms);
        let st_access_fields = unit
            .interface
            .fields_accessing_state(&state_syms, &state_bits);

        // construct the program builder
        let mut builder = operations::ProgramsBuilder::new();
        for v in m_fn.args.iter() {
            builder.add_var(v.name.clone());
        }

        for f in st_access_fields.iter() {
            let mut parts = f.split('.');
            let _ = parts.next();
            let field = parts.next().unwrap();
            if let Some(slice) = parts.next() {
                builder.add_field_slice(field, slice);
            } else {
                //builder.add_field(field);
            }
        }

        let progs = builder.construct_programs(false);

        let tickets = self.check_programs_precond(m_fn, t_fn, Some(i), false, progs);
        t_fn_tickets.push(tickets);

        // let _progs = builder.construct_programs(true);

        // TODO: construct the task
    }

    let now = Instant::now();
    let diff = now.saturating_duration_since(t_start);
    println!("map: tfn precond, {:7}, us  ", diff.as_micros());

    // --------------------------------------------------------------------------------------
    // Matchflags: Add a query for each of the pre-conditions of the function
    // --------------------------------------------------------------------------------------

    let mut f_fn_tickets = Vec::new();
    for (i, pre) in f_fn
        .requires
        .iter()
        .filter(|p| p.has_state_references())
        .enumerate()
    {
        let state_syms = pre.get_state_references();

        let state_bits = unit.state.referenced_field_bits(&state_syms);
        let st_access_fields = unit
            .interface
            .fields_accessing_state(&state_syms, &state_bits);

        // construct the program builder
        let mut builder = operations::ProgramsBuilder::new();
        for v in m_fn.args.iter() {
            builder.add_var(v.name.clone());
        }

        for f in st_access_fields.iter() {
            let mut parts = f.split('.');
            let _ = parts.next();
            let field = parts.next().unwrap();
            let slice = parts.next().unwrap();

            builder.add_field_slice(field, slice);
        }

        let progs = builder.construct_programs(false);

        let tickets = self.check_programs_precond(m_fn, f_fn, Some(i), false, progs);
        f_fn_tickets.push(tickets);

        // let progs = builder.construct_programs(true);

        // TODO: construct the task
    }
    let now = Instant::now();
    let diff = now.saturating_duration_since(t_start);
    println!("map: ffn precond, {:7}, us  ", diff.as_micros());

    // --------------------------------------------------------------------------------------
    // Translate: check translation result
    // --------------------------------------------------------------------------------------

    let tr_res_tickets = {
        let state_syms = t_fn.get_state_references_body();
        let state_bits = unit.state.referenced_field_bits(&state_syms);
        let st_access_fields = unit
            .interface
            .fields_accessing_state(&state_syms, &state_bits);

        // construct the program builder
        let mut builder = operations::ProgramsBuilder::new();
        for v in m_fn.args.iter() {
            builder.add_var(v.name.clone());
        }

        for f in st_access_fields.iter() {
            let mut parts = f.split('.');
            let _ = parts.next();
            let field = parts.next().unwrap();
            let slice = parts.next().unwrap();

            builder.add_field_slice(field, slice);
        }

        let progs = builder.construct_programs(true);
        self.check_programs_translate(m_fn, t_fn, progs)
    };

    let now = Instant::now();
    let diff = now.saturating_duration_since(t_start);
    println!("map: translate, {:7}, us  ", diff.as_micros());

    // --------------------------------------------------------------------------------------
    // Matchflags: check the expression result
    // --------------------------------------------------------------------------------------

    let mf_res_tickets = {
        let state_syms = f_fn.get_state_references_body();
        let state_bits = unit.state.referenced_field_bits(&state_syms);
        let st_access_fields = unit
            .interface
            .fields_accessing_state(&state_syms, &state_bits);

        // construct the program builder
        let mut builder = operations::ProgramsBuilder::new();
        for v in f_fn.args.iter() {
            if v.ptype == Type::Flags {
                if let Some(flags) = &unit.flags {
                    let var = Arc::new(v.name.clone());
                    for f in flags.flags.iter() {
                        builder.add_flags(var.clone(), f.name.clone());
                    }
                }
            } else {
                builder.add_var(v.name.clone());
            }
        }

        for f in st_access_fields.iter() {
            let mut parts = f.split('.');
            let _ = parts.next();
            let field = parts.next().unwrap();
            let slice = parts.next().unwrap();
            builder.add_field_slice(field, slice);
        }

        let progs = builder.construct_programs(true);
        self.check_programs_matchflags(m_fn, f_fn, progs)
    };

    let now = Instant::now();
    let diff = now.saturating_duration_since(t_start);
    println!("map: matchflags, {:7}, us  ", diff.as_micros());

    vec![
        t_fn_tickets,
        f_fn_tickets,
        vec![tr_res_tickets],
        vec![mf_res_tickets],
    ]
}

fn check_synth_map_tasks(&mut self, unit: &mut Segment, mut tickets: Vec<Vec<Vec<Z3Ticket>>>) {
    // get the map functions
    let m_fn = unit.get_method("map").unwrap();
    // get the translate function
    let t_fn = unit.get_method("translate").unwrap();
    // get the translate function
    let f_fn = unit.get_method("matchflags").unwrap();

    let results = Arc::new(
        tickets
            .drain(..)
            .flat_map(|t| self.obtain_sat_results(t))
            .collect::<Vec<_>>(),
    );

    // the completed candidate program
    let mut candidate_programs: Vec<Vec<&Program>> = vec![Vec::new()];

    for res in results.iter() {
        // new candidate programs
        let mut new_candidate_programs = Vec::new();

        for prog in candidate_programs {
            for r in res {
                // expand all candidate programs with the new program
                let mut new_prog = prog.clone();
                new_prog.push(r.query().program().unwrap());
                new_candidate_programs.push(new_prog);
            }
        }

        // update the candidate programs
        candidate_programs = new_candidate_programs;
    }

    let mut candidate_programs: Vec<Program> = candidate_programs
        .iter_mut()
        .map(|p| p.iter_mut().fold(Program::new(), |acc, x| acc.merge(x)))
        .collect();

    for prog in candidate_programs.drain(..) {
        println!("checking: {:?}", prog);
        let mut p_tickets =
            self.check_programs_precond(m_fn, f_fn, None, false, vec![prog.clone()]);
        p_tickets.extend(self.check_programs_precond(
            m_fn,
            t_fn,
            None,
            false,
            vec![prog.clone()],
        ));
        p_tickets.extend(self.check_programs_translate(m_fn, t_fn, vec![prog.clone()]));
        p_tickets.extend(self.check_programs_matchflags(m_fn, f_fn, vec![prog.clone()]));

        let mut all_sat = true;
        for t in p_tickets {
            let res = self.workerpool.wait_for_result(t);
            let mut reslines = res.result().lines();
            all_sat &= reslines.next() == Some("sat");
        }

        if all_sat {
            println!("found candidate program: {:?}", prog);
            unit.map_ops = Some(prog.into());
            return;
        }
    }
    println!("no candidate program found");
}
