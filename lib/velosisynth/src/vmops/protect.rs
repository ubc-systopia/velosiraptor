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

//! Synthesis of Virtual Memory Operations: Protect



fn add_synth_protect_tasks(&mut self, unit: &mut Segment) -> Vec<Vec<Vec<Z3Ticket>>> {
    // get the map functions
    let p_fn = unit.get_method("protect").unwrap();
    // get the translate function
    let t_fn = unit.get_method("translate").unwrap();
    // get the translate function
    let f_fn = unit.get_method("matchflags").unwrap();

    // --------------------------------------------------------------------------------------
    // Check whether the pre-conditions can be satisfied
    // --------------------------------------------------------------------------------------

    self.check_precondition_satisfiability(p_fn, t_fn, f_fn);

    // --------------------------------------------------------------------------------------
    // Matchflags: check the expression result
    // --------------------------------------------------------------------------------------
    // TODO: that on here might be memoised...

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
        self.check_programs_protect(p_fn, f_fn, t_fn, progs)
    };

    vec![vec![mf_res_tickets]]

    // change permissions
    //   post: matchflags(s') && translate(s') == translate(s)
}


fn check_synth_protect_tasks(
    &mut self,
    unit: &mut Segment,
    mut tickets: Vec<Vec<Vec<Z3Ticket>>>,
) {
    // get the map functions
    let p_fn = unit.get_method("protect").unwrap();
    // get the translate function
    let t_fn = unit.get_method("translate").unwrap();
    // get the translate function
    let f_fn = unit.get_method("matchflags").unwrap();

    let results = tickets
        .drain(..)
        .flat_map(|t| self.obtain_sat_results(t))
        .collect::<Vec<_>>();

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

        let p_tickets = self.check_programs_protect(p_fn, f_fn, t_fn, vec![prog.clone()]);

        let mut all_sat = true;
        for t in p_tickets {
            let res = self.workerpool.wait_for_result(t);
            let mut reslines = res.result().lines();
            all_sat &= reslines.next() == Some("sat");
        }
        if all_sat {
            println!("found candidate program: {:?}", prog);
            unit.protect_ops = Some(prog.into());
            return;
        }
    }
    println!("no candidate program found");
}