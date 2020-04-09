use z3::ast::Ast;
use z3::*;

enum ConcolicType<'a> {
    Int(ConcolicInt<'a>),
    Bool(ConcolicBool<'a>)
}

#[derive(PartialEq, Debug)]
enum ArgType {
    Int(i32)
}

struct ConcolicInt <'a> {
    symbolic_value: z3::ast::Int<'a>,
}

struct ConcolicBool <'a> {
    symbolic_value : z3::ast::Bool<'a>,
}

impl<'a> ConcolicInt<'a> {
    fn New(ctx: &'a Context, value: i32 ) -> ConcolicInt<'a> {
        ConcolicInt { symbolic_value: ast::Int::from_i64(ctx, value as i64) }
    }

    fn NewConst(ctx: &'a Context, variable_name: &str, value: i32 ) -> ConcolicInt<'a> {
        ConcolicInt { symbolic_value: ast::Int::new_const(&ctx, variable_name) }
    }

    fn add (&self , input: &ConcolicInt<'a> ) -> ConcolicInt<'a> {
        ConcolicInt {
            symbolic_value: self.symbolic_value.add (&[&input.symbolic_value]),
        }
    }

    fn eq (&self, input: &ConcolicInt<'a> ) -> ConcolicBool<'a> {
        ConcolicBool {
            symbolic_value : self.symbolic_value._eq(&input.symbolic_value),
        }
    }

    fn mul(&self, input: &ConcolicInt<'a>) -> ConcolicInt <'a> {
        ConcolicInt {
            symbolic_value : self.symbolic_value.mul(&[&input.symbolic_value]),
        }
    }
}

impl<'a> ConcolicBool<'a> {
    fn not(&self) -> ConcolicBool<'a> {
        ConcolicBool {
            symbolic_value: self.symbolic_value.not(),
        }
    }

    fn and(&self, other: &[Self]) -> Self {
        let foo: Vec<&z3 :: ast :: Bool<'a>> = other.iter().map(|x| &x.symbolic_value).collect();
        let symbolic = self.symbolic_value.and(foo.as_slice());
        ConcolicBool {
            symbolic_value: symbolic
        }
    }
}

struct ConcolicMachine<'a> {
    ctx: &'a Context,
    variables: Vec<ConcolicType<'a>>,
    constraints_path: Vec<ConcolicBool<'a>>,
}

impl<'a> ConcolicMachine<'a> {
    fn concolic_find_input<'b>(&self, solver: &z3::Solver, constraint: &ConcolicBool<'a>) -> Vec<ArgType> {
        solver.push();
        solver.assert(&constraint.symbolic_value);

        let solver_result = solver.check();
        let mut results: Vec<ArgType> = Vec::new();

        if solver_result == SatResult::Sat {
            let sat_model = solver.get_model();

            for v in self.variables.iter() {
                match v {
                    ConcolicType::Int(concolic_int) => {
                        let result_value = sat_model.eval( &concolic_int.symbolic_value).unwrap().as_i64().unwrap();
                        results.push(ArgType::Int(result_value as i32));
                    },
                    _ => ()
                }
            }
        }

        solver.pop(1);
        return results;
    }

    fn generate_constraint<'b>(&self) -> ConcolicBool<'a> {
        let constraints = &self.constraints_path;
        let constraint_len = constraints.len();
        let last_constraint = constraints.last().unwrap();

        if constraint_len > 1 {
            constraints[0].and(&constraints[1..constraint_len-1]).and(&[last_constraint.not()])
        } else {
            constraints[0].not().not()
        }
    }

    fn execute_concolic<'b>(&self,
                            solver: &z3::Solver,
                            constraint: &ConcolicBool<'a>,
                            used_inputs: &'b Vec<Vec<ArgType>>,
                            inputs:&'b mut Vec<Vec<ArgType>>) {
        let new_input = self.concolic_find_input(&solver, &constraint);

        if new_input.len() > 0 {
            let input_already_saved = inputs.iter().any(|v| ((v[0] == new_input[0]) && (v[1] == new_input[1])));
            let input_already_used = used_inputs.iter().any(|v| ((v[0] == new_input[0]) && (v[1] == new_input[1])));

            if !input_already_saved && !input_already_used {
                inputs.push(new_input);
            }
        }
    }

    fn execute(&mut self, f: &dyn Fn(&'a Context, & mut Vec<ConcolicBool<'a>>, & mut Vec<ConcolicType<'a>>, & Vec<ArgType>)) {
        let solver = Solver::new(&self.ctx);

        let mut concrete_input: Vec<ArgType> = Vec::new();
        concrete_input.push(ArgType::Int(2));
        concrete_input.push(ArgType::Int(2));
        f(&self.ctx, &mut self.constraints_path, &mut self.variables, &concrete_input);

        let concrete_constraint = self.generate_constraint();
        let concrete_input = self.concolic_find_input(&solver, &concrete_constraint);

        let mut inputs: Vec<Vec<ArgType>> = Vec::new();
        let mut used_inputs: Vec<Vec<ArgType>> = Vec::new();

        inputs.push(concrete_input);
        for iterations in 0..100 {
            self.constraints_path.clear();
            self.variables.clear();

            let current_input = inputs.pop().unwrap();
            f(&self.ctx, &mut self.constraints_path, &mut self.variables, &current_input);

            used_inputs.push(current_input);

            let constraint = self.generate_constraint();
            self.execute_concolic(&solver, &constraint, &used_inputs, &mut inputs);

            let neg_constraint = constraint.not();
            self.execute_concolic(&solver, &neg_constraint, &used_inputs, &mut inputs);
        }
    }
}

/*
  if 2 * x == y {
    if y == x + 10 {
      panic!
    }
  }
*/

fn concolic_test_me<'a>(ctx: &'a Context, constraints_path: & mut Vec<ConcolicBool<'a>>, variables: & mut Vec<ConcolicType<'a>>, input: & Vec<ArgType>) {
    let ArgType::Int(x) = input[0];
    let ArgType::Int(y) = input[1];
    let conc_x = ConcolicInt::NewConst(&ctx, "x", x);
    let conc_y = ConcolicInt::NewConst(&ctx, "y", y);

    if 2 * x == y {
        constraints_path.push(ConcolicInt::New(&ctx, 2).mul(&conc_x).eq(&conc_y));
        if y == x + 10 {
            constraints_path.push(conc_y.eq(&conc_x.add(&ConcolicInt::New(&ctx,10))));
            panic!("this is a terrible mistake!");
        } else {
            constraints_path.push(conc_y.eq(&conc_x.add(&ConcolicInt::New(&ctx,10))).not());
        }
    } else {
        constraints_path.push(ConcolicInt::New(&ctx, 2).mul(&conc_x).eq(&conc_y).not());
    }

    variables.push(ConcolicType::Int(conc_x));
    variables.push(ConcolicType::Int(conc_y));
}

fn main() {
    let cfg = Config::new();
    let mut conc_machine = ConcolicMachine {
        ctx: &Context::new(&cfg),
        variables: Vec::new(),
        constraints_path: Vec::new()
    };

    conc_machine.execute(&concolic_test_me);
}
