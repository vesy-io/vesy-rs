use z3::ast::Ast;
use z3::*;

struct ConcolicInt <'a> {
    value : i32,
    symbolic_value : z3::ast::Int<'a>,
}

struct ConcolicBool <'a> {
    value : bool,
    symbolic_value : z3 :: ast :: Bool<'a>,
}

impl<'a> ConcolicInt<'a> {
    fn New(ctx: &'a Context, value: i32 ) -> ConcolicInt<'a> {
        ConcolicInt { value: value , symbolic_value: ast::Int::from_i64 (ctx , value as i64) }
    }

    fn NewConst(ctx: &'a Context, variable_name: &str, value: i32 ) -> ConcolicInt<'a> {
        ConcolicInt { value: value , symbolic_value: ast::Int::new_const(&ctx, variable_name) }
    }

    fn add (&self , input: &ConcolicInt<'a> ) -> ConcolicInt<'a> {
        ConcolicInt {
            value: self.value + input.value,
            symbolic_value: self.symbolic_value.add (&[&input.symbolic_value]),
        }
    }

    fn eq (&self, input: &ConcolicInt<'a> ) -> ConcolicBool<'a> {
        ConcolicBool {
            value : self.value == input.value,
            symbolic_value : self.symbolic_value._eq(&input.symbolic_value),
        }
    }

    fn mul(&self, input: &ConcolicInt<'a>) -> ConcolicInt <'a> {
        ConcolicInt {
            value : self.value * input.value,
            symbolic_value : self.symbolic_value.mul(&[&input.symbolic_value]),
        }
    }
}

impl<'a> ConcolicBool<'a> {
    fn not(&self) -> ConcolicBool<'a> {
        ConcolicBool {
            value : self.value,
            symbolic_value: self.symbolic_value.not(),
        }
    }

    fn and(&self, other: &[Self]) -> Self {
        let foo: Vec<&z3 :: ast :: Bool<'a>> = other.iter().map(|x| &x.symbolic_value).collect();
        let symbolic = self.symbolic_value.and(foo.as_slice());
        ConcolicBool {
            value: self.value,
            symbolic_value: symbolic
        }
    }
}

fn concolic_find_input<'ctx, 'a>(solver: &z3::Solver, constraint: &ConcolicBool<'ctx>, variables: &'a Vec<ConcolicInt<'ctx>>) -> Vec<i32> {
    solver.push();
    solver.assert(&constraint.symbolic_value);

    let solver_result = solver.check();
    let mut results: Vec<i32> = Vec::new();

    if solver_result == SatResult::Sat {
        let sat_model = solver.get_model();

        for v in variables.into_iter() {
            let result_value = sat_model.eval(&v.symbolic_value).unwrap().as_i64().unwrap();
            results.push(result_value as i32);
        }
    }

    solver.pop(1);
    return results;
}

/*
  if 2 * x == y {
    if y == x + 10 {
      panic!
    }
  }
*/

fn test_me<'a, 'b>(ctx: &'a Context, constraints_path: &'b mut Vec<ConcolicBool<'a>>, variables: &'b mut Vec<ConcolicInt<'a>>, x: i32 , y: i32) {
    let conc_x = ConcolicInt::NewConst(&ctx, "x", x);
    let conc_y = ConcolicInt::NewConst(&ctx, "y", y);

    if ConcolicInt::New(&ctx, 2).mul(&conc_x).eq(&conc_y).value {
        constraints_path.push(ConcolicInt::New(&ctx, 2).mul(&conc_x).eq(&conc_y));
        if conc_y.eq(&conc_x.add(&ConcolicInt::New(&ctx,10))).value {
            constraints_path.push(conc_y.eq(&conc_x.add(&ConcolicInt::New(&ctx,10))));
            panic!("this is a terrible mistake!");
        } else {
            constraints_path.push(conc_y.eq(&conc_x.add(&ConcolicInt::New(&ctx,10))).not());
        }
    } else {
        constraints_path.push(ConcolicInt::New(&ctx, 2).mul(&conc_x).eq(&conc_y).not());
    }

    variables.push(conc_x);
    variables.push(conc_y);
}

fn generate_constraint<'a, 'b>(constraints: &'b Vec<ConcolicBool<'a>>) -> ConcolicBool<'a> {
    let constraint_len = constraints.len();
    let last_constraint = constraints.last().unwrap();

    if constraint_len > 1 {
        constraints[0].and(&constraints[1..constraint_len-1]).and(&[last_constraint.not()])
    } else {
        constraints[0].not().not()
    }
}

fn execute_concolic<'a, 'b>(solver: &z3::Solver,
                            constraint: &ConcolicBool<'a>,
                            concolic_variables: &'b Vec<ConcolicInt<'a>>,
                            used_inputs: &'b Vec<Vec<i32>>,
                            inputs:&'b mut Vec<Vec<i32>>) {
    let new_input = concolic_find_input(&solver, &constraint, &concolic_variables);

    if new_input.len() > 0 {
        let input_already_saved = inputs.iter().any(|v| ((v[0] == new_input[0]) && (v[1] == new_input[1])));
        let input_already_used = used_inputs.iter().any(|v| ((v[0] == new_input[0]) && (v[1] == new_input[1])));

        if !input_already_saved && !input_already_used {
            inputs.push(new_input);
        }
    }
}

fn main() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    let mut constraints_path: Vec<ConcolicBool> = Vec::new();
    let mut concolic_variables: Vec<ConcolicInt> = Vec::new();

    test_me(&ctx, &mut constraints_path, &mut concolic_variables, 2, 2);
    let concrete_input = concolic_find_input(&solver, &constraints_path.pop().unwrap(), &concolic_variables);
    let mut inputs: Vec<Vec<i32>> = Vec::new();
    let mut used_inputs: Vec<Vec<i32>> = Vec::new();

    inputs.push(concrete_input);

    for iterations in 0..100 {
        constraints_path.clear();
        concolic_variables.clear();

        let current_input = inputs.pop().unwrap();
        test_me(&ctx, &mut constraints_path, &mut concolic_variables, current_input[0], current_input[1]);

        used_inputs.push(current_input);

        let constraint= generate_constraint(&constraints_path);
        execute_concolic(&solver, &constraint, &concolic_variables, &used_inputs, &mut inputs);

        let neg_constraint = constraint.not();
        execute_concolic(&solver, &neg_constraint, &concolic_variables, &used_inputs, &mut inputs);
    }
}