use z3::ast::Ast;
use z3::*;

struct ConcolicInt <'a> {
    value : i32 ,
    symbolic_value : z3::ast::Int<'a> ,
}

struct ConcolicBool <'a> {
    value : bool ,
    symbolic_value : z3 :: ast :: Bool<'a> ,
}

impl<'a> ConcolicInt<'a> {
    fn New(ctx: &'a Context, value: i32 ) -> ConcolicInt<'a> {
        ConcolicInt { value : value , symbolic_value : ast :: Int :: from_i64 (ctx , value as i64) }
    }

    fn NewConst(ctx: &'a Context, variable_name: &str, value: i32 ) -> ConcolicInt<'a> {
        ConcolicInt { value : value , symbolic_value : ast::Int::new_const(&ctx, variable_name) }
    }

    fn add ( & self , input : &ConcolicInt<'a> ) -> ConcolicInt <'a> {
        ConcolicInt {
            value : self . value + input . value ,
            symbolic_value : self . symbolic_value . add ( &[&input . symbolic_value] ) ,
        }
    }

    fn eq ( & self , input : &ConcolicInt<'a> ) -> ConcolicBool<'a> {
        ConcolicBool {
            value : self . value == input . value ,
            symbolic_value : self . symbolic_value . _eq ( &input . symbolic_value ) ,
        }
    }

    fn mul(&self, input: &ConcolicInt<'a>) -> ConcolicInt <'a> {
        ConcolicInt {
            value : self . value * input . value ,
            symbolic_value : self . symbolic_value . mul ( &[&input . symbolic_value] ) ,
        }
    }
}

impl<'a> ConcolicBool<'a> {
    fn not(&self) -> ConcolicBool<'a> {
        ConcolicBool {
            value : self . value,
            symbolic_value : self . symbolic_value . not (),
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

    // println!("{:?}", constraint.symbolic_value);
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
  if 2 * x == y:
    if y == x + 10:
      assert False
*/

fn test_me<'a, 'b>(ctx: &'a Context, currPathConstrsGlobal: &'b mut Vec<ConcolicBool<'a>>, variables: &'b mut Vec<ConcolicInt<'a>>, x : i32 , y : i32 ) {
    let conc_x = ConcolicInt::NewConst(&ctx, "x", x); //ConcolicInt::New ( &ctx, y ) ;
    let conc_y = ConcolicInt::NewConst(&ctx, "y", y);//ConcolicInt::New ( &ctx, x ) ;

    if ConcolicInt::New(&ctx, 2).mul(&conc_x).eq(&conc_y).value {
        currPathConstrsGlobal.push(ConcolicInt::New(&ctx, 2).mul(&conc_x).eq(&conc_y));
        if conc_y.eq(&conc_x.add(&ConcolicInt::New(&ctx,10))).value {
            currPathConstrsGlobal.push(conc_y.eq(&conc_x.add(&ConcolicInt::New(&ctx,10))));
            panic!("this is a terrible mistake!");
        } else {
            currPathConstrsGlobal.push(conc_y.eq(&conc_x.add(&ConcolicInt::New(&ctx,10))).not());
        }
    } else {
        currPathConstrsGlobal.push(ConcolicInt::New(&ctx, 2).mul(&conc_x).eq(&conc_y).not());
    }

    variables.push(conc_x);
    variables.push(conc_y);
}

fn main() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    let mut currPathConstrsGlobal: Vec<ConcolicBool> = Vec::new();
    let mut concolic_variables: Vec<ConcolicInt> = Vec::new();

    test_me(&ctx, &mut currPathConstrsGlobal, &mut concolic_variables, 2, 2);
    let concrete_input = concolic_find_input(&solver, &currPathConstrsGlobal.pop().unwrap(), &concolic_variables);
    let mut inputs: Vec<Vec<i32>> = Vec::new();
    let mut used_inputs: Vec<Vec<i32>> = Vec::new();

    inputs.push(concrete_input);

    for iterations in 0..100 {
        currPathConstrsGlobal.clear();
        concolic_variables.clear();

        let bar = inputs.pop().unwrap();
        test_me(&ctx, &mut currPathConstrsGlobal, &mut concolic_variables, bar[0], bar[1]);

        used_inputs.push(bar);

        let constraint_len = currPathConstrsGlobal.len();
        let last_constraint = currPathConstrsGlobal.last().unwrap();

        let constraint =
            if constraint_len > 1 {
                currPathConstrsGlobal[0].and(&currPathConstrsGlobal[1..constraint_len-1]).and(&[last_constraint.not()])
            } else {
                currPathConstrsGlobal[0].not().not()
            };
        let temp_input = concolic_find_input(&solver, &constraint, &concolic_variables);

        if temp_input.len() > 0 {
            let foo = inputs.iter().any(|v| ((v[0] == temp_input[0]) && (v[1] == temp_input[1])));
            let foo_used = used_inputs.iter().any(|v| ((v[0] == temp_input[0]) && (v[1] == temp_input[1])));

            if !foo && !foo_used {
                inputs.push(temp_input);
            }
        }

        let neg_constraint =
            if constraint_len > 1 {
                currPathConstrsGlobal[0].and(&currPathConstrsGlobal[1..constraint_len-1]).and(&[last_constraint.not()]).not()
            } else {
                currPathConstrsGlobal[0].not()
            };


        let temp_input2 = concolic_find_input(&solver, &neg_constraint, &concolic_variables);
        let foo2 = inputs.iter().any(|v| ((v[0] == temp_input2[0]) && (v[1] == temp_input2[1])));
        let foo2_used = used_inputs.iter().any(|v| ((v[0] == temp_input2[0]) && (v[1] == temp_input2[1])));


        if !foo2 && !foo2_used{
            inputs.push(temp_input2);
        }
    }
}