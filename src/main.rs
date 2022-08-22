use std::rc::Rc;

#[derive(PartialEq, Eq, Debug)]
enum Node {
    Int(i32),
    Cons(RNode, RNode),
    Symbol(String),
}

macro_rules! parse {
    (($hd:tt)) => {
        Rc::new(Node::Cons(parse!($hd), parse!(nil)))
    };
    (($hd:tt $($tl:tt)+ )) => {
        Rc::new(Node::Cons(parse!($hd), parse!(($($tl)+))))
    };
    ($int:literal) => {
        Rc::new(Node::Int($int))
    };
    ($sym:ident) => {
        Rc::new(Node::Symbol(stringify!($sym).into()))
    };
}

impl Node {
    fn int(&self) -> EvalRes<i32> {
        match self {
            Self::Int(i) => Ok(*i),
            _ => Err(EvalError::new_msg(Type, "not an int")),
        }
    }
    fn sym(&self) -> EvalRes<&str> {
        match self {
            Self::Symbol(sym) => Ok(sym),
            _ => Err(EvalError::new_msg(Type, "not a symbol")),
        }
    }
    fn nil(&self) -> EvalRes<()> {
        if self.is_nil() {
            Ok(())
        } else {
            Err(EvalError::new_msg(Type, "not nil"))
        }
    }
    fn head(&self) -> EvalResult {
        if let Self::Cons(head, _) = self {
            Ok(head.clone())
        } else {
            Err(EvalError::new_msg(Type, "not a list (head)"))
        }
    }
    fn tail(&self) -> EvalResult {
        if let Self::Cons(_, tail) = self {
            Ok(tail.clone())
        } else {
            Err(EvalError::new_msg(Type, "not a list (tail)"))
        }
    }
    fn is_sym(&self, sym: &str) -> bool {
        match self {
            Self::Symbol(s) => s == sym,
            _ => false,
        }
    }
    fn is_nil(&self) -> bool {
        self.is_sym("nil")
    }
    fn is_lambda(&self) -> bool {
        match self {
            Self::Cons(lambda, _) => lambda.is_sym("lambda"),
            _ => false,
        }
    }
    fn is_cons(&self) -> bool {
        matches!(self, Self::Cons(..))
    }
    fn is_def(&self) -> bool {
        match self {
            Self::Cons(def, _) => def.is_sym("def"),
            _ => false,
        }
    }

    fn args_contains(&self, arg: &str) -> EvalRes<bool> {
        if self.is_nil() {
            Ok(false)
        } else if self.head()?.is_sym(arg) {
            Ok(true)
        } else {
            self.tail()?.args_contains(arg)
        }
    }

    /// Beta reduction
    fn beta(node: RNode, var: &str, val: RNode) -> EvalResult {
        if node.is_lambda() {
            let formal_args = node.tail()?.head()?;
            if formal_args.args_contains(var)? {
                return Ok(node);
            }
        }
        Ok(match &*node {
            Self::Symbol(sym) if sym == var => val,
            Self::Cons(l, r) => Rc::new(Self::Cons(
                Self::beta(l.clone(), var, val.clone())?,
                Self::beta(r.clone(), var, val.clone())?,
            )),
            _ => node,
        })
    }
}

use std::fmt::{self, Display, Formatter};
impl Display for Node {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Int(int) => write!(f, "{int}"),
            Self::Cons(..) => {
                write!(f, "(")?;
                let mut val = self;
                let mut begun = false;
                while let Self::Cons(hd, tl) = val {
                    if begun {
                        write!(f, " ")?;
                    }
                    write!(f, "{hd}")?;
                    val = tl;
                    begun = true;
                }
                write!(f, ")")
            }
            Self::Symbol(sym) => write!(f, "{sym}"),
        }
    }
}

type RNode = Rc<Node>;
#[derive(Debug)]
enum ErrorKind {
    Lookup,
    Type,
    Shape,
}
use ErrorKind::*;
#[derive(Debug)]
struct EvalError {
    kind: ErrorKind,
    msg: Option<String>,
}

impl EvalError {
    fn new(kind: ErrorKind) -> Self {
        Self { kind, msg: None }
    }
    fn new_msg(kind: ErrorKind, msg: impl Into<String>) -> Self {
        Self {
            kind,
            msg: Some(msg.into()),
        }
    }
}

type EvalRes<T> = Result<T, EvalError>;
type EvalResult = EvalRes<RNode>;

fn lookup_pair(bind: RNode, var: &str) -> EvalResult {
    if bind.head()?.sym()? == var {
        bind.tail()
    } else {
        Err(EvalError::new(Lookup))
    }
}
fn lookup(env: RNode, var: &str) -> EvalResult {
    if env.is_nil() {
        Err(EvalError::new(Lookup))
    } else {
        lookup_pair(env.head()?, var).or_else(|_| lookup(env.tail()?, var))
    }
}

macro_rules! pop {
    ($node:ident) => {{
        let elem = $node.head()?;
        $node = $node.tail()?;
        elem
    }};
}
fn builtin_macro(name: &str, env: RNode, args: RNode) -> Option<EvalResult> {
    let cond = |mut args: RNode| {
        while !args.is_nil() {
            let mut branch = args.head()?;
            let condition = pop!(branch);
            let branch_code = pop!(branch);
            assert!(branch.is_nil());

            if !eval(env.clone(), condition)?.is_nil() {
                return Ok(branch_code);
            }

            args = args.tail()?;
        }
        Ok(parse!(nil))
    };

    let eval1 = |mut args: RNode| {
        let env = pop!(args);
        let expr = pop!(args);
        args.nil()?;
        eval(env, expr)
    };

    let handler: &dyn Fn(RNode) -> EvalResult = match name {
        "cond" => &cond,
        "eval" => &eval1,
        _ => return None,
    };

    let expanded = match handler(args) {
        Ok(o) => o,
        Err(e) => return Some(Err(e)),
    };
    Some(eval(env.clone(), expanded))
}
fn builtin_func(name: &str, env: RNode, mut args: RNode) -> Option<EvalResult> {
    fn evaluate_args(env: &RNode, args: RNode) -> EvalResult {
        if args.is_nil() {
            Ok(parse!(nil))
        } else {
            let arg = eval(env.clone(), args.head()?)?;
            let args = evaluate_args(env, args.tail()?)?;
            Ok(Rc::new(Node::Cons(arg, args)))
        }
    }
    args = match evaluate_args(&env, args) {
        Ok(a) => a,
        Err(e) => return Some(Err(e)),
    };
    let sum = |mut args: RNode| {
        let mut s = 0;
        while !args.is_nil() {
            s += pop!(args).int()?;
        }
        Ok(Rc::new(Node::Int(s)))
    };
    let prod = |mut args: RNode| {
        let mut p = 1;
        while !args.is_nil() {
            p *= pop!(args).int()?;
        }
        Ok(Rc::new(Node::Int(p)))
    };
    let lt = |mut args: RNode| {
        if args.is_nil() {
            Ok(Rc::new(Node::Int(1)))
        } else {
            let mut a = pop!(args).int()?;
            while !args.is_nil() {
                let x = pop!(args).int()?;
                if a >= x {
                    return Ok(parse!(nil));
                }
                a = x;
            }
            Ok(Rc::new(Node::Int(1)))
        }
    };
    let minus = |mut args: RNode| {
        let lhs = pop!(args).int()?;
        let rhs = pop!(args).int()?;
        args.nil()?;
        Ok(Rc::new(Node::Int(lhs - rhs)))
    };
    Some(match name {
        "sum" => sum(args),
        "prod" => prod(args),
        "lt" => lt(args),
        "minus" => minus(args),
        _ => return None,
    })
}
fn eval(env: RNode, value: RNode) -> EvalResult {
    fn inner(env: RNode, value: RNode) -> EvalResult {
        Ok(match &*value {
            _ if value.is_nil() || value.is_lambda() => value,
            Node::Int(_) => value,
            Node::Symbol(var) => lookup(env, var)?,
            Node::Cons(def, prog) if def.is_def() => {
                // get rid of def symbol
                let mut def = def.tail()?;

                let def_var = pop!(def);
                let def_val = pop!(def);
                def.nil()?;

                let def_val_eval = eval(env.clone(), def_val)?;
                let env = Rc::new(Node::Cons(Rc::new(Node::Cons(def_var, def_val_eval)), env));

                eval(env, prog.clone())?
            }
            Node::Cons(func, concrete_args) => {
                let mut concrete_args = concrete_args.clone();

                if let &Node::Symbol(..) = &**func {
                    if let Some(result) =
                        builtin_macro(func.sym()?, env.clone(), concrete_args.clone())
                    {
                        return result;
                    }
                    if let Some(result) =
                        builtin_func(func.sym()?, env.clone(), concrete_args.clone())
                    {
                        return result;
                    }
                }

                let func = eval(env.clone(), func.clone())?;

                if !func.is_lambda() {
                    concrete_args.nil()?;
                    return Ok(func);
                }

                // get rid of the preceding `lambda`
                let func = func.tail()?;

                let mut formal_args = func
                    .head()
                    .map_err(|_| EvalError::new_msg(Shape, "Malformed Formal Arguments"))?;
                let mut body = func
                    .tail()?
                    .head()
                    .map_err(|_| EvalError::new_msg(Shape, "Malformed Function Body"))?;

                while !formal_args.is_nil() {
                    let f_arg = pop!(formal_args);
                    let c_arg = eval(env.clone(), pop!(concrete_args))?;
                    body = Node::beta(body, f_arg.sym()?, c_arg)?;
                }

                concrete_args.nil()?;

                eval(env, body)?
            }
        })
    }
    let res = inner(env.clone(), value.clone());
    if res.is_err() {
        eprintln!("Failed to evaluate `{value}` in environment `{env}`");
    }
    res
}

macro_rules! test {
    ($res:tt = $($expr:tt)*) => {{
        let env = parse!(nil);
        let expr = parse!($($expr)*);
        let expected = parse!($res);
        let evaluated = eval(env, expr).unwrap();
        assert_eq!(expected, evaluated);
    }}
}

#[test]
fn simple_tests() {
    test!(42 = ((lambda (x) x) 42));
    test!(0 = (((lambda (x) x) (lambda (x) x)) 0));
    test!(69 = ((lambda (x y) y) 68 69));
    test!(68 = ((lambda (x y) x) 68 69));
    test!(1 = (
        cond
        (nil 2)
        (42 1)
    ));
    test!(10 = (sum 1 2 3 4));
    test!(24 = (prod 1 2 3 4));
    test!(43 = (sum 1 (sum 42)));
    test!(1 = ((lambda (x) ((lambda (x) x) x)) 1));
    test!(1 = (eval nil 1));
    test!(13 = (
        (def x 13)
        x
    ));
}

fn main() {
    let env = parse!(nil);
    let prog = parse!((
        (def t 1)
        (def and (lambda (a b) (cond (a b))))
        (def or (lambda (a b) (cond (a t) (b t))))
        (def not (lambda (x) (cond (x nil) (t t))))
        (def fib 
            (lambda (x) 
            (cond
                ((lt x 2) x)
                (t (sum 
                    (fib (minus x 1)) 
                    (fib (minus x 2))
                ))
            )
        ))
        (fib 20)
    ));
    println!("{}", eval(env, prog).unwrap());
}
