use std::rc::Rc;

#[derive(PartialEq, Eq, Debug)]
enum Node {
    Int(i32),
    Cons(RNode, RNode),
    Symbol(String),
}

macro_rules! parse {
    (()) => {
        parse!(nil)
    };
    (#$var:expr) => {
        $var
    };
    (($hd:tt)) => {
        Rc::new(Node::Cons(parse!($hd), parse!(nil)))
    };
    (($hd:tt #$var:tt $($tl:tt)*)) => {
        Rc::new(Node::Cons(parse!($hd), Rc::new(Node::Cons($var, parse!(($($tl)*))))))
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

#[derive(Clone)]
struct Trace {
    ctr: usize,
    depth: usize,
    trace: RNode,
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
            Self::Cons(lambda, _) => lambda.is_sym("lambda") || lambda.is_sym("lambdav"),
            _ => false,
        }
    }
    fn is_variadic(&self) -> bool {
        match self {
            Self::Cons(lambda, _) => lambda.is_sym("lambdav"),
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
    fn truncate(s: &RNode, len: usize) -> RNode {
        if len <= 1 {s.clone()} else {
        match &**s {
            Self::Cons(h, t) => Rc::new(Self::Cons(h.clone(), Self::truncate(t, len - 1))),
            _ => s.clone(),
        }
    }
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
        eprintln!("failed to look up `{var}`");
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

fn evaluate_args(env: &RNode, args: RNode, trace: &Trace) -> EvalResult {
    let mut walker = args;
    let mut rev_args = parse!(nil);

    while !walker.is_nil() {
        let arg = walker.head()?;
        rev_args = Rc::new(Node::Cons(arg, rev_args));
        walker = walker.tail()?;
    }

    let mut walker = rev_args;
    let mut eval_args = parse!(nil);

    while !walker.is_nil() {
        let arg = walker.head()?;
        let arg  = eval(env.clone(), arg, trace)?;
        eval_args = Rc::new(Node::Cons(arg, eval_args));
        walker = walker.tail()?;
    }

    Ok(eval_args)
}
fn builtin_func(name: &str, env: RNode, mut args: RNode, trace: &Trace) -> Option<EvalResult> {
    args = match evaluate_args(&env, args, trace) {
        Ok(a) => a,
        Err(e) => return Some(Err(e)),
    };
    let nilp = |mut args: RNode| {
        let x = pop!(args);
        args.nil()?;
        if x.is_nil() {
            Ok(parse!(1))
        } else {
            Ok(parse!(nil))
        }
    };
    let hd = |mut args: RNode| {
        let list = pop!(args);
        args.nil()?;
        list.head()
    };
    let tl = |mut args: RNode| {
        let list = pop!(args);
        args.nil()?;
        list.tail()
    };
    let cons = |mut args: RNode| {
        let head = pop!(args);
        let tail = pop!(args);
        args.nil()?;
        Ok(Rc::new(Node::Cons(head, tail)))
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
            Ok(parse!(1))
        } else {
            let mut a = pop!(args).int()?;
            while !args.is_nil() {
                let x = pop!(args).int()?;
                if a >= x {
                    return Ok(parse!(nil));
                }
                a = x;
            }
            Ok(parse!(1))
        }
    };
    let minus = |mut args: RNode| {
        let lhs = pop!(args).int()?;
        let rhs = pop!(args).int()?;
        args.nil()?;
        Ok(Rc::new(Node::Int(lhs - rhs)))
    };
    Some(match name {
        "hd" => hd(args),
        "tl" => tl(args),
        "nilp" => nilp(args),
        "cons" => cons(args),
        "list" => Ok(args),
        "sum" => sum(args),
        "prod" => prod(args),
        "lt" => lt(args),
        "minus" => minus(args),
        _ => return None,
    })
}

impl Trace {
    fn new(depth: usize) -> Self {
        Self {
            depth,
            trace: parse!(nil),
            ctr: 0,
        }
    }
    fn log(&self, value: &RNode) -> Self {
        if self.depth == 0 {
            return self.clone()
        }
        let mut ctr = self.ctr + 1;
        let mut trace = self.trace.clone();
        if ctr % self.depth == 0 {
            ctr = self.depth;
            trace = Node::truncate(&trace, self.depth);
        }
        trace = Rc::new(Node::Cons(value.clone(), trace));
        Self {
            ctr,trace, depth: self.depth
        }
    }
}

fn eval(mut env: RNode, mut value: RNode, trace: &Trace) -> EvalResult {
    let mut cloned_trace = trace.clone();

    
    'eval: loop {
        macro_rules! eval {
            ($env:expr, $value:expr) => {{
                env = $env;
                value = $value;
                continue 'eval;
            }}
        }

        cloned_trace = cloned_trace.log(&value);
        let trace = &cloned_trace;

        break Ok(match &*value {
            _ if value.is_nil() || value.is_lambda() => value,
            Node::Int(_) => value,
            Node::Symbol(var) => lookup(env, var)?,
            Node::Cons(def, prog) if def.is_def() => {
                // get rid of def symbol
                let mut def = def.tail()?;

                let def_var = pop!(def);
                let def_val = pop!(def);
                def.nil()?;

                let def_val_eval = eval(env.clone(), def_val, trace)?;
                let new_env = Rc::new(Node::Cons(Rc::new(Node::Cons(def_var, def_val_eval)), env));
                eval!(new_env, prog.clone())
            }
            Node::Cons(func, concrete_args) => {
                let mut concrete_args = concrete_args.clone();

                if let &Node::Symbol(..) = &**func {
                    let mut args = concrete_args.clone();
                    match func.sym()? {
                        "quote" => {
                            return args.head()
                        },
                        "cond" => {
                            while !args.is_nil() {
                                let mut branch = args.head()?;
                                let condition = pop!(branch);
                                let branch_code = pop!(branch);
                                branch.nil()?;

                                if !eval(env.clone(), condition, trace)?.is_nil() {
                                    eval!(env, branch_code);
                                }

                                args = args.tail()?;
                            }
                            return Ok(parse!(nil))
                        },
                        "eval" => {
                            let env = pop!(args);
                            let expr = pop!(args);
                            args.nil()?;
                            eval!(env, expr)
                        },
                        _ => (),
                    }
                    if let Some(result) =
                        builtin_func(func.sym()?, env.clone(), concrete_args.clone(), trace)
                    {
                        return result;
                    }
                }

                let func = eval(env.clone(), func.clone(), trace)?;

                if !func.is_lambda() {
                    concrete_args.nil()?;
                    return Ok(func);
                }

                // get rid of the preceding `lambda`
                let variadic = func.is_variadic();
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
                    let c_arg = if formal_args.is_nil() && variadic {
                        let args = evaluate_args(&env, concrete_args.clone(), trace)?;
                        concrete_args = parse!(nil);
                        args
                    } else {
                        eval(env.clone(), pop!(concrete_args), trace)? 
                    };
                    body = Node::beta(body, f_arg.sym()?, parse!((quote #c_arg)))?;
                }

                concrete_args.nil()?;
                eval!(env, body)
            }
        })
    }
}

macro_rules! test {
    ($name:ident : $res:tt = $($expr:tt)*) => {
        #[test]
        fn $name() {
            let env = parse!(nil);
            let expr = parse!($($expr)*);
            let expected = parse!($res);
            let evaluated = eval(env, expr, &Trace::new(0)).unwrap();
            assert_eq!(expected, evaluated);
        }
    }
}

test!(fun_app_1 : 42 = ((lambda (x) x) 42));
test!(fun_app_2 : 0 = (((lambda (x) x) (lambda (x) x)) 0));
test!(fun_app_2_args_1 : 69 = ((lambda (x y) y) 68 69));
test!(fun_app_2_args_2 : 68 = ((lambda (x y) x) 68 69));
test!(cond1 : 1 = (
    cond
    (nil 2)
    (42 1)
));
test!(sum1: 10 = (sum 1 2 3 4));
test!(prod1: 24 = (prod 1 2 3 4));
test!(sum_with_evaluated_args: 43 = (sum 1 (sum 42)));
test!(lambda_with_same_varname : 1 = ((lambda (x) ((lambda (x) x) x)) 1));
test!(eval1 : 1 = (eval nil 1));
test!(def1 : 13 = (
    (def x 13)
    x
));

test!(long_list : 1 = (
    (def repeat (lambda (reps elem)(
        (def aux (lambda (reps elem acc)
            (cond
                ((lt reps 1) acc)
                (1 (aux (minus reps 1) elem (cons elem acc)))
            )
        ))
        (aux reps elem nil)
    )))
    (hd (repeat 40000 1))
));

fn main() {
    let env = parse!(nil);
    let prog = parse!((
        (def t 1)
        (def and (lambdav (bs)(
            (def aux (lambda (bs)
                (cond 
                    ((nilp bs) t)
                    (t (cond ((hd bs) (aux (tl bs)))))
                )))
            (aux bs)
        )))
        (def or (lambdav (bs)(
            (def aux (lambda (bs)
                (cond 
                    ((nilp bs) nil)
                    (t (
                        cond 
                        ((hd bs) t)
                        (t (aux (tl bs))))
                    )
                ))
            )
            (aux bs)
        )))
        (def not (lambda (x) (cond (x nil) (t t))))
        (def fib 
            (lambda (x)(
            (def aux (lambda (x a b)
                (cond 
                    ((lt x 1) a)
                    (t (aux (minus x 1) (sum a b) a))
            )))
            (aux x 0 1)
        )))
        (def concat (lambda (xs ys)
            (cond
                ((nilp xs) ys)
                (t (cons (hd xs) (concat (tl xs) ys)))
            )
        ))
        (def rev (lambda (ls)(
            (def aux (lambda (ls ts)
                (cond
                    ((nilp ls) ts)
                    (t (aux (tl ls) (cons (hd ls) ts)))
                )
            ))
            (aux ls nil)
        )))
        (def fibs (lambda (x)
            (cond
                ((lt x 1) nil)
                (t (cons (list x (fib x)) (fibs (minus x 1))))
            )
        ))
        (def repeat (lambda (reps elem)(
            (def aux (lambda (reps elem acc)
                (cond
                    ((lt reps 1) acc)
                    (1 (aux (minus reps 1) elem (cons elem acc)))
                )
            ))
            (aux reps elem nil)
        )))
        (def iter (lambda (reps func init)(
            (def aux (lambda (reps func acc val)
                (cond 
                    ((lt reps 1) acc)
                    (1 (aux 
                        (minus reps 1) 
                        func 
                        (cons (func val) acc)
                        (func val)
                    ))
                )
            ))
            (rev (aux reps func nil init))
        )))
        (iter 10 (lambda (x) (sum x 1)) 0)
    ));

    println!("{}", eval(env, prog, &Trace::new(10)).unwrap());
}
