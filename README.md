# Overview
Originally an assignment from UCSC class CSE-114A. \
Understand the notions of:
  * Scoping
  * Binding
  * Environments and Closures

by creating an interpreter for a subset of Haskell.

### Binary Operators

Nano uses the following **binary** operators encoded
within the interpreter as values of type `Binop`.

```haskell
data Binop
  = Plus
  | Minus
  | Mul
  | Div
  | Eq
  | Ne
  | Lt
  | Le
  | And
  | Or
  | Cons
```

### Expressions

All Nano programs correspond to **expressions**,
each of which will be represented within your
interpreter by Haskell values of type `Expr`:

```haskell
data Expr
  = EInt  Int
  | EBool Bool
  | ENil
  | EVar Id
  | EBin Binop Expr Expr
  | EIf  Expr Expr  Expr
  | ELet Id   Expr  Expr
  | EApp Expr Expr
  | ELam Id   Expr
  deriving (Eq)
```

where `Id` is just a type alias for `String` used to represent
variable names:

```haskell
type Id = String
```

The following lists some example Nano expressions,
and the corresponding values of type `Expr` used to represent
the expression inside your interpreter.

1. `Let`-expressions

The `let`-expression

```haskell
let x = 3 in x + x		
```

is represented by

```haskell
ELet "x" (EInt 3)
  (EBin Plus (EVar "x") (EVar "x"))
```

2. Anonymous function definitions

The function

```haskell
\x -> x + 1
```

is represented by

```haskell
ELam "x" (EBin Plus (EVar "x") (EInt 1))
```

3. Function applications (also known as "function calls")

The function application

```haskell
f x									
```

is represented by

```haskell
EApp (EVar "f") (EVar "x")
```

4. (Recursive) named function definitions

The expression

```haskell
let f = \x -> f x in
  f 5	    
```

is represented by

```haskell
ELet "f" (ELam "x" (EApp (EVar "f") (EVar "x")))
  (EApp (Var "f") (EInt 5))
```

### Values

We will represent Nano **values**, i.e., the results
of evaluation, using the following datatype:

```haskell
data Value
  = VInt  Int
  | VBool Bool
  | VClos Env Id Expr
  | VNil
  | VPair Value Value
  | VPrim (Value -> Value)
```

where an `Env` is simply a *dictionary* -- a list of pairs
of variable names and the values they are bound to:

```haskell
type Env = [(Id, Value)]
```

Intuitively, the Nano integer value `4` and Boolean value
`True` are represented respectively as `VInt 4` and `VBool True`.

- `VClos env "x" e` represents a function with argument `"x"`
   and body expression `e` that was defined in an environment
   `env`.
