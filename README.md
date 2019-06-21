# Titan

Titan is an experimental type checker implementation written in Haskell.

## Features

This implementation is based on the implementation of [Typing Haskell in Haskell](https://web.cecs.pdx.edu/~mpj/thih/) type checker. I'm going to implement some additional features like:

* [x] Parsers and (poor) pretty-printers
* [x] Implicit universal quantification
* [x] Kind inference
* [x] Explicit kind signatures and scoped type variables
* [x] Multi-parameter type classes
* [x] Pattern exhaustiveness/useless checker
* [x] Functional dependencies
* [ ] Row polymorphism
* [ ] Effects

## Syntax overview

### Comments
```
// comment
/* comment */
```

### Kinds
```
_a            // var (internal)
*             // types of values
?             // constraints
k -> k        // function kind
```

### Types
```
_a            // var (internal)
Int           // con
Pair a b      // app
a -> b        // app (arrow)
a             // quantified var
```

### Constraints
```
Coercible a b // class consraints
(c, c)        // set of constraints
```

### Type schemes
```
// type variables are implicitly quantified
a -> f a where Applicative f

// specifying quantification explicitly
[a f] a -> f a where Applicative f

// specifying quantification with kind signatures
[(a : *) (f : * -> *)] a -> f a where Applicative f
```

### Literals
```
123           // integer
'a'           // char
3.14          // float
"hello"       // string
```

### Patterns
```
x             // var
x@p           // as var
_             // wildcard
Pair a b      // decon
123           // lit
```

### Expressions
```
x             // var
Pair          // con
Pair a b      // app
123           // lit
let id = e, id = e in e    // let
fun pats -> e | pats -> e  // lam
```

### Declarations
```
// explicitly typed def
val id : ts
val id : ts = e

// implicitly typed def
val id = e

// data type
data List a {
  con Cons a (List a)
  con Nil
}

// type class
class Eq a {
  val eq : a -> a -> Bool
}

class Ord a where Eq a {
  val compare : a -> a -> Ordering
}

class MonadState s m | m ~> s where Monad m {
  val get : m s
  val put : s -> m Unit
}

// instance
instance Eq (Pair a b) where (Eq a, Eq b)

// default
default {
  Maybe
  Integer
}

// dump
dump(type) val id = fun x -> x
dump(kind) data Free f a {
  con Pure a
  con Free (f (Free f a))
}
```

## References

- [Mark P. Jones: Typing Haskell in Haskell](https://web.cecs.pdx.edu/~mpj/thih/)
- [Didier Rémy: Extension of ML type system with a sorted equational theory on types](https://hal.inria.fr/inria-00077006/document)
- [LUC MARANGET: Warnings for pattern matching](http://moscova.inria.fr/~maranget/papers/warn/index.html)
- [Mark P. Jones: Language and Program Design for Functional Dependencies](https://web.cecs.pdx.edu/~mpj/pubs/fundeps-design.pdf)

