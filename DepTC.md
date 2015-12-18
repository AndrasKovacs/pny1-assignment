
#### The future of type classes in (dependently typed) programming

##### 1. Introduction

Type classes are on the rise. Major modern programming languages such as Scala, Rust and Swift support type class-based abstraction. Microsoft Research's new theorem prover, Lean was designed from ground-up with type classes in mind, and Agda and Coq, two existing proof assistants, have also added support. The C++17 standard will hopefully also add type classes under the name of "Concept"-s, after much languishing and delays. 

Despite type classes' tremendous success in the Haskell ecosystem - which likely crucially influenced its adoption elsewhere - there's always been criticism. Some say that first-class modules, generic programming or dependent types obviate much the need for type classes. Also, there's yet another debate about the relative merits of coherent type classes (as featured in Haskell and Rust) and implicit dictionary-passing (as featured in Scala, Idris, Coq, and Agda). 

There are also unsolved questions regarding the implementation of type classes in advanced type systems. In particular, while coherence is arguably a desired property, no dependently typed language attempted to implement coherent classes so far. Agda, Coq, Idris and Lean all forgo coherence. Moreover, even more powerful potential type systems with richer propositional equalities are inherently at odds with class coherence.

Below I discuss the merits and prospects of type classes, with focus on advanced future languages. I try to adopt a general perspective, from which type classes can be viewed as a particular method of program inference and synthesis. 

##### 2. What are type classes?

In a nutshell, type classes enable automatic code generation by constrained search. What do we mean by "constrained" and "search" here, though? The illuminate this, let us first consider a general unconstrained search problem, as a simple Haskell programming task. Suppose our context has the following data and function definitions (with implementations that aren't relevant to us now):

```haskell
data A a
data B
f :: B -> String
g :: forall a. (a -> String) -> A a -> String
```

We would like to implement a function of the following type:

```haskell
h :: A B -> String
```

A natural solution would be `h ab = g f ab`. We can arrive at the solution by searching the available definitions in the context and trying to plug them together in a way that results in the desired type. This activity is analoguous to formal proof writing as per the Curry-Howard correspondence. A large part of practical programming can be understood as a task like the above: given a context of already implemented code, write additional code with given type and semantics. Note that our toy example is solvable purely by playing with types, but given some formal notion of semantics "search" can encompass that as well. 

Automatic search techniques do exist, but they are largely unusable for everyday programming because of the following reasons:

- The necessity of painstaking formal specification of search goals. If our specification isn't precise enough, then it's not guaranteed that search results will be satisfactory. 
- Search spaces are prohibitively large for all but the simplest problems. 

Type classes mitigate both problems by *constraining* search. We can reframe our toy problem with type classes:

```haskell
-- definitions as before
data A a
data B
f :: B -> String
g :: forall a. (a -> String) -> A a -> String

class Show a where
  show :: a -> String

instance Show B where
  show = f
  
instance Show a => Show (A a) where
  show = g show
  
h :: A B -> String
h = show
```

In the example above, we have merely written `h = show` instead of the more detailed `h = g f` definition. We employed automatic search by invoking the `show` class method. Our Haskell compiler performed roughly the following steps:

1. Try to prove `Show (A B)`
2. Find `instance Show a => Show (A a)` as a matching instance.
3. Unify `A B` with `A a`, instantiating `a` to `B`. 
4. Try to prove `Show B` (the instantiated constraint on the `Show (A B)` instance).
5. Find `instance Show B` as a matching instance. 




- What they are
- Why do I think they are good, in what ways
   - OOP types: enforce static relations, dep types: act on information carried by types 
   - most programming tasks are implications in the BHK sense: given a context of code,
     can we implement some other code? OOP doesn't help in that; inherited code is
     either already written, or must be reimplemented each time if it's virtual. 
   - but: if there is information encoded in the structure of types, we should find ways
       to actually make use of it. 
   -  most generally: large elimination on type universes
   -  usefully approximated by structural recursion on term language of type constructors
   
- Different flavors
  - coherent/non-coherent
  - first-class dictionaries
  - other extensions: associated types, multi-param, fundeps, kinds class .. blah blah
    - plz discuss only the important core features
    

##### 3. Interlude: 
  - methods of code generation: 
      - program inference
      - proofs search: ad-hoc, instance-guided
      - irrelevant types: the class of types for which automatic search is always permissible. 
  - What do we talk about when we talk about writing programs?
      - mcbride's post-HM vision:
          - write types, then syntetise programs
          - compute types from data and programs
          - 
      - We don't write proof terms, we write
          - programs that output proof terms when we run them
          - inputs to programs that output proof terms





