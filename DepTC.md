
#### The future of type classes in (dependently typed) programming

##### 1. Introduction

Type classes are on the rise. Major modern programming languages such as Scala, Rust and Swift support type class-based abstraction. Microsoft Research's new theorem prover, Lean was designed from ground-up with type classes in mind, and Agda and Coq, two existing proof assistants, have also added support. The C++17 standard will hopefully also add type classes under the name of "Concept"-s, after much languishing and delays. 

Despite type classes' tremendous success in the Haskell ecosystem - which likely crucially influenced its adoption elsewhere - there's always been criticism. Some say that first-class modules, generic programming or dependent types obviate much the need for type classes. Also, there's yet another debate about the relative merits of coherent type classes (as featured in Haskell and Rust) and implicit dictionary-passing (as featured in Scala, Idris, Coq, and Agda). 

There are also unsolved questions regarding the implementation of type classes in advanced type systems. In particular, while coherence is arguably a desired property, no dependently typed language attempted to implement coherent classes so far. Agda, Coq, Idris and Lean all forgo coherence. Moreover, even more powerful potential type systems with richer propositional equalities are inherently at odds with class coherence.

Below I discuss the merits and prospects of type classes, with focus on advanced future languages. I try to adopt a general perspective, from which type classes can be viewed as a particular method of program inference and synthesis. 

##### 2. What are type classes anyway?
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





