
### The future of type classes in (dependently typed) programming


#### 1. Introduction

Type classes are on the rise. Major modern programming languages such as Scala, Rust and Swift support type class-based abstraction. Microsoft Research's new theorem prover, Lean was designed from ground-up with type classes in mind, and Agda and Coq, two existing proof assistants, have also added support. The C++17 standard will hopefully also add type classes under the name of "Concept"-s, after much languishing and delays. 

Despite type classes' tremendous success in the Haskell ecosystem - which likely crucially influenced its adoption elsewhere - there's always been criticism. Some say that first-class modules, generic programming or dependent types obviate much the need for type classes. Also, there's yet another debate about the relative merits of coherent type classes (as featured in Haskell and Rust) and implicit dictionary-passing (as featured in Scala, Idris, Coq, and Agda). 

There are also unsolved questions regarding the implementation of type classes in advanced type systems. In particular, while coherence is arguably a desired property, no dependently typed language attempted to implement coherent classes so far. Agda, Coq, Idris and Lean all forgo coherence. Moreover, even more powerful potential type systems with richer propositional equalities are inherently at odds with class coherence.

Below I discuss the merits and prospects of type classes, with focus on advanced future languages. I try to adopt a general perspective, from which type classes can be viewed as a particular method of program inference and synthesis. 

#### 2. About type classes

##### 2.1. Overview

Type classes were originally invented (wadler 88, wiki) as a principled and efficiently implementable form of ad-hoc polymorphism. I do not aim to provide an introduction to type classes in this article; I assume that the reader is already familiar with them. Instead I seek to conceptualize them in a slightly unusual way. Thus, my short definition has a different emphasis than ad-hoc polymorphism: 

> **Type classes are systems enabling automatic code generation through constrained search.**

What do we mean by "constrained" and "search" here, though? The illuminate this, let us first consider a general unconstrained search problem, as a simple Haskell programming task. Suppose our context has the following data and function definitions (with implementations that aren't relevant to us now):

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

A natural solution would be `h ab = g f ab`. We can arrive at the solution by searching the available definitions in the context and trying to plug them together in a way that results in the desired type. This activity is analoguous to formal proof writing as per the Curry-Howard correspondence. A large part of practical programming can be understood as a task like the above: given a context of already implemented code, write additional code with given type and semantics. Note that our toy example is solvable purely by playing with types, but given some formal notion of semantics, "search" can encompass that as well. 

Automatic search techniques do exist, but they are largely unusable for everyday programming for the following reasons:

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

In the example above, we have merely written `h = show` instead of the more fine-grained `h = g f` definition. We employed automatic search by invoking the `show` class method. Our Haskell compiler performed roughly the following steps:

1. Try to prove `Show (A B)`
2. Find `instance Show a => Show (A a)` as a matching instance.
3. Unify `A B` with `A a`, instantiating `a` to `B`. 
4. Try to prove `Show B` (the instantiated constraint on the `Show (A B)` instance).
5. Find `instance Show B` as a matching instance. 

A succesful search allows the compiler to plug in the appropriate `show` definitions, thereby producing a "proof". In fact, the above procedure is just a simple form of resolution, similar to that used in logic programming.

As long as instance and class definitions are kept in a tractable form (in Haskell's case, instances are Horn clauses), instance resolution remains a tractable problem. This constitutes a solution to the first problem, the problem of large search spaces. Practical implementations in programming languages all use some variation of type-directed resolution, but in principle search could be constrained in different ways. This is a topic that could be worthwhile to explore. 

As to the problem of specifications, programmers can manually implement instance methods, thereby exerting control over the semantics of generated code. Instances become the basic building blocks, and instance resolution only provides the "plumbing". Of course, this means that a significant amount of program logic is still written by hand. It's a general trade-off; depdending on the expressiveness of the ambient type system programmers may be able to increase or decrease the amount of code obligations. 

##### 2.2. Advantages of type classes

Types are the primary carriers of information in static systems. It's desirable that we be able to make as much as possible use of this information, and do this *inside* the language. 

Polymorhic (or "generic") data types generate a rich expression language, in contrast to monomorphic types. Consider the following data type:

```haskell
data PairOfInts = Pair Int Int
```

Just by looking at the name `PairOfInts`, we don't get any information about the values of the type. The naming is just sensible practice from the programmer's part, but it enforces nothing inside the language. The compiler does know internally that `PairOfInts` is a pair of integers, because it has to check its uses and generate code for field accesses, and it may even abstract internally over common shapes of structs, but this information remains inaccessible to programmers. Contrast a generic pair:

```haskell
data Pair a b = Pair a b
```

`Pair` and `Int` now generate an infinite language containing `Pair Int Int`, `Pair (Pair Int Int) Int` and so on, types with all different values. With this state of affairs, the properties of specific `Pair a b`-s depend on the properties of the `a`-s and `b`-s inside. Type classes can express this:

```haskell
class Eq a where
  (==) :: a -> a -> Bool
  
-- a Prolog "rule":
instance (Eq a, Eq b) => Eq (Pair a b) where
  Pair a b == Pair a' b' = a == a' && b == b'
```

In contrast, the above notion is not readily expressible in Java or Eiffel. In Java one could try the following:

```java
interface Eq<A> {
    public boolean eq(A other);
}

class Pair<A extends Eq<A>, B extends Eq<B>> implements Eq<Pair<A, B>> {
    A a;
    B b;
    public boolean eq(Pair<A, B> other){
        return a.eq(other.a) && b.eq(other.b);
    }
}
```

But this largely defeats the purpose, since now `Pair` itself is restricted to `Eq` fields. It's still true in Java and Eiffel that there is a straightforward `eq` method implementation for `Pair` whenever the fields also implement `eq`, but that implementation must be written out each time, or abstracted as a higher-order function with `Comparator` objects, which also requires manual plumbing on use sites. 

Type classes enable recursion on the structure of types, making choices based on specific subtypes. Note though that types classes are not the only way to achieve this, and there are theoretically more straigthforward ways, which we'll explore in chapter (TODO chapter num). 

> Should types expose information, or instead hide unnecessary details? In the brave new world of (dependent) type-theory-based programming my choice shall be firmly the former option. Information hiding only makes sense in a dangerous world where programmers communicate intent by giving classes descriptive English names and preventing (with more or less success) breaking invariants by making method private. `MouseEventAdapter` is in the eye of the beholder. Its meaning is hinted at by its name, and defined by the implementation. Its productive use hinges on mutual understanding of programming patterns. 

> But if types carry more information, they can be more useful, and we can also prove and enforce more properties. `Pair` is more informative than `PairOfInt`, and in turn least fixed points of functors are more informative than plain recursive data types. In the brave new world, we could have analogues of `MouseEventAdapter` types that encode their meaning in their structure, and invariants could be preserved by making illegal states unrepresentable. In that world, the name `MousEventAdapter` could be still useful as a shorthand, and we could still present lean API-s, but there wouldn't be nearly as much reason to hide details. After all, those with a clean record shouldn't have anything to fear, right?

On another note, type classes also have a favorable weight-to-power ratio in terms of runtime performance. The Rust programming language extensively uses type classes, but without any runtime cost, since the relatively simple Rust type system (no higher-rank polymorphism, no polymorphic recursion) allows compile time specialization and inlining of all instances. Inlining and specialization can cause excessive code size though, which should be considered. The point is that type classes give compilers considerable freedom to specialize as they see fit. This compares favorably to OOP polymorphism, where devirtualization can't be performed as robustly or universally, or it requires runtime JIT assistance, as in the case of Java. Generally, more information in static types helps code optimization as well. 

> Current dependently typed languages tend to have an *excess* of static information that is largely ignored by backends, because there hasn't been yet relevant research in this area, or there hasn't been need for that much performance.

##### 2.4 Coherent and incoherent type classes

Let's start off by defining coherence:

> **An implementation of type classes is coherent if all instances with equal types are equal.**

Runtime, instances are just records of values and functions, similar to virtual tables in C++ (supposed that there are instances that persist runtime after specialization and static dispatch). Instances are passed around as implicit arguments, and in some languages they can be also stored in runtime containers. In Haskell, a class constraint is dynamically equivalent to an extra function argument:

```haskell
f :: Eq a => a -> a -> a -> a
f a b default = if a == b then a else default
```

This is desuraged roughly into the following code in GHC's internal representation:

```haskell
f :: Eq a -> a -> a -> a -> a
f eqA a b default = if ((==) eqA a b) then a else default
```

where `(==) eqA` looks up the `==` method from the `eqA` instance. Also, instances can be put into runtime boxes:

```haskell
data ShowBox a where
  Box :: Show a => ShowBox
```

`Box` holds a dynamic `Show a` instance, and we can write code that releases the instance into the outer scope by pattern matching on the box:

```haskell
applyBox :: ShowBox a -> a -> String
applyBox Box a = show a
```

Here, we were able to use the `show` method because by "opening" the box we made the `Show` instance available. 




The type is desugared into `Eq a -> a -> a -> a -> a` in GHC's intermediate representation. 


--------------------------------

-- performance....

  - Types carry information. By inspecting the structure of types we get a lot of information, and type classes allow us to *act* on that information. It also allows us to make our data types as lean and general as possible ("dumb reusable data"), and implement Prolog "rule" instances instead of "fact" instances. Type classes operate over a potentially infinite term language of type constructors (example: Show (a, b), Show ((a, b), (c, d)) etc.). 
  - Class methods can be dispatched statically in the vast majority of cases. Rust only uses static dispatch. The compiler has great freedom to dispatch statically or dinamically as it sees fit. The programmer can precisely introduce dynamic dispatch via existentially boxed instances and higher-order functions. 
  - Proven abstractions from algebra and category theory relatively well expressible with type classes. 
  - Contrast OOP abstraction: its primary job is *enforcing* structural and nominal relations. OOP doesn't generate code; we can either inherit existing code or override it. Class hierarchies are glued together nominally, and just sort of sit there. Example: inability in Java or Eiffel to have a generic pair type that's Eq iff the two fields are Eq. Abstraction by polymorphism involves lots of virtual calls, Java has to rely on JIT to devirtualize. Type classes are closer to actual programming problems ("given context of code implement some other code" versus "let's try to come up with a bunch of complicated structural relations between objects that gives us maximal code reuse by inclusion"). 

##### 2.3. Coherent versus incoherent classes 

- What do they mean
- Advantages of coherence (robustness, definitional instance equality, entailment as logic)
- Advantages of incoherence (first-class dictionaries, backtracking, overlapping)
- Examples and anecdotes
- coherence in programming languages vs coherence in proof assistants
- We'll consider coherence as important point later in dep types. 

#### Back a bit to code gen

- Code /= program. There is a mapping from code to program ("elaboration"). 
- The compiler fills in details that follow from the semantics expressed in the source code.
- The mapping should be easy to reason about.
- There should be no arbitrary choices and choices that depend on source code non-compositionally

- Types of program inference:
   - as extension of type inference: based on type dependencies. Completely unambiguous.
   - Proof search: based on searching contexts. Instance resolution a special case.

- When is it safe to do arbitrary search? Irrelevant (propositional types)
   - We can throw anything at irrelevant types. SMT is nice. 
   
#### Throw dep types and first-class modules in

- Are classes still needed? 
    - at least *some* mechanism that emulates math's "convention of notation" should be available
    - first class modules as alternative
    - generic prog as alternative
- What about coherence:
    - Problem: undecidable propositional apartness!
        - solutions:
          - proof obligations of apartness (I sort of like it)
          - restriction of language fragment in instance heads  (like current GHC)
          - restriction of usage of instances
    - more problems: univalent / observational type theories
    - How to provide internal proof of coherence?
       - I have no idea. Need some simple Agda model. 
- Instead of coherence
    - Use propositional classes
        - technique: refine classes until they are propositional 
           - example: Eq vs DecEq
              - but what bout bigger eqv. relations for Eq instance?
                 - just use (higher inductive) quotient newtypes, lol
    - encode relevant info in types, make coherence redundant
      - but what about Monad, Traversable etc? Don't want to suddenly traverse backwards
      - It's very complicated to encode traversal order, plus it screws up all existing infrastructure
    - What solutions are there that forgo coherence but still provide enough reliability?
      - some kind of local instance scoping? But we could do first class module opening instead.
         
    
    
   








   
- Different flavors
  - coherent/non-coherent
  - first-class dictionaries
  - other extensions: associated types, multi-param, fundeps, kinds class .. blah blah
    - plz discuss only the important core features
    

##### 3. More generally on code generation: 
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





