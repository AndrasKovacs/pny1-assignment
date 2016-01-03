
### The future of type classes in (dependently typed) programming


#### 1. Introduction

Type classes are on the rise. Major modern programming languages such as Scala, Rust and Swift support type class-based abstraction. Microsoft Research's new theorem prover, Lean was designed from ground-up with type classes in mind, and Agda and Coq, two existing proof assistants, have also added support. The C++17 standard will hopefully also add type classes under the name of "Concept"-s, after much languishing and delays. 

Despite type classes' tremendous success in the Haskell ecosystem - which likely crucially influenced its adoption elsewhere - there's always been criticism. Some say that first-class modules, generic programming or dependent types obviate much the need for type classes. Also, there's yet another debate about the relative merits of coherent type classes (as featured in Haskell, Rust and Purescript) and incoherent type classes (as featured in Scala, Idris, Coq, and Agda). 

There are also unsolved questions regarding the implementation of type classes in advanced type systems. In particular, while coherence is arguably a desired property, no dependently typed language attempted to implement coherent classes so far. Agda, Coq, Idris and Lean all forgo coherence. Moreover, some stronger type systems with richer notions of equality are inherently at odds with class coherence.

Below I discuss the merits and prospects of type classes, with focus on advanced future languages. I try to adopt a general perspective, from which type classes can be viewed as a particular method of program inference and synthesis. 

#### 2. About type classes

##### 2.1. Overview

Type classes were originally invented (wadler 88, wiki) as a principled and efficiently implementable form of ad-hoc polymorphism. I do not aim to provide an introduction to type classes in this article; I assume that the reader is already familiar with them. Instead I seek to conceptualize them in a slightly unusual way. Thus, my short definition has a different emphasis than ad-hoc polymorphism: 

> **Type classes are systems enabling automatic code generation through constrained search.**

What do we mean by "constrained" and "search" here, though? To illuminate this, let us first consider a general unconstrained search problem, as a simple Haskell programming task. Suppose our context has the following data and function definitions (with implementations that aren't relevant to us now):

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

A natural solution would be `h ab = g f ab`. We can arrive at the solution by searching the available definitions in the context and trying to plug them together in a way that yields the desired type. This activity is analoguous to formal proof writing as per the Curry-Howard correspondence. A large part of practical programming can be understood as a task like the above one: given a context of already implemented code, write additional code with given type and semantics. Note that our toy example is solvable purely by playing with types, but given some formal notion of semantics, "search" can encompass that as well. 

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

> *In the instance declaration `instance Show a => Show (A a) where ...`, we call `(A a)` the instance head and `Show a` the instance constraint.*

In the example above, we have merely written `h = show` instead of the more fine-grained `h = g f` definition. We employed automatic search by invoking the `show` class method. Our Haskell compiler performed roughly the following steps:

1. Try to prove `Show (A B)`
2. Find `instance Show a => Show (A a)` as a matching instance.
3. Unify `A B` with `A a`, instantiating `a` to `B`. 
4. Try to prove `Show B` (the instantiated constraint on the `Show (A B)` instance).
5. Find `instance Show B` as a matching instance. 

A succesful search allows the compiler to plug in the appropriate `show` definitions, thereby producing a "proof". In fact, the above procedure is just a simple form of resolution, similar to that used in logic programming.

As long as instance and class definitions are kept in a tractable form (in Haskell's case, instances are Horn clauses), instance resolution remains a tractable problem. This constitutes a solution to the first problem, the problem of large search spaces. Practical implementations in programming languages all use some variation of type-directed resolution, but in principle search could be constrained in different ways (this is a topic that could be worthwhile to explore).

As to the problem of specifications, programmers can manually implement instance methods, thereby exerting control over the semantics of generated code. Instances become the basic building blocks, and instance resolution only provides the "plumbing". Of course, this means that a significant amount of program logic is still written by hand. It's a general trade-off; depdending on the expressiveness of the ambient type system programmers may be able to increase or decrease the amount of obligations for hand-written code.

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

`Pair` and `Int` now generate an infinite language containing `Pair Int Int`, `Pair (Pair Int Int) Int` and so on, types with all different values. With this state of affairs, the properties of specific `Pair a b`-s depend on the properties of the `a`-s and `b`-s inside. Type classes can express this dependency:

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

But this largely defeats the purpose, since now `Pair` itself is restricted to `Eq` fields. It's still true in Java and Eiffel that there is a straightforward `eq` method implementation for `Pair` whenever the fields also implement `eq`, but that implementation must be written out each time, or abstracted as a higher-order function with `Comparator` inputs, which also requires manual plumbing on use sites. 

Type classes enable recursion on the structure of types, making choices based on specific subtypes. Note though that types classes are not the only way to achieve this, and we'll explore alternative solution in section 3. 

> Should types expose information, or instead hide unnecessary details? In the brave new world of (dependent) type-theory-based programming my choice shall be firmly the former option. Information hiding only makes sense in a dangerous world where programmers communicate intent by giving classes descriptive English names and preventing (with more or less success) breaking invariants by making methods private. `MouseEventAdapter` is in the eye of the beholder. Its meaning is hinted at by its name, and defined by the implementation. Its productive use hinges on mutual understanding of programming patterns. 

> But if types carry more information, they can be more useful, and we can also prove and enforce more properties. `Pair` is more informative than `PairOfInt`, and in turn least fixed points of functors are more informative than plain recursive data types. In the brave new world, we could have analogues of `MouseEventAdapter` types that encode their meaning in their structure, and invariants could be preserved by making illegal states unrepresentable. In that world, the name `MousEventAdapter` could be still useful as a shorthand, and we could still present lean API-s, but there wouldn't be nearly as much reason to hide details. After all, those with a clean record shouldn't have anything to fear.

On another note, type classes also have a favorable weight-to-power ratio in terms of runtime performance. The Rust programming language extensively uses type classes, but without any runtime cost, since the relatively simple Rust type system (no higher-rank polymorphism, no polymorphic values inside data types) allows compile-time specialization and inlining of all instances. Inlining and specialization can cause excessive code size though, which should be considered as a trade-off, but type classes give compilers considerable freedom to specialize where they see benefit to it. This compares favorably to OOP polymorphism, where devirtualization can't be performed as robustly or universally, or it requires runtime JIT assistance, as in the case of Java. In general, more information in static types helps code optimization as well. 

> Current dependently typed languages tend to have an *excess* of static information that is largely ignored by backends, because there hasn't been yet relevant research in this area, or there hasn't been need for that much performance.

##### 2.4 Coherent type classes

Let's start off by defining coherence:

> **An implementation of type classes is coherent if all instances with equal types are equal.**

(TODO: src on this coherence)

Let's provide some backgrouond exaplanation. Runtime instances are just records of values and functions, similar to virtual tables in C++ (provided that there are instances that persist runtime after specialization and static dispatch). Instances are passed around as implicit arguments, and in some languages they can be also stored in runtime containers. In Haskell, a class constraint is dynamically equivalent to an extra function argument:

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

`Box` holds a dynamic `Show a` instance. We can release the instance into the outer scope by pattern matching on the box:

```haskell
applyBox :: ShowBox a -> a -> String
applyBox Box a = show a
```

However, this flexible treatment of instances leads to a potential dilemma. Suppose that there are multiple instances in scope, all with the same type. Which one do we actually use when we invoke a method?

```haskell
dilemma :: Show a => ShowBox a -> a -> String
dilemma Box a = show a
```

Haskell programmers have no control over which instance is used here. But that's no issue; coherence implies that the two instances are the same, so chosing one or another makes no difference. 

Coherence significantly enhances robustness. It implies that all the following factors are irrelevant to type class semantics:

- The order of local bindings
- The order of top-level bindings
- The order of module imports
- Visibility modifiers on module imports and exports
- The order of class constraints in classes, instances and definitions

Coherent classes also have the "diamond" property, namely that there could be multiple derivations of *constraint entailment*, but all derivations result in the same instance:


```
          Ord a
        /       \
       /         \
    Eq a       Ord (List a)
      \           /
       \         /
        \       /
        Eq (List a)
```

In the above diagram, we have `class Eq a => Ord`, `instance Eq a => Eq (List a)` and `instance Ord a => Ord (List a)`. Therefore, if we know `Ord a`, we can derive `Eq (List a)` in two different ways. 

The first derivation takes the left path, using the `Ord` superclass to get to `Eq a`, then the `List` `Eq` instances. The right derivation first follows the `Ord (List a)` instance and follows the `Ord` superclass thereafter. 

Of course, coherence already implies that all derivations must agree. The diamond property is interesting because is illustrates that coherent systems can hide the details of resolution algorithms from programmers. Incoherent systems should also behave in a well-defined and sensible way, but they must necessarily expose the resolution procedure so that programmers can anticipate its effects. 

What makes coherent type classes such? Certainly, we should expect that strong guarantees are realized through restrictions, which is the case here:

- All instances must be defined in instance declarations and cannot be passed around explicitly. Such explicit passing obviously contradicts coherence, since it allows creating instances from arbitrary values. 
- The instance heads of a class
    - Must be disjunct and non-overlapping, provided that we allow modularity, i. e. different sets of instances visible in different modules. If we allow both modularity and overlapping then it could be the case that a module defines a more specific overlapping instance than another module, and thus two different runtime instances may end up in the program. On the other hand, overlapping instances could be made coherent if we give up modularity, i. e. mandate a single globally consistent set of instances, but this option isn't practical in any realistic module system. 
- There must be no "orphan instances", i. e. instances such that their classes aren't declared in the module of the instance, and the types in their heads aren't defined in the module either. In the presence of orphan instances we could just define two different orphan instances in different modules, then export them wrapped in a runtime box, to be used in a single module - destroying coherence.

Backtracking instance resolution is also incompatible with coherence and modularity. Disjunct instance heads eliminate non-determinism in instance matching, so the only remaining point for backtracking choice would be instance constraints. In pseudo-Haskell:

```haskell
instance (Ord a || Eq a) => Foo a where ...
  -- There must be some mechanism here for dispatching on the presence of `Ord a` or `Eq a`
```

However, it's easy to see that this is equivalent to backtracking choice with two obviously overlapping instances:

```haskell
instance Ord a => Foo a where ...
instance Eq a => Foo a where ...
```

There is some variation in the handling of overlapping and orphan instances in languages with coherent classes. GHC Haskell allows orphan instances (with compile-time warnings), and one can also enable overlapping instances through a compiler pragma. Rust disallows both.

##### 2.5 Incoherent type classes

Incoherent classes have their own set of advantages: they can be considerably more flexible.

First, they allow first-class treatment of instances: they become ordinary values that can be explicitly passed around. Programmers can override implicits with explicit details.

In Agda notation, instance arguments are indicated by double braces:

```agda
record Monoid (A : Set) : Set where
  field
    mempty : A
    mappend : A -> A -> A

twice : forall {A : Set}. {{monA : Monoid A}} -> A -> A
twice a = mappend a a
```

In the above code, `twice` takes an instance of the type `Monoid A`. `twice` can be used with a single `A` argument, and the compiler would try to pass an available instance implicitly (the implicits mechanism in Scala works similarly). But we can also invoke `twice` as follows:

```agda
postulate
  A : Set
  monA : Monoid A
  x : A

foo : A
foo = twice {{monA = monA}} x
```

There is a mechanism in Agda for defining Haskell-style instances, but instance arguments can be still used in their absence.

Also, we saw that Agda classes are just *records*, and instances are just certain values with record types. We could implement two different `Monoid Nat` instances for natural numbers, one with addition as operation and one with multiplication:

```agda

plusMonoid : Monoid Nat
plusMonoid = record {mempty = 0; mappend = _+_}

multMonoid : Monoid Nat
multMonoid = record {mempty = 1; mappend = _*_}

```

With coherent instances, we're forced to have only one instance for an instance head, even when there could be plausibly more. In Haskell, multiple instances are handled through "newtype-s", i. e. unary wrappers without runtime cost that introduce a strongly-typed aliases.

```haskell
newtype Sum a = Sum a
newtype Product a = Product a

instance Num a => Monoid (Pls a) where
  mempty = Sum 0
  mappend (Sum a) (Sum b) = Sum (a + b)

instance Num a => Monoid (Product a) where
  mempty = Product 1
  mappend (Product a) (Product b) = Product (a * b)
```

`Sum a` and `Product a` are types that differ from the underlying `a`-s, although they have the same runtime representation. They allow us to define to different `Monoid` instances. Their drawback is that we must use the `Plus` and `Product` constructors to wrap and unwrap values. This can be annoying, so Haskell has a mechanism for safely coercing values between representationally equal types:

```haskell
foo :: List Product
foo = map Product [0..10]

bar :: List Sum
bar = coerce foo
```

Also, incoherent classes may support backtracking resolution, which makes it possible to vary and specialize implementations based on the availability of certain instances. For example, backtracking makes it possible to implement the removal of duplicate elements from a list (`nub`) in `O(n * log n)` if the elements can be ordered, and fall back to an `O(n^2)` definition if the elements only support equality. Coq and Lean support such backtracking.

Incoherence also makes it possible to make search more liberal, as in prior Agda versions where data constructors and ordinary bindings were also searched for instances (this feature is being phased out though). 

The main drawbacks of incoherence are: 

> **1. Complexity of instance resolution, fragile semantics with respect to small program transformations**

Naturally, the lack of coherence's robustness manifests itself as fragility, for example as a Scala program that breaks after someone alphabetizes the package imports. 

> **2. Some uses cases ruled out by lack of coherence**

A classic example is ordered sets and associative data structures ordered by keys. To modify such data structures we need functions for comparing keys. Most importantly, each modification must use the same comparison function in order to maintain structural invariants. In Haskell, a `Ord` class constraint implies that invariants are preserved, by class coherence.

```haskell
insert :: Ord k => Map k v -> k -> v -> Map k v
```
In the absence of coherence, `Map`-s must either
- Store a comparison method internally
- Have a type-level dependency on a particular comparison method

The first solution has significant drawbacks. Algorithms that require having the same ordering for two containers (for example, efficient set union) are impossible to implement. I find the second solution better and its complexity cost acceptable. An example for the second solution in the wild is C++ STL containers.

##### 2.6 Comparing merits

What's the verdict on coherence, then? 

First, I posit that coherence has significant benefits in robustness and scalability, and thus I will henceforth consider it desirable in hypothetical languages. A good heuristic in programming and mathematics is to use the least powerful tool that gets the job done, because they tend to be simpler, easier to reason about, and also more generally applicable (that said, in software development we have a great number of tools that are complicated and weak at the same time).  

Still, there are many caveats and footnotes to this. 

First, coherence and incoherence are a convenient and simple categorization of real-world systems, but there are many features and details that determine type classes' usability in the context of a given language. There's a great variance in the methods for incoherent search. The `IncoherentInstances` extension of GHC Haskell is rather simple, Agda's instance search is more complex, Coq also features backtracking, while Scala's search doesn't have backtracking but is very complex partly because it's embedded in a complex language. It might be the case that some real-world systems benefit from incoherence and never suffer from their drawbacks, or there may be some sweet spot of search complexity that balances robustness and flexibility, and it isn't necessarily coherent search. 

> This connects to the general issue of software methodology and productivity research, which hasn't delivered specatular results so far (that I know of). In particular, there is a large amount of quantitative research that could be potentially done to inform programming language design. Such reasearch would be preferable to the status quo of language design which mostly builds upon accumulated subjective experience of programmers and public discussion (where the most vociferous participants may or may not emphasize the practicaly most important points).

Second, proof writing and software development have differences that affect the usefulness of various search techniques. 

In software development, the norm is that programs carry relatively few proofs and semantics is only loosely determined by types. Software projects comparatively larger amount of code and more complex modularization, and code tends to be refactored and modified more frequently. Here, a large chunk of program semantics is not formalized and instead managed mentally by developers. In this environemnt coherence provides a relatively large benefit, as it alleviates mental burden and makes programs more robust to modification. 

In proof writing, very frequently the operational semantics or performance of code (proof terms) isn't relevant at all; the primary goal is to provide *some* proof. This ethos is exemplified by Coq where users often just throw powerful automated search at various problems without even making an effort to understand the resulting proof (if there is one). It's not an inherently bad practice, since there is finite amount of human effort that can be expended on understanding things, and it's often better to focus on understanding the most important points and leave dirty work to automation. Also, since specifications are so precise, erratic instance resolution rarely causes sneaky errors. Plugging in a wrong instance tends to prevent type checking, since proofs often rely on the implementations of class methods. In this environment coherence provides a relatively small benefit. 

However, we would like to ultimately integrate software development and proof writing seamlessly. Currently, Coq and Agda are very cumbersome for software development, and Haskell is very cumbersome and unreliable for proof writing. Designing type classes for an integrated environemnt would require a careful balancing act or provision of orthogonal search techniques for proof and program writing. Some of this will be discussed later. 

#### 3. Advanced language features versus type classes

In this section we examine whether some advances features and techniques could make type classes superfluous. 

##### 3.1. Generic programming

By "generic programming" I mean programming with closed type universes, which includes solutions such as Scrap Your Boilerplate and GHC.Generics in Haskell and direct uses of type universes in dependent languages. 

The general idea is that we have *descriptions* or *codes* for datatypes inside the language, and we can use descriptions to guide computation on values of described types. Type universes are data types whose values are descriptions (although full-fledged universes require dependent typing).

What makes type universes different from regular user-defined types in Haskell or Agda is that they are *closed* and *open for inspection*. Regular user-defined data types are more like axioms to the system, and yield opaque types with hidden structure. If we define natural numbers as

```haskell
data Nat = Zero | Succ Nat
```

then just by looking at the name `Nat` we can't glean any information about its constructors and general shape. In Agda, we can define a simple universe for types (least fixpoints of polynomial functors), and give a description for Nat in that universe:

```agda
data Desc : Set where
  _+_   : Desc → Desc → Desc  -- sum
  _*_   : Desc → Desc → Desc  -- product
  rec   : Desc                -- recursion
  one   : Desc                -- unit
  
Nat : Desc
Nat = one + rec
```
The `Nat` description can be now interpreted as a polynomial functor in Agda (and we can take its fixpoint), and use that in lieu of the old `Nat`, but now the structure of the type is available for inspection. 

For the sake of brevity I shall omit more Agda code here. The rest of the example can be [found here](https://github.com/AndrasKovacs/pny1-assignment/blob/master/SimpleGenerics.agda). The key point is that by having an internal description of types, we can define generic operations that work on values of *all* described types. For example, we can implement generic equality, pretty printing, serialization, zippers, lenses and more. In more advanced (dependent) languages we can define subsets of a larger universe using type-theoretic predicates, and define generic function that work only on some subsets; for example generic equality that only works on types that doesn't contain function fields. 

In practical implementations of generic programming in Haskell, Clean or Purescript, and generic functions are used via an extra conversion from user-defined types to generic representations and back. This has some performance overhead, and generic representations also tend to have greater memory footprint. Nevertheless, optimized generics are possible, as are languages that have generic types by default, or have *all* types in generic form.

Turning back to type classes, can we expect that generic programming can replace them? 

The answer is likely no. Generic programming does overlap with type classes, and it's usually a good choice in those cases (decidable equality, enumeration, serialization, etc.), but many classes are extremely hard to express generically. For example, instances for most algebraic structures cannot be derived mechanically. For example, natural numbers form a ring, but ring-ness can't be easily decided for arbitrary types.

Also, despite our best intentions a large amount of meaning and intent will be always expressed by the *naming* of types. Programmers often use isomorphic but differently named types, because most of the time there's no need or energy to express all relevant semantics in types. Thus, generics may be good for serialization, but not quite good for pretty printing, since generic functions are don't know much about the context in which a type is used or the intent of the programmer. It's a common bit of pain in programming languages that support some form of printing for all types: the printed outputs tend to be messy, verbose or uninformative. 

But I must stress that there is a considerable amount of research on dependently typed generic programming that enable extremely powerful abstractions (mind-blowing is an appropriate term). For example, see Conor McBride's work on algebraic ornaments, which are descriptions of *annotations*, *modifications* and *information erasure* on types. Ornaments describe notions such as "lists are natural numbers annotated with fields of some type" and "the erasure of fields from lists yields a natural number which is the length of the list", and they also enable some automatic lifting of functions operating on a type to a modified version of that type. Generics also tend to synergize with type classes: in Haskell, a less expressive language, type classes are even required for defining generic functions, since they're the main mechanism for dispatching on types. 







--------------------------------


##### 2.3. Coherent versus incoherent classes

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





