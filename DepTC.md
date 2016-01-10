
### The future of type classes in dependently typed programming


#### 1. Introduction

Type classes are on the rise. Major modern programming languages such as [Scala](http://www.scala-lang.org/docu/files/ScalaReference.pdf), [Rust](https://doc.rust-lang.org/book/traits.html) and [Swift](https://developer.apple.com/library/ios/documentation/Swift/Conceptual/Swift_Programming_Language/Protocols.html) support type class-based abstraction. Microsoft Research's new theorem prover, [Lean](https://leanprover.github.io/) was designed from ground-up with type classes in mind, and [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.InstanceArguments) and [Coq](https://coq.inria.fr/refman/Reference-Manual022.html), two existing proof assistants, have also added support. The C++17 standard will hopefully also add type classes under the name of ["Concept"](http://en.cppreference.com/w/cpp/concept)-s, after much languishing and delays. 

Despite type classes' tremendous success in the Haskell ecosystem - which likely crucially influenced its adoption elsewhere - there's always been criticism. Some say that first-class modules, generic programming or dependent types obviate much the need for type classes. Also, there's yet another debate about the relative merits of coherent type classes (as featured in Haskell, Rust and [Purescript](https://leanpub.com/purescript/read#leanpub-auto-type-classes) and incoherent type classes (as featured in Scala, [Idris](http://docs.idris-lang.org/en/latest/tutorial/classes.html), Coq, and Agda). 

There are also unsolved questions regarding the implementation of type classes in advanced type systems. In particular, while coherence is arguably a desired property, no dependently typed language attempted to implement coherent classes so far. Agda, Coq, Idris and Lean all forgo coherence. Moreover, some stronger type systems with richer notions of equality are inherently at odds with class coherence.

Below I discuss the merits and prospects of type classes, with focus on advanced future languages. I try to adopt a general perspective, from which type classes can be viewed as a particular method of program inference and synthesis. 

#### 2. About type classes

##### 2.1. Overview

Type classes were originally introduced by [Wadler](http://homepages.inf.ed.ac.uk/wadler/topics/type-classes.html) as a principled and efficiently implementable form of ad-hoc polymorphism. I do not aim to provide an introduction to type classes in this article; I assume that the reader is already familiar with them. Instead I seek to conceptualize them in a slightly unusual way. Thus, my short definition has a different emphasis than ad-hoc polymorphism: 

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

A natural solution would be `h ab = g f ab`. We can arrive at the solution by searching the available definitions in the context and trying to plug them together in a way that yields the desired type. This activity is analoguous to formal proof writing as per the [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence). A large part of practical programming can be understood as a task like the above one: given a context of already implemented code, write additional code with given type and semantics. Note that our toy example is solvable purely by playing with types, but given some formal notion of semantics, "search" can encompass that as well. 

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

A succesful search allows the compiler to plug in the appropriate `show` definitions, thereby producing a "proof". In fact, the above procedure is just a simple form of [resolution](https://en.wikipedia.org/wiki/SLD_resolution), similar to that used in logic programming.

As long as instance and class definitions are kept in a tractable form (in Haskell's case, instances are [Horn clauses](https://en.wikipedia.org/wiki/Horn_clause)), instance resolution remains a tractable problem. This constitutes a solution to the first problem, the problem of large search spaces. Practical implementations in programming languages all use some variation of type-directed resolution, but in principle search could be constrained in different ways (this is a topic that could be worthwhile to explore).

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

In contrast, the above notion is not readily expressible in [Java](http://stackoverflow.com/questions/32789437/constrained-interface-implementation) or Eiffel. In Java one could try the following:

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

Type classes enable recursion on the structure of types, making choices based on specific subtypes. Note though that types classes are not the only way to achieve this, and we'll explore alternative solutions in section 3. 

> Should types expose information, or instead hide unnecessary details? In the brave new world of (dependent) type-theory-based programming my choice shall be firmly the former option. Information hiding only makes sense in a dangerous world where programmers communicate intent by giving classes descriptive English names and preventing (with more or less success) breaking invariants by making methods private. `MouseEventAdapter` is in the eye of the beholder. Its meaning is hinted at by its name, and defined by the implementation. Its productive use hinges on mutual understanding of programming patterns. 

> But if types carry more information, they can be more useful, and we can also prove and enforce more properties. `Pair` is more informative than `PairOfInt`, and in turn [least fixed points of functors](https://en.wikipedia.org/wiki/Initial_algebra) are more informative than plain recursive data types. In the brave new world, we could have analogues of `MouseEventAdapter` types that encode their meaning in their structure, and invariants could be preserved by making illegal states unrepresentable. In that world, the name `MousEventAdapter` could be still useful as a shorthand, and we could still present lean API-s, but there wouldn't be nearly as much reason to hide details. After all, those with a clean record shouldn't have anything to fear.

On another note, type classes also have a favorable weight-to-power ratio in terms of runtime performance. The Rust programming language extensively uses type classes, but without any runtime cost, since the relatively simple Rust type system (no higher-rank polymorphism, no polymorphic values inside data types) allows compile-time specialization and inlining of all instances. Inlining and specialization can cause excessive code size though, which should be considered as a trade-off, but type classes give compilers considerable freedom to specialize where they see benefit to it. This compares favorably to OOP polymorphism, where devirtualization can't be performed as robustly or universally, or it requires runtime JIT assistance, as in the case of Java. In general, more information in static types helps code optimization as well. 

> Current dependently typed languages tend to have an *excess* of static information that is largely ignored by backends, because there hasn't been yet relevant research in this area, or there hasn't been need for that much performance.

##### 2.4. Coherent type classes

Let's start off by defining coherence:

> **An implementation of type classes is coherent if all instances with equal types are equal.**

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

Coherent classes also have the "diamond" property (see e. g. [Edward Kmett](https://www.youtube.com/watch?v=hIZxTQP1ifo)), namely that there could be multiple derivations of *constraint entailment*, but all derivations result in the same instance:


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

Of course, coherence already implies that all derivations must agree. The diamond property is interesting because it illustrates that coherent systems can hide the details of resolution algorithms from programmers. Incoherent systems should also behave in a well-defined and sensible way, but they must necessarily expose the resolution procedure so that programmers can anticipate its effects. 

What makes coherent type classes such? Certainly, we should expect that strong guarantees are realized through restrictions, which is the case here:

- All instances must be defined in instance declarations and cannot be passed around explicitly. Such explicit passing obviously contradicts coherence, since it allows creating instances from arbitrary values. 
- The instance heads of a class must be disjoint and non-overlapping, provided that we allow modularity, i. e. different sets of instances visible in different modules. If we allow both modularity and overlapping then it could be the case that a module defines a more specific overlapping instance than another module, and thus two different runtime instances may end up in the program. On the other hand, overlapping instances could be made coherent if we give up modularity, i. e. mandate a single globally consistent set of instances, but this option isn't practical in any realistic module system. 
- There must be no "orphan instances", i. e. instances such that their classes aren't declared in the module of the instance, and the types in their heads aren't defined in the module either. In the presence of orphan instances we could just define two different orphan instances in different modules, then export them wrapped in a runtime box, to be used in a single module - destroying coherence.

Backtracking instance resolution is also incompatible with coherence and modularity. Disjoint instance heads eliminate non-determinism in instance matching, so the only remaining point for backtracking choice would be instance constraints. In pseudo-Haskell:

```haskell
instance (Ord a || Eq a) => Foo a where ...
  -- There must be some mechanism here for dispatching on the presence of `Ord a` or `Eq a`
```

However, it's easy to see that this is equivalent to backtracking choice with two obviously overlapping instances:

```haskell
instance Ord a => Foo a where ...
instance Eq a => Foo a where ...
```

There is some variation in the handling of overlapping and orphan instances in languages with coherent classes. GHC Haskell allows orphan instances (with compile-time warnings), and one can also [enable overlapping instances](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/type-class-extensions.html#instance-overlap) through a compiler pragma. Rust disallows both.

##### 2.5. Incoherent type classes

Incoherent classes have their own set of advantages: they can be considerably more flexible.

First, they allow first-class treatment of instances: they become ordinary values that can be explicitly passed around. Programmers can override implicits with explicit details.

In Agda notation, instance arguments are indicated by double braces:

```agda
record Monoid (A : Set) : Set where
  field
    mempty : A
    mappend : A -> A -> A

twice : {A : Set} {{monA : Monoid A}} -> A -> A
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

With coherent instances, we're forced to have only one instance for an instance head, even when there could be plausibly more. In Haskell, multiple instances are handled through "newtype"-s, i. e. unary wrappers without runtime cost that introduce strongly-typed aliases.

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

`Sum a` and `Product a` are types that differ from the underlying `a`-s, although they have the same runtime representation. They allow us to define to different `Monoid` instances. Their drawback is that we must use the `Plus` and `Product` constructors to wrap and unwrap values. This can be annoying, so Haskell [has a mechanism](https://www.cis.upenn.edu/~eir/papers/2014/coercible/coercible.pdf) for safely coercing values between representationally equal types:

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

The first solution has significant drawbacks. Algorithms that require having the same ordering for two containers (for example, efficient set union) are impossible to implement. I find the second solution better and its complexity cost acceptable. An example for the second solution in the wild is [C++ STL containers](http://en.cppreference.com/w/cpp/container).

##### 2.6. Comparing merits

What's the verdict on coherence, then? 

First, I posit that coherence has significant benefits in robustness and scalability, and thus I will henceforth consider it desirable in hypothetical languages. A good heuristic in programming and mathematics is to use the least powerful tool that gets the job done, because they tend to be simpler, easier to reason about, and also more generally applicable (that said, in software development we have a great number of tools that are complicated and weak at the same time).  

Still, there are many caveats and footnotes to this. 

First, coherence and incoherence are a convenient and simple categorization of real-world systems, but there are many features and details that determine type classes' usability in the context of a given language. There's a great variance in the methods for incoherent search. The [`IncoherentInstances`](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/type-class-extensions.html#instance-overlap) extension of GHC Haskell is rather simple, Agda's instance search is more complex, Coq also features backtracking, while Scala's search doesn't have backtracking but is very complex partly because it's embedded in a complex language. It might be the case that some real-world systems benefit from incoherence and never suffer from their drawbacks, or there may be some sweet spot of search complexity that balances robustness and flexibility, and it isn't necessarily coherent search. 

> This connects to the general issue of software methodology and productivity research, which hasn't delivered specatular results so far (that I know of). In particular, there is a large amount of quantitative research that could be potentially done to inform programming language design. Such reasearch would be preferable to the status quo of language design which mostly builds upon accumulated subjective experience of programmers and public discussion (where the most vociferous participants may or may not emphasize the practicaly most important points).

Second, proof writing and software development have differences that affect the usefulness of various search techniques. 

In software development, the norm is that programs carry relatively few proofs and semantics is only loosely determined by types. Software projects have comparatively large amount of code and complex modularization, and code tends to be refactored and modified more frequently. Here, a large chunk of program semantics is not formalized and instead kept managed mentally by developers. In this environemnt coherence provides a relatively large benefit, as it alleviates mental burden and makes programs more robust to modification. 

In proof writing, very frequently the operational semantics or performance of code (proof terms) isn't relevant at all; the primary goal is to provide *some* proof. This ethos is exemplified by Coq where users often just throw powerful automated search at various problems without even making an effort to understand the resulting proof (if there is one). It's not an inherently bad practice, since there is finite amount of human effort that can be expended on understanding things, and it's often better to focus on understanding the most important points and leave dirty work to automation. Also, since specifications are so precise, erratic instance resolution rarely causes sneaky errors. Plugging in a wrong instance tends to prevent type checking, since proofs often rely on the implementations of class methods. In this environment coherence provides a relatively small benefit. 

However, we would like to ultimately integrate software development and proof writing seamlessly. Currently, Coq and Agda are very cumbersome for software development, and Haskell is very cumbersome and unreliable for proof writing. Designing type classes for an integrated environemnt would require a careful balancing act and provision of orthogonal search techniques for proof and program writing. 

#### 3. Alternatives to type classes

In this section I examine whether some features and techniques could make type classes superfluous. I single out features such that I have in the past encountered people characterizing them as alternatives to classes (though I'm afraid I cannot provide specific references to such discussions). 

##### 3.1. Generic programming

By "generic programming" I mean programming with closed type universes, which includes solutions such as ["Scrap Your Boilerplate"](https://hackage.haskell.org/package/syb) and [GHC.Generics](https://hackage.haskell.org/package/base-4.8.1.0/docs/GHC-Generics.html) in Haskell and direct uses of type universes in dependent languages (see e. g. [McBride](https://www.cs.ox.ac.uk/projects/utgp/school/conor.pdf)).

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

For the sake of brevity I shall omit more Agda code here. The rest of my example can be [found here](https://github.com/AndrasKovacs/pny1-assignment/blob/master/SimpleGenerics.agda). The key point is that by having an internal description of types, we can define generic operations that work on values of *all* described types. For example, we can implement [generic equality](https://github.com/AndrasKovacs/pny1-assignment/blob/master/SimpleGenerics.agda#L72), pretty printing, serialization, zippers, lenses and more. In more advanced (dependent) languages we can define subsets of a larger universe using type-theoretic predicates, and define generic functions that work only on some subsets; for example generic equality that only works on types that doesn't contain function fields. 

In practical implementations of generic programming in Haskell, [Clean](http://clean.cs.ru.nl/download/html_report/CleanRep.2.2_9.htm#_Toc311798067) or [Purescript](http://pursuit.purescript.org/packages/purescript-generics/0.7.0), generic functions are used via an extra conversion from user-defined types to generic representations and back. This has some performance overhead, and generic representations also tend to have greater memory footprint. Nevertheless, optimized generics are possible, as are languages that have generic types by default, or have [*all* types](http://www.ioc.ee/~james/papers/levitation.pdf) in generic form.

Turning back to type classes, can we expect that generic programming can replace them? 

The answer is likely no. Generic programming does overlap with type classes, and it's usually a good choice in the overlapping cases (decidable equality, enumeration, serialization, etc.), but many classes are extremely hard to express generically. For example, instances for most algebraic structures cannot be derived mechanically. Natural numbers form a ring, but ring-ness can't be easily decided for arbitrary types.

Also, despite our best intentions a large amount of meaning and intent is expressed by the *naming* of types. Programmers often use isomorphic but differently named types, because most of the time there's no need or energy to express all relevant semantics in types. Thus, generics may be good for serialization, but not quite good for pretty printing, since generic functions don't know much about the context in which a type is used or the intent of the programmer. It's a common point of pain in programming languages that support some form of printing for all types: the printed outputs tend to be messy, verbose or uninformative. 

But I must stress that there is a considerable amount of research on dependently typed generic programming that enables extremely powerful abstractions (mind-blowing is an appropriate term). For example, see Conor McBride's work on [ornaments](https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/LitOrn.pdf), which are descriptions of *annotations*, *modifications* and *information erasure* on types. Ornaments describe notions such as "lists are natural numbers annotated with fields of some type" and "the erasure of fields from lists yields a natural number which is the length of the list", and they also enable some automatic lifting of functions operating on a type to a modified version of that type. Generics also tend to synergize with type classes: in Haskell, a less expressive language, type classes are even required for defining generic functions, since they're the main mechanism for dispatching on types. 

##### 3.2. Higher-order modules

These come under a variety of names. They first became popular in ML, where they're called ["functors"](https://www.cl.cam.ac.uk/teaching/1011/ConceptsPL/SMLmodules.pdf). Sometimes they're called first-class modules. The core features are:

- Modules can be parametrized by values, types and other modules, and can be applied to parameters like functions.
- Modules support existential (abstract) types, or more generally, existential quantification.
- Modules form namespaces that can be nested, and name visibility can be flexibly controlled.

Coq, Agda and Lean all support such modules. Higher-order modules combined with dependent types are extremely powerful and can easily express any [*algebraic specification*](https://en.wikipedia.org/wiki/Algebraic_specification). From now on I'll call them "Agda-style modules" and provide examples in Agda since that's I'm familiar with the most (see [this page](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.Modules) for reference on Agda modules). 

Agda-style modules disallow any kind of nominal ambiguity and overloading. Instead, it provides the programmer extremely fine-grained control over namespaces and makes it possible to assemble modules and namespaces on-the-fly. In Agda, it is possible to import modules inside *arbitrary expressions*, including *type annotations*, and we can declare (nested) modules even in local scope. We can also qualify, rename and hide imported names. 

Thus, the Agda standard library deliberately has many colliding names. The standard practice is to have only a small amount of top-level imports in a source file, and import locally whenever some functionality is needed. For a silly example, lists have an obvious `Monoid` implementation, and we can locally use the standard `Monoid` names, which are `∙` for the binary operation and `ε` for identity:

```agda
open import Algebra   -- contains the Monoid record declaration
open import Data.List -- contains the monoid implementation for List

myListFun : {A : Set} → List A → List A → List A
myListFun xs ys = ys'
  where
    open Monoid (Data.List.monoid _) -- locally open module    
    xss = xs ∙ xs    
    ys' = ys ∙ xs ∙ ε
```

Here, in `open Monoid (Data.List.monoid _)`, `Monoid` refers to the declaration in `Algebra`, and `Data.List.monoid` refers to the implementation for lists. Also, `Monoid` is just a record declaration whose fields are the monoid operations and axioms - records are also modules. It's possible to write custom `Monoid` implementations, and open them instead. It's also possible to override any field of a record, or selectively hide, redefine or reexport record/module fields. 

This is a lot of power. The Agda standard library makes judicious use of it, and takes abstraction and modularization rather far, which can be downright scary for newcomers. For an illustration, see the source for [`Algebra`](https://github.com/agda/agda-stdlib/blob/master/src/Algebra.agda). 

The class constraints that we had in our type-class-based code, can be directly rewritten as explicit dictionary passing:

```haskell
class Foo a where
  ...
  
f :: Foo a => t
f = ...
```

The new code is:

```agda
record Foo (A : Set) : Set where
  -- ...
  
f : {A : Set} -> Foo A -> T
f foo = ...
  where open Foo foo
  ...
```

However, this quickly leads to tedious manual plumbing of dictionaries. In many cases, we can introduce a new module, and parametrize a large block of code with a dictionary:

```agda

module M (A : Set) (foo : Foo A) where
  open Foo foo
  
  f : ...
  f = ...
```

Now, by `open M A foo`, we pass a dictionary to an entire namespace, so there's much less need for manually applying functions to `foo` instances. 

So, should we scrap type classes and use modules instead? Well, probably not.

It's indeed possible to have a *decent* programming experience only with modules. But modules are a bit too literal-minded and laborous. They present a non-trivial amount of inconvenience that lazy programmers are all too keen to avoid. They don't really do *search*, which as I described previously is at the heart of type classes. They make it very easy to do instance search manually, they make it easy to navigate namespaces, they just don't search for us. 

In general, methods for overloading and code abstraction should let us write code that looks a bit like mathematics papers. There, authors often spend a paragraph or two reviewing notation, then dive into the subject, or often just assume the usual notational conventions. They also tend to overload symbols based on their usage, without spending too much time pointing out different usages. The reason why code should look so is that math papers evolved over a long time for optimal ability to convey ideas, and strike a good balance between literal-minded verbosity and obscure terseness. Type classes come pretty close to this. In contrast, modules mandate an explicitness that's tad too stifling. 

It's a good idea though to have higher-order modules and type classes at the same time, and indeed it's done so in Agda, Coq and Lean.

#### 4. Coherent classes in dependent languages

In dependent languages, the language of types and terms are the same. Given that types can be indexed or parametrized by values, values must be able to appear in instance heads. It's reasonable to allow class parameters that are values, or any terms indeed, therefore it might be better to speak of simply "classes". I'll still use "type classes" though, for consistence. 

##### 4.1. Reviewing equality

As I mentioned in the introduction, no dependently typed language implements coherent type classes as of now. To see why, let's review and expand the definition of coherence:

> **An implementation of type classes is coherent if all instances with equal types are equal.**

However, the exact notion of equality is very important here, both of types and values. In dependently typed languages equality  greatly influences the range and style of proofs that can be expressed, and it's probably the most important point of divergence among different languages (extensional vs. intensional type theories, univalent type theories etc...).

In type theories we usually consider two concepts of equality (for a short alternative overview, see [Gratzer](http://jozefg.bitbucket.org/posts/2014-08-06-equality.html)).

*Definitional equality* is the kind of equality that is decidable by the type checker. For example, whenever we have a function application `(f x)`, the type checker must be able to decide that the input type of `f` is equal to the type of `x`. 

*Propositional equality* is can be proved inside the language and can be used to prove properties or coerce values between equal types. Propositional and definitional equality usually coincide for *closed expressions*, i. e. expressions that contain no free variables. For example, all closed terms with natural number types must reduce to a specific numeral (in a total language):

```agda
(3 + 4 + 0) -- reduces to 7
```

However, open terms may or may not do so:

```agda
_+_ : Nat -> Nat -> Nat
0     + b = b
suc a + b = suc (a + b

-- (n + 0) is in normal form
-- (0 + n) reduces to n
```

Here `n + 0` and `n` are not definitionally equal. Definitional equality usually contains equality modulo alpha-beta-eta conversion; here we have beta conversion between `0 + n` and `n` since we defined addition with recursion on the first argument. `0 + n` is definitionally equal to `n` for any specific `n` numeral, but the type checker doesn't know this (and in general such equalitites are undecidable). We can rectify this issue in a dependent language by introducing types that carry evidence for equality:

```agda
-- in Agda (simplified)
data _≡_ {A : Set} (x : A) : (y : A) → Set where
  refl : x ≡ x
  
-- in Haskell
data (:~:) (x :: k) (y :: k) :: * where
  Refl :: x :~: x 
```

Now we can write a function with type `(n : Nat) -> n + 0 ≡ n` ([see proof](https://github.com/AndrasKovacs/pny1-assignment/blob/master/Notes.agda#L4)). We say that `x` is propositionally equal to `y` if `x ≡ y` or `x :~: y` is provable inside the language. 

With type classes, propositional equality becomes important when matching instance heads. Recall from section 2.4 that coherent type classes must have disjoint instance heads. We refine this to the following:

> **Coherent type classes must have propositionally disjoint heads.**

Consider a class has two instances that are inequal definitionally, but equal propositionally:

```haskell
-- not valid Haskell
class Foo (n :: Nat) where foo :: String
instance Foo (n + 0) where foo = "A"
instance Foo n       where foo = "B"
```

In an open context with `n :: Nat`, instance resolution may give us a dictionary with type `Foo (n + 0)`, but we can coerce that to `Foo n` using the proof that `(n + 0) :~: n`. The coerced dictionary is inequal to the dictionary resulting from resolving `Foo n`. For this reason, Haskell prohibits type families (which are like functions on the type level) in instance heads. 

##### 4.2. Preserving coherence

In general, one can preserve coherence by restricting instance heads to a language fragment with decidable propositional equality. Haskell does exactly this: it has a first-order term language of (necessarily injective) type constructors. However, the same solution would be awkward in a dependent language, since many commonly used types are parametrized with functions, for instance [sigma types](https://en.wikipedia.org/wiki/Dependent_type#Dependent_pair_type). Let's review some potential solutions. 

**First**, if our language doesn't have [function extensionality](https://ncatlab.org/nlab/show/function+extensionality), then we have considerable amount leeway to use functions, since in this case definitional equality of functions coincides with propositional equality. The only expressions with undecidable propositional equality are *open expressions with non-function types containing function applications*. 

For example, if `f` and `g` are top level functions, then `f` and `g` are OK in instance heads. `f x` is also OK if `f x` still has a function type (it's an unsaturated application) and `x` is OK as an expression. On the other hand, `n + 0` is not OK, since it has a value type (`Nat`), and it contains a function application. 

Restricting instance heads in this manner seems a good compromise. From the top of my head, I can't think of a useful type that would be exiled from classes. We lose one use case though, namely reflection of open expressions, which can be convenient for automatic solvers. 

For example, we might want to use [proof by reflection](http://adam.chlipala.net/cpdt/html/Reflection.html) for solving equations on monoids. It consists of taking equations like `a * ((b * 0) * c) = a * (0 * (b * c))`, normalizing both sides by reassociating operations and eliminating identities, then checking for definitional equality. We could implement this using classes by writing one instance for one normalization rule, while simultaneously building a proof that the normal form is equal to the original expression. See [this file](https://github.com/AndrasKovacs/pny1-assignment/blob/master/ClassySolver.agda) for a complete Agda example. 

Fortunately, there is already native reflection support for such solvers in [Coq](http://adam.chlipala.net/cpdt/html/Reflection.html) and [Agda](https://www.staff.science.uu.nl/~swier004/Publications/EngineeringReflection.pdf). Reflection returns a syntactic representation of the type of a hole or metavariable, which can be subsequently used to compute proofs. Thus, it's not painful to eschew reflection by type classes. Also, natively supported reflection should be more convenient and performant than classes. 

**Second**, we can require proofs of propositional disjointness from programmers. In other words, the compiler tries to prove disjointness of instances by some incomplete procedure, and demands a proof from the programmer if it gets stuck. 

This may seem a bit intrusive. It's also anti-modular in the sense that programmers would have to add or remove proofs to their instance definitions depending on other instances in scope, which may come from imported modules (even transitively!). However, given a sufficiently smart compiler, the amount of proof obligations could turn out to be pretty low, especially considering that useful instances rarely have undecidable equality, as we've seen. But then we might ask whether it pays off to support this mechanism - why not just stick with the previous solution in this section and restrict the instance heads?

However, as we move up to type theories with more sophisticated equality, this option could become more viable.

##### 4.3. Adding extensionality

An obvious power-up would be adding function extensionality to our language. This is relatively realistic in a future language, since [NuPRL](http://www.nuprl.org/) already has it, and even in intensional type theories one can find potential solutions, such as [Observational Type Theory](http://www.cs.nott.ac.uk/~psztxa/publ/obseqnow.pdf), and univalent type theories also have function extensionality (see on [page 144](https://hott.github.io/book/nightly/hott-online-1007-ga1d0d9d.pdf)). We'll discuss univalence later in more detail.

Now, functions can *never* appear in instance heads, simply because any function can be proven equal to another by extensionality. This is a rather serious limitation, and it makes it all the more appealing to require proofs of disjointness. 

There are other forms of extensionality. If our language supports codata and coinduction, then it could as well support extensionality for codata. In languages without such extensionality, values of codata are equal if they are definitionallly equal. For example, an infinite stream of repeated numbers is definitionally equal only to itself, but it's observationally equal to any suffix of itself. 

```idris
-- pseudo-Idris
codata Stream : Type -> Type where
  Cons : a -> Stream a -> Stream a
  
head : Stream a -> a
head (Cons a as) = a

drop : Int -> Stream a -> Stream a
drop n as | n <= 0 = as
drop n (Cons a as) = drop (n - 1) as

ones : Stream Int
ones = Cons 1 ones

ones' : Stream Int
ones' = drop 10 ones -- equal to "ones", but we can't prove this
```

We can define stream equality as a stream of equalities (in other words, a [bisimulation](https://en.wikipedia.org/wiki/Bisimulation)):

```idris
codata StreamEq {a : Type} : Stream a -> Stream a -> Type where
  Cons : 
    {x : a} -> {y : a} -> {xs : Stream a} -> {ys : Stream a} 
    -> x = y -> StreamEq a xs ys -> StreamEq a (Cons x xs) (Cons y ys)
```
`StreamEq xs ys` supplies pairwise equality proofs for all elements. However, it's not as nearly convenient as full propositional equality, because it's not substitutive, and we also have to define types like `StreamEq` over and over for different codata. Codata extensionality allows us to derive propositional equality from bisimulations. Similarly as with function extensionality, codata extensionality makes disjointness of instance heads with codata undecidable. 

Other forms of extensionality are [propositional extensionality](https://ncatlab.org/nlab/show/propositional+extensionality) and [quotient types](https://en.wikipedia.org/wiki/Quotient_type), which I shall not discuss in detail here. Let it be said that they are nice things that we would like to have in our type theory, but they also make propositional equality less decidable.

We shall say more about the Holy Grail of extensionality: univalence.

##### 4.4. Univalence

Univalence can be described as "universe extensionality". Defining the concept:

- Two `A` and `B` types are equivalent if there exist `f : A -> B` and `g : B -> A` functions that are each other's inverses.
- A universe of types is univalent if from each `A ~ B` equivalence we can derive an `A ≡ B` proof of propositional equality.

In Agda notation (ignoring universe levels):

```agda

open import Data.Product
open import Relation.Binary.PropositionalEquality

Eqv : Set → Set → Set
Eqv A B =
  ∃ λ (f : A → B) → ∃ λ (g : B → A)
  → (∀ a → g (f a) ≡ a) × (∀ b → f (g b) ≡ b)
  
univalence : Set₁
univalence = ∀ {A B} → Eqv A B → A ≡ B
```

More succinctly, the univalence axiom says that equivalence is equivalent to equality. From equality we can trivially derive equivalence:

```agda
idToEqv : ∀ {A B} → A ≡ B → Eqv A B
idToEqv refl = (λ x → x) , (λ x → x) , (λ x → refl) , (λ x → refl)
```

Univalence completes the equivalence in the other direction. 

Intensional type theory together with univalence as axiom can be viewed as a formalization of homotopy theory. A good comprehensive introduction to the subject can be found in the [Homotopy Type Theory book](http://homotopytypetheory.org/book/). 

Note that working with equality proofs in univalent theories can involve a significant amount of computation. In plain old type theories, equality proofs can be usually erased from runtime, since they express that two objects are represented by literally the same pattern of bytes (in intensional type theory) or that objects are computationally indistinguishable from within the system (when we add various forms of extensionality). With univalence, there can be many different proofs for `A ≡ B`, since there can be many different equivalences between types. For example we could use both `id` and `not` in a proof for `Bool ≡ Bool`.  Also, there is non-trivial machinery that makes use of the computational content of equality proofs to generate new implementations whenever we use equalities to coerce values or substitute types within types. 

For a while it's been an open problem whether it's possible at all to implement such machinery. Currently, there is research in [cubical type theory](http://www.math.ias.edu/~amortberg/papers/cubicaltt.pdf) that demonstrates that effective computation with univalence is possible, and also some [experimental implementation](https://github.com/mortberg/cubicaltt). Thus, there is good reason to believe that a practical implementation of univalent type theory will eventually emerge.  

It's hard to overstate the sheer power of univalence. 

As an example, suppose that we implement unary natural numbers and the usual arithemtic operations. We also define binary numbers as an inductive type. Now, if we prove equivalence of the two representations, from any function that operates on unary numbers, we automatically get a new function operating on binary numbers such that *it preserves all semantic properties* of the original function, translated to the new representation. 

In a sense, univalence is the ultimate constructive demonstration of subsitutability of equals: it lets us substitute equivalent types in any context, and spits out new proofs (implementations) automatically. 

Needless to say, univalence completely crushes any attempt of coherent type classes. 

The whole notion of `newtype` as it's in Haskell is futile now. Since newtypes introduce isomorphic types, they also introduce equal types here. Any type with a countably infinite number of elements is now equal to natural numbers - so we can't define different instances for them. We can't define different `Show` instances for `BinaryTree Nat` and `List Nat`. Generally, with any definition we define a whole equivalence class of types, of which our defined type is a representative.

Before in section 2.2 I talked chidingly about types whose intended meaning is encoded in their names, instead promoting types that encode meaning in their structure. Univalence takes this ethos to its logical conclusion, stripping type definitions of all surface qualities and going right to their abstract core.

#### 5. Taming incoherent classes

We've seen that in the long term (i. e. with univalence) it might be not feasible to keep coherence. Let's review some solutions and factors that might make incoherence more palatable. 

There's a family of types for which coherence is always assured, independently from any search procedure. These are *irrelevant* or [*propositional*](https://ncatlab.org/nlab/show/mere+proposition) types:

>**Propositional types are types that have at most one element up to propositional equality.**

Class instances are just a product of the class methods, so if all methods are propositional, then the type of instances is also propositional - therefore the class is coherent. The question is: how many useful classes are propositional? 

Actually, quite a few. Often, if we pin down the properties of a class precisely enough it becomes uniquely specified.

A classic example is decidable equality. While regular `A -> A -> Bool` equality admits many implementations, decidable equality  with type `(x y : A) → (x ≡ y) ∨ ((x ≡ y) → ⊥)` has an extensionally unique implementation ([see my proof here](https://github.com/AndrasKovacs/pny1-assignment/blob/master/DecEqProp.agda). This means that we can have a `DecEq` class, and recover simple Boolean equality from decidable equality, or we could have both equalities as methods, and require a proof (a third method) that they agree with each other. 

What about specialized equalities? In Haskell, people sometimes use `newtype` wrappers to provide alternative instances for common classes. For example we could have a syntax tree with labels and other metadata that we would like to ignore when computing equality. With decidable equality, we can't implement "forgetful" alternative instances, right? Well, we can, if we use some homotopy-flavored type theory with [higher inductive types](https://ncatlab.org/nlab/show/higher+inductive+type). Higher induction allows us to specify *equality* constructors for data types, along with the old constructors for values. For example, a HIT wrapper that "forgets" the first field of a tuple could be the following:

```agda
data SquashFst (A B : Set) : Set where
  wrap   : (A , B) → SmashFst A B  -- value constructor
  squash : ∀ (a a' b) → wrap (a , b) ≡ wrap (a' , b)  -- equality constructor
```

`squash` makes the first elements irrelevant in determining equality of the wrapped pairs. We are then restricted (by the rules of HIT-s) to only write `f : SquashFst A B -> C` functions such that `∀ a a' b → f (wrap (a, b)) ≡ f (wrap (a', b))`, i. e. all functions must respect `squash`. Thus, `SquashFst` works like our usual Haskell `newtype` wrappers, except that it captures our intent far more precisely.

A striking property of propositional types is that *any* search and automation is safe to employ. In fact, search on propositional types is the defining and most important feature of refinement types, which is a promising area for lightweight program verification; see e. g. [Liquid Haskell](http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/about/).

However, many types are not propositional, and it's very hard to make them so by unique specification. For example, take the usual [`Traversable`](https://hackage.haskell.org/package/base-4.8.1.0/docs/Data-Traversable.html) class from Haskell. Technically, traversal in any linear order is lawful (see the laws in the precious link), but we certainly don't want to mix together forwards and reverse traversals haphazardly in our code (which might be the case with incoherent `Traversable` instances lying around). However, specifying traversal order is difficult and requires complicated setup. 

Some types are propositional, but can't be easily proven so, because the proofs rely on parametricity which is usually inexpressible inside the language. For example, `{A : Set} → A → A` and the class `Functor` are propositional. 

"If you rely on a property, why don't you specify it in types?" is a valid retort to proponents of coherence. Dependent types let us specify almost all relevant semantic properties. But sometimes the cost of specification and proving is too high, and we would rather just write and push out working code as quickly as possible. Of course, it's not a binary question of writing proofs or not. If we specify more precisely, our code gets more resilient to any kind of bugs, including those bugs that may result from class incoherence. 

#### 6. Conclusion

Wrapping up our main points:

- Type classes are very effective at introducing code generation and boilerplate removal in a way that is intuitive and lends itself easily to software abstraction.
- Proposed alternatives to type classes fall short of providing the same set of benefits. 
- Class coherence is important, especially in the context of software development.
- However, maintaining coherence gets more difficult as we switch to more expressive languages, and it becomes outright infeasible when we get to univalent type theories. 
- Precise specification offsets fragility introduced by incoherent classes. 

As to future research, I briefly mentioned in section 2.1. that *constrained search* could denote a wide range of solutions, which wouldn't necessarily be similar to type classes. For example, SMT solvers used in refinement type systems can be also viewed as a tool for constrained search. It would be interesting to try come up with radically different designs. 

Also, it would be a fun and useful project to formalize class coherence, preferably in some existing machine-checked system, but it would be good if we had any sort of formal model. Currently, type classes are viewed (rightfully) as a theoretically ad-hoc preprocessing stage before translating frontend code to elegant and small core type theories. I also don't know of any formalization effort, and as of recently even [experts](http://cstheory.stackexchange.com/a/12530/22548) were like me in this regard.

#### Appendix: test code for classes in Idris, Coq and Agda

I included some bits of test code for the above three languages. I tried to investigate how they handle propositionally overlapping instances with function applications. 

In [Idris](https://github.com/AndrasKovacs/pny1-assignment/blob/master/ClassTest.idr), I found out that the language is just bugged out in this regard, and doesn't attempt to implement it properly. 

In [Agda](https://github.com/AndrasKovacs/pny1-assignment/blob/master/ClassTest.agda), I found that instance resolution usually refuses to decide in ambiguous cases with function applications, but I haven't yet looked at the underlying causes or the details of the implementation. Agda's type class implementation still has rough edges, and usually it's just not performant and stable enough for large-scale uses. 

In [Coq](https://github.com/AndrasKovacs/pny1-assignment/blob/master/ClassTest.v), I found that the language has pretty robust instance resolution (which is borrowed wholesale from the pre-existing tactics langauge), but also that it's very "trigger-happy" and silently solves even badly-behaved and silly examples, such as the `Foo` class in my example files. 

I have not played around with the [Lean](http://leanprover.github.io/) prover. It might be worth a look, especially since Lean prides itself on very fast instance resolution that is organically integrated into the elaborator.  



