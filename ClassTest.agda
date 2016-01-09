open import Data.Nat
open import Relation.Binary.PropositionalEquality

module _ (n : ℕ) where

  record Foo (n : ℕ) : Set where
    field
      foo : ℕ
  
  foo : ∀ n ⦃ dict : Foo n ⦄ → ℕ
  foo n ⦃ dict ⦄ = Foo.foo dict
  
  instance
    fooA : ∀ {n} → Foo (suc n)
    fooA = record { foo = 0 }
  
    fooB : ∀ {n} → Foo (n + 0)
    fooB = record { foo = 1 }
  
  record Bar (f : ℕ → ℕ → ℕ) : Set where
    field
      bar : ℕ
  
  bar : ∀ f ⦃ dict : Bar f ⦄ → ℕ
  bar f ⦃ dict ⦄ = Bar.bar dict
  
  instance
    barA : Bar _+_
    barA = record { bar = 0 }
  
    barB : Bar _∸_
    barB = record { bar = 1 }

  b : ℕ
  b = foo 1 -- unsolved meta, however it becomes solved if we remove "fooB"

  a : ℕ
  a = foo (n + 0) -- unsolved meta

  c : ℕ
  c = bar _+_

  d : ℕ
  d = bar _∸_
