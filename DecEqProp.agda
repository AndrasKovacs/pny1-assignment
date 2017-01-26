
-- proof that decidable equality is propositional
-- assuming fun. ext. + Axiom K, but actually this is true even without Axiom K
-- since any type with dec. equality is a set by Hedberg's theorem (which I omit here).

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty

postulate
  funext :
    ∀ {α β}{A : Set α}{B : A → Set β}(f g : (a : A) → B a) → (∀ a → f a ≡ g a) → f ≡ g

IsProp : ∀ {α} → Set α → Set α
IsProp A = (x y : A) → x ≡ y

DecEq : ∀ {α} → Set α → Set α
DecEq A = (x y : A) → Dec (x ≡ y)

⊥-prop : IsProp ⊥
⊥-prop () ()

lem : ∀{α}{A : Set α} → (f g : (a a' : A) → Dec (a ≡ a')) → ∀ a a' → f a a' ≡ g a a'
lem f g a a' with f a a' | g a a'
lem f g a .a | yes refl | yes refl = refl
... | yes p | no ¬p = ⊥-elim (¬p p)
... | no ¬p | yes p = ⊥-elim (¬p p)
... | no ¬p | no ¬p₁ = cong no (funext ¬p ¬p₁ (λ a → ⊥-prop (¬p a) (¬p₁ a)))

eq-prop : ∀ {α} A → IsProp {α} (DecEq A)
eq-prop A f g = funext f g (λ a → funext (f a) (g a) (lem f g a))
