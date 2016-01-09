open import Data.Nat
open import Relation.Binary.PropositionalEquality

n+0≡0 : ∀ n → n + 0 ≡ n
n+0≡0 zero    = refl
n+0≡0 (suc n) = cong suc (n+0≡0 n)

-- equality proofs allow coercion
coerce : ∀ {A B : Set} → A ≡ B → A → B
coerce refl a = a
