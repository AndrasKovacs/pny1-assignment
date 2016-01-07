open import Data.Nat
open import Relation.Binary.PropositionalEquality

n+0≡0 : ∀ n → n + 0 ≡ n
n+0≡0 zero    = refl
n+0≡0 (suc n) = cong suc (n+0≡0 n)
