module ClassySolver where

-- Monoid solver using instance resolution. Doesn't fully work (unsolved metas),
-- but it illustrates the idea, in particular it would work if Agda's class implementation were more
-- robust and mature. 

open import Algebra
open import Data.Product
open import Level 

module MonoidSolver {l c}(mon : Monoid l c) where
  open Monoid mon

  record Normalize (x : Carrier) : Set (l ⊔ c) where
    constructor rec
    field
      normal : Carrier
      eq : x ≈ normal
  open Normalize ⦃...⦄ public

  normalize : (x : Carrier)⦃ _ : Normalize x ⦄ → Carrier
  normalize x ⦃ rec x' _ ⦄ = x'

  instance
    empty : Normalize ε
    empty = rec ε refl

    left-id : ∀ {x} → Normalize (ε ∙ x)
    left-id {x} = rec x (proj₁ identity x)

    right-id : ∀ {x} → Normalize (x ∙ ε)
    right-id {x} = rec x (proj₂ identity x)

    assoc-ok :
        ∀ {x y z}
      → ⦃ _ : Normalize x ⦄
      → ⦃ _ : Normalize y ⦄
      → ⦃ _ : Normalize z ⦄
      → Normalize (x ∙ (y ∙ z))
    assoc-ok {{rec x' px}}{{rec y' py}}{{rec z' pz}} =
      rec (x' ∙ (y' ∙ z')) (∙-cong px (∙-cong py pz))

    reassoc :
        ∀ {x y z}
      → ⦃ _ : Normalize x ⦄
      → ⦃ _ : Normalize y ⦄
      → ⦃ _ : Normalize z ⦄
      → Normalize ((x ∙ y) ∙ z)
    reassoc {x}{y}{z}{{rec x' px}}{{rec y' py}}{{rec z' pz}} =
      rec (x' ∙ (y' ∙ z')) (trans (assoc x y z) (∙-cong px (∙-cong py pz)))

    open-term : ∀ {x} → Normalize x
    open-term {x} = rec x refl

  solve :
    ∀ {x y : Carrier}
    ⦃ nx : Normalize x ⦄ ⦃ ny : Normalize y ⦄
    → Normalize.normal nx ≈ Normalize.normal ny
    → x ≈ y
  solve {x}{y}{{rec x' px}}{{rec y' py}} p = trans px (trans p (sym py))


open import Data.Nat
open import Data.List

open Monoid (Data.List.monoid ℕ)
module LM {α A} = MonoidSolver (monoid {α} A)

-- doesn't actually work fully, but it's cute
f : (xs : List ℕ) → xs ∙ [] ≈ xs
f xs = LM.solve refl
