data Desc : Set where
  _+_   : Desc → Desc → Desc  -- sum
  _*_   : Desc → Desc → Desc  -- product
  rec   : Desc                -- recursion
  fix   : Desc → Desc         -- constant field
  one   : Desc                -- unit

data ⊤ : Set where
  tt : ⊤

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B 

data _⊎_ (A B : Set) : Set where
  l : A → (A ⊎ B)
  r : B → (A ⊎ B)

mutual 
  ⟦_⟧ : Desc → Set → Set
  ⟦ a + b ⟧ i = ⟦ a ⟧ i ⊎ ⟦ b ⟧ i
  ⟦ a * b ⟧ i = ⟦ a ⟧ i × ⟦ b ⟧ i  
  ⟦ rec   ⟧ i = i
  ⟦ fix d ⟧ i = μ d
  ⟦ one   ⟧ i = ⊤
  
  data μ (d : Desc) : Set where -- fixpoint
    ⟨_⟩ : ⟦ d ⟧ (μ d) → μ d


-- Examples
------------------------------------------------------------

Nat Bool : Desc
Nat  = one + rec
Bool = one + one

List : Desc → Desc
List A = one + (fix A * rec)

pattern true  = ⟨ l tt ⟩
pattern false = ⟨ r tt ⟩

pattern zero = ⟨ l tt ⟩
pattern suc n = ⟨ r n ⟩

pattern nil = ⟨ l tt ⟩
pattern cons x xs = ⟨ r (x , xs) ⟩

four : μ Nat
four = suc (suc (suc (suc zero)))

add : μ Nat → μ Nat → μ Nat
add zero    b = b
add (suc a) b = suc (add a b)

concat : ∀ {A} → μ (List A) → μ (List A) → μ (List A)
concat nil         ys = ys
concat (cons x xs) ys = cons x (concat xs ys)

and : μ Bool → μ Bool → μ Bool
and true true = true
and _    _    = false

or : μ Bool → μ Bool → μ Bool
or true _ = true
or _    b = b


-- Generic equality
------------------------------------------------------------

mutual
  gEq : ∀ {A} → μ A → μ A → μ Bool
  gEq {A} ⟨ a ⟩ ⟨ a' ⟩ = gEq' {A} a a'

  gEq' : ∀ {A d} → ⟦ A ⟧ (μ d) → ⟦ A ⟧ (μ d)  → μ Bool
  gEq' {A + B} (l a)   (l a')    = gEq' {A} a a'
  gEq' {A + B} (r b)   (r b')    = gEq' {B} b b'
  gEq' {A + B} _       _         = false
  gEq' {A * B} (a , b) (a' , b') = and (gEq' {A} a a') (gEq' {B} b b')
  gEq' {rec}   a       b         = gEq a b
  gEq' {fix A} a       b         = gEq a b
  gEq' {one}   _       _         = true
