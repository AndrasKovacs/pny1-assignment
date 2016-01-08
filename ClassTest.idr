-- "type class arguments must be injective"
class Foo (n : Nat) where
  foo : Nat
  
instance Foo (S n) where
  foo = Z
  
instance Foo (plus n Z) where
  foo = S Z  

-- simply bugged - plus checks for "Nat -> Nat" too
class Bar (f : Nat -> Nat -> Nat) where
  bar : Nat
  
instance Bar plus where
  bar = Z
  
instance Bar minus where
  bar = S Z  
