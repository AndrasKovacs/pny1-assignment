
Section ClassTest.
  Require Import Arith.  
  Variable N : nat.
  
  Class Foo (n : nat) := {
    foo : nat }.
  
  Instance fooA (n : nat) : Foo (n + 0) := {
    foo := 0 }.
  
  Instance fooB (n : nat) : Foo (S n) := {
    foo := 1 }.
    
  Definition foo' : forall (n : nat) {dict : Foo (n + 0)}, nat :=
    fun n dict => foo.

  Class Bar (f : nat -> nat -> nat) := {
    bar : nat }.

  Instance barA : Bar plus := {
    bar := 0 }.

  Instance barB : Bar minus := {
    bar := 1 }.

  Definition bar' : forall f {dict : Bar f}, nat :=
    fun f dict => bar.

  Compute (foo' 0). (* 0 *)
  Compute (foo' N). (* 0 *)
  Compute (foo' (N + 0)). (* 0 *)
  Compute (foo' (1 + N)). (* 1 *)

  Compute (bar' plus). (* 0 *)
  Compute (bar' minus). (* 1 *)

End ClassTest.
