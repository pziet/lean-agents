import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

def Surjective {A B : Type} (f : A → B) : Prop :=
  ∀ y : B, ∃ x : A, f x = y
