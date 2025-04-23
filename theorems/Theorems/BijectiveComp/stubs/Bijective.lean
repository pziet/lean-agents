import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Theorems.BijectiveComp.stubs.Injective
import Theorems.BijectiveComp.stubs.Surjective

def Bijective {A B : Type} (f : A → B) : Prop :=
  Injective f ∧ Surjective f
