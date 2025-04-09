import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import BijectiveComp.stubs.Injective
import BijectiveComp.stubs.Surjective

def Bijective {A B : Type} (f : A → B) : Prop :=
  Injective f ∧ Surjective f
