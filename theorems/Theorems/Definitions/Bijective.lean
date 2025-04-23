import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Theorems.Definitions.Injective
import Theorems.Definitions.Surjective

def Bijective {A B : Type} (f : A → B) : Prop :=
  Injective f ∧ Surjective f
