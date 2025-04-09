import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

def Injective {A B : Type} (f : A → B) : Prop :=
  ∀ x₁ x₂ : A, f x₁ = f x₂ → x₁ = x₂
