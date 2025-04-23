import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Theorems.Definitions.Injective

variable {A B : Type} {f : A → B}

/--
Lemma 2: If f is injective and f(x₁) = f(x₂), then x₁ = x₂
-/
lemma injective_cancel_inner (hf : Injective f) (x₁ x₂ : A) (h : f x₁ = f x₂) :
  x₁ = x₂ :=
  sorry
