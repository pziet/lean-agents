import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import BijectiveComp.stubs.Injective

variable {A B C : Type} {f : A → B} {g : B → C}

/--
Lemma 1: If g is injective and g(f(x₁)) = g(f(x₂)), then f(x₁) = f(x₂)
-/
lemma injective_cancel_outer (hg : Injective g) (x₁ x₂ : A) (h : g (f x₁) = g (f x₂)) :
  f x₁ = f x₂ :=
  sorry
