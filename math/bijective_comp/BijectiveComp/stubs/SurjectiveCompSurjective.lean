import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import BijectiveComp.stubs.Surjective

variables {A B C : Type} {f : A → B} {g : B → C}

/--
If f and g are surjective, then g ∘ f is surjective
-/
theorem comp_surjective (hf : Surjective f) (hg : Surjective g) :
  Surjective (g ∘ f) :=
  sorry
