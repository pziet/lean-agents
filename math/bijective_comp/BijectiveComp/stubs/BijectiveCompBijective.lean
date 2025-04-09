import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import BijectiveComp.stubs.Bijective
import BijectiveComp.stubs.InjectiveCompInjective
import BijectiveComp.stubs.SurjectiveCompSurjective

variable {A B C : Type} {f : A → B} {g : B → C}

/--
If f and g are bijective, then g ∘ f is bijective
-/
theorem comp_bijective (hf : Bijective f) (hg : Bijective g) :
  Bijective (g ∘ f) :=
  sorry
