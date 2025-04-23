import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Theorems.Definitions.Bijective
import Theorems.BijectiveComp.stubs.InjectiveCompInjective
import Theorems.BijectiveComp.stubs.SurjectiveCompSurjective

variable {A B C : Type} {f : A → B} {g : B → C}

/--
If f and g are bijective, then g ∘ f is bijective
-/
theorem comp_bijective (hf : Bijective f) (hg : Bijective g) :
  Bijective (g ∘ f) :=
  sorry
