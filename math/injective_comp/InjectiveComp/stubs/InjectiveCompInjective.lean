import Mathlib.Tactic
import InjectiveComp.stubs.Injective
import InjectiveComp.stubs.InjectiveCancelOuter
import InjectiveComp.stubs.InjectiveCancelInner

variable {A B C : Type} {f : A → B} {g : B → C}

/--
Theorem: If f and g are injective, then g ∘ f is injective
-/
theorem comp_injective (hf : Injective f) (hg : Injective g) :
  Injective (g ∘ f) :=
  sorry
