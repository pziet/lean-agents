import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import BijectiveComp.stubs.Injective
import BijectiveComp.stubs.InjectiveCancelOuter
import BijectiveComp.stubs.InjectiveCancelInner

variable {A B C : Type} {f : A → B} {g : B → C}

/--
Theorem: If f and g are injective, then g ∘ f is injective
-/
theorem comp_injective (hf : Injective f) (hg : Injective g) :
  Injective (g ∘ f) :=
  sorry
