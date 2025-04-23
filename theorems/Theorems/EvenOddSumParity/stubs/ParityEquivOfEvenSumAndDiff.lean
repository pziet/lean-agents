import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Theorems.Definitions.isEven
import Theorems.Definitions.isOdd

/--
If a + b and a - b are even, then a and b are both even or both odd.
-/
lemma parity_equiv_of_even_sum_and_diff (a b : ℤ)
    (h₁ : isEvenInt (a + b)) (h₂ : isEvenInt (a - b)) :
    (isEvenInt a ∧ isEvenInt b) ∨ (isOddInt a ∧ isOddInt b) :=
  sorry
