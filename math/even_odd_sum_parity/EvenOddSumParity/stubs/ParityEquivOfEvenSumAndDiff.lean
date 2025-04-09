import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import EvenOddSumParity.stubs.isEven
import EvenOddSumParity.stubs.isOdd

/--
If a + b and a - b are even, then a and b are both even or both odd.
-/
lemma parity_equiv_of_even_sum_and_diff (a b : ℤ)
    (h₁ : isEven (a + b)) (h₂ : isEven (a - b)) :
    (isEven a ∧ isEven b) ∨ (isOdd a ∧ isOdd b) :=
  sorry
