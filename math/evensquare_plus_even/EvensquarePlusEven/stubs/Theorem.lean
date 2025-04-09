import Mathlib.Tactic
import EvensquarePlusEven.stubs.isEven
import EvensquarePlusEven.stubs.EvenSquare
import EvensquarePlusEven.stubs.EvenPlusEven
-- Prove that is n, m are even then n^2 + m is even
theorem even_square_plus_even (n m : ℕ) (hn : isEven n) (hm : isEven m) : isEven (n * n + m) := by
  sorry
