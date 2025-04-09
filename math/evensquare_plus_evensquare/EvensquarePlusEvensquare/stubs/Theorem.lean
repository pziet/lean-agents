import Mathlib.Tactic
import EvensquarePlusEvensquare.stubs.isEven
import EvensquarePlusEvensquare.stubs.EvenSquare
import EvensquarePlusEvensquare.stubs.EvenPlusEven

-- Prove that if n and m are even, then n^2 + m^2 is even
theorem even_square_plus_even_square (n m : ℕ) (hn : isEven n) (hm : isEven m) : isEven (n * n + m * m) := by
  sorry
