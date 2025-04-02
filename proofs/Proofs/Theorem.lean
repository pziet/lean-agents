import Mathlib.Tactic
import «Proofs».Definitions.isEven
import «Proofs».Lemmas.EvenSquare

-- Prove that is n, m are even then n^2 + m is even
theorem even_square_plus_even (n m : ℕ) (hn : isEven n) (hm : isEven m) : isEven (n * n + m) := by
  sorry
