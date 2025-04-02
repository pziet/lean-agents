import Mathlib.Tactic
import «Proofs».Definitions.isEven
import «Proofs».Lemmas.EvenSquare

-- Prove that is n, m are even then n^2 + m is even
theorem even_square_plus_even (n m : ℕ) (hn : isEven n) (hm : isEven m) : isEven (n * n + m) := by
  -- sorry
  rcases even_square n hn with ⟨k1, hk1⟩    -- n^2 = 2 * k1
  rcases hm with ⟨k2, hk2⟩                 -- m = 2 * k2
  use k1 + k2                              -- Claim: n^2 + m = 2 * (k1 + k2)
  rw [hk1, hk2]
  ring
