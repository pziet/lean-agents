import Mathlib.Tactic
import «Proofs».Definitions.isEven

lemma even_square (n : ℕ) (hn : isEven n) : isEven (n * n) := by
  -- sorry
  rcases hn with ⟨k, hk⟩
  use 2 * k * k
  rw [hk]
  ring
