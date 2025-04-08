import Mathlib.Tactic
import Mock.stubs.isEven

lemma even_square (n : ℕ) (hn : isEven n) : isEven (n * n) := by
  rcases hn with ⟨k, hk⟩
  use 2 * k * k
  rw [hk]
  ring_nf