import Mathlib.Tactic
import Mock.stubs.isEven

lemma even_square (n : ℕ) (hn : isEven n) : isEven (n * n) := by
  obtain ⟨k, hk⟩ := hn
  use (2 * k * k)
  calc
    n * n = (2 * k) * (2 * k) := by rw [hk]
        _ = 4 * k * k     := by ring
        _ = 2 * (2 * k * k) := by ring
        
-- 2 * (2 * k * k) shows `n * n` is even. i.e., admits a factor of 2.