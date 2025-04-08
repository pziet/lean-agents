-- Prove that if n, m are even then n^2 + m is even
import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

def isEven (n: ℕ) : Prop :=
  ∃ k : ℕ, n = 2 * k

-- Prove that if n is even then n^2 is even
lemma even_square (n : ℕ) (hn : isEven n) : isEven (n * n) := by
  -- sorry
  rcases hn with ⟨k, hk⟩
  use 2 * k * k
  rw [hk]
  ring

-- Prove that is n, m are even then n^2 + m is even
theorem even_square_plus_even (n m : ℕ) (hn : isEven n) (hm : isEven m) : isEven (n * n + m) := by
  rcases even_square n hn with ⟨k1, hk1⟩    -- n^2 = 2 * k1
  rcases hm with ⟨k2, hk2⟩                 -- m = 2 * k2
  use k1 + k2                              -- Claim: n^2 + m = 2 * (k1 + k2)
  rw [hk1, hk2]
  ring
