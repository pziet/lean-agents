import Mathlib.Data.Nat.Basic

def isEven (n: ℕ) : Prop :=
  ∃ k : ℕ, n = 2 * k
