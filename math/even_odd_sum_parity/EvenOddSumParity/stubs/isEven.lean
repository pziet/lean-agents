import Mathlib.Data.Int.Basic

def isEven (n: ℤ) : Prop :=
  ∃ k : ℤ, n = 2 * k
