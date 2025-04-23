import Mathlib.Data.Int.Basic

def isOdd (n: ℤ) : Prop :=
  ∃ k : ℤ, n = 2 * k + 1
