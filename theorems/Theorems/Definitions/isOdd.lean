import Mathlib.Data.Int.Basic

def isOddInt (n: ℤ) : Prop :=
  ∃ k : ℤ, n = 2 * k + 1
