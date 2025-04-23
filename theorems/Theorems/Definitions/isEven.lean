import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
def isEven (n: ℕ) : Prop :=
  ∃ k : ℕ, n = 2 * k

def isEvenInt (n: ℤ) : Prop :=
  ∃ k : ℤ, n = 2 * k
