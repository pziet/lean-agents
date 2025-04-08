import Mathlib.Data.Nat.Basic

-- isEven is already defined as a predicate stating that a number is twice some natural number,
-- i.e., there exists a k such that n = 2 * k.

def isEven (n: ℕ) : Prop :=
  ∃ k : ℕ, n = 2 * k

-- There is no need for proof here since this is a definition.
-- The definition itself implicitly contains the "proof" of what it means for a number to be even. This is the nature of Lean's logic system:
-- definitions are axioms or assumed truths based on their logical construction.

-- Therefore, we can use this definition as is without needing extra lemma or proof.