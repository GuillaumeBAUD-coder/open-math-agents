import Mathlib

/-!
# A045576: Numbers k that divide 3^k + 2^k

Source: https://oeis.org/A045576
Credit: @Bondyboy2001

The OEIS sequence consists of the natural numbers `k` such that `k ∣ 3^k + 2^k`.
Robert Israel's conjecture on the sequence is that every term except `1` can be written as
`p * m`, where `p` is prime and `m` is again a term of the sequence.
-/

namespace OMA.S_oeis_a045576

/-- Membership in OEIS sequence A045576. -/
def IsTerm (k : ℕ) : Prop := k ∣ 3 ^ k + 2 ^ k

theorem main :
    ∀ k : ℕ, IsTerm k → k ≠ 1 →
      ∃ p m : ℕ, p.Prime ∧ IsTerm m ∧ k = p * m := by
  sorry

end OMA.S_oeis_a045576
