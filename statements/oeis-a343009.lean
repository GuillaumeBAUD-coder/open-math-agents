import Mathlib

/-!
# A343009: a(n) = (n^(2n)-1)/(n^2-1) for n > 1, a(1) = 1

Source: https://oeis.org/A343009
Credit: @xor2k

Formalizes the OEIS A343009 conjecture: for n > 2, a(n) is a Fermat pseudoprime to base n.

Conventions: offset 1 as in OEIS; `a 1 = 1` and otherwise `a n = (n^(2n) - 1) / (n^2 - 1)` with
natural-number division, which is exact for `n > 1` (a(n) = Sum_{k=0..n-1} n^(2k)); the value at
`n = 0` is irrelevant. A Fermat pseudoprime to base `b` is a composite number `m` with
`b^(m-1) ≡ 1 (mod m)`; this is Mathlib's `Nat.FermatPsp m b`, which unfolds to
`m ∣ b ^ (m - 1) - 1`, `¬ m.Prime` and `1 < m`. The claim is asserted for every `n > 2`.
-/

namespace OMA.S_oeis_a343009

/-- A343009: a(1) = 1 and a(n) = (n^(2n)-1)/(n^2-1) for n > 1. -/
def a (n : ℕ) : ℕ := if n = 1 then 1 else (n ^ (2 * n) - 1) / (n ^ 2 - 1)

/-- For every `n > 2`, `a n` is a Fermat pseudoprime to base `n`. -/
theorem main : ∀ n : ℕ, 2 < n → Nat.FermatPsp (a n) n := by
  sorry

end OMA.S_oeis_a343009
