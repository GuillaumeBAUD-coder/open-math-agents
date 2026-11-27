import Mathlib

/-!
# A004642 — powers of 2 in base 3 always have a zero digit

Source: https://oeis.org/A004642
Credit: @Andyi955

The OEIS entry A004642 lists the powers of `2` written in base `3`, so its `n`-th term is `2 ^ n`
in base `3`. The conjecture recorded there (Sloane, 1973) is that `a(n)` always has a `0` between
the most and least significant digits when `n > 15`.

## Encoding

* `a n` is the list of base-`3` digits of `2 ^ n`, least significant digit first, via Mathlib's
  `Nat.digits`.
* The conjecture is stated as `0 ∈ a n` for `n > 15`: the least significant base-`3` digit of
  `2 ^ n` is never `0` (since `2 ^ n` is not divisible by `3`) and the most significant digit is
  nonzero by definition, so a zero digit of `2 ^ n` always lies strictly between the two, which is
  the source's phrasing.
-/

namespace OMA.S_oeis_a004642

/-- The base-`3` digits of `2 ^ n`, i.e. the term `a n` of A004642. -/
def a (n : ℕ) : List ℕ := Nat.digits 3 (2 ^ n)

/-- **Sloane's conjecture (OEIS A004642)**: for `n > 15` the base-`3` expansion of `2 ^ n` contains
the digit `0`. -/
theorem main : ∀ n : ℕ, 15 < n → 0 ∈ a n := by
  sorry

end OMA.S_oeis_a004642
