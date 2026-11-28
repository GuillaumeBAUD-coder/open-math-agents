import Mathlib

/-!
# A004257: a(n) = round(log_2(n)).

Source: https://oeis.org/A004257
Credit: @vivanpoddar

The sequence (offset 1) begins 0, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, ...
It is defined as in the name of the entry, with the real logarithm to base 2 and rounding to the
nearest integer (log_2(n) is never a half-integer for an integer n, so the tie rule is immaterial).

Conjecture (Mikhail Kurkov, Sep 11 2019): a(n) = A000523(n^2) - A000523(n),
where A000523(n) = floor(log_2(n)), which is Nat.log 2 n. The offset is 1, so it is stated for n >= 1.
-/

namespace OMA.S_oeis_a004257

/-- A004257: log_2(n) rounded to the nearest integer. -/
noncomputable def a (n : ℕ) : ℤ := round (Real.logb 2 (n : ℝ))

/-- A000523: floor(log_2(n)). -/
def b (n : ℕ) : ℕ := Nat.log 2 n

/-- The conjectured identity for A004257. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = (b (n ^ 2) : ℤ) - (b n : ℤ) := by
  sorry

end OMA.S_oeis_a004257
