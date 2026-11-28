import Mathlib

/-!
# A recurrence for OEIS A026327

Source: https://oeis.org/A026327
Credit: @hermitokatt

The sequence (offset 2): a(n) is the number of sequences `(s(0), …, s(n))` of nonnegative integers with `|s(i) - s(i-1)| ≤ 1` for `i = 1, …, n`, `s(0) = 2` and `s(n) = 4`.
Data: 1, 3, 10, 30, 90, 266, ….

The conjecture (R. J. Mathar, Jun 23 2013):
`-(n+8)(n-2) a(n) + 3(2n^2+7n-28) a(n-1) + 3(-3n^2-n+36) a(n-2) - 4(n+4)(n-1) a(n-3) + 12(n-1)(n-2) a(n-4) = 0`.

Reading.
* Each recurrence is stated for every `n` for which all its terms are defined: `n ≥ 6` (the offset is 2);
  checked numerically against a direct count for `n ≤ 39`, and the count reproduces the
  listed data.
* A sequence `(s(0), …, s(n))` is a function `Fin (n + 1) → ℕ`; the set of admissible ones is
  finite (each `s(i)` is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026327

/-- The admissible sequences `(s(0), …, s(n))`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 2) ∧
       (∀ i : Fin (n + 1), i.val = n → s i = 4) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → |(s j : ℤ) - (s i : ℤ)| ≤ 1)}

/-- A026327: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 6`. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    -((n : ℤ) + 8) * ((n : ℤ) - 2) * a n + 3 * (2 * (n : ℤ) ^ 2 + 7 * (n : ℤ) - 28) * a (n - 1) +
      3 * (-3 * (n : ℤ) ^ 2 - (n : ℤ) + 36) * a (n - 2) - 4 * ((n : ℤ) + 4) * ((n : ℤ) - 1) * a (n - 3) +
      12 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026327
