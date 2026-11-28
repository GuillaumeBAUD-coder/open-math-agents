import Mathlib

/-!
# A recurrence for OEIS A026122

Source: https://oeis.org/A026122
Credit: @hermitokatt

The sequence (offset 2): a(n) is the number of sequences `(s(0), s(1), …, s(n))` of nonnegative integers with `s(0) = 1`, `s(n) = 1`, `|s(1) - s(0)| = 1` and `|s(i) - s(i-1)| ≤ 1` for `i ≥ 2`.
Data: 2, 4, 11, 28, 74, 196, ….

The conjecture (R. J. Mathar, Jun 23 2013):
`(n+4) a(n) + (-3n-5) a(n-1) + (-n-6) a(n-2) + 3(n-3) a(n-3) = 0`.

Reading.
* The recurrence is stated for every `n` for which all its terms are defined, i.e. `n ≥ 5`
  (the offset is 2); checked numerically against a direct count for `5 ≤ n ≤ 39`, and the
  count reproduces the listed data.
* A sequence `(s(0), …)` is a function on `Fin` positions; the set of admissible ones is finite
  (each value is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026122

/-- Sequences `(s(0), …, s(n))` of naturals: start `1`, end `1`, first step `±1`, later steps in `{-1, 0, 1}`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 1) ∧
       (∀ i : Fin (n + 1), i.val = n → s i = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → j.val ≤ 1 → |(s j : ℤ) - (s i : ℤ)| = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → 1 < j.val → |(s j : ℤ) - (s i : ℤ)| ≤ 1)}

/-- A026122: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 5`. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 4) * a n + (-3 * (n : ℤ) - 5) * a (n - 1) + (-(n : ℤ) - 6) * a (n - 2) +
      3 * ((n : ℤ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026122
