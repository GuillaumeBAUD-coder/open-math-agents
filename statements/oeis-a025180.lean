import Mathlib

/-!
# A recurrence for OEIS A025180

Source: https://oeis.org/A025180
Credit: @hermitokatt

The sequence (offset 2): a(n) is the number of sequences `(s(0), s(1), …, s(n))` of integers with `s(0) = 0`, `|s(1)| = 1`, `|s(i) - s(i-1)| ≤ 1` for `i ≥ 2`, and `s(n) = 2`.
Data: 1, 2, 7, 20, 60, 176, 518, ….

The conjecture (R. J. Mathar, Feb 25 2015):
`-(n+2)(n-3) a(n) + 2(2n+1)(n-3) a(n-1) + (-n^2+10n-18) a(n-2) - 3(2n-3)(n-3) a(n-3) = 0`.

Reading.
* The values `s(i)` are arbitrary integers (no nonnegativity condition), as in the source;
  `|s(1)| = 1` is `|s(1) - s(0)| = 1` since `s(0) = 0`.
* The recurrence is stated for every `n` for which all its terms are defined, i.e. `n ≥ 5`
  (the offset is 2); checked numerically against a direct count for `5 ≤ n ≤ 39`, and the
  count reproduces the listed data.
* A sequence `(s(0), …)` is a function on `Fin` positions; the set of admissible ones is finite
  (each value is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a025180

/-- Integer sequences `(s(0), …, s(n))`: start `0`, end `2`, first step `±1`, later steps in `{-1, 0, 1}`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 0) ∧
       (∀ i : Fin (n + 1), i.val = n → s i = 2) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → j.val ≤ 1 → |s j - s i| = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → 1 < j.val → |s j - s i| ≤ 1)}

/-- A025180: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 5`. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    -((n : ℤ) + 2) * ((n : ℤ) - 3) * a n + 2 * (2 * (n : ℤ) + 1) * ((n : ℤ) - 3) * a (n - 1) +
      (-(n : ℤ) ^ 2 + 10 * (n : ℤ) - 18) * a (n - 2) - 3 * (2 * (n : ℤ) - 3) * ((n : ℤ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a025180
