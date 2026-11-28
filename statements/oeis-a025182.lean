import Mathlib

/-!
# Two recurrences for OEIS A025182

Source: https://oeis.org/A025182
Credit: @hermitokatt

The sequence (offset 4): a(n) is the number of sequences `(s(0), …, s(n))` of integers with `s(0) = 0`, `|s(1)| = 1`, `|s(i) - s(i-1)| ≤ 1` for `i ≥ 2`, and `s(n) = 4`.
Data: 1, 4, 16, 56, 189, 616, ….

The entry records two conjectures (R. J. Mathar, Feb 25 2015):
1. `-(n-4)(n+4) a(n) + (4n^2-7n-29) a(n-1) + (-2n^2+17n-2) a(n-2) - (4n+1)(n-3) a(n-3) + 3(n-3)(n-4) a(n-4) = 0`;
2. `-(n-4)(n+4)(n^2-3n+6) a(n) + (n-1)(2n^3-5n^2+11n-36) a(n-1) + 3(n-1)(n-2)(n^2-n+4) a(n-2) = 0`.
`main` states both.

Reading.
* The values `s(i)` are arbitrary integers (no nonnegativity condition), as in the source.
* `|s(1)| = 1` is `|s(1) - s(0)| = 1`, since `s(0) = 0`.
* Each recurrence is stated for every `n` for which all its terms are defined: `n ≥ 8` for the first and `n ≥ 6` for the second (the offset is 4);
  checked numerically against a direct count for `n ≤ 39`, and the count reproduces the
  listed data.
* A sequence `(s(0), …, s(n))` is a function `Fin (n + 1) → ℤ`; the set of admissible ones is
  finite (each `s(i)` is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a025182

/-- The admissible sequences `(s(0), …, s(n))`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 0) ∧
       (∀ i : Fin (n + 1), i.val = n → s i = 4) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → j.val ≤ 1 → |s j - s i| = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → 1 < j.val → |s j - s i| ≤ 1)}

/-- A025182: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Both of Mathar's conjectured recurrences. -/
theorem main :
    (∀ n : ℕ, 8 ≤ n →
      -((n : ℤ) - 4) * ((n : ℤ) + 4) * a n + (4 * (n : ℤ) ^ 2 - 7 * (n : ℤ) - 29) * a (n - 1) +
        (-2 * (n : ℤ) ^ 2 + 17 * (n : ℤ) - 2) * a (n - 2) - (4 * (n : ℤ) + 1) * ((n : ℤ) - 3) * a (n - 3) +
        3 * ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 4) = 0) ∧
    (∀ n : ℕ, 6 ≤ n →
      -((n : ℤ) - 4) * ((n : ℤ) + 4) * ((n : ℤ) ^ 2 - 3 * (n : ℤ) + 6) * a n +
        ((n : ℤ) - 1) * (2 * (n : ℤ) ^ 3 - 5 * (n : ℤ) ^ 2 + 11 * (n : ℤ) - 36) * a (n - 1) +
        3 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 - (n : ℤ) + 4) * a (n - 2) = 0) := by
  sorry

end OMA.S_oeis_a025182
