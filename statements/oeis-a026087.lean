import Mathlib

/-!
# A recurrence for OEIS A026087

Source: https://oeis.org/A026087
Credit: @hermitokatt

The sequence (offset 4): a(n) is the number of sequences `(s(0), …, s(n))` of integers with `s(0) = 0`, `|s(i) - s(i-1)| = 1` for `i = 1, 2, 3`, `|s(i) - s(i-1)| ≤ 1` for `i ≥ 4`, and `s(n) = 4`.
Data: 1, 2, 9, 28, 93, 294, ….

The conjecture (R. J. Mathar, Jun 23 2013):
`-(n-4)(n+4) a(n) + (4n^2-11n-27) a(n-1) + (-2n^2+29n-24) a(n-2) - (4n+5)(n-5) a(n-3) + 3(n-5)(n-6) a(n-4) = 0`.

Reading.
* The values `s(i)` are arbitrary integers (no nonnegativity condition), as in the source.
* Each recurrence is stated for every `n` for which all its terms are defined: `n ≥ 8` (the offset is 4);
  checked numerically against a direct count for `n ≤ 39`, and the count reproduces the
  listed data.
* A sequence `(s(0), …, s(n))` is a function `Fin (n + 1) → ℤ`; the set of admissible ones is
  finite (each `s(i)` is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026087

/-- The admissible sequences `(s(0), …, s(n))`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 0) ∧
       (∀ i : Fin (n + 1), i.val = n → s i = 4) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → j.val ≤ 3 → |s j - s i| = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → 3 < j.val → |s j - s i| ≤ 1)}

/-- A026087: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 8`. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    -((n : ℤ) - 4) * ((n : ℤ) + 4) * a n + (4 * (n : ℤ) ^ 2 - 11 * (n : ℤ) - 27) * a (n - 1) +
      (-2 * (n : ℤ) ^ 2 + 29 * (n : ℤ) - 24) * a (n - 2) - (4 * (n : ℤ) + 5) * ((n : ℤ) - 5) * a (n - 3) +
      3 * ((n : ℤ) - 5) * ((n : ℤ) - 6) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026087
