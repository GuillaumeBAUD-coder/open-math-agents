import Mathlib

/-!
# A recurrence for OEIS A026085

Source: https://oeis.org/A026085
Credit: @hermitokatt

The sequence (offset 4): a(n) is the number of sequences `(s(0), …, s(n))` of integers with `s(0) = 0`, `|s(i) - s(i-1)| = 1` for `i = 1, 2, 3`, `|s(i) - s(i-1)| ≤ 1` for `i ≥ 4`, and `s(n) = 2`.
Data: 4, 8, 27, 76, 226, 660, ….

The conjecture (R. J. Mathar, Jun 23 2013):
`(n+2) a(n) + (-5n-1) a(n-1) + 4(n-4) a(n-2) + 8(n-1) a(n-3) + (-5n+34) a(n-4) + 3(-n+7) a(n-5) = 0`.

Reading.
* The values `s(i)` are arbitrary integers (no nonnegativity condition), as in the source.
* Each recurrence is stated for every `n` for which all its terms are defined: `n ≥ 9` (the offset is 4);
  checked numerically against a direct count for `n ≤ 39`, and the count reproduces the
  listed data.
* A sequence `(s(0), …, s(n))` is a function `Fin (n + 1) → ℤ`; the set of admissible ones is
  finite (each `s(i)` is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026085

/-- The admissible sequences `(s(0), …, s(n))`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 0) ∧
       (∀ i : Fin (n + 1), i.val = n → s i = 2) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → j.val ≤ 3 → |s j - s i| = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → 3 < j.val → |s j - s i| ≤ 1)}

/-- A026085: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 9`. -/
theorem main : ∀ n : ℕ, 9 ≤ n →
    ((n : ℤ) + 2) * a n + (-5 * (n : ℤ) - 1) * a (n - 1) + 4 * ((n : ℤ) - 4) * a (n - 2) +
      8 * ((n : ℤ) - 1) * a (n - 3) + (-5 * (n : ℤ) + 34) * a (n - 4) + 3 * (-(n : ℤ) + 7) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a026085
