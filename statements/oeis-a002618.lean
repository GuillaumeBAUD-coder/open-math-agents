import Mathlib

/-!
# A002618: a(n) = n*phi(n).

Source: https://oeis.org/A002618
Credit: @MartinFoxy

The entry carries the comment (Zhi-Wei Sun, Sep 24 2015): Conjecture: All the rational numbers
`Sum_{i=j..k} 1/a(i)` with `0 < min{2,k} <= j <= k` have pairwise distinct fractional parts.

Formalization notes:
* The sequence has offset 1 and is defined by its name, `a(n) = n * phi(n)` with `phi` Euler's
  totient function (data from n = 1: 1, 2, 6, 8, 20, 12, 42, ...).
* The index pairs are the `(j, k)` with `0 < min{2,k} <= j <= k`, that is `(1, 1)` and all
  `2 <= j <= k`. `Admissible j k` is this condition, written with `min 2 k`.
* Pairwise distinct fractional parts is stated as: two admissible pairs whose sums have the
  same fractional part are the same pair. Sums and fractional parts are taken in `ℚ`.
-/

namespace OMA.S_oeis_a002618

/-- A002618 (offset 1): `a(n) = n * phi(n)`. -/
def a (n : ℕ) : ℕ := n * Nat.totient n

/-- The sum `Sum_{i=j..k} 1/a(i)`. -/
def S (j k : ℕ) : ℚ := ∑ i ∈ Finset.Icc j k, (1 : ℚ) / (a i : ℚ)

/-- The index condition `0 < min{2,k} <= j <= k`. -/
def Admissible (j k : ℕ) : Prop := 0 < min 2 k ∧ min 2 k ≤ j ∧ j ≤ k

/-- Zhi-Wei Sun's conjecture: the sums over admissible index pairs have pairwise distinct
fractional parts. -/
theorem main : ∀ j k j' k' : ℕ, Admissible j k → Admissible j' k' →
    Int.fract (S j k) = Int.fract (S j' k') → j = j' ∧ k = k' := by
  sorry

end OMA.S_oeis_a002618
