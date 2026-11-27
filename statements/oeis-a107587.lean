import Mathlib

/-!
# A107587: conjectured recurrences for Motzkin paths with an even number of up steps

Source: https://oeis.org/A107587
Credit: @sntntHb

`a(n)` (offset 0) is the number of Motzkin `n`-paths with an even number of up steps, with the
formula `a(n) = Sum_{k=0..floor(n/2)} binomial(n, 2k) * C(k) * ((k+1) mod 2)` recorded in the entry
(`C` the Catalan numbers): a Motzkin path with `k` up steps is a choice of the `2k` positions of its
up and down steps together with a Dyck path on them, and only even `k` are counted. The data starts
`1, 1, 1, 1, 3, 11, 31, 71, 155, 379, 1051, ...`.

The entry records two conjectures (R. J. Mathar, Feb 20 2015; checked for `n = 0..800` by Gennady
Eremin):
1. `n(n+2) a(n) + (-5n^2 - n + 3) a(n-1) + (10n^2 - 16n + 3) a(n-2) + (-10n^2 + 34n - 27) a(n-3)
   - (11n - 5)(n - 3) a(n-4) + 15(n - 3)(n - 4) a(n-5) = 0`;
2. `n(n-2)(n+2) a(n) - (2n - 1)(2n^2 - 2n - 3) a(n-1) + 3(n - 1)(2n^2 - 4n + 1) a(n-2)
   - 2(n - 1)(n - 2)(2n - 3) a(n-3) - 15(n - 1)(n - 2)(n - 3) a(n-4) = 0`.

Both are stated for the `n` at which every index is a valid term (`n ≥ 5`, resp. `n ≥ 4`); with
`a(m) = 0` for negative `m` they also hold for the smaller `n`. `main` is their conjunction.
-/

namespace OMA.S_oeis_a107587

/-- OEIS A107587: Motzkin `n`-paths with an even number of up steps. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ (Finset.range (n / 2 + 1)).filter (fun k => Even k), (n.choose (2 * k) * catalan k : ℤ)

/-- Mathar's two conjectured recurrences for A107587. -/
theorem main :
    (∀ n : ℕ, 5 ≤ n →
      (n : ℤ) * (n + 2) * a n + (-5 * (n : ℤ) ^ 2 - n + 3) * a (n - 1) +
        (10 * (n : ℤ) ^ 2 - 16 * n + 3) * a (n - 2) + (-10 * (n : ℤ) ^ 2 + 34 * n - 27) * a (n - 3) -
        (11 * (n : ℤ) - 5) * (n - 3) * a (n - 4) + 15 * ((n : ℤ) - 3) * (n - 4) * a (n - 5) = 0) ∧
    (∀ n : ℕ, 4 ≤ n →
      (n : ℤ) * (n - 2) * (n + 2) * a n - (2 * (n : ℤ) - 1) * (2 * n ^ 2 - 2 * n - 3) * a (n - 1) +
        3 * ((n : ℤ) - 1) * (2 * n ^ 2 - 4 * n + 1) * a (n - 2) -
        2 * ((n : ℤ) - 1) * (n - 2) * (2 * n - 3) * a (n - 3) -
        15 * ((n : ℤ) - 1) * (n - 2) * (n - 3) * a (n - 4) = 0) := by
  sorry

end OMA.S_oeis_a107587
