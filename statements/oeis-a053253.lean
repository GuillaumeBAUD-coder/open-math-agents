import Mathlib

/-!
# A053253: Coefficients of the '3rd-order' mock theta function omega(q).

Source: https://oeis.org/A053253
Credit: @<your GitHub handle>

The entry records the empirical observation (John M. Campbell, Apr 24 2020), restated by Gus Wiseman
(Jun 26 2022) as "Campbell's conjecture":
"a(n) is the number of integer partitions mu of 2n+1 such that the diagram of mu has an odd number
of cells in each row and in each column", i.e. "the number of partitions of 2n+1 with all odd parts
and all odd conjugate parts".

Conventions (please review):
* `a(n)` (offset 0: `1, 2, 3, 4, 6, 8, 10, 14, ...`) is the coefficient of `q^n` in Ramanujan's third
  order mock theta function
  `omega(q) = Sum_{k >= 0} q^(2k(k+1)) / ((1-q)(1-q^3)...(1-q^(2k+1)))^2`.
  Each summand is computed in `ℚ⟦X⟧` (the denominator has constant coefficient `1`, so `⁻¹` is the
  true inverse). The `k`-th summand is divisible by `X^(2k(k+1))`, so the coefficient of `X^m` only
  receives contributions from `k ≤ m`; we define `a(m)` as the finite sum over `k ∈ {0, ..., m}`.
* A partition `μ` of `2n+1` is a `Nat.Partition (2 * n + 1)`. Its rows are its parts. Column `c`
  (0-indexed) of its Ferrers diagram has as many cells as there are parts `> c`; the nonempty columns
  are exactly the parts of the conjugate partition. "An odd number of cells in each column" means:
  every nonempty column has odd length.
-/

namespace OMA.S_oeis_a053253

open PowerSeries

/-- The `k`-th summand of `omega(q)`: `q^(2k(k+1)) / Prod_{j=0..k} (1 - q^(2j+1))^2`. -/
noncomputable def omegaTerm (k : ℕ) : ℚ⟦X⟧ :=
  X ^ (2 * k * (k + 1)) * ((∏ j ∈ Finset.range (k + 1), (1 - X ^ (2 * j + 1))) ^ 2)⁻¹

/-- A053253: the coefficient of `q^m` in the mock theta function `omega(q)`. -/
noncomputable def a (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), coeff m (omegaTerm k)

/-- Number of cells in column `c` (0-indexed) of the Ferrers diagram of `μ`: the number of parts
of `μ` that exceed `c`. -/
def colLen {N : ℕ} (μ : Nat.Partition N) (c : ℕ) : ℕ :=
  (μ.parts.filter (fun p => c < p)).card

/-- Every row and every (nonempty) column of the Ferrers diagram of `μ` has an odd number of cells. -/
def OddRowsCols {N : ℕ} (μ : Nat.Partition N) : Prop :=
  (∀ p ∈ μ.parts, Odd p) ∧ ∀ c : ℕ, colLen μ c ≠ 0 → Odd (colLen μ c)

/-- Campbell's conjecture in OEIS A053253: `a(n)` is the number of partitions of `2n+1` whose
Ferrers diagram has an odd number of cells in each row and in each column. -/
theorem main : ∀ n : ℕ,
    a n = (Nat.card {μ : Nat.Partition (2 * n + 1) // OddRowsCols μ} : ℚ) := by
  sorry

end OMA.S_oeis_a053253
