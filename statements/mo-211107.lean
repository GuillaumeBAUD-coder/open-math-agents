import Mathlib

/-!
# Counting k-subsets with bounded intersections with the blocks of a partition

Source: https://mathoverflow.net/questions/211107
Credit: Sudharsan Rajendiran

Fix a partition `T_1, …, T_m` of `[m k] = {1, …, m k}` into `m` blocks of size `k`. Let
`n(m, k, j)` be the number of `k`-element subsets `C ⊆ [m k]` with `max_i |T_i ∩ C| = j`, and
`N(m, k, j) = Σ_{i ≤ j} n(m, k, i)` the number of those with `max_i |T_i ∩ C| ≤ j`. The question
asks for a formula for `n(m, k, j)`.

The answer https://mathoverflow.net/a/211120 by Max Alekseyev shows that `N(m, k, j)` is the
coefficient of `x^k` in `(Σ_{i=0}^{j} C(k, i) x^i)^m`, and hence `n(m, k, j) = N(m, k, j) - N(m, k, j - 1)`.
We state both formulas (the second for `j ≥ 1`, as an identity in `ℤ`).

Conventions:
- The ground set `[m k]` is modelled as `Fin m × Fin k`, and the block `T_i` is `{i} ×ˢ univ`.
- The maximum `max_i |T_i ∩ C|` is `Finset.univ.sup` over `i : Fin m` (it is `0` when `m = 0`).
- The polynomial `Σ_{i=0}^{j} C(k, i) x^i` is a polynomial with natural-number coefficients.
-/

namespace OMA.S_mo_211107

/-- The block `T_i = {i} × [k]` of the partition of the ground set `Fin m × Fin k`. -/
def block (m k : ℕ) (i : Fin m) : Finset (Fin m × Fin k) := {i} ×ˢ Finset.univ

/-- The maximum over all blocks `T_i` of `|T_i ∩ C|`. -/
def maxMeet (m k : ℕ) (C : Finset (Fin m × Fin k)) : ℕ :=
  Finset.univ.sup fun i => (block m k i ∩ C).card

/-- `N(m, k, j)`: the number of `k`-subsets `C` of the ground set with `max_i |T_i ∩ C| ≤ j`. -/
def bigN (m k j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin k)).powersetCard k |>.filter fun C => maxMeet m k C ≤ j).card

/-- `n(m, k, j)`: the number of `k`-subsets `C` of the ground set with `max_i |T_i ∩ C| = j`. -/
def smallN (m k j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin k)).powersetCard k |>.filter fun C => maxMeet m k C = j).card

/-- The polynomial `Σ_{i=0}^{j} C(k, i) x^i`. -/
noncomputable def blockPoly (k j : ℕ) : Polynomial ℕ :=
  ∑ i ∈ Finset.range (j + 1), Polynomial.C (k.choose i) * Polynomial.X ^ i

theorem main : ∀ m k j : ℕ, bigN m k j = ((blockPoly k j) ^ m).coeff k ∧
    (1 ≤ j → (smallN m k j : ℤ) = (bigN m k j : ℤ) - (bigN m k (j - 1) : ℤ)) := by
  sorry

end OMA.S_mo_211107
