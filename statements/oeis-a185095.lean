import Mathlib

/-!
# The three conjectures for A185095

Source: https://oeis.org/A185095
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a185095

noncomputable def term (q r : ℕ) : PowerSeries ℝ :=
  PowerSeries.C ((-1:ℝ)^r * (2*q-r).choose r) * PowerSeries.X^r

noncomputable def row (q : ℕ) : PowerSeries ℝ :=
  (∑ r ∈ Finset.range q, PowerSeries.C ((q-r:ℕ):ℝ) * term q r) *
    (∑ r ∈ Finset.range (q+1), term q r)⁻¹

noncomputable def R (q k : ℕ) : ℝ := PowerSeries.coeff k (row q)

def walks (m k : ℕ) : ℕ := Matrix.trace (((SimpleGraph.pathGraph m).adjMatrix ℕ)^(2*k))

theorem main :
    (∀ q k : ℕ, 1 ≤ q → R q k =
      2^(2*k) * ∑ j ∈ Finset.range (k+1), Real.cos (((j:ℝ)+1)*Real.pi/(2*q+1))^(2*k)) ∧
    (∀ k : ℕ, ∃ H : Polynomial ℝ,
      PowerSeries.mk (fun q => R (q+1) k) * (1-PowerSeries.X)^2 = (H : PowerSeries ℝ)) ∧
    (∀ q k : ℕ, 1 ≤ q → 2*R q k = walks (2*q) k) := by
  sorry

end OMA.S_oeis_a185095
