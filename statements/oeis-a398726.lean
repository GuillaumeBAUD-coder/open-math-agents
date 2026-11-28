import Mathlib

namespace OMA.S_oeis_a398726

/-- For a permutation `σ` of `Fin n`, `distinctCycleSizes σ` is the finset of distinct cycle
lengths of `σ` (where fixed points have cycle length `1`). -/
noncomputable def distinctCycleSizes {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  Finset.univ.image (fun x : Fin n => Function.minimalPeriod σ x)

/-- OEIS A398726: `a(n)` is the sum, over all permutations `σ` of `{0, ..., n - 1}`, of the sum
of the distinct cycle sizes of `σ`. -/
noncomputable def a398726 (n : ℕ) : ℕ :=
  ∑ σ : Equiv.Perm (Fin n), ∑ k ∈ distinctCycleSizes σ, k

/-- OEIS A398726 Conjecture (Vaclav Kotesovec, 2026): `a(n) ~ n * n!` as `n → ∞`, i.e.,
`a(n) / (n * n!) → 1`. -/
theorem main :
    Filter.Tendsto
      (fun n : ℕ => (a398726 n : ℝ) / ((n : ℝ) * (n.factorial : ℝ)))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a398726
