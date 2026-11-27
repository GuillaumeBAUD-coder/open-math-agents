import FormalConjectures.ErdosProblems.«5»

-- Reduction Erdos5.erdos_5.variants.hildebrand_maier.R1 of Erdős Problem 5 — hildebrand maier
-- Credit: @minimumnz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1

open Filter Real Set Erdos5

-- At the prime scale, arbitrarily high bounded windows recur infinitely often.
def H1 : Prop := ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 ≤ B ∧
    ∃ᶠ n : ℕ in atTop,
      A * log (Nat.nth Nat.Prime n) ≤ (primeGap n : ℝ) ∧
      (primeGap n : ℝ) ≤ B * log (Nat.nth Nat.Prime n)

-- A coarse comparison suffices to transfer both endpoints to the index scale.
def H2 : Prop := ∀ᶠ n : ℕ in atTop, 0 < log n ∧
    log n ≤ log (Nat.nth Nat.Prime n) ∧ log (Nat.nth Nat.Prime n) ≤ 2 * log n

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5.variants.hildebrand_maier := by
  intro windows scale C
  let A := max C 0 + 1
  have hA : 0 < A := by dsimp [A]; linarith [le_max_right C 0]
  obtain ⟨B, hB, hits⟩ := windows A hA
  have visits : ∃ᶠ n : ℕ in atTop, normalizedGap n ∈ Icc A (B * 2) := by
    apply (hits.and_eventually scale).mono
    rintro n ⟨⟨lo, hi⟩, pos, lower, upper⟩
    constructor
    · exact (le_div_iff₀ pos).2 ((mul_le_mul_of_nonneg_left lower hA.le).trans lo)
    · apply (div_le_iff₀ pos).2
      simpa only [mul_assoc] using hi.trans (mul_le_mul_of_nonneg_left upper hB)
  obtain ⟨x, hx, cluster⟩ := isCompact_Icc.exists_mapClusterPt_of_frequently visits
  refine ⟨x, cluster, lt_of_lt_of_le ?_ hx.1⟩
  dsimp [A]
  linarith [le_max_left C 0]

end OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1
