import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R1

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1.R1.H1.R1 of step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1.R1.H1
-- Credit: @jktcv2kz4f-cyber

/-!
# Geometric subprogression density-increment reduction of the additive potential step

We reduce the additive subprogression potential step `R2.H1.R1.H2.R1.H1.R1.H1` to a
geometric log-density increment onto a subprogression (`p' ≤ (1 - η) * p`) with
sublinear double-logarithmic scale loss (`log log N ≤ log log M + K * p ^ β`, `0 < β < 1`),
split between the four-term (`k = 4`, `H1`) and higher-length (`k ≥ 5`, `H2`) regimes.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R1_H1_R1

open Real

/-- Four-term geometric log-density increment onto a subprogression with sublinear scale loss. -/
def H1 : Prop :=
  ∃ η β K L T : ℝ, 0 < η ∧ η < 1 ∧ 0 < β ∧ β < 1 ∧ 0 < K ∧ 0 < L ∧
    ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
      let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      T < p → L * p ^ β ≤ Real.log (Real.log (N : ℝ)) →
      ∃ (a q M : ℕ), 0 < q ∧ 2 ≤ M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
        let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
        let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
        0 < U.card ∧ p' ≤ (1 - η) * p ∧
          Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M : ℝ)) + K * p ^ β

/-- Higher-length (k ≥ 5) geometric log-density increment onto a subprogression. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ η β K L T : ℝ, 0 < η ∧ η < 1 ∧ 0 < β ∧ β < 1 ∧ 0 < K ∧ 0 < L ∧
    ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      T < p → L * p ^ β ≤ Real.log (Real.log (N : ℝ)) →
      ∃ (a q M : ℕ), 0 < q ∧ 2 ≤ M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
        let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
        let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
        0 < U.card ∧ p' ≤ (1 - η) * p ∧
          Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M : ℝ)) + K * p ^ β

lemma subprog_potential_of_geometric {k : ℕ}
    (hstep : ∃ η β K L T : ℝ, 0 < η ∧ η < 1 ∧ 0 < β ∧ β < 1 ∧ 0 < K ∧ 0 < L ∧
      ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
        T < p → L * p ^ β ≤ Real.log (Real.log (N : ℝ)) →
        ∃ (a q M : ℕ), 0 < q ∧ 2 ≤ M ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
          let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
          0 < U.card ∧ p' ≤ (1 - η) * p ∧
            Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M : ℝ)) + K * p ^ β) :
    ∃ (β C T R₀ : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ (N : ℕ) (S : Finset ℕ),
        2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
          (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
        T < p → C * p ^ β + R ≤ Real.log (Real.log (N : ℝ)) →
          ∃ (a q M : ℕ), 0 < q ∧ 2 ≤ M ∧
            (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
            let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
            let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
            0 < U.card ∧ p' + 1 ≤ p ∧ C * p' ^ β + R ≤ Real.log (Real.log (M : ℝ)) := by
  obtain ⟨η, β, K, L, T, hη0, hη1, hβ0, hβ1, hK, hL, hinc⟩ := hstep
  have h1mη_pos : 0 < 1 - η := sub_pos.mpr hη1
  have h1mη_lt1 : 1 - η < 1 := by linarith
  have hrpow_lt1 : (1 - η) ^ β < 1 := Real.rpow_lt_one h1mη_pos.le h1mη_lt1 hβ0
  have hgap : 0 < 1 - (1 - η) ^ β := sub_pos.mpr hrpow_lt1
  let C : ℝ := max L (K / (1 - (1 - η) ^ β))
  have hCL : L ≤ C := le_max_left _ _
  have hCK : K / (1 - (1 - η) ^ β) ≤ C := le_max_right _ _
  have hC : 0 < C := lt_of_lt_of_le hL hCL
  refine ⟨β, C, max T (1 / η), 0, hβ0, hβ1, hC, ?_⟩
  intro R hR N S hN hS hScard hfree p hpT hbudget
  have hp2 : 2 ≤ p := le_max_left _ _
  have hp0 : 0 ≤ p := by linarith
  have hpNT : T < p := lt_of_le_of_lt (le_max_left T (1 / η)) hpT
  have hpNη : 1 / η < p := lt_of_le_of_lt (le_max_right T (1 / η)) hpT
  have hLbudget : L * p ^ β ≤ Real.log (Real.log (N : ℝ)) := by
    have h1 : L * p ^ β ≤ C * p ^ β :=
      mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg hp0 β)
    linarith
  obtain ⟨a, q, M, hq, hM, hprog, hUpos, hp'_le, hscale⟩ :=
    hinc N S hN hS hScard hfree hpNT hLbudget
  refine ⟨a, q, M, hq, hM, hprog, hUpos, ?_, ?_⟩
  · have h1 : 1 < p * η := (div_lt_iff₀ hη0).mp hpNη
    linarith
  · set p' : ℝ := max 2 (Real.log (2 * (M : ℝ) / (((Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)).card : ℝ)))
    have hp'2 : 2 ≤ p' := le_max_left _ _
    have hp'0 : 0 ≤ p' := by linarith
    have hp'rpow : p' ^ β ≤ (1 - η) ^ β * p ^ β := by
      have h1 : p' ^ β ≤ ((1 - η) * p) ^ β := Real.rpow_le_rpow hp'0 hp'_le hβ0.le
      rwa [Real.mul_rpow h1mη_pos.le hp0] at h1
    have hCp' : C * p' ^ β ≤ C * (1 - η) ^ β * p ^ β := by
      have := mul_le_mul_of_nonneg_left hp'rpow hC.le
      linarith
    have hKC : K ≤ C * (1 - (1 - η) ^ β) := (div_le_iff₀ hgap).mp hCK
    have hKdrop : K * p ^ β ≤ C * (1 - (1 - η) ^ β) * p ^ β :=
      mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg hp0 β)
    linarith

theorem main :
    H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R1.H1 := by
  intro h4 h5 k hk
  by_cases hk4 : k = 4
  · subst hk4
    exact subprog_potential_of_geometric h4
  · exact subprog_potential_of_geometric (h5 k (by omega))

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R1_H1_R1
