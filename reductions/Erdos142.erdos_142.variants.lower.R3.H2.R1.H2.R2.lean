import OMAReductions.R_Erdos142_erdos_142_variants_lower_R3_H2_R1

-- Reduction Erdos142.erdos_142.variants.lower.R3.H2.R1.H2.R2 of step Erdos142.erdos_142.variants.lower.R3.H2.R1.H2
-- Credit: @jktcv2kz4f-cyber

/-!
# Sublinear-cost geometric density increment reduction of the sparse potential step

We reduce the sparse additive-potential descent step `R3.H2.R1.H2` to a geometric log-density
increment (`p' ≤ (1 - η) * p`) with sublinear double-logarithmic scale loss
(`log log N ≤ log log M + K * p ^ β`, `0 < β < 1`), split between the four-term (`k = 4`, `H1`)
and higher-length (`k ≥ 5`, `H2`) progression regimes.

Given any such geometric increment, setting the potential `F(x) = A * x ^ β` with
`A = max L (K / (1 - (1 - η) ^ β))` converts each geometric step into an additive potential
decrease absorbing the scale loss `K * p ^ β`, while weighted AM-GM yields `F(x) ≤ x / 2 + D`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1_H2_R2

open Real

/-- Four-term geometric log-density increment with sublinear double-logarithmic scale loss. -/
def H1 : Prop :=
  ∃ η β K L T : ℝ, 0 < η ∧ η < 1 ∧ 0 < β ∧ β < 1 ∧ 0 < K ∧ 0 < L ∧
    let p := fun (N : ℕ) (S : Finset ℕ) => max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
    let valid := fun (N : ℕ) (S : Finset ℕ) => 1 < N ∧ S.Nonempty ∧ S ⊆ Finset.Icc 1 N ∧
      ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S
    ∀ (N : ℕ) (S : Finset ℕ), valid N S → T < p N S →
      L * (p N S) ^ β ≤ log (log (N : ℝ)) →
      ∃ (M : ℕ) (B : Finset ℕ), valid M B ∧
        p M B ≤ (1 - η) * p N S ∧
        log (log (N : ℝ)) ≤ log (log (M : ℝ)) + K * (p N S) ^ β

/-- Higher-length (k ≥ 5) geometric log-density increment with sublinear scale loss. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ η β K L T : ℝ, 0 < η ∧ η < 1 ∧ 0 < β ∧ β < 1 ∧ 0 < K ∧ 0 < L ∧
    let p := fun (N : ℕ) (S : Finset ℕ) => max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
    let valid := fun (N : ℕ) (S : Finset ℕ) => 1 < N ∧ S.Nonempty ∧ S ⊆ Finset.Icc 1 N ∧
      ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S
    ∀ (N : ℕ) (S : Finset ℕ), valid N S → T < p N S →
      L * (p N S) ^ β ≤ log (log (N : ℝ)) →
      ∃ (M : ℕ) (B : Finset ℕ), valid M B ∧
        p M B ≤ (1 - η) * p N S ∧
        log (log (N : ℝ)) ≤ log (log (M : ℝ)) + K * (p N S) ^ β

lemma sublinear_rpow_le_half_add {A β : ℝ} (hA : 0 < A) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ D : ℝ, ∀ x : ℝ, 2 ≤ x → A * x ^ β ≤ x / 2 + D := by
  have h1mβ : 0 < 1 - β := sub_pos.mpr hβ1
  let B : ℝ := A * (2 : ℝ) ^ β
  have hB : 0 < B := by positivity
  let D : ℝ := B ^ (1 / (1 - β))
  have hD : 0 ≤ D := by positivity
  refine ⟨D, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hhalf : 0 ≤ x / 2 := by linarith
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hβ0.le h1mβ.le hhalf hD (by ring)
  have h2pow : (0 : ℝ) < (2 : ℝ) ^ β := by positivity
  have hBpow : D ^ (1 - β) = B := by
    dsimp [D]
    rw [← Real.rpow_mul hB.le, one_div_mul_cancel h1mβ.ne', Real.rpow_one]
  have hlhs : (x / 2) ^ β * D ^ (1 - β) = A * x ^ β := by
    rw [hBpow, Real.div_rpow hx0 (by norm_num : (0 : ℝ) ≤ 2)]
    dsimp [B]
    field_simp [h2pow.ne']
  rw [hlhs] at hamgm
  have hterm1 : β * (x / 2) ≤ x / 2 := by nlinarith
  have hterm2 : (1 - β) * D ≤ D := by nlinarith
  linarith

lemma potential_of_geometric {k : ℕ}
    (hstep : ∃ η β K L T : ℝ, 0 < η ∧ η < 1 ∧ 0 < β ∧ β < 1 ∧ 0 < K ∧ 0 < L ∧
      let p := fun (N : ℕ) (S : Finset ℕ) => max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
      let valid := fun (N : ℕ) (S : Finset ℕ) => 1 < N ∧ S.Nonempty ∧ S ⊆ Finset.Icc 1 N ∧
        ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S
      ∀ (N : ℕ) (S : Finset ℕ), valid N S → T < p N S →
        L * (p N S) ^ β ≤ log (log (N : ℝ)) →
        ∃ (M : ℕ) (B : Finset ℕ), valid M B ∧
          p M B ≤ (1 - η) * p N S ∧
          log (log (N : ℝ)) ≤ log (log (M : ℝ)) + K * (p N S) ^ β) :
    ∃ (F : ℝ → ℝ) (T D Cmin : ℝ),
      (∀ x ≥ 2, 0 ≤ F x ∧ F x ≤ x / 2 + D) ∧
      let p := fun (N : ℕ) (S : Finset ℕ) => max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
      let valid := fun (N : ℕ) (S : Finset ℕ) => 1 < N ∧ S.Nonempty ∧ S ⊆ Finset.Icc 1 N ∧
        ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S
      ∀ C ≥ Cmin, ∀ (N : ℕ) (S : Finset ℕ), valid N S → T < p N S →
        F (p N S) + C ≤ log (log (N : ℝ)) → ∃ (M : ℕ) (B : Finset ℕ),
          valid M B ∧ F (p M B) + C ≤ log (log (M : ℝ)) ∧ p M B + 1 ≤ p N S := by
  obtain ⟨η, β, K, L, T, hη0, hη1, hβ0, hβ1, hK, hL, hinc⟩ := hstep
  have h1mη_pos : 0 < 1 - η := sub_pos.mpr hη1
  have h1mη_lt1 : 1 - η < 1 := by linarith
  have hrpow_lt1 : (1 - η) ^ β < 1 := Real.rpow_lt_one h1mη_pos.le h1mη_lt1 hβ0
  have hgap : 0 < 1 - (1 - η) ^ β := sub_pos.mpr hrpow_lt1
  let A : ℝ := max L (K / (1 - (1 - η) ^ β))
  have hAL : L ≤ A := le_max_left _ _
  have hAK : K / (1 - (1 - η) ^ β) ≤ A := le_max_right _ _
  have hA : 0 < A := lt_of_lt_of_le hL hAL
  obtain ⟨D, hD⟩ := sublinear_rpow_le_half_add hA hβ0 hβ1
  let F : ℝ → ℝ := fun x => A * x ^ β
  let T' : ℝ := max T (1 / η)
  refine ⟨F, T', D, 0, ?_, ?_⟩
  · intro x hx
    refine ⟨?_, hD x hx⟩
    dsimp [F]
    have hx0 : 0 ≤ x := by linarith
    positivity
  · dsimp only
    intro C hC N S hvalid hpT hbudget
    let pN : ℝ := max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
    have hpN2 : 2 ≤ pN := le_max_left _ _
    have hpN0 : 0 ≤ pN := by linarith
    have hpNT : T < pN := lt_of_le_of_lt (le_max_left T (1 / η)) hpT
    have hpNη : 1 / η < pN := lt_of_le_of_lt (le_max_right T (1 / η)) hpT
    have hLbudget : L * pN ^ β ≤ log (log (N : ℝ)) := by
      have h1 : L * pN ^ β ≤ A * pN ^ β :=
        mul_le_mul_of_nonneg_right hAL (Real.rpow_nonneg hpN0 β)
      change A * pN ^ β + C ≤ log (log (N : ℝ)) at hbudget
      linarith
    obtain ⟨M, B, hBvalid, hpM_le, hscale⟩ := hinc N S hvalid hpNT hLbudget
    let pM : ℝ := max 2 (log (2 * (M : ℝ) / (B.card : ℝ)))
    have hpM2 : 2 ≤ pM := le_max_left _ _
    have hpM0 : 0 ≤ pM := by linarith
    have hgain : pM + 1 ≤ pN := by
      have h1 : 1 < pN * η := (div_lt_iff₀ hη0).mp hpNη
      change pM ≤ (1 - η) * pN at hpM_le
      linarith
    have hFpM : F pM ≤ A * (1 - η) ^ β * pN ^ β := by
      dsimp [F]
      have h1 : pM ^ β ≤ ((1 - η) * pN) ^ β :=
        Real.rpow_le_rpow hpM0 hpM_le hβ0.le
      rw [Real.mul_rpow h1mη_pos.le hpN0] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hA.le
      linarith
    have hKA : K ≤ A * (1 - (1 - η) ^ β) := (div_le_iff₀ hgap).mp hAK
    have hdrop : K * pN ^ β ≤ F pN - F pM := by
      have h1 : K * pN ^ β ≤ A * (1 - (1 - η) ^ β) * pN ^ β :=
        mul_le_mul_of_nonneg_right hKA (Real.rpow_nonneg hpN0 β)
      dsimp [F] at hFpM ⊢
      linarith
    have hMbudget : F pM + C ≤ log (log (M : ℝ)) := by
      change F pN + C ≤ log (log (N : ℝ)) at hbudget
      linarith
    exact ⟨M, B, hBvalid, hMbudget, hgain⟩

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1.H2 := by
  intro h4 h5 k hk
  by_cases hk4 : k = 4
  · subst hk4
    exact potential_of_geometric h4
  · exact potential_of_geometric (h5 k (by omega))

end OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1_H2_R2
