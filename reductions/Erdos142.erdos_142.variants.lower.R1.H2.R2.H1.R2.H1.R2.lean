import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R2
import Mathlib

/-!
# Polynomial-gain affine density increment with concavity budget transfer for k = 4 and k >= 5

Reduces the subquadratic affine density increment for all `k >= 4`
(`C * p ^ β + R ≤ log log N` preserved with `p' + 1 ≤ p`) to a polynomial-gain,
strictly-smaller-power log-log loss increment (`p' + c * p ^ ν ≤ p`,
`log log N - log log M ≤ L * p ^ α` with `0 ≤ α < ν < 1`), split into
`k = 4` (`H1`) and `k >= 5` (`H2`), via weighted AM-GM concavity of `x ↦ x ^ β`
with `β = 1 - (ν - α) / 2`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R2_H1_R2

open Filter Real

/-- Polynomial-gain affine density increment with strictly smaller power log-log loss for `k = 4`. -/
def H1 : Prop :=
  ∃ (α ν c L K₀ T₀ B₀ : ℝ), 0 ≤ α ∧ α < ν ∧ ν < 1 ∧ 0 < c ∧ 0 < L ∧ 0 < K₀ ∧
    ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
      let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      T₀ < p → K₀ * p ^ (1 - (ν - α) / 2) + B₀ ≤ Real.log (Real.log (N : ℝ)) →
      ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
        let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
        let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
        0 < U.card ∧ p' + c * p ^ ν ≤ p ∧
        Real.log (Real.log (N : ℝ)) - Real.log (Real.log (M : ℝ)) ≤ L * p ^ α

/-- Polynomial-gain affine density increment with strictly smaller power log-log loss for `k >= 5`. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k →
    ∃ (α ν c L K₀ T₀ B₀ : ℝ), 0 ≤ α ∧ α < ν ∧ ν < 1 ∧ 0 < c ∧ 0 < L ∧ 0 < K₀ ∧
      ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
        T₀ < p → K₀ * p ^ (1 - (ν - α) / 2) + B₀ ≤ Real.log (Real.log (N : ℝ)) →
        ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
          let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
          0 < U.card ∧ p' + c * p ^ ν ≤ p ∧
          Real.log (Real.log (N : ℝ)) - Real.log (Real.log (M : ℝ)) ≤ L * p ^ α

lemma rpow_sub_rpow_ge {x y β : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    β * x ^ (β - 1) * (x - y) ≤ x ^ β - y ^ β := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  have h1β : 0 ≤ 1 - β := by linarith
  have hAM := Real.geom_mean_le_arith_mean2_weighted hβ0 h1β (div_nonneg hy.le hx.le) zero_le_one
    (by ring)
  rw [Real.one_rpow, mul_one, mul_one, Real.div_rpow hy.le hx.le] at hAM
  have hmul := mul_le_mul_of_nonneg_right hAM (Real.rpow_nonneg hx.le β)
  rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hx β).ne'] at hmul
  have hdiv : (y / x) * x ^ β = y * x ^ (β - 1) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp [hx.ne']
  have hxp : x * x ^ (β - 1) = x ^ β := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp [hx.ne']
  have hlin : (β * (y / x) + (1 - β)) * x ^ β = x ^ β - β * x ^ (β - 1) * (x - y) := by
    calc
      (β * (y / x) + (1 - β)) * x ^ β
          = β * ((y / x) * x ^ β) + (1 - β) * x ^ β := by ring
      _ = β * (y * x ^ (β - 1)) + x ^ β - β * (x * x ^ (β - 1)) := by rw [hdiv, hxp]; ring
      _ = x ^ β - β * x ^ (β - 1) * (x - y) := by ring
  rw [hlin] at hmul
  linarith

lemma budget_step_of_poly_gain {k : ℕ}
    (hinc : ∃ (α ν c L K₀ T₀ B₀ : ℝ), 0 ≤ α ∧ α < ν ∧ ν < 1 ∧ 0 < c ∧ 0 < L ∧ 0 < K₀ ∧
      ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
        T₀ < p → K₀ * p ^ (1 - (ν - α) / 2) + B₀ ≤ Real.log (Real.log (N : ℝ)) →
        ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
          let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
          0 < U.card ∧ p' + c * p ^ ν ≤ p ∧
          Real.log (Real.log (N : ℝ)) - Real.log (Real.log (M : ℝ)) ≤ L * p ^ α) :
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
  obtain ⟨α, ν, c, L, K₀, T₀, B₀, hα0, hαν, hν1, hc, hL, hK₀, hstep⟩ := hinc
  let β : ℝ := 1 - (ν - α) / 2
  have hβ0 : 0 < β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  have hν0 : 0 < ν := lt_of_le_of_lt hα0 hαν
  let K : ℝ := max K₀ (L / (β * c))
  have hK_pos : 0 < K := lt_of_lt_of_le hK₀ (le_max_left _ _)
  have hK₀_le : K₀ ≤ K := le_max_left _ _
  have hKL_le : L / (β * c) ≤ K := le_max_right _ _
  let T : ℝ := max T₀ ((1 / c) ^ (1 / ν))
  refine ⟨β, K, T, B₀, hβ0, hβ1, hK_pos, ?_⟩
  intro R hR N S hN2 hSsub hScard hSfree
  dsimp only
  set pN : ℝ := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
  intro hTp hbud
  have hp2 : (2 : ℝ) ≤ pN := le_max_left _ _
  have hp_pos : 0 < pN := by linarith
  have hT₀p : T₀ < pN := lt_of_le_of_lt (le_max_left _ _) hTp
  have h1cp : (1 / c) ^ (1 / ν) < pN := lt_of_le_of_lt (le_max_right _ _) hTp
  have hbud₀ : K₀ * pN ^ β + B₀ ≤ Real.log (Real.log (N : ℝ)) := by
    have hKmul : K₀ * pN ^ β ≤ K * pN ^ β :=
      mul_le_mul_of_nonneg_right hK₀_le (Real.rpow_nonneg hp_pos.le β)
    linarith
  obtain ⟨a, q, M, hq, hM2, hAff, hUcard, hgain, hloss⟩ :=
    hstep N S hN2 hSsub hScard hSfree hT₀p hbud₀
  let U : Finset ℕ := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
  set pM : ℝ := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
  have hpM_pos : 0 < pM := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hc_pow : 1 ≤ c * pN ^ ν := by
    have hpow : ((1 / c) ^ (1 / ν)) ^ ν ≤ pN ^ ν :=
      Real.rpow_le_rpow (by positivity) h1cp.le hν0.le
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / c), one_div_mul_cancel hν0.ne',
      Real.rpow_one] at hpow
    have hmul := mul_le_mul_of_nonneg_left hpow hc.le
    rwa [mul_one_div_cancel hc.ne'] at hmul
  have hpM_le : pM ≤ pN := by linarith
  have hdrop : β * pN ^ (β - 1) * (pN - pM) ≤ pN ^ β - pM ^ β :=
    rpow_sub_rpow_ge hpM_pos hpM_le hβ0.le hβ1.le
  have hdiff_ge : c * pN ^ ν ≤ pN - pM := by linarith
  have hexp_ge : α ≤ β - 1 + ν := by dsimp [β]; linarith
  have hp_exp : pN ^ α ≤ pN ^ (β - 1 + ν) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ pN) hexp_ge
  have hprod_pow : pN ^ (β - 1) * pN ^ ν = pN ^ (β - 1 + ν) :=
    (Real.rpow_add hp_pos (β - 1) ν).symm
  have hKβc : L ≤ K * β * c := by
    have hβc : 0 < β * c := mul_pos hβ0 hc
    have h1 := (div_le_iff₀ hβc).mp hKL_le
    linarith
  have hFdrop : L * pN ^ α ≤ K * pN ^ β - K * pM ^ β := by
    calc
      L * pN ^ α ≤ (K * β * c) * pN ^ (β - 1 + ν) :=
        mul_le_mul hKβc hp_exp (Real.rpow_nonneg hp_pos.le α) (by positivity)
      _ = K * (β * pN ^ (β - 1) * (c * pN ^ ν)) := by rw [← hprod_pow]; ring
      _ ≤ K * (β * pN ^ (β - 1) * (pN - pM)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiff_ge (by positivity)) hK_pos.le
      _ ≤ K * (pN ^ β - pM ^ β) := mul_le_mul_of_nonneg_left hdrop hK_pos.le
      _ = K * pN ^ β - K * pM ^ β := by ring
  refine ⟨a, q, M, hq, hM2, hAff, hUcard, ?_, ?_⟩
  · linarith
  · linarith

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R2.H1 := by
  intro h4 h5 k hk
  rcases eq_or_lt_of_le hk with rfl | hk5
  · exact budget_step_of_poly_gain h4
  · exact budget_step_of_poly_gain (h5 k hk5)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R2_H1_R2
