import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R1
import Mathlib

/-!
# Inverse-power log-log loss reduction at exponential thresholds for k >= 5

Reduces the discrete power-difference density increment at exponential thresholds for
all `k >= 5` (`log log N - log log M ≤ C * ((j + 1)^β - j^β)`) to an inverse-power
step loss bound (`log log N - log log M ≤ L / (j + 1)^γ` with `0 < γ < 1`), split into
`k = 5` (`H1`) and `k >= 6` (`H2`), using the weighted AM-GM concavity bound
`(j + 1)^β - j^β ≥ β * (j + 1)^(β - 1)` with `β = 1 - γ`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R1_H1_R1

open Erdos142 Filter Real

/-- Exponential-threshold density increment for `k = 5` with inverse-power log-log loss. -/
def H1 : Prop :=
  ∃ (γ L K₀ B₀ : ℝ) (J₀ : ℕ), 0 < γ ∧ γ < 1 ∧ 0 < L ∧ 0 < K₀ ∧
    ∀ j : ℕ, J₀ ≤ j → ∀ (N : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 5, a + i * d ∈ S) →
      (N : ℝ) * exp (-((j + 1 : ℕ) : ℝ)) ≤ S.card →
      K₀ * ((j + 1 : ℕ) : ℝ) ^ (1 - γ) + B₀ ≤ log (log N) →
      ∃ a q M : ℕ, 0 < q ∧ 0 < M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
        (M : ℝ) * exp (-(j : ℝ)) ≤
          ((Finset.Icc 1 M).filter fun i ↦ a + (i - 1) * q ∈ S).card ∧
        log (log (N : ℝ)) - log (log (M : ℝ)) ≤ L / ((j + 1 : ℕ) : ℝ) ^ γ

/-- Exponential-threshold density increment for `k >= 6` with inverse-power log-log loss. -/
def H2 : Prop :=
  ∀ k : ℕ, 6 ≤ k →
    ∃ (γ L K₀ B₀ : ℝ) (J₀ : ℕ), 0 < γ ∧ γ < 1 ∧ 0 < L ∧ 0 < K₀ ∧
      ∀ j : ℕ, J₀ ≤ j → ∀ (N : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc 1 N →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        (N : ℝ) * exp (-((j + 1 : ℕ) : ℝ)) ≤ S.card →
        K₀ * ((j + 1 : ℕ) : ℝ) ^ (1 - γ) + B₀ ≤ log (log N) →
        ∃ a q M : ℕ, 0 < q ∧ 0 < M ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          (M : ℝ) * exp (-(j : ℝ)) ≤
            ((Finset.Icc 1 M).filter fun i ↦ a + (i - 1) * q ∈ S).card ∧
          log (log (N : ℝ)) - log (log (M : ℝ)) ≤ L / ((j + 1 : ℕ) : ℝ) ^ γ

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

lemma discrete_diff_of_inv_power {k : ℕ}
    (hinc : ∃ (γ L K₀ B₀ : ℝ) (J₀ : ℕ), 0 < γ ∧ γ < 1 ∧ 0 < L ∧ 0 < K₀ ∧
      ∀ j : ℕ, J₀ ≤ j → ∀ (N : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc 1 N →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        (N : ℝ) * exp (-((j + 1 : ℕ) : ℝ)) ≤ S.card →
        K₀ * ((j + 1 : ℕ) : ℝ) ^ (1 - γ) + B₀ ≤ log (log N) →
        ∃ a q M : ℕ, 0 < q ∧ 0 < M ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          (M : ℝ) * exp (-(j : ℝ)) ≤
            ((Finset.Icc 1 M).filter fun i ↦ a + (i - 1) * q ∈ S).card ∧
          log (log (N : ℝ)) - log (log (M : ℝ)) ≤ L / ((j + 1 : ℕ) : ℝ) ^ γ) :
    ∃ (β C B : ℝ) (J : ℕ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ j : ℕ, J ≤ j → ∀ (N : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc 1 N →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        (N : ℝ) * exp (-((j + 1 : ℕ) : ℝ)) ≤ S.card →
        C * ((j + 1 : ℕ) : ℝ) ^ β + B ≤ log (log N) →
        ∃ a q M : ℕ, 0 < q ∧ 0 < M ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          (M : ℝ) * exp (-(j : ℝ)) ≤
            ((Finset.Icc 1 M).filter fun i ↦ a + (i - 1) * q ∈ S).card ∧
          log (log (N : ℝ)) - log (log (M : ℝ)) ≤
            C * (((j + 1 : ℕ) : ℝ) ^ β - (j : ℝ) ^ β) := by
  obtain ⟨γ, L, K₀, B₀, J₀, hγ0, hγ1, hL, hK₀, hstep⟩ := hinc
  let β : ℝ := 1 - γ
  have hβ0 : 0 < β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  let C : ℝ := max K₀ (L / β)
  have hC_pos : 0 < C := lt_of_lt_of_le hK₀ (le_max_left _ _)
  refine ⟨β, C, B₀, max J₀ 1, hβ0, hβ1, hC_pos, ?_⟩
  intro j hj N S hSsub hSfree hdens hbud
  have hjJ₀ : J₀ ≤ j := (le_max_left _ _).trans hj
  have hj1 : 1 ≤ j := (le_max_right _ _).trans hj
  have hK₀C : K₀ ≤ C := le_max_left _ _
  have hLβC : L / β ≤ C := le_max_right _ _
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hj1pos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hbud₀ : K₀ * ((j + 1 : ℕ) : ℝ) ^ (1 - γ) + B₀ ≤ log (log N) := by
    have hpow0 : 0 ≤ ((j + 1 : ℕ) : ℝ) ^ β := Real.rpow_nonneg hj1pos.le β
    have hmul : K₀ * ((j + 1 : ℕ) : ℝ) ^ β ≤ C * ((j + 1 : ℕ) : ℝ) ^ β :=
      mul_le_mul_of_nonneg_right hK₀C hpow0
    dsimp [β] at hmul
    linarith
  obtain ⟨a, q, M, hq, hM, hAff, hUcard, hloss⟩ :=
    hstep j hjJ₀ N S hSsub hSfree hdens hbud₀
  refine ⟨a, q, M, hq, hM, hAff, hUcard, ?_⟩
  have hdiff : ((j + 1 : ℕ) : ℝ) - (j : ℝ) = 1 := by push_cast; ring
  have hdrop := rpow_sub_rpow_ge hjpos (by push_cast; linarith : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ))
    hβ0.le hβ1.le
  rw [hdiff, mul_one] at hdrop
  have hexp : β - 1 = -γ := by dsimp [β]; ring
  rw [hexp, Real.rpow_neg hj1pos.le] at hdrop
  have hL_le : L ≤ C * β := (div_le_iff₀ hβ0).mp hLβC
  have hstep_le : L / ((j + 1 : ℕ) : ℝ) ^ γ ≤ C * (((j + 1 : ℕ) : ℝ) ^ β - (j : ℝ) ^ β) := by
    calc
      L / ((j + 1 : ℕ) : ℝ) ^ γ = L * (((j + 1 : ℕ) : ℝ) ^ γ)⁻¹ := div_eq_mul_inv _ _
      _ ≤ (C * β) * (((j + 1 : ℕ) : ℝ) ^ γ)⁻¹ :=
          mul_le_mul_of_nonneg_right hL_le (by positivity)
      _ = C * (β * (((j + 1 : ℕ) : ℝ) ^ γ)⁻¹) := by ring
      _ ≤ C * (((j + 1 : ℕ) : ℝ) ^ β - (j : ℝ) ^ β) :=
          mul_le_mul_of_nonneg_left hdrop hC_pos.le
  linarith

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R1.H1 := by
  intro h5 h6 k hk
  rcases eq_or_lt_of_le hk with rfl | hk6
  · exact discrete_diff_of_inv_power h5
  · exact discrete_diff_of_inv_power (h6 k hk6)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R1_H1_R1
