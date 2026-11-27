import FormalConjectures.ErdosProblems.«1099»
import Mathlib.Analysis.PSeries

-- Adapted from the factorial reduction by dk8827. H1 is the central divisor
-- estimate for least common multiples. H2 is Tenenbaum's general summation
-- theorem. The LCM increment divides k times the preceding LCM, giving the
-- logarithmic weight needed for the convergent majorant.

open Finset
open scoped BigOperators

namespace OMA.R_Erdos1099_erdos_1099_variants_lcm_R1

def H1 : Prop :=
  ∀ β : ℝ, 0 < β → ∃ M : ℝ, 0 < M ∧
    ∀ k : ℕ, 2 ≤ k → ∀ x : ℝ,
      Real.sqrt (((Icc 1 (k - 1)).lcm id : ℕ) : ℝ) < x →
      x ≤ Real.sqrt (((Icc 1 k).lcm id : ℕ) : ℝ) →
      ∃ d : ℕ, d ∣ (Icc 1 k).lcm id ∧ x < (d : ℝ) ∧
        (d : ℝ) ≤ (1 + M * (k : ℝ) ^ (-β)) * x

def H2 : Prop :=
  ∀ α : ℝ, 1 < α → ∀ (N : ℕ → ℕ) (ε : ℕ → ℝ),
    N 0 = 1 → N 1 = 1 → (∀ k, 0 < N k) → (∀ k, N k ∣ N (k + 1)) →
    (∀ k ≥ 2, 0 < ε k) →
    (∀ k ≥ 2, ∀ x : ℝ, Real.sqrt (N (k - 1) : ℝ) < x → x ≤ Real.sqrt (N k : ℝ) →
      ∃ d : ℕ, d ∣ N k ∧ x < (d : ℝ) ∧ (d : ℝ) ≤ (1 + ε k) * x) →
    ∀ n, Erdos1099.h α (N n) ≤
      ∑ k ∈ Icc 2 n, (1 + ε k) * (α * (ε k) ^ (α - 1)) *
        Real.log ((N k : ℝ) / (N (k - 1) : ℝ))

theorem main : H1 → H2 → type_of% @Erdos1099.erdos_1099.variants.lcm := by
  intro admissible sum_bound α hα
  let L (k : ℕ) := (Icc 1 k).lcm id
  have hpos (k : ℕ) : 0 < L k := by
    apply Nat.pos_of_ne_zero
    exact lcm_ne_zero_iff.mpr fun i hi => Nat.ne_of_gt (mem_Icc.mp hi).1
  have hstep (k : ℕ) : L k ∣ L (k + 1) := by
    apply Finset.lcm_dvd
    intro i hi
    exact Finset.dvd_lcm (mem_Icc.mpr ⟨(mem_Icc.mp hi).1, Nat.le_succ_of_le (mem_Icc.mp hi).2⟩)
  have hproduct (k : ℕ) : L k ∣ k * L (k - 1) := by
    apply Finset.lcm_dvd
    intro i hi
    by_cases he : i = k
    · subst i
      exact dvd_mul_right _ _
    · have hle := (mem_Icc.mp hi).2
      have hd : i ∣ L (k - 1) := Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨(mem_Icc.mp hi).1, by omega⟩)
      exact hd.trans (dvd_mul_left _ _)
  have hα1 : 0 < α - 1 := by linarith
  let β : ℝ := 3 / (α - 1)
  have hβ : 0 < β := by positivity
  obtain ⟨M, hM, hAdm⟩ := admissible β hβ
  let ε : ℕ → ℝ := fun k => M * (k : ℝ) ^ (-β)
  have εpos (k : ℕ) (hk : 2 ≤ k) : 0 < ε k := by
    have hkpos : (0 : ℝ) < k := by positivity
    exact mul_pos hM (Real.rpow_pos_of_pos hkpos _)
  let K := (1 + M) * (α * M ^ (α - 1))
  have hK : 0 ≤ K := by
    have hα0 : 0 < α := by linarith
    dsimp only [K]
    positivity
  have term_le (k : ℕ) (hk : 2 ≤ k) :
      (1 + ε k) * (α * (ε k) ^ (α - 1)) *
          Real.log ((L k : ℝ) / (L (k - 1) : ℝ)) ≤
        K * (k : ℝ) ^ (-2 : ℝ) := by
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hkpos : (0 : ℝ) < k := zero_lt_one.trans_le hkone
    have hden : (0 : ℝ) < L (k - 1) := by exact_mod_cast hpos (k - 1)
    have hrat : (L k : ℝ) / (L (k - 1) : ℝ) ≤ k := by
      apply (div_le_iff₀ hden).mpr
      exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (by omega) (hpos (k - 1))) (hproduct k)
    have hεle : ε k ≤ M := by
      simpa only [ε, mul_one] using mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hkone (neg_nonpos.mpr hβ.le)) hM.le
    have hexp : (-β) * (α - 1) = -3 := by
      dsimp only [β]
      field_simp [hα1.ne']
    have hpow : (ε k) ^ (α - 1) = M ^ (α - 1) * (k : ℝ) ^ (-3 : ℝ) := by
      dsimp only [ε]
      rw [Real.mul_rpow hM.le (by positivity), ← Real.rpow_mul hkpos.le, hexp]
    have hlog : Real.log (k : ℝ) ≤ k := by
      linarith [Real.log_le_sub_one_of_pos hkpos]
    have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hkone
    have hweight : 0 ≤ α * (ε k) ^ (α - 1) := by
      have hα0 : 0 < α := by linarith
      exact mul_nonneg hα0.le (Real.rpow_nonneg (εpos k hk).le _)
    have harg : (0 : ℝ) < (L k : ℝ) / L (k - 1) := div_pos (by exact_mod_cast hpos k) hden
    calc
      _ ≤ (1 + M) * (α * (ε k) ^ (α - 1)) * (k : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log harg hrat) (by positivity)) <| mul_le_mul
          (mul_le_mul_of_nonneg_right (add_le_add_right hεle 1) hweight)
          hlog hlog0 (by positivity)
      _ = K * ((k : ℝ) ^ (-3 : ℝ) * (k : ℝ) ^ (1 : ℝ)) := by
        rw [hpow, Real.rpow_one]
        dsimp only [K]
        ring
      _ = _ := by
        rw [← Real.rpow_add hkpos]
        norm_num
  have hs : Summable (fun k : ℕ => K * (k : ℝ) ^ (-2 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left K
  refine ⟨∑' k : ℕ, K * (k : ℝ) ^ (-2 : ℝ), fun n => ?_⟩
  calc
    Erdos1099.h α (L n) ≤ _ :=
      sum_bound α hα L ε (by simp [L]) (by simp [L]) hpos hstep εpos hAdm n
    _ ≤ ∑ k ∈ Icc 2 n, K * (k : ℝ) ^ (-2 : ℝ) :=
      sum_le_sum (fun k hk => term_le k (mem_Icc.1 hk).1)
    _ ≤ _ := hs.sum_le_tsum _ (fun k _ => mul_nonneg hK (Real.rpow_nonneg (by positivity) _))

end OMA.R_Erdos1099_erdos_1099_variants_lcm_R1
