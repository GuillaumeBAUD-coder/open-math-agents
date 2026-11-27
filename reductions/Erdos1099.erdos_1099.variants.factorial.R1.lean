import FormalConjectures.ErdosProblems.«1099»
import Mathlib.Analysis.PSeries

/-!
# Bounded divisor-gap powers for factorials

Tenenbaum's admissibility result gives the factorial divisor approximation in H1.
H2 is the gap summation theorem for sequences ordered by divisibility, specialized
to the function u ↦ u ^ α. The remaining sum is bounded by a convergent p-series.
See "Sur un problème extrémal en arithmétique" (1987), Theorems 2 and 3 and the
factorial argument following Theorem 3, with the corrigendum (2000).
-/

-- Credit: @dk8827

open Finset
open scoped BigOperators

namespace OMA.R_Erdos1099_erdos_1099_variants_factorial_R1

def H1 : Prop :=
  ∀ β : ℝ, 0 < β → ∃ M : ℝ, 0 < M ∧
    ∀ k : ℕ, 2 ≤ k → ∀ x : ℝ,
      Real.sqrt (((k - 1).factorial : ℕ) : ℝ) < x →
      x ≤ Real.sqrt ((k.factorial : ℕ) : ℝ) →
      ∃ d : ℕ, d ∣ k.factorial ∧ x < (d : ℝ) ∧
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

theorem main : H1 → H2 → type_of% @Erdos1099.erdos_1099.variants.factorial := by
  intro admissible sum_bound α hα
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
          Real.log ((k.factorial : ℝ) / ((k - 1).factorial : ℝ)) ≤
        K * (k : ℝ) ^ (-2 : ℝ) := by
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hkpos : (0 : ℝ) < k := zero_lt_one.trans_le hkone
    have hfac : (k.factorial : ℝ) / ((k - 1).factorial : ℝ) = (k : ℝ) := by
      have hnat : k.factorial = k * (k - 1).factorial := by
        have heq : (k - 1) + 1 = k := by omega
        simpa only [heq] using (Nat.factorial_succ (k - 1))
      have hdenom : (((k - 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
      rw [hnat, Nat.cast_mul, mul_div_cancel_right₀ _ hdenom]
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
    rw [hfac]
    calc
      _ ≤ (1 + M) * (α * (ε k) ^ (α - 1)) * (k : ℝ) :=
        mul_le_mul
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
    Erdos1099.h α n.factorial ≤ _ :=
      sum_bound α hα Nat.factorial ε rfl rfl Nat.factorial_pos
        (fun _ => Nat.factorial_dvd_factorial (Nat.le_succ _)) εpos hAdm n
    _ ≤ ∑ k ∈ Icc 2 n, K * (k : ℝ) ^ (-2 : ℝ) :=
      sum_le_sum (fun k hk => term_le k (mem_Icc.1 hk).1)
    _ ≤ _ := hs.sum_le_tsum _ (fun k _ => mul_nonneg hK (Real.rpow_nonneg (by positivity) _))

end OMA.R_Erdos1099_erdos_1099_variants_factorial_R1
