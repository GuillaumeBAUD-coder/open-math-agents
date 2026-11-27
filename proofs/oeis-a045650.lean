import OMAStatements.S_oeis_a045650
import Mathlib

namespace LogarithmicGaps

open OMA.S_oeis_a045650 Filter Asymptotics Real
open scoped Topology

private noncomputable def gap (j : ℕ) : ℕ :=
  if j = 0 then 0 else ⌈exp (j : ℝ)⌉₊ + j - 1

/-- Zero and the integer skipped at each exponential threshold belong to the set. -/
private theorem gap_mem (j : ℕ) : P (gap j) := by
  by_cases hj : j = 0
  · subst j
    rw [gap, if_pos rfl]
    rintro ⟨k,hk,he⟩
    have hf : 0 ≤ ⌊log (k : ℝ)⌋ :=
      Int.le_floor.mpr (by simpa only [Int.cast_zero] using log_nonneg (show (1 : ℝ) ≤ k by exact_mod_cast hk))
    omega
  · rw [gap, if_neg hj]
    rintro ⟨k,hk,he⟩
    let m := ⌈exp (j : ℝ)⌉₊
    change ((m+j-1 : ℕ) : ℤ) = (k : ℤ) + ⌊log (k : ℝ)⌋ at he
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    by_cases hkm : k < m
    · have hl : log (k : ℝ) < (j : ℝ) :=
        (log_lt_iff_lt_exp hkpos).2 (Nat.lt_ceil.mp hkm)
      have hf : ⌊log (k : ℝ)⌋ < (j : ℤ) :=
        Int.floor_lt.mpr (by simpa only [Int.cast_natCast] using hl)
      omega
    · have he' : exp (j : ℝ) ≤ (k : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast le_of_not_gt hkm)
      have hl : (j : ℝ) ≤ log (k : ℝ) := (le_log_iff_exp_le hkpos).2 he'
      have hf : (j : ℤ) ≤ ⌊log (k : ℝ)⌋ :=
        Int.le_floor.mpr (by simpa only [Int.cast_natCast] using hl)
      omega

private theorem gap_mono : StrictMono gap := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h : ⌈exp (n : ℝ)⌉₊ ≤ ⌈exp ((n+1 : ℕ) : ℝ)⌉₊ :=
    Nat.ceil_mono (exp_le_exp.mpr (by exact_mod_cast Nat.le_succ n))
  by_cases hn : n = 0
  · subst n
    simpa [gap] using
      (Nat.ceil_pos.mpr (exp_pos (1 : ℝ)))
  · rw [gap, if_neg hn, gap, if_neg (by omega : n+1 ≠ 0)]
    omega

private theorem bound (n : ℕ) (hn : 1 ≤ n) :
    (a (n+1) : ℝ) ≤ exp (n : ℝ) + ((n : ℝ)+1) := by
  have h : a (n+1) ≤ gap n := by
    rw [a,Nat.add_sub_cancel]
    refine Nat.nth_le_of_strictMonoOn_of_mapsTo (p := P) gap ?_ (gap_mono.strictMonoOn _)
    exact fun j _ => gap_mem j
  have hgap : gap n ≤ ⌈exp (n : ℝ)⌉₊ + n := by
    rw [gap,if_neg (by omega : n ≠ 0)]
    omega
  calc
    (a (n+1) : ℝ) ≤ ((⌈exp (n : ℝ)⌉₊ + n : ℕ) : ℝ) := by
      exact_mod_cast h.trans hgap
    _ ≤ _ := by
      push_cast
      linarith [Nat.ceil_lt_add_one (exp_pos (n : ℝ)).le]

theorem ratio_upper :
    Tendsto (fun n : ℕ => (exp (n : ℝ) + ((n : ℝ)+1)) / exp ((n : ℝ)+1))
      atTop (𝓝 (1/exp 1)) := by
  have hc : Tendsto (fun _ : ℕ => (1:ℝ)/exp 1) atTop (𝓝 (1/exp 1)) :=
    tendsto_const_nhds
  have hr : Tendsto (fun x : ℝ => x / exp x) atTop (𝓝 0) := by
    simpa only [pow_one, exp_neg, div_eq_mul_inv] using
      tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop := by
    have h : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hh := h.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hsum : Tendsto (fun n : ℕ => 1/exp 1 + ((n : ℝ)+1)/exp ((n : ℝ)+1))
      atTop (𝓝 (1/exp 1)) := by
    simpa only [Function.comp_apply,add_zero] using hc.add (hr.comp hn)
  refine hsum.congr fun n => ?_
  rw [add_div]
  rw [exp_add]
  field_simp

theorem not_main : ¬ ((fun n : ℕ => (a n : ℝ)) ~[atTop] fun n => exp n) := by
  intro h
  have he : ∀ᶠ n : ℕ in atTop, exp (n : ℝ) ≠ 0 :=
    Eventually.of_forall fun _ => (exp_pos _).ne'
  have ht : Tendsto (fun n : ℕ => (a (n+1) : ℝ)/exp ((n : ℝ)+1)) atTop (𝓝 1) := by
    have hh := ((isEquivalent_iff_tendsto_one he).mp h).comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n : ℕ => (a (n+1) : ℝ)/exp ((n+1 : ℕ) : ℝ)) atTop (𝓝 1) at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hle : (1:ℝ) ≤ 1 / exp 1 := by
    refine le_of_tendsto_of_tendsto ht ratio_upper ?_
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    exact div_le_div_of_nonneg_right (bound n hn) (exp_pos _).le
  have hcontra := (le_div_iff₀ (exp_pos (1:ℝ))).mp hle
  linarith [exp_one_gt_two]

end LogarithmicGaps

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a045650.main) := LogarithmicGaps.not_main