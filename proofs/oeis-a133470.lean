import OMAStatements.S_oeis_a133470

open Filter OMA.S_oeis_a133470
open scoped Topology

namespace A133470Proof

noncomputable local instance : DecidablePred flat := Classical.decPred _

private lemma b_step (n : ℕ) :
    b (n + 1) = b n + ((n : ℝ) + 1) / (n + 3) := Finset.sum_range_succ ..

private lemma rank (n : ℕ) :
    ⌊b (n + 1)⌋ + (Nat.count flat n : ℤ) = n := by
  induction n with
  | zero => norm_num [b, Int.floor_eq_iff]
  | succ n ih =>
    have step := b_step (n + 1)
    push_cast at step
    have hlo : ⌊b (n + 1)⌋ ≤ ⌊b (n + 2)⌋ := by
      apply Int.floor_mono
      rw [step]
      exact le_add_of_nonneg_right (by positivity)
    have hhi : ⌊b (n + 2)⌋ < ⌊b (n + 1)⌋ + 2 := by
      apply Int.floor_lt.mpr
      push_cast
      have : ((n : ℝ) + 1 + 1) / (n + 1 + 3) < 1 := by
        apply (div_lt_one (by positivity)).mpr
        linarith
      linarith [Int.lt_floor_add_one (b (n + 1))]
    change ⌊b (n + 2)⌋ + (Nat.count flat (n + 1) : ℤ) = (↑(n + 1) : ℤ)
    rw [Nat.count_succ]
    split_ifs with h <;> simp only [Nat.cast_add, Nat.cast_zero, Nat.cast_succ] <;>
      unfold flat at h <;> omega

private lemma b_harmonic (n : ℕ) :
    b n = n + 3 - 2 * (harmonic (n + 2) : ℝ) := by
  induction n with
  | zero => norm_num [b, harmonic_succ, harmonic_zero, harmonic]
  | succ n ih =>
    rw [b_step, ih, show n + 1 + 2 = (n + 2) + 1 by omega, harmonic_succ (n + 2)]
    push_cast
    field_simp
    ring

private lemma infinite_flat : (Set.ofPred flat).Infinite := by
  intro hf
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (hf.toFinset.card + 5 : ℝ))
  have hl : (hf.toFinset.card : ℝ) + 5 < Real.log (↑(n + 3 + 1) : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
    push_cast
    linarith
  have hh := log_add_one_le_harmonic (n + 3)
  have hc := Nat.count_le_card hf n
  have hr : (⌊b (n + 1)⌋ : ℝ) + (Nat.count flat n : ℝ) = n := by exact_mod_cast rank n
  have hfloor := Int.floor_le (b (n + 1))
  conv_rhs at hfloor => rw [b_harmonic]
  rw [show n + 1 + 2 = n + 3 by omega] at hfloor
  push_cast at hfloor
  have hcard : (Nat.count flat n : ℝ) ≤ hf.toFinset.card := by exact_mod_cast hc
  linarith

private lemma threshold (n : ℕ) :
    0 ≤ 2 * (harmonic (term n + 2) : ℝ) - (n + 4) ∧
    2 * (harmonic (term n + 2) : ℝ) - (n + 4) ≤ 2 / ((term n : ℝ) + 2) := by
  let j := Nat.nth flat n
  have hj : flat j := Nat.nth_mem_of_infinite infinite_flat n
  have hr := rank j
  rw [show Nat.count flat j = n from Nat.count_nth_of_infinite infinite_flat n] at hr
  have hi := Int.lt_floor_add_one (b (j + 2))
  have lo := Int.floor_le (b (j + 1))
  unfold flat at hj
  rw [hj] at hi
  have hreal : (⌊b (j + 1)⌋ : ℝ) + n = j := by exact_mod_cast hr
  rw [b_harmonic] at hi
  conv_rhs at lo => rw [b_harmonic]
  rw [show j + 1 + 2 = j + 3 by omega] at lo
  change 0 ≤ 2 * (harmonic ((j + 2) + 2) : ℝ) - (n + 4) ∧
    2 * (harmonic ((j + 2) + 2) : ℝ) - (n + 4) ≤ 2 / (↑(j + 2) + 2)
  push_cast at hi lo ⊢
  constructor
  · linarith
  · rw [show j + 2 + 2 = (j + 3) + 1 by omega, harmonic_succ (j + 3)]
    push_cast
    rw [show (j : ℝ) + 3 + 1 = j + 2 + 2 by ring]
    simp only [div_eq_mul_inv]
    linarith

private theorem log_asymptotic :
    Tendsto (fun n : ℕ ↦ 2 * Real.log (term n) - (n + 4))
      atTop (𝓝 (-2 * Real.eulerMascheroniConstant)) := by
  have ht : Tendsto term atTop atTop :=
    (tendsto_add_atTop_nat 2).comp (Nat.nth_strictMono infinite_flat).tendsto_atTop
  have hinv (k : ℕ) : Tendsto (fun n ↦ 2 / ((term n : ℝ) + k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add] using
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp ((tendsto_add_atTop_nat k).comp ht)
  have he : Tendsto (fun n : ℕ ↦ 2 * (harmonic (term n + 2) : ℝ) - (n + 4))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hinv 2) (fun n ↦ (threshold n).1) (fun n ↦ (threshold n).2)
  have hh := Real.tendsto_harmonic_sub_log.comp ht
  have h := ((he.sub (hinv 2)).sub (hinv 1)).sub (hh.const_mul 2)
  convert h using 1
  · ext n
    simp only [Function.comp_apply, Nat.cast_ofNat, Nat.cast_one]
    rw [show term n + 2 = (term n + 1) + 1 by omega, harmonic_succ, harmonic_succ (term n)]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  · congr 1
    ring

private theorem ratio :
    Tendsto (fun n : ℕ ↦ (term (n + 1) : ℝ) / term n)
      atTop (𝓝 (Real.sqrt (Real.exp 1))) := by
  have h := (log_asymptotic.comp (tendsto_add_atTop_nat 1)).sub log_asymptotic
  have d : Tendsto (fun n : ℕ ↦ Real.log (term (n + 1)) - Real.log (term n))
      atTop (𝓝 (1 / 2)) := by
    convert (h.add_const 1).div_const 2 using 1
    · ext n
      simp
      ring
    · norm_num
  rw [← Real.exp_half]
  convert Real.continuous_exp.continuousAt.tendsto.comp d using 1
  ext n
  simp only [Function.comp_apply, Real.exp_sub]
  rw [Real.exp_log (by unfold term; positivity), Real.exp_log (by unfold term; positivity)]

end A133470Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a133470.main := A133470Proof.ratio
