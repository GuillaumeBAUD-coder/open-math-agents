import OMAReductions.R_Erdos319_erdos_319_variants_lb_R1

/-!
# Missing denominators in a unit-fraction expansion

Each omitted denominator contributes at least 1/N to the harmonic sum.
The inequality 1 - x⁻¹ ≤ log x bounds that sum by telescoping over the interval.
-/

open Finset

private lemma reciprocal_le_log_difference (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℝ) / k ≤ Real.log k - Real.log ((k : ℝ) - 1) := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have h₀ : (0 : ℝ) < k := by linarith
  have h₁ : 0 < (k : ℝ) - 1 := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos h₀ h₁)
  rw [inv_div, Real.log_div h₀.ne' h₁.ne'] at h
  convert h using 1
  field_simp
  ring

private lemma harmonic_interval (B N : ℕ) (hB : 2 ≤ B) (hBN : B ≤ N) :
    (∑ i ∈ Icc B N, (1 : ℝ) / i) ≤ Real.log N - Real.log ((B : ℝ) - 1) := by
  induction N, hBN using Nat.le_induction with
  | base => simpa using reciprocal_le_log_difference B hB
  | succ n hn ih =>
    have hI : Icc B (n+1) = insert (n+1) (Icc B n) := by
      ext i
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, sum_insert (by simp)]
    have step := reciprocal_le_log_difference (n+1) (by omega)
    simp only [Nat.cast_add_one, add_sub_cancel_right] at step ⊢
    linarith

theorem OMA.solution : OMA.R_Erdos319_erdos_319_variants_lb_R1.H2 := by
  intro B N S hB hBN hS hsum
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB' : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  have mass : (∑ i ∈ S, (1 : ℝ) / i) = 1 := by
    have hr := congrArg (fun z : ℚ => (z : ℝ)) hsum
    push_cast at hr
    exact hr
  have missing : (((Icc B N \ S).card : ℝ) / N) ≤ ∑ i ∈ Icc B N \ S, (1 : ℝ) / i := calc
    _ = ∑ _i ∈ Icc B N \ S, (1 : ℝ) / N := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      obtain ⟨lo, high⟩ := mem_Icc.mp (mem_sdiff.mp hi).1
      exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < i by omega)) (by exact_mod_cast high)
  rw [card_sdiff_of_subset hS, Nat.cast_sub (card_le_card hS)] at missing
  have split := sum_sdiff (f := fun i : ℕ => (1 : ℝ) / i) hS
  rw [Real.log_div hN.ne' (by linarith)]
  linarith [harmonic_interval B N hB hBN]
