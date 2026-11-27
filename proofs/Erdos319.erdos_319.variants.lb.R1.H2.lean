import OMAReductions.R_Erdos319_erdos_319_variants_lb_R1

open Finset

namespace OMAHarm

lemma step (x : ℝ) (hx : 0 < x) : 1 / (x + 1) ≤ Real.log ((x + 1) / x) := by
  have h1 : Real.log (x / (x + 1)) ≤ x / (x + 1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log ((x + 1) / x) = -Real.log (x / (x + 1)) := by
    rw [← Real.log_inv, inv_div]
  have h3 : x / (x + 1) - 1 = -(1 / (x + 1)) := by
    field_simp
    ring
  rw [h2]
  linarith

lemma harm (B N : ℕ) (hB : 2 ≤ B) (hBN : B ≤ N) :
    ∑ i ∈ Finset.Icc B N, (1 : ℝ) / i ≤ Real.log ((N : ℝ) / ((B : ℝ) - 1)) := by
  have hB1 : (0 : ℝ) < (B : ℝ) - 1 := by
    have : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  induction N, hBN using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    have := step ((B : ℝ) - 1) hB1
    rw [sub_add_cancel] at this
    exact this
  | succ N hN ih =>
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := step (N : ℝ) hN0
    have h2 : Real.log (((N + 1 : ℕ) : ℝ) / ((B : ℝ) - 1)) =
        Real.log ((N : ℝ) / ((B : ℝ) - 1)) + Real.log (((N : ℝ) + 1) / N) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      push_cast
      field_simp
    rw [h2]
    push_cast
    linarith

end OMAHarm

theorem OMA.solution : OMA.R_Erdos319_erdos_319_variants_lb_R1.H2 := by
  intro B N S hB hBN hS hsum
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsumR : ∑ i ∈ S, (1 : ℝ) / i = 1 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hsum
    simpa using this
  have hsplit := Finset.sum_sdiff hS (f := fun i : ℕ => (1 : ℝ) / i)
  have hlow : ((Finset.Icc B N \ S).card : ℝ) * (1 / (N : ℝ)) ≤
      ∑ i ∈ Finset.Icc B N \ S, (1 : ℝ) / i := by
    have := Finset.card_nsmul_le_sum (Finset.Icc B N \ S) (fun i : ℕ => (1 : ℝ) / i) (1 / (N : ℝ))
      (by
        intro i hi
        have hi' := Finset.mem_Icc.1 (Finset.mem_sdiff.1 hi).1
        apply one_div_le_one_div_of_le
        · exact_mod_cast (by omega : 0 < i)
        · exact_mod_cast hi'.2)
    rwa [nsmul_eq_mul] at this
  have hcard : ((Finset.Icc B N \ S).card : ℝ) = ((Finset.Icc B N).card : ℝ) - S.card := by
    rw [Finset.card_sdiff_of_subset hS, Nat.cast_sub (Finset.card_le_card hS)]
  have hh := OMAHarm.harm B N hB hBN
  rw [div_eq_mul_one_div, ← hcard]
  linarith
