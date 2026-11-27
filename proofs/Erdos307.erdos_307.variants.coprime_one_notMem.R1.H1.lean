import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1
import Mathlib.Tactic

-- Step Erdos307.erdos_307.variants.coprime_one_notMem.R1.H1
-- Credit: @nijv

open Finset

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H1 := by
  unfold OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H1
  intro A hApos
  constructor
  · rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hdvd : a ∣ ∏ x ∈ A, x := Finset.dvd_prod_of_mem _ ha
    have hane : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hApos a ha).ne'
    rw [Nat.cast_div hdvd hane, Nat.cast_prod, div_eq_mul_inv]
  · intro w hwpos hwnot
    rw [Finset.sum_insert hwnot, Finset.prod_insert hwnot]
    have hfirst : (w * ∏ x ∈ A, x) / w = ∏ x ∈ A, x := Nat.mul_div_right _ hwpos
    have hrest : (∑ a ∈ A, (w * ∏ x ∈ A, x) / a) = w * ∑ a ∈ A, (∏ x ∈ A, x) / a := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x : ℕ => x) ha
      have hwk : w * (a * k) = a * (w * k) := by ring
      rw [hk, hwk, Nat.mul_div_right _ (hApos a ha), Nat.mul_div_right _ (hApos a ha)]
    omega
