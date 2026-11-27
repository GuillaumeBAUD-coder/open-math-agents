import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1
import Mathlib

/-! Pull out the common denominator by erasing one factor at a time. -/

open Finset

namespace OMA.CoprimeFrame

theorem denominator_and_insert (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ((∏ a ∈ A, (a : ℚ)) * (∑ a ∈ A, (a : ℚ)⁻¹) =
      ((∑ a ∈ A, (∏ x ∈ A, x) / a : ℕ) : ℚ)) ∧
    ∀ w : ℕ, 0 < w → w ∉ A →
      (∑ a ∈ insert w A, (∏ x ∈ insert w A, x) / a) =
        w * (∑ a ∈ A, (∏ x ∈ A, x) / a) + ∏ x ∈ A, x := by
  constructor
  · rw [mul_sum,Nat.cast_sum]
    apply sum_congr rfl
    intro a ha
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (hA a ha).ne'
    have hProdN : (∏ x ∈ A, x) / a = ∏ x ∈ A.erase a, x := by
      rw [← mul_prod_erase A (fun x : ℕ => x) ha]
      simp [Nat.mul_div_cancel_left _ (hA a ha)]
    rw [hProdN,Nat.cast_prod,← mul_prod_erase A (fun x : ℕ => (x : ℚ)) ha]
    rw [mul_comm (a : ℚ),mul_assoc,mul_inv_cancel₀ ha0,mul_one]
  · intro w hw hNew
    have hW : ∏ x ∈ insert w A,x = w*(∏ x ∈ A,x) := prod_insert hNew
    rw [sum_insert hNew,hW]
    rw [Nat.mul_div_cancel_left _ hw,add_comm]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    exact Nat.mul_div_assoc _ (dvd_prod_of_mem id ha)

end OMA.CoprimeFrame


theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H1 :=
  OMA.CoprimeFrame.denominator_and_insert
