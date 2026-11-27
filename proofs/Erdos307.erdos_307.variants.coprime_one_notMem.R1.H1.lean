import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1

-- Step Erdos307.erdos_307.variants.coprime_one_notMem.R1.H1: hypothesis H1 of reduction Erdos307.erdos_307.variants.coprime_one_notMem.R1
-- Credit: @ivillar
-- Proof: each a in A divides the product, so the natural division is exact (Nat.cast_div,
-- Nat.mul_div_assoc); then distribute the product over the sum.

namespace OMA.W3Erdos307H1

open Finset

theorem key : ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
    ((∏ a ∈ A, (a : ℚ)) * (∑ a ∈ A, (a : ℚ)⁻¹) =
      ((∑ a ∈ A, (∏ x ∈ A, x) / a : ℕ) : ℚ)) ∧
    ∀ w : ℕ, 0 < w → w ∉ A →
      (∑ a ∈ insert w A, (∏ x ∈ insert w A, x) / a) =
        w * (∑ a ∈ A, (∏ x ∈ A, x) / a) + ∏ x ∈ A, x := by
  intro A hA
  refine ⟨?_, ?_⟩
  · rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have hdvd : a ∣ ∏ x ∈ A, x := Finset.dvd_prod_of_mem _ ha
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (hA a ha).ne'
    rw [Nat.cast_div hdvd ha0, Nat.cast_prod, div_eq_mul_inv]
  · intro w hw hwA
    rw [Finset.sum_insert hwA, Finset.prod_insert hwA, Nat.mul_div_cancel_left _ hw, Finset.mul_sum,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun a ha => ?_)
    exact Nat.mul_div_assoc w (Finset.dvd_prod_of_mem _ ha)

end OMA.W3Erdos307H1

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H1 := by
  unfold OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H1
  exact OMA.W3Erdos307H1.key
