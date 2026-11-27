import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1

-- Step Erdos307.erdos_307.variants.coprime_one_notMem.R1.H1: hypothesis H1 of reduction Erdos307.erdos_307.variants.coprime_one_notMem.R1
-- Credit: @DeepDuke
-- H1 := ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →     ((∏ a ∈ A, (a : ℚ)) * (∑ a ∈ A, (a : ℚ)⁻¹) =       ((∑ a ∈ A, (∏ x ∈ A, x) / a : ℕ) : ℚ)) ∧     ∀ w : ℕ, 0 < w → w ∉ A →       (∑ a ∈ insert w A, (∏ x ∈ insert w A, x) / a) =         w * (∑ a ∈ A, (∏ x ∈ A, x) / a) + ∏ x ∈ A, x  -- H2: Any integer closing quotients p, q >= 2 produced by the Frame Rule automatically avoid P0, Q0 -- and preserve pairwise coprimality on insert p P0 and insert q Q0 without extra gcd hypotheses.

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H1 := by
  intro A hA
  constructor
  · rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Nat.cast_div (Finset.dvd_prod_of_mem (fun x => x) ha)
      (by exact_mod_cast (hA a ha).ne')]
    simp only [Nat.cast_prod, div_eq_mul_inv]
  · intro w hw hnot
    rw [Finset.prod_insert hnot, Finset.sum_insert hnot,
      Nat.mul_div_cancel_left _ hw, Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    exact Nat.mul_div_assoc w (Finset.dvd_prod_of_mem (fun x => x) ha)

