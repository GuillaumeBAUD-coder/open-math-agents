import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1

/-! Clear each reciprocal denominator using its exact cofactor in the product. -/

open Finset

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H1 := by
  intro A hA
  let M : ℕ := ∏ a ∈ A, a
  have hd (a : ℕ) (ha : a ∈ A) : a ∣ M :=
    Finset.dvd_prod_of_mem id ha
  constructor
  · rw [Nat.cast_sum, ← Nat.cast_prod, Finset.mul_sum]
    apply sum_congr rfl
    intro a ha
    change (M : ℚ) * (a : ℚ)⁻¹ = ((M / a : ℕ) : ℚ)
    have hcancel : (M / a) * a = M := Nat.div_mul_cancel (hd a ha)
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (hA a ha).ne'
    rw [← div_eq_mul_inv]
    exact ((eq_div_iff ha0).mpr (by exact_mod_cast hcancel)).symm
  · intro w hw hwA
    have hM : (∏ x ∈ insert w A, x) = w * M := prod_insert hwA
    rw [hM, sum_insert hwA, Nat.mul_div_cancel_left M hw]
    change M + (∑ a ∈ A, (w * M) / a) = w * (∑ a ∈ A, M / a) + M
    rw [Finset.mul_sum, add_comm M]
    congr 1
    exact sum_congr rfl fun a ha => Nat.mul_div_assoc w (hd a ha)
