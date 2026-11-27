import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R2

open Finset

namespace E307

theorem key (P : Finset ℕ) (h : ∀ a ∈ P, 2 ≤ a) :
    (((∑ a ∈ P, ∏ x ∈ P.erase a, x : ℕ)) : ℚ) =
      (∏ a ∈ P, (a : ℚ)) * ∑ a ∈ P, (a : ℚ)⁻¹ := by
  push_cast
  rw [mul_sum]
  refine sum_congr rfl (fun a ha => ?_)
  rw [← mul_prod_erase P (fun x : ℕ => (x : ℚ)) ha]
  have : (a : ℚ) ≠ 0 := by have := h a ha; positivity
  field_simp

theorem prod_ne (P : Finset ℕ) (h : ∀ a ∈ P, 2 ≤ a) : (∏ a ∈ P, (a : ℚ)) ≠ 0 := by
  rw [prod_ne_zero_iff]
  intro a ha
  have := h a ha
  positivity

end E307

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R2.H2 := by
  intro P Q hP hQ
  have hP0 := E307.prod_ne P hP
  have hQ0 := E307.prod_ne Q hQ
  rw [← Nat.cast_inj (R := ℚ)]
  push_cast only [Nat.cast_mul]
  rw [E307.key P hP, E307.key Q hQ]
  push_cast
  constructor
  · intro h
    have h2 : ((∏ a ∈ P, (a : ℚ)) * ∏ b ∈ Q, (b : ℚ)) *
        ((∑ a ∈ P, (a : ℚ)⁻¹) * ∑ b ∈ Q, (b : ℚ)⁻¹) =
        ((∏ a ∈ P, (a : ℚ)) * ∏ b ∈ Q, (b : ℚ)) * 1 := by
      linear_combination h
    exact mul_left_cancel₀ (mul_ne_zero hP0 hQ0) h2
  · intro h
    calc _ = ((∏ a ∈ P, (a : ℚ)) * ∏ b ∈ Q, (b : ℚ)) *
        ((∑ a ∈ P, (a : ℚ)⁻¹) * ∑ b ∈ Q, (b : ℚ)⁻¹) := by ring
      _ = _ := by rw [h, mul_one]
