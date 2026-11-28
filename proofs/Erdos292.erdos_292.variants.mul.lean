import FormalConjectures.ErdosProblems.«292»

/-! Replace `1 / m` in the representation for `m` by `m⁻¹` times the representation for `n`. -/

open Finset in
theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.mul := by
  rintro m ⟨S, hS, hm, h⟩ n ⟨T, hT, hn, k⟩
  have mp := (mem_Icc.1 (hS hm)).1
  have np := (mem_Icc.1 (hT hn)).1
  refine ⟨S.erase m ∪ T.image (m * ·), fun a ha => mem_Icc.2 ?_, by simp; exact .inr ⟨n, hn, .inl rfl⟩, ?_⟩
  · rcases mem_union.1 ha with ha | ha
    · have := mem_Icc.1 (hS (mem_erase.1 ha).2)
      exact ⟨this.1, this.2.trans (Nat.le_mul_of_pos_right m np)⟩
    · obtain ⟨b, hb, rfl⟩ := mem_image.1 ha
      obtain ⟨lo, hi⟩ := mem_Icc.1 (hT hb)
      exact ⟨Nat.mul_pos mp lo, Nat.mul_le_mul_left m hi⟩
  · rw [sum_union (disjoint_left.2 fun a ha hb => by
      obtain ⟨hne, ha⟩ := mem_erase.1 ha
      obtain ⟨b, hb', rfl⟩ := mem_image.1 hb
      have := (mem_Icc.1 (hS ha)).2
      have := Nat.le_mul_of_pos_right m (mem_Icc.1 (hT hb')).1
      omega), sum_erase_eq_sub hm, sum_image fun _ _ _ _ e => mul_left_cancel₀ (by omega) e]
    simp only [Nat.cast_mul, ← one_div_mul_one_div, ← mul_sum, h, k]; ring
