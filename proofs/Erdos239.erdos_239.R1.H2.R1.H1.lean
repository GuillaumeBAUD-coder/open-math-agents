import OMAReductions.R_Erdos239_erdos_239_R1_H2_R1

-- The open regions where a finite sum exceeds B form a directed cover.
theorem OMA.solution : OMA.R_Erdos239_erdos_239_R1_H2_R1.H1 := by
  classical
  intro f hf hdiv T B
  let w (t : ℝ) (p : Nat.Primes) : ℝ :=
    (1 - f p * Real.cos (t * Real.log p.val)) / p.val
  have nonneg (t : ℝ) (p : Nat.Primes) : 0 ≤ w t p := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply sub_nonneg.mpr
    calc
      f p * Real.cos (t * Real.log p.val) ≤ |f p * Real.cos (t * Real.log p.val)| := le_abs_self _
      _ = |f p| * |Real.cos (t * Real.log p.val)| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hf p p.property.one_le) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul _
  let U (S : Finset Nat.Primes) := {t : ℝ | B < ∑ p ∈ S, w t p}
  have hmono {S R : Finset Nat.Primes} (h : S ⊆ R) : U S ⊆ U R := by
    intro t ht
    exact lt_of_lt_of_le ht (Finset.sum_mono_set_of_nonneg (nonneg t) h)
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := -T) (b := T)).elim_directed_cover U
    (fun S => isOpen_lt continuous_const (continuous_finset_sum _ fun p _ =>
      (continuous_const.sub (continuous_const.mul (Real.continuous_cos.comp
        (continuous_id.mul continuous_const)))).div_const _))
    (by
      intro t _
      apply Set.mem_iUnion.mpr
      by_contra! h
      apply hdiv t
      apply summable_of_sum_le (nonneg t) (c := B)
      intro S
      exact le_of_not_gt (h S))
    (fun S R => ⟨S ∪ R, hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩)
  exact ⟨S, fun t ht => hS ht⟩
