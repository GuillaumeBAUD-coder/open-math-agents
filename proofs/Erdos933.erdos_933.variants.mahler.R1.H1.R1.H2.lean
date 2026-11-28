import OMAReductions.R_Erdos933_erdos_933_variants_mahler_R1_H1_R1

-- Step Erdos933.erdos_933.variants.mahler.R1.H1.R1.H2: hypothesis H2 of reduction Erdos933.erdos_933.variants.mahler.R1.H1.R1
-- Credit: @JamesSlash. If (n, n + 1) and (m, m + 1) both lie in W with n different from m, they span Q x Q
-- (determinant n - m is nonzero): (x, y) = a (n, n + 1) + b (m, m + 1) with a = (x - (y - x) m) / (n - m) and
-- b = y - x - a. So a proper subspace contains at most one such vector, and the set is finite.

theorem OMA.solution : OMA.R_Erdos933_erdos_933_variants_mahler_R1_H1_R1.H2 := by
  intro W hW
  apply Set.Subsingleton.finite
  intro n hn m hm
  by_contra hne
  apply hW
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  have hnm : ((n : ℚ) - m) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have hn' : ((n : ℚ), (n : ℚ) + 1) ∈ W := hn
  have hm' : ((m : ℚ), (m : ℚ) + 1) ∈ W := hm
  have hxy : ((x, y) : ℚ × ℚ) =
      ((x - (y - x) * m) / ((n : ℚ) - m)) • ((n : ℚ), (n : ℚ) + 1) +
        ((y - x) - (x - (y - x) * m) / ((n : ℚ) - m)) • ((m : ℚ), (m : ℚ) + 1) := by
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    ext
    · field_simp
      ring
    · field_simp
      ring
  rw [hxy]
  exact W.add_mem (W.smul_mem _ hn') (W.smul_mem _ hm')
