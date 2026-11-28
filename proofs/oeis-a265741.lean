import OMAStatements.S_oeis_a265741

-- The argument follows the accepted proof of the template entry OEIS A265735 when e is
-- irrational (Dirichlet approximation); the case of a rational e is handled directly.

open OMA.S_oeis_a265741 in
theorem OMA.solution : type_of% @OMA.S_oeis_a265741.main := by
  intro hT
  obtain ⟨B, hB⟩ := hT.bddAbove
  have he : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  by_cases hirr : Irrational (Real.exp 1)
  swap
  · -- if `e = p / q` were rational, every multiple of `p` would be a term
    obtain ⟨q, hq⟩ : ∃ q : ℚ, (q : ℝ) = Real.exp 1 := by
      by_contra h
      exact hirr (fun ⟨q, hq'⟩ => h ⟨q, hq'⟩)
    have hd := q.den_pos
    have hqpos : (0 : ℚ) < q := by
      have : (0 : ℝ) < q := by rw [hq]; positivity
      exact_mod_cast this
    have hnum : 0 < q.num := Rat.num_pos.mpr hqpos
    set t := B.toNat
    have hk : (1 : ℕ) ≤ q.den * (t + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hmem : q.num * (t + 1) ∈ {m : ℤ | IsTerm m} := by
      refine ⟨q.den * (t + 1), hk, ?_⟩
      have h0 : Real.exp 1 * ((q.den * (t + 1) : ℕ) : ℝ) - ((q.num * (t + 1) : ℤ) : ℝ) = 0 := by
        have hqd : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
        rw [← hq]; push_cast
        rw [← hqd]; ring
      rw [h0, abs_zero]
      positivity
    have h1 := hB hmem
    have h2 : B ≤ (t : ℤ) := Int.self_le_toNat B
    have h3 : (t : ℤ) + 1 ≤ q.num * (t + 1) := by nlinarith
    omega
  have hS := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hirr
  have key : ∀ q : ℚ, |Real.exp 1 - q| < 1 / (q.den : ℝ) ^ 2 →
      q.num ∈ {m : ℤ | IsTerm m} ∧ (q.den : ℤ) < q.num := by
    intro q hq
    have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hd1 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
    have hqq : (q : ℝ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
    have e : |Real.exp 1 * q.den - q.num| = |Real.exp 1 - q| * q.den := by
      rw [hqq, ← abs_of_pos hd, ← abs_mul, abs_of_pos hd]; congr 1; field_simp
    have h2 : |Real.exp 1 * q.den - q.num| < 1 / q.den := by
      rw [e]; calc |Real.exp 1 - q| * q.den < 1 / (q.den : ℝ) ^ 2 * q.den := by gcongr
        _ = 1 / q.den := by field_simp
    refine ⟨⟨q.den, q.den_pos, h2.le⟩, ?_⟩
    have h3 := (abs_lt.mp h2).2
    have h4 : 1 / (q.den : ℝ) ≤ 1 := by rw [div_le_one hd]; exact hd1
    have : (q.den : ℝ) < q.num := by nlinarith
    exact_mod_cast this
  apply hS
  apply Set.Finite.of_finite_image (f := fun q : ℚ => (q.num, q.den))
  · apply Set.Finite.subset ((Set.finite_Icc (-1 : ℤ) B).prod (Set.finite_Iic B.toNat))
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨h1, h2⟩ := key q hq
    have h5 := hB h1
    have : (0:ℤ) < q.den := by exact_mod_cast q.den_pos
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Iic]
    refine ⟨⟨by omega, h5⟩, by omega⟩
  · intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    exact Rat.ext h.1 h.2
