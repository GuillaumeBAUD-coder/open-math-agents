import FormalConjectures.OptimizationConstants.«7a»

-- Problem: Tao's Optimization Constant 7a / The Irrationality Measure of $\pi$ — two le irrationalityExponent
-- Upstream: formal-conjectures FormalConjectures/OptimizationConstants/7a.lean:98 (declaration Constant7a.two_le_irrationalityExponent)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Constant7a.two_le_irrationalityExponent := by
  intro x hx
  have hS : {q : ℚ | |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2}.Infinite :=
    Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  have hT : {n : ℕ | ∃ m : ℤ, x ≠ (m : ℝ) / (n : ℝ) ∧
      |x - (m : ℝ) / (n : ℝ)| < 1 / (n : ℝ) ^ (2 : ℝ)}.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    have hfin : {q : ℚ | |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2}.Finite := by
      refine Set.Finite.subset
        (((Set.finite_Icc (-(⌈|x| * (N : ℝ)⌉ + 1)) (⌈|x| * (N : ℝ)⌉ + 1)).prod
          (Set.finite_Icc 1 N)).image (fun p : ℤ × ℕ => ((p.1 : ℚ) / (p.2 : ℚ)))) ?_
      rintro q hq
      have hd1 : (1 : ℝ) ≤ (q.den : ℝ) := by exact_mod_cast q.pos
      have hd : (0 : ℝ) < (q.den : ℝ) := by linarith
      have hd0 : (q.den : ℝ) ≠ 0 := hd.ne'
      have hc : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := (Rat.cast_def q).symm
      have hqd : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
        rw [← hc]; exact div_mul_cancel₀ _ hd0
      have hne : x ≠ (q.num : ℝ) / (q.den : ℝ) := by
        intro h
        apply hx
        exact ⟨q, by rw [← hc]; exact h.symm⟩
      have hlt' : |x - (q.num : ℝ) / (q.den : ℝ)| < 1 / (q.den : ℝ) ^ (2 : ℝ) := by
        rw [hc, Real.rpow_two]; exact hq
      have hdN : q.den ≤ N := hN (show q.den ∈ {n : ℕ | ∃ m : ℤ, x ≠ (m : ℝ) / (n : ℝ) ∧
          |x - (m : ℝ) / (n : ℝ)| < 1 / (n : ℝ) ^ (2 : ℝ)} from ⟨q.num, hne, hlt'⟩)
      have hdN' : (q.den : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
      have hm : (q.den : ℝ) * |x - (q : ℝ)| < (q.den : ℝ) * (1 / (q.den : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left hq hd
      have hdiv : (q.den : ℝ) * (1 / (q.den : ℝ) ^ 2) ≤ 1 := by
        have e : (q.den : ℝ) * (1 / (q.den : ℝ) ^ 2) = 1 / (q.den : ℝ) := by
          field_simp
        rw [e, div_le_one hd]; exact hd1
      have habs : |(q.den : ℝ) * (x - (q : ℝ))| < 1 := by
        rw [abs_mul, abs_of_pos hd]; linarith
      have hnum : x * (q.den : ℝ) - (q.num : ℝ) = (q.den : ℝ) * (x - (q : ℝ)) := by
        linear_combination hqd
      have hbd : |x * (q.den : ℝ) - (q.num : ℝ)| < 1 := by rw [hnum]; exact habs
      rw [abs_lt] at hbd
      obtain ⟨hl, hu⟩ := hbd
      have hx_le : x * (q.den : ℝ) ≤ |x| * (N : ℝ) := by
        have h1 : x * (q.den : ℝ) ≤ |x| * (q.den : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self x) hd.le
        have h2 : |x| * (q.den : ℝ) ≤ |x| * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hdN' (abs_nonneg x)
        linarith
      have hgeq : -(x * (q.den : ℝ)) ≤ |x| * (N : ℝ) := by
        have h1 : -x * (q.den : ℝ) ≤ |x| * (q.den : ℝ) :=
          mul_le_mul_of_nonneg_right (neg_le_abs x) hd.le
        have h2 : |x| * (q.den : ℝ) ≤ |x| * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hdN' (abs_nonneg x)
        linarith
      have hc1 : |x| * (N : ℝ) ≤ (⌈|x| * (N : ℝ)⌉ : ℝ) := Int.le_ceil _
      have hlo : -(⌈|x| * (N : ℝ)⌉ + 1) ≤ q.num := by
        have : ((-(⌈|x| * (N : ℝ)⌉ + 1) : ℤ) : ℝ) ≤ (q.num : ℝ) := by
          push_cast; linarith
        exact_mod_cast this
      have hhi : q.num ≤ ⌈|x| * (N : ℝ)⌉ + 1 := by
        have : (q.num : ℝ) ≤ ((⌈|x| * (N : ℝ)⌉ + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast this
      exact ⟨(q.num, q.den), ⟨⟨hlo, hhi⟩, ⟨q.pos, hdN⟩⟩, Rat.num_div_den q⟩
    exact hS hfin
  have h2 : LiouvilleWith 2 x := by
    refine ⟨1, ?_⟩
    exact Nat.frequently_atTop_iff_infinite.mpr hT
  rw [Constant7a.le_irrationalityExponent_iff]
  intro z hz
  have hz' : z < 2 := by exact_mod_cast hz
  have hz2 : (z : ℝ) ≤ 2 := by exact_mod_cast hz'.le
  exact h2.mono hz2
