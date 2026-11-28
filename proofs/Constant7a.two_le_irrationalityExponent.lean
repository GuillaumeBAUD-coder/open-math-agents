import FormalConjectures.OptimizationConstants.«7a»

/-!
For each denominator bound N, all rationals with denominator at most N lie on
the grid of multiples of 1/N!. Improve on the nearest grid point using
Dirichlet's theorem. The resulting rational must have denominator greater than N.

The earlier formalization is due to @DasPechCodeWeg in PR #286.
-/

theorem OMA.solution : type_of% @Constant7a.two_le_irrationalityExponent := by
  intro x hx
  suffices h : LiouvilleWith 2 x by
    exact le_sSup ⟨(2 : NNReal), by simpa using h, by norm_num⟩
  refine ⟨1, Filter.frequently_atTop.mpr ?_⟩
  intro N
  have hM : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  let a := round (x * (N.factorial : ℝ))
  let q₀ : ℚ := (a : ℚ) / (N.factorial : ℚ)
  obtain ⟨q, hq, hcloser⟩ := Real.exists_rat_abs_sub_lt_and_lt_of_irrational hx q₀
  have distance (b : ℝ) : |x - b / (N.factorial : ℝ)| =
      |x * (N.factorial : ℝ) - b| / (N.factorial : ℝ) := by
    calc
      _ = |(x * (N.factorial : ℝ) - b) / (N.factorial : ℝ)| := by
        congr 1
        field_simp
      _ = _ := by rw [abs_div, abs_of_pos hM]
  have hden : N < q.den := by
    by_contra! hsmall
    obtain ⟨k, hk⟩ := Nat.dvd_factorial q.den_pos hsmall
    have hgrid : (q : ℝ) = ((q.num * (k : ℤ) : ℤ) : ℝ) / (N.factorial : ℝ) := by
      have hk₀ : k ≠ 0 := by
        rintro rfl
        exact Nat.factorial_ne_zero N (by simpa using hk)
      rw [Rat.cast_def, hk]
      push_cast
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk₀
      exact (mul_div_mul_right (q.num : ℝ) (q.den : ℝ) hkR).symm
    have hq₀ : (q₀ : ℝ) = (a : ℝ) / (N.factorial : ℝ) := by simp [q₀]
    have hnearest : |x - (q₀ : ℝ)| ≤ |x - (q : ℝ)| := by
      rw [hq₀, hgrid, distance, distance]
      exact div_le_div_of_nonneg_right (round_le _ _) hM.le
    exact hcloser.not_ge hnearest
  have hcast : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := (Rat.cast_def q).symm
  refine ⟨q.den, hden.le, q.num, ?_, ?_⟩
  · rw [hcast]
    exact hx.ne_rat q
  · rw [hcast, Real.rpow_two]
    exact hq
