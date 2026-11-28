import FormalConjectures.OptimizationConstants.«7a»

open Filter Set

theorem OMA.solution : type_of% @Constant7a.two_le_irrationalityExponent := by
  intro x hx
  refine le_sSup ⟨2, ?_, by norm_num⟩
  norm_num
  refine ⟨1, frequently_atTop.mpr fun N => ?_⟩
  obtain ⟨C, hC⟩ := exists_int_ge ((|x| + 1) * (N : ℝ))
  have fin : {q : ℚ | |x - q| < 1 / (q.den : ℝ)^2 ∧ q.den ≤ N}.Finite := by
    refine Finite.of_injOn (f := fun q => (q.num, q.den)) ?_ (fun a _ b _ e => Rat.ext (Prod.mk.inj e).1 (Prod.mk.inj e).2) ((finite_Icc (-C) C).prod (finite_Iic N))
    rintro q ⟨hq, hn⟩
    have h₂ := abs_lt.mp (hq.trans_le <| div_le_one_of_le₀ (one_le_pow₀ (mod_cast q.den_pos)) (by positivity))
    have e : (q.num : ℝ) = q * q.den := by exact_mod_cast q.mul_den_eq_num.symm
    have h4 : (q.den : ℝ) ≤ N := mod_cast hn
    exact ⟨by exact_mod_cast (by constructor <;> nlinarith [abs_nonneg x, le_abs_self x, neg_abs_le x] : (-C:ℝ) ≤ q.num ∧ (q.num:ℝ) ≤ C), hn⟩
  obtain ⟨q, hq, hl⟩ := (Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx).exists_notMem_finite fin
  exact ⟨q.den, le_of_not_ge fun h => hl ⟨hq, h⟩, q.num, by rw [← Rat.cast_def]; exact hx.ne_rat q, by simpa [← Rat.cast_def] using hq⟩

