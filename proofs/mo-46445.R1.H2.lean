import OMAReductions.R_mo_46445_R1

-- Step mo-46445.R1.H2: hypothesis H2 of reduction mo-46445.R1
-- Credit: @nnkostov

/-!
# Strict Decrease of a Shifted Cotangent on a Pole-Free Open Interval

For `t > 0`, wherever `sin ((x + c) * t) ≠ 0` on an open interval `Ioo a b`,
the shifted cotangent `x ↦ cot ((x + c) * t) = cos ((x + c) * t) / sin ((x + c) * t)`
is differentiable with derivative `-t / sin ((x + c) * t) ^ 2 < 0`, and is
therefore strictly decreasing on `Ioo a b` by the mean-value monotonicity theorem.
-/

open Real Set

theorem OMA.solution : OMA.R_mo_46445_R1.H2 := by
  intro a b c t ht hsin
  have hderiv : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y : ℝ => cot ((y + c) * t)) (-t / sin ((x + c) * t) ^ 2) x := by
    intro x hx
    have hs : sin ((x + c) * t) ≠ 0 := hsin x hx
    have hlin : HasDerivAt (fun y : ℝ => (y + c) * t) t x := by
      have h := ((hasDerivAt_id' x).add_const c).mul_const t
      rwa [one_mul] at h
    have hcos : HasDerivAt (fun y : ℝ => cos ((y + c) * t)) (-sin ((x + c) * t) * t) x :=
      hlin.cos
    have hsin_d : HasDerivAt (fun y : ℝ => sin ((y + c) * t)) (cos ((x + c) * t) * t) x :=
      hlin.sin
    have hdiv := hcos.div hsin_d hs
    have hnum : (-sin ((x + c) * t) * t * sin ((x + c) * t) -
        cos ((x + c) * t) * (cos ((x + c) * t) * t)) / sin ((x + c) * t) ^ 2 =
        -t / sin ((x + c) * t) ^ 2 := by
      have hsc := Real.sin_sq_add_cos_sq ((x + c) * t)
      congr 1
      linear_combination -t * hsc
    have hfeq : (fun y : ℝ => cot ((y + c) * t)) =
        fun y : ℝ => cos ((y + c) * t) / sin ((y + c) * t) :=
      funext fun y => Real.cot_eq_cos_div_sin _
    rw [hfeq, ← hnum]
    exact hdiv
  refine strictAntiOn_of_deriv_neg (convex_Ioo a b) ?_ ?_
  · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [isOpen_Ioo.interior_eq] at hx
    rw [(hderiv x hx).deriv]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr ht) (sq_pos_of_ne_zero (hsin x hx))
