import OMAStatements.S_mo_312279

-- Problem: MathOverflow 312279, 1-Lipschitz retracts of a real Hilbert space are exactly the nonempty
-- closed convex sets. (=>) C is the fixed set of a continuous map, hence closed; for x, y in C and
-- z = (1-b) x + b y, d(x, r z) <= b d(x,y) and d(r z, y) <= (1-b) d(x,y), so both are equalities and strict
-- convexity forces r z = z, i.e. z in C. (<=) the metric projection: the variational inequality
-- <u - Pu, w - Pu> <= 0 for both points gives |Pu1 - Pu2|^2 <= <u1 - u2, Pu1 - Pu2>.

theorem OMA.solution : type_of% @OMA.S_mo_312279.main := by
  intro H _ _ _ C
  constructor
  · rintro ⟨r, hr, hrC, hfix⟩
    have hd : ∀ a b, dist (r a) (r b) ≤ dist a b := fun a b => by
      simpa using hr.dist_le_mul a b
    refine ⟨⟨r 0, hrC 0⟩, ?_, ?_⟩
    · have : C = {x | r x = x} := by
        ext x; exact ⟨fun hx => hfix x hx, fun hx => hx ▸ hrC x⟩
      rw [this]
      exact isClosed_eq hr.continuous continuous_id
    · intro x hx y hy a b ha hb hab
      have hz : a • x + b • y = AffineMap.lineMap x y b := by
        rw [AffineMap.lineMap_apply_module, ← hab, add_sub_cancel_right]
      rw [hz]
      set z := AffineMap.lineMap x y b with hzdef
      have h1 : dist x (r z) ≤ b * dist x y := by
        calc dist x (r z) = dist (r z) (r x) := by rw [dist_comm, hfix x hx]
          _ ≤ dist z x := hd z x
          _ = b * dist x y := by rw [hzdef, dist_lineMap_left, Real.norm_of_nonneg hb]
      have h2 : dist (r z) y ≤ (1 - b) * dist x y := by
        calc dist (r z) y = dist (r z) (r y) := by rw [hfix y hy]
          _ ≤ dist z y := hd z y
          _ = (1 - b) * dist x y := by
            rw [hzdef, dist_lineMap_right, Real.norm_of_nonneg (by linarith)]
      have h3 := dist_triangle x (r z) y
      have e1 : dist x (r z) = b * dist x y := by nlinarith
      have e2 : dist (r z) y = (1 - b) * dist x y := by nlinarith
      have : r z = z := eq_lineMap_of_dist_eq_mul_of_dist_eq_mul e1 e2
      rw [← this]; exact hrC z
  · rintro ⟨hne, hcl, hcv⟩
    have hcomp : IsComplete C := hcl.isComplete
    have hex := exists_norm_eq_iInf_of_complete_convex hne hcomp hcv
    choose r hrC hrmin using hex
    have hinner : ∀ u, ∀ w ∈ C, inner ℝ (u - r u) (w - r u) ≤ 0 := fun u =>
      (norm_eq_iInf_iff_real_inner_le_zero hcv (hrC u)).mp (hrmin u)
    refine ⟨r, ?_, hrC, ?_⟩
    · refine LipschitzWith.of_dist_le_mul fun u1 u2 => ?_
      simp only [NNReal.coe_one, one_mul, dist_eq_norm]
      have i1 := hinner u1 (r u2) (hrC u2)
      have i2 := hinner u2 (r u1) (hrC u1)
      have key : inner ℝ (r u1 - r u2) (r u1 - r u2) ≤ inner ℝ (u1 - u2) (r u1 - r u2) := by
        simp only [inner_sub_left, inner_sub_right, real_inner_comm] at i1 i2 ⊢
        linarith
      rw [real_inner_self_eq_norm_sq] at key
      have hcs := real_inner_le_norm (u1 - u2) (r u1 - r u2)
      have hn1 := norm_nonneg (r u1 - r u2)
      have hn2 := norm_nonneg (u1 - u2)
      nlinarith
    · intro x hx
      have h := hinner x x hx
      rw [real_inner_self_eq_norm_sq] at h
      have : ‖x - r x‖ = 0 := by nlinarith [norm_nonneg (x - r x)]
      rw [norm_eq_zero, sub_eq_zero] at this
      exact this.symm
