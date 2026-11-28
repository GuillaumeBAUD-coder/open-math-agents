import OMAStatements.S_mo_462279

-- Problem: MathOverflow 462279. Let g(x) be the maximizer of y -> f(x, y) and M(x) = f(x, g(x)).
-- Strong concavity of f (and |x1 - x2| <= ||p1 - p2||) makes M strongly concave on R, hence continuous,
-- and comparing with the points 0, ±1 gives M(t) <= t M(±1) - (t-1) M(0) - m/2 t(t-1), so M < M(0)
-- outside a compact interval: M has a global maximizer x*, and (x*, g(x*)) is a global maximizer of f.
-- Two maximizers p, q: strong concavity at the midpoint gives m/8 ||p - q||^2 <= 0.

theorem OMA.solution : type_of% @OMA.S_mo_462279.main := by
  intro f m hm hf hx _
  choose g hg _ using hx
  set M : ℝ → ℝ := fun x => f (x, g x) with hMdef
  -- strong concavity of the partial maximum
  have hM : ∀ x1 x2 a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a * M x1 + b * M x2 + a * b * (m / 2 * |x1 - x2| ^ 2) ≤ M (a * x1 + b * x2) := by
    intro x1 x2 a b ha hb hab
    have h := hf.2 (Set.mem_univ (x1, g x1)) (Set.mem_univ (x2, g x2)) ha hb hab
    have hle : |x1 - x2| ≤ ‖(x1, g x1) - (x2, g x2)‖ := by
      have := norm_fst_le ((x1, g x1) - (x2, g x2))
      simpa [Real.norm_eq_abs] using this
    have hsq : |x1 - x2| ^ 2 ≤ ‖(x1, g x1) - (x2, g x2)‖ ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hle 2
    have hab0 : 0 ≤ a * b := mul_nonneg ha hb
    have h2 : f (a • (x1, g x1) + b • (x2, g x2)) ≤ M (a * x1 + b * x2) := by
      have : a • (x1, g x1) + b • (x2, g x2) = (a * x1 + b * x2, a * g x1 + b * g x2) := by
        ext <;> simp
      rw [this]; exact hg _ _
    simp only [smul_eq_mul] at h
    have : a * b * (m / 2 * |x1 - x2| ^ 2) ≤ a * b * (m / 2 * ‖(x1, g x1) - (x2, g x2)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by linarith)) hab0
    simp only [hMdef]
    linarith
  have hconc : ConcaveOn ℝ Set.univ M := by
    refine ⟨convex_univ, fun x1 _ x2 _ a b ha hb hab => ?_⟩
    have := hM x1 x2 a b ha hb hab
    have : 0 ≤ a * b * (m / 2 * |x1 - x2| ^ 2) := by positivity
    simp only [smul_eq_mul]
    linarith
  have hcont : Continuous M := by
    rw [← continuousOn_univ]; exact hconc.continuousOn isOpen_univ
  -- coercivity
  have hbound : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ t : ℝ, 1 ≤ t →
      M (t * s) ≤ t * M s - (t - 1) * M 0 - m / 2 * t * (t - 1) := by
    intro s hs t ht
    have ht0 : 0 < t := by linarith
    have h := hM 0 (t * s) (1 - 1 / t) (1 / t) (by rw [sub_nonneg, div_le_one ht0]; exact ht)
      (by positivity) (by ring)
    have e1 : (1 - 1 / t) * 0 + 1 / t * (t * s) = s := by field_simp; ring
    have e2 : |0 - t * s| ^ 2 = t ^ 2 := by
      rcases hs with rfl | rfl <;> simp [sq_abs]
    rw [e1, e2] at h
    have key : t * ((1 - 1 / t) * M 0 + 1 / t * M (t * s) + (1 - 1 / t) * (1 / t) * (m / 2 * t ^ 2))
        = (t - 1) * M 0 + M (t * s) + m / 2 * t * (t - 1) := by field_simp
    nlinarith
  set R : ℝ := 2 + 2 * |M 1 - M 0| / m + 2 * |M (-1) - M 0| / m with hR
  have hR1 : 1 ≤ R := by have : 0 ≤ 2 * |M 1 - M 0| / m := by positivity
                         have : 0 ≤ 2 * |M (-1) - M 0| / m := by positivity
                         linarith
  have hout : ∀ x : ℝ, R < |x| → M x < M 0 := by
    intro x hx
    rcases le_or_gt 0 x with h0 | h0
    · rw [abs_of_nonneg h0] at hx
      have h := hbound 1 (Or.inl rfl) x (by linarith)
      rw [mul_one] at h
      have hA : M 1 - M 0 ≤ |M 1 - M 0| := le_abs_self _
      have hB : 2 * |M 1 - M 0| / m + 2 < x := by
        have : 0 ≤ 2 * |M (-1) - M 0| / m := by positivity
        linarith
      have hC : (M 1 - M 0) < m / 2 * (x - 1) := by
        rw [div_add' _ _ _ hm.ne', div_lt_iff₀ hm] at hB
        nlinarith
      nlinarith
    · rw [abs_of_neg h0] at hx
      have h := hbound (-1) (Or.inr rfl) (-x) (by linarith)
      rw [show -x * -1 = x by ring] at h
      have hA : M (-1) - M 0 ≤ |M (-1) - M 0| := le_abs_self _
      have hB : 2 * |M (-1) - M 0| / m + 2 < -x := by
        have : 0 ≤ 2 * |M 1 - M 0| / m := by positivity
        linarith
      have hC : (M (-1) - M 0) < m / 2 * (-x - 1) := by
        rw [div_add' _ _ _ hm.ne', div_lt_iff₀ hm] at hB
        nlinarith
      nlinarith
  obtain ⟨xs, hxs, hmax⟩ := (isCompact_Icc (a := -R) (b := R)).exists_isMaxOn
    ⟨0, by constructor <;> linarith⟩ hcont.continuousOn
  have hglob : ∀ x, M x ≤ M xs := by
    intro x
    by_cases hx : |x| ≤ R
    · exact hmax (abs_le.mp hx)
    · have h0 : M 0 ≤ M xs := hmax ⟨by linarith, by linarith⟩
      exact ((hout x (lt_of_not_ge hx)).trans_le h0).le
  refine ⟨(xs, g xs), fun q => ((hg q.1 q.2).trans (hglob q.1)), ?_⟩
  intro q hq
  have hp : ∀ r : ℝ × ℝ, f r ≤ f (xs, g xs) := fun r => (hg r.1 r.2).trans (hglob r.1)
  have e1 := hq (xs, g xs)
  have e2 := hp q
  have h := hf.2 (Set.mem_univ q) (Set.mem_univ (xs, g xs)) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have h3 := hq ((1 / 2 : ℝ) • q + (1 / 2 : ℝ) • (xs, g xs))
  simp only [smul_eq_mul] at h
  have hn : ‖q - (xs, g xs)‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖q - (xs, g xs)‖ = 0 := by nlinarith [norm_nonneg (q - (xs, g xs))]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)
