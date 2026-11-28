import OMAStatements.S_mse_1911440

/-!
At stage n, flatten the map quadratically around the image of the n-th rational.
The edit is the identity at all earlier images. Its Lipschitz factor is bounded
by the ratio of two consecutive terms of a sequence in [1, 2]. Each rational
image therefore stabilizes, and the local quadratic estimate survives all later
edits.
-/

private def tail (d x : ℚ) : ℚ := max 0 (x - d)

private def capacity (e d : ℚ) : ℚ := d / (2 * e)

private def flatPos (e d x : ℚ) : ℚ :=
  tail d x + (min x d) ^ 2 / (2 * d) + e * min (tail d x) (capacity e d)

private def flat (e d x : ℚ) : ℚ :=
  if 0 ≤ x then flatPos e d x else -flatPos e d (-x)

private theorem tail_decompose (d x : ℚ) : min x d + tail d x = x := by
  unfold tail
  by_cases hx : x ≤ d
  · simp [min_eq_left hx, max_eq_left (sub_nonpos.mpr hx)]
  · rw [min_eq_right (le_of_not_ge hx), max_eq_right (sub_nonneg.mpr (le_of_not_ge hx))]
    ring

private theorem flatPos_controls {e d x y : ℚ} (he : 0 < e) (hd : 0 < d)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    (x < y → flatPos e d x < flatPos e d y) ∧
      flatPos e d y - flatPos e d x ≤ (1 + e) * (y - x) := by
  have htail : tail d x ≤ tail d y := max_le_max_left _ (sub_le_sub_right hxy _)
  have hmin : min x d ≤ min y d := min_le_min_right _ hxy
  have hzero : 0 ≤ min x d := le_min hx hd.le
  have hcap : min (tail d x) (capacity e d) ≤ min (tail d y) (capacity e d) :=
    min_le_min_right _ htail
  have hcDiff : min (tail d y) (capacity e d) - min (tail d x) (capacity e d) ≤
      tail d y - tail d x := by
    by_cases h : tail d x ≤ capacity e d
    · rw [min_eq_left h]
      have hy := min_le_left (tail d y) (capacity e d)
      linarith
    · rw [min_eq_right (le_of_not_ge h)]
      have hy := min_le_right (tail d y) (capacity e d)
      linarith
  have hsquare : (min x d)^2 ≤ (min y d)^2 :=
    pow_le_pow_left₀ hzero hmin _
  have hcentral : (min y d)^2 / (2*d) - (min x d)^2 / (2*d) ≤ min y d - min x d := by
    rw [← sub_div]
    apply (div_le_iff₀ (by positivity)).2
    have hmul := mul_nonneg (sub_nonneg.mpr hmin)
      (sub_nonneg.mpr (add_le_add (min_le_right x d) (min_le_right y d)))
    nlinarith only [hmul]
  constructor
  · intro hlt
    by_cases ht : tail d x < tail d y
    · unfold flatPos
      have hq := div_le_div_of_nonneg_right hsquare (show 0 ≤ 2*d by positivity)
      have hm := mul_le_mul_of_nonneg_left hcap he.le
      linarith
    · have hq : min x d < min y d := by
        linarith [tail_decompose d x, tail_decompose d y, le_of_not_gt ht]
      have hs : (min x d)^2 < (min y d)^2 :=
        pow_lt_pow_left₀ hq hzero (by decide)
      unfold flatPos
      have hdm : (min x d)^2 / (2*d) < (min y d)^2 / (2*d) :=
        div_lt_div_of_pos_right hs (by positivity)
      have hm := mul_le_mul_of_nonneg_left hcap he.le
      linarith
  · have htDiff : tail d y - tail d x ≤ y-x := by
      linarith [tail_decompose d x, tail_decompose d y]
    have hm := mul_le_mul_of_nonneg_left (hcDiff.trans htDiff) he.le
    unfold flatPos
    nlinarith only [hcentral, hm, tail_decompose d x, tail_decompose d y]

private theorem flatPos_zero {e d : ℚ} (he : 0 < e) (hd : 0 < d) : flatPos e d 0 = 0 := by
  have hcap : 0 ≤ capacity e d := by unfold capacity; positivity
  simp [flatPos, tail, min_eq_left hd.le, max_eq_left (neg_nonpos.mpr hd.le), min_eq_left hcap]

private theorem flat_controls {e d x y : ℚ} (he : 0 < e) (hd : 0 < d) (hxy : x ≤ y) :
    (x < y → flat e d x < flat e d y) ∧
      flat e d y - flat e d x ≤ (1 + e) * (y - x) := by
  by_cases hx : 0 ≤ x
  · simpa only [flat, if_pos hx, if_pos (hx.trans hxy)] using flatPos_controls he hd hx hxy
  · by_cases hy : 0 ≤ y
    · rw [flat, if_neg hx, flat, if_pos hy]
      have hx' : 0 < -x := by linarith
      obtain ⟨hxp, hxb⟩ := flatPos_controls he hd le_rfl hx'.le
      obtain ⟨hyp, hyb⟩ := flatPos_controls he hd le_rfl hy
      have hy' : 0 ≤ flatPos e d y := by
        rcases hy.eq_or_lt with hy | hy
        · rw [← hy, flatPos_zero he hd]
        · rw [← flatPos_zero he hd]
          exact (hyp hy).le
      simp only [flatPos_zero he hd, sub_zero] at hxp hxb hyb
      constructor
      · intro _
        linarith [hxp hx']
      · nlinarith only [hxb, hyb]
    · rw [flat, if_neg hx, flat, if_neg hy]
      obtain ⟨hmono, hbound⟩ := flatPos_controls he hd
        (neg_nonneg.mpr (le_of_not_ge hy)) (neg_le_neg hxy)
      exact ⟨fun h => neg_lt_neg (hmono (neg_lt_neg h)), by linarith⟩

private theorem flat_zero {e d : ℚ} (he : 0 < e) (hd : 0 < d) : flat e d 0 = 0 := by
  simpa [flat] using flatPos_zero he hd

private theorem flat_outside {e d x : ℚ} (he : 0 < e) (hd : 0 < d)
    (hx : d + capacity e d ≤ |x|) : flat e d x = x := by
  have haux (u : ℚ) (hu : d + capacity e d ≤ u) : flatPos e d u = u := by
    have hcap : 0 ≤ capacity e d := by unfold capacity; positivity
    have hdu : d ≤ u := by linarith
    unfold flatPos tail
    rw [max_eq_right (sub_nonneg.mpr hdu), min_eq_right hdu, min_eq_right (by linarith : capacity e d ≤ u-d)]
    unfold capacity
    field_simp
    ring
  by_cases hx0 : 0 ≤ x
  · simp only [flat, if_pos hx0]
    exact haux x (by simpa [abs_of_nonneg hx0] using hx)
  · simp only [flat, if_neg hx0]
    rw [haux (-x) (by simpa [abs_of_nonpos (le_of_not_ge hx0)] using hx), neg_neg]

private theorem flat_center {e d x : ℚ} (he : 0 < e) (hd : 0 < d)
    (hx : |x| ≤ d) : |flat e d x| = |x| ^ 2 / (2*d) := by
  have haux (u : ℚ) (hu : u ≤ d) : flatPos e d u = u^2/(2*d) := by
    have hcap : 0 ≤ capacity e d := by unfold capacity; positivity
    simp [flatPos, tail, min_eq_left hu, max_eq_left (sub_nonpos.mpr hu), min_eq_left hcap]
  by_cases hx0 : 0 ≤ x
  · simp only [flat, if_pos hx0, abs_of_nonneg hx0]
    rw [haux x (by simpa [abs_of_nonneg hx0] using hx), abs_of_nonneg (by positivity)]
  · simp only [flat, if_neg hx0, abs_neg, abs_of_nonpos (le_of_not_ge hx0)]
    rw [haux (-x) (by simpa [abs_of_nonpos (le_of_not_ge hx0)] using hx), abs_of_nonneg (by positivity)]

open Filter Asymptotics
open scoped Topology

private def enumerate : ℕ ≃ ℚ := (Denumerable.eqv ℚ).symm

private def epsilon (n : ℕ) : ℚ := 1 / (((n : ℚ) + 1) * ((n : ℚ) + 3))
private def bound (n : ℕ) : ℚ := 2 * ((n : ℚ) + 1) / ((n : ℚ) + 2)

private theorem epsilon_pos (n : ℕ) : 0 < epsilon n := by unfold epsilon; positivity
private theorem bound_pos (n : ℕ) : 0 < bound n := by unfold bound; positivity
private theorem bound_lower (n : ℕ) : 1 ≤ bound n := by
  unfold bound
  apply (le_div_iff₀ (by positivity)).mpr
  linarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]
private theorem bound_upper (n : ℕ) : bound n ≤ 2 := by
  unfold bound
  apply (div_le_iff₀ (by positivity)).mpr
  linarith
private theorem bound_step (n : ℕ) : bound (n + 1) = (1 + epsilon n) * bound n := by
  unfold bound epsilon
  push_cast
  field_simp
  ring

private def inverseRadius (n : ℕ) (f : ℚ → ℚ) : ℚ :=
  1 + ∑ j ∈ Finset.range n, |f (enumerate j) - f (enumerate n)|⁻¹

private theorem inverseRadius_pos (n : ℕ) (f : ℚ → ℚ) : 0 < inverseRadius n f := by
  unfold inverseRadius
  positivity

private def innerWidth (n : ℕ) (f : ℚ → ℚ) : ℚ :=
  (2 * epsilon n) / (1 + 2 * epsilon n) * (inverseRadius n f)⁻¹

private theorem inner_pos (n : ℕ) (f : ℚ → ℚ) : 0 < innerWidth n f := by
  have he := epsilon_pos n
  have hr := inverseRadius_pos n f
  unfold innerWidth
  positivity

private theorem inner_radius (n : ℕ) (f : ℚ → ℚ) :
    innerWidth n f + capacity (epsilon n) (innerWidth n f) = (inverseRadius n f)⁻¹ := by
  have he := epsilon_pos n
  have hr := inverseRadius_pos n f
  unfold innerWidth capacity
  field_simp
  ring

private theorem radius_avoids {n j : ℕ} {f : ℚ → ℚ} (hf : StrictMono f) (h : j < n) :
    (inverseRadius n f)⁻¹ ≤ |f (enumerate j) - f (enumerate n)| := by
  let gap := |f (enumerate j) - f (enumerate n)|
  have hgap : 0 < gap := by
    apply abs_pos.mpr
    exact sub_ne_zero.mpr (fun he => h.ne (enumerate.injective (hf.injective he)))
  have hsum : gap⁻¹ ≤ ∑ i ∈ Finset.range n, |f (enumerate i) - f (enumerate n)|⁻¹ :=
    Finset.single_le_sum (f := fun i : ℕ => |f (enumerate i) - f (enumerate n)|⁻¹)
      (fun i _ => by positivity) (Finset.mem_range.mpr h)
  have hlarge : gap⁻¹ ≤ inverseRadius n f := by unfold inverseRadius; linarith
  change (inverseRadius n f)⁻¹ ≤ gap
  simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hgap) hlarge

private def edit (n : ℕ) (f : ℚ → ℚ) (u : ℚ) : ℚ :=
  let p := f (enumerate n)
  p + flat (epsilon n) (innerWidth n f) (u - p)

private theorem edit_strictMono (n : ℕ) (f : ℚ → ℚ) : StrictMono (edit n f) := by
  intro x y h
  have hsub := sub_lt_sub_right h (f (enumerate n))
  have hl := (flat_controls (epsilon_pos n) (inner_pos n f) hsub.le).1 hsub
  unfold edit
  dsimp only
  linarith

private theorem edit_abs (n : ℕ) (f : ℚ → ℚ) (x y : ℚ) :
    |edit n f x - edit n f y| ≤ (1 + epsilon n) * |x - y| := by
  have aux (u v : ℚ) (h : v ≤ u) :
      |edit n f u - edit n f v| ≤ (1 + epsilon n) * |u-v| := by
    rw [abs_of_nonneg (sub_nonneg.mpr ((edit_strictMono n f).monotone h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    have hu := flat_controls (epsilon_pos n) (inner_pos n f)
      (sub_le_sub_right h (f (enumerate n)))
    unfold edit
    dsimp only
    linarith only [hu.2]
  rcases le_total y x with h | h
  · exact aux x y h
  · rw [abs_sub_comm x y, abs_sub_comm (edit n f x) (edit n f y)]
    exact aux y x h

private def stage : ℕ → ℚ → ℚ
  | 0 => id
  | n + 1 => fun q => edit n (stage n) (stage n q)

private theorem stage_strict (n : ℕ) : StrictMono (stage n) := by
  induction n with
  | zero => exact strictMono_id
  | succ n ih => exact (edit_strictMono n (stage n)).comp ih

private theorem stage_step_fixed {j n : ℕ} (h : j ≤ n) :
    stage (n+1) (enumerate j) = stage n (enumerate j) := by
  change edit n (stage n) (stage n (enumerate j)) = _
  unfold edit
  dsimp only
  rcases h.lt_or_eq with h | heq
  · have hw := radius_avoids (stage_strict n) h
    rw [← inner_radius n (stage n)] at hw
    rw [flat_outside (epsilon_pos n) (inner_pos n (stage n)) hw]
    ring
  · subst j
    rw [sub_self, flat_zero (epsilon_pos n) (inner_pos n (stage n)), add_zero]

private theorem stage_stable {j n : ℕ} (h : j ≤ n) :
    stage n (enumerate j) = stage j (enumerate j) := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih => exact (stage_step_fixed hm).trans ih

private def limit (q : ℚ) : ℚ := stage (enumerate.symm q) q

private theorem limit_eq_stage (q : ℚ) (n : ℕ) (h : enumerate.symm q ≤ n) :
    limit q = stage n q := by
  have hs := stage_stable h
  rw [Equiv.apply_symm_apply] at hs
  exact hs.symm

private theorem limit_strict : StrictMono limit := by
  intro x y h
  let n := max (enumerate.symm x) (enumerate.symm y)
  rw [limit_eq_stage x n (le_max_left _ _), limit_eq_stage y n (le_max_right _ _)]
  exact stage_strict n h

private theorem stage_ratio {n m : ℕ} (h : n ≤ m) (x y : ℚ) :
    |stage m x - stage m y| ≤ bound m / bound n * |stage n x - stage n y| := by
  induction m, h using Nat.le_induction with
  | base => simp [ne_of_gt (bound_pos n)]
  | succ k hk ih =>
    calc
      _ ≤ (1 + epsilon k) * |stage k x - stage k y| :=
        edit_abs k (stage k) (stage k x) (stage k y)
      _ ≤ (1 + epsilon k) * (bound k / bound n * |stage n x - stage n y|) :=
        mul_le_mul_of_nonneg_left ih (by have := epsilon_pos k; positivity)
      _ = _ := by rw [bound_step]; ring

private theorem stage_control {n m : ℕ} (h : n ≤ m) (x y : ℚ) :
    |stage m x - stage m y| ≤ 2 * |stage n x - stage n y| := by
  apply (stage_ratio h x y).trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply (div_le_iff₀ (bound_pos n)).mpr
  linarith [bound_lower n, bound_upper m]

private theorem limit_control (n : ℕ) (x y : ℚ) :
    |limit x - limit y| ≤ 2 * |stage n x - stage n y| := by
  let k := max (enumerate.symm x) (enumerate.symm y)
  let m := max n k
  rw [limit_eq_stage x m ((le_max_left _ _).trans (le_max_right _ _)),
    limit_eq_stage y m ((le_max_right _ _).trans (le_max_right _ _))]
  exact stage_control (le_max_left _ _) x y

private theorem limit_near (n : ℕ) (x : ℚ)
    (hx : |x - enumerate n| ≤ innerWidth n (stage n) / 2) :
    |limit x - limit (enumerate n)| ≤ 4 / innerWidth n (stage n) * |x - enumerate n| ^ 2 := by
  let d := innerWidth n (stage n)
  let p := stage n (enumerate n)
  have hd : 0 < d := inner_pos n (stage n)
  have hinput : |stage n x - p| ≤ 2 * |x - enumerate n| :=
    stage_control (Nat.zero_le n) x (enumerate n)
  have hcenter : |stage n x - p| ≤ d := by linarith
  have hfirst : |stage (n+1) x - stage (n+1) (enumerate n)| =
      |stage n x - p| ^ 2 / (2*d) := by
    rw [stage_step_fixed (le_refl n)]
    change |p + flat (epsilon n) d (stage n x - p) - p| = _
    rw [add_sub_cancel_left, flat_center (epsilon_pos n) hd hcenter]
  calc
    _ ≤ 2 * |stage (n + 1) x - stage (n + 1) (enumerate n)| := limit_control _ _ _
    _ = |stage n x - p| ^ 2 / d := by rw [hfirst]; ring
    _ ≤ (2 * |x - enumerate n|) ^ 2 / d :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hinput _) hd.le
    _ = _ := by change _ = 4 / d * _; ring

theorem OMA.solution : type_of% @OMA.S_mse_1911440.main := by
  refine ⟨limit, limit_strict, ?_⟩
  intro q
  obtain ⟨n, rfl⟩ := enumerate.surjective q
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  let d : ℚ := innerWidth n (stage n)
  have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast inner_pos n (stage n)
  have hr : 0 < min ((d : ℝ) / 2) (c * (d : ℝ) / 4) :=
    lt_min (by positivity) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (enumerate n) hr] with x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hclose : |x - enumerate n| ≤ d / 2 := by
    have h := hx.le.trans (min_le_left _ _)
    rw [← Rat.norm_cast_real, Real.norm_eq_abs, ← Rat.cast_abs] at h
    exact_mod_cast h
  have hraw := limit_near n x hclose
  have hrawR : ((|limit x - limit (enumerate n)| : ℚ) : ℝ) ≤
      4 / (d : ℝ) * ((|x - enumerate n| : ℚ) : ℝ) ^ 2 := by
    exact_mod_cast hraw
  simp only [smul_zero, sub_zero, ← Rat.norm_cast_real, Real.norm_eq_abs, ← Rat.cast_abs]
  apply hrawR.trans
  have hxbound := hx.le.trans (min_le_right _ _)
  rw [← Rat.norm_cast_real, Real.norm_eq_abs, ← Rat.cast_abs] at hxbound
  have hprod : 4 / (d : ℝ) * ((|x - enumerate n| : ℚ) : ℝ) ≤ c := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    linarith
  have hnonneg : (0 : ℝ) ≤ ((|x - enumerate n| : ℚ) : ℝ) := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right hprod hnonneg]
