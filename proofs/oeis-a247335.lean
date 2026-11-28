import OMAStatements.S_oeis_a247335

/-!
Proof of the statement of A247335 (curvatures of the circle chain in the larger segment).

* An inscribed circle (center `(x, r)`, radius `r`, internally tangent to `C`) satisfies
  `x^2 = 4/9 (1 - r)`. Two such circles that touch must touch externally (internal tangency
  forces equal abscissas, hence equal radii, hence the same circle), so `(x' - x)^2 = 4 r r'`.
* Eliminating `x, x'` gives `r^2 + r'^2 - 38 r r' + 18 r r' (r + r') + 81 r^2 r'^2 = 0`, i.e. the
  curvatures `k = 1/r`, `k' = 1/r'` satisfy `k^2 + k'^2 - 38 k k' + 18 (k + k') + 81 = 0`.
* With `c 0 = 1`, `c 1 = 10`, `c (n + 2) = 38 c (n + 1) - c n - 18`, consecutive terms satisfy
  the same relation, and `c` is increasing with `c (n + 1) ≥ 10`. From `R 0 = 1` the relation
  forces `1 / R 1 = 10`; then, by induction, `1 / R (n + 2)` is a root of the quadratic whose
  roots are `c n` and `c (n + 2)`. The root `c n` would give `R (n + 2) = R n`, and then either
  `C_(n+2) = C_n` (excluded), or `C_(n+1)` is the middle circle (abscissa 0, radius 1, excluded
  since `c (n + 1) ≥ 10`), or two consecutive circles share their abscissa (excluded). So
  `1 / R n = c n` for every `n`.
* Barker's recurrence follows by subtracting two consecutive three-term recurrences, and the
  g.f. by comparing coefficients.
* A chain exists: `R n = v n = 1 / c n`, `u n = (2/3) sqrt (1 - 1 / c n)`; the tangency of
  consecutive circles reduces to the same quadratic relation.
-/

namespace OMA.Helpers

open OMA.S_oeis_a247335

/-- The curvatures: `c 0 = 1`, `c 1 = 10`, `c (n + 2) = 38 c (n + 1) - c n - 18`. -/
noncomputable def curvA247335 : ℕ → ℝ
  | 0 => 1
  | 1 => 10
  | (n + 2) => 38 * curvA247335 (n + 1) - curvA247335 n - 18

theorem curvSuccSuccA247335 (n : ℕ) :
    curvA247335 (n + 2) = 38 * curvA247335 (n + 1) - curvA247335 n - 18 := rfl

/-- Consecutive curvatures: increasing, at least one, and on the conic
`k^2 + k'^2 - 38 k k' + 18 (k + k') + 81 = 0`. -/
theorem curvFactsA247335 (n : ℕ) :
    1 ≤ curvA247335 n ∧ curvA247335 n < curvA247335 (n + 1) ∧ 10 ≤ curvA247335 (n + 1) ∧
      curvA247335 n ^ 2 + curvA247335 (n + 1) ^ 2 - 38 * curvA247335 n * curvA247335 (n + 1) +
        18 * (curvA247335 n + curvA247335 (n + 1)) + 81 = 0 := by
  induction n with
  | zero => norm_num [curvA247335]
  | succ n ih =>
    obtain ⟨h1, h2, h0, h3⟩ := ih
    rw [curvSuccSuccA247335]
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    linear_combination h3

/-- An inscribed circle: `x^2 = 4/9 (1 - r)`. -/
theorem inscribedSqA247335 {x y r : ℝ} (h : Inscribed x y r) : x ^ 2 = 4 / 9 * (1 - r) := by
  obtain ⟨-, rfl, -, -, -, h⟩ := h
  linear_combination h

/-- Two touching inscribed circles touch externally: `(x' - x)^2 = 4 r r'`. -/
theorem touchExtA247335 {x y r x' y' r' : ℝ} (h : Inscribed x y r) (h' : Inscribed x' y' r')
    (ht : Touch x y r x' y' r') : (x' - x) ^ 2 = 4 * r * r' := by
  have e := inscribedSqA247335 h
  have e' := inscribedSqA247335 h'
  obtain ⟨-, hy, -⟩ := h
  obtain ⟨-, hy', -⟩ := h'
  obtain ⟨hne, hd | hd⟩ := ht
  · rw [hy, hy'] at hd
    linear_combination hd
  · rw [hy, hy'] at hd
    have hx : (x' - x) ^ 2 = 0 := by linear_combination hd
    have hx' : x' = x := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx
      linarith
    have hr : r' = r := by
      rw [hx'] at e'
      linarith
    exact absurd (by rw [hx', hy, hy', hr]) hne

/-- The conic relation between the curvatures of two touching inscribed circles. -/
theorem conicA247335 {x r x' r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (e : x ^ 2 = 4 / 9 * (1 - r))
    (e' : x' ^ 2 = 4 / 9 * (1 - r')) (h : (x' - x) ^ 2 = 4 * r * r') :
    (1 / r) ^ 2 + (1 / r') ^ 2 - 38 * (1 / r) * (1 / r') + 18 * (1 / r + 1 / r') + 81 = 0 := by
  have h3 : ((x' - x) ^ 2 - 4 * r' * r) * ((x' + x) ^ 2 - 4 * r' * r) = 0 := by
    rw [h]; ring
  have h4 : (x ^ 2 + x' ^ 2 - 4 * r * r') ^ 2 - 4 * x ^ 2 * x' ^ 2 = 0 := by
    linear_combination h3
  rw [e, e'] at h4
  have key : r' ^ 2 + r ^ 2 - 38 * r * r' + 18 * r * r' * (r + r') + 81 * r ^ 2 * r' ^ 2 = 0 := by
    linear_combination (81 / 16) * h4
  have hrr : r ^ 2 * r' ^ 2 ≠ 0 := by positivity
  have hid : (1 / r) ^ 2 + (1 / r') ^ 2 - 38 * (1 / r) * (1 / r') + 18 * (1 / r + 1 / r') + 81 =
      (r' ^ 2 + r ^ 2 - 38 * r * r' + 18 * r * r' * (r + r') + 81 * r ^ 2 * r' ^ 2) /
        (r ^ 2 * r' ^ 2) := by
    field_simp
    ring
  rw [hid, key, zero_div]


/-- Along a chain, the curvature `1 / R n` is `curvA247335 n`. -/
theorem chainCurvA247335 {u v R : ℕ → ℝ} (hc : IsChain u v R) (n : ℕ) :
    1 / R n = curvA247335 n := by
  obtain ⟨hI, h0, hT, hN⟩ := hc
  have hpos : ∀ n, 0 < R n := fun n => (hI n).1
  have hv : ∀ n, v n = R n := fun n => (hI n).2.1
  have hsq : ∀ n, u n ^ 2 = 4 / 9 * (1 - R n) := fun n => inscribedSqA247335 (hI n)
  have hext : ∀ n, (u (n + 1) - u n) ^ 2 = 4 * R n * R (n + 1) :=
    fun n => touchExtA247335 (hI n) (hI (n + 1)) (hT n)
  have hq : ∀ n, (1 / R n) ^ 2 + (1 / R (n + 1)) ^ 2 - 38 * (1 / R n) * (1 / R (n + 1)) +
      18 * (1 / R n + 1 / R (n + 1)) + 81 = 0 :=
    fun n => conicA247335 (hpos n) (hpos (n + 1)) (hsq n) (hsq (n + 1)) (hext n)
  have two : ∀ n, 1 / R n = curvA247335 n ∧ 1 / R (n + 1) = curvA247335 (n + 1) := by
    intro n
    induction n with
    | zero =>
      have h1 := hq 0
      rw [h0] at h1
      have h2 : (1 / R 1 - 10) ^ 2 = 0 := by linear_combination h1
      have h3 := (pow_eq_zero_iff (n := 2) (by norm_num)).1 h2
      refine ⟨by rw [h0]; norm_num [curvA247335], ?_⟩
      have h4 : curvA247335 1 = 10 := rfl
      rw [h4]
      linarith
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨ih2, ?_⟩
      obtain ⟨c1, c2, c0, c3⟩ := curvFactsA247335 n
      have hq1 : (1 / R (n + 1)) ^ 2 + (1 / R (n + 2)) ^ 2 -
          38 * (1 / R (n + 1)) * (1 / R (n + 2)) + 18 * (1 / R (n + 1) + 1 / R (n + 2)) + 81 = 0 :=
        hq (n + 1)
      rw [ih2] at hq1
      have hfac : (1 / R (n + 2) - curvA247335 n) * (1 / R (n + 2) - curvA247335 (n + 2)) = 0 := by
        rw [curvSuccSuccA247335]
        linear_combination hq1 - c3
      rcases mul_eq_zero.1 hfac with h | h
      · exfalso
        have hR : R (n + 2) = R n := by
          have e : 1 / R (n + 2) = 1 / R n := by rw [ih1]; linarith
          exact inv_inj.1 (by simpa only [one_div] using e)
        have hsq2 : u (n + 2) ^ 2 = u n ^ 2 := by rw [hsq (n + 2), hsq n, hR]
        have e1 : (u (n + 1) - u n) ^ 2 = 4 * R n * R (n + 1) := hext n
        have e2 : (u (n + 2) - u (n + 1)) ^ 2 = 4 * R (n + 1) * R (n + 2) := hext (n + 1)
        rw [hR] at e2
        have hfac2 : (u (n + 2) - u n) * (u (n + 2) - 2 * u (n + 1) + u n) = 0 := by
          linear_combination e2 - e1
        rcases mul_eq_zero.1 hfac2 with h' | h'
        · apply hN n
          rw [hv (n + 2), hv n, hR, show u (n + 2) = u n by linarith]
        · have hu2 : u (n + 2) = 2 * u (n + 1) - u n := by linarith
          rw [hu2] at hsq2
          have hfac3 : u (n + 1) * (u (n + 1) - u n) = 0 := by linear_combination hsq2 / 4
          rcases mul_eq_zero.1 hfac3 with h'' | h''
          · have hR1 : R (n + 1) = 1 := by
              have := hsq (n + 1)
              rw [h''] at this
              linarith
            rw [hR1] at ih2
            norm_num at ih2
            linarith
          · have hu1 : u (n + 1) = u n := by linarith
            rw [hu1, sub_self] at e1
            have := mul_pos (hpos n) (hpos (n + 1))
            nlinarith
      · linarith
  exact (two n).1

/-- Barker's recurrence for the curvatures. -/
theorem curvRecA247335 (n : ℕ) (hn : 3 ≤ n) :
    curvA247335 n = 39 * curvA247335 (n - 1) - 39 * curvA247335 (n - 2) + curvA247335 (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have h1 : curvA247335 (m + 3) = 38 * curvA247335 (m + 2) - curvA247335 (m + 1) - 18 :=
    curvSuccSuccA247335 (m + 1)
  have h2 : curvA247335 (m + 2) = 38 * curvA247335 (m + 1) - curvA247335 m - 18 :=
    curvSuccSuccA247335 m
  linear_combination h1 - h2

open PowerSeries in
/-- Barker's generating function for the curvatures. -/
theorem curvGenFunA247335 :
    PowerSeries.mk curvA247335 * ((X - 1) * (X ^ 2 - 38 * X + 1)) =
      -(10 * X ^ 2 - 29 * X + 1) := by
  have key : PowerSeries.mk curvA247335 * ((X - 1) * (X ^ 2 - 38 * X + 1)) =
      C 1 * (PowerSeries.mk curvA247335 * X ^ 3) - C 39 * (PowerSeries.mk curvA247335 * X ^ 2) +
        C 39 * (PowerSeries.mk curvA247335 * X ^ 1) -
        C 1 * (PowerSeries.mk curvA247335 * X ^ 0) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (-(10 * X ^ 2 - 29 * X + 1) : PowerSeries ℝ) =
      C 29 * X ^ 1 - C 10 * X ^ 2 - C 1 * X ^ 0 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 3
  · interval_cases k <;> norm_num [curvA247335]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hr := curvRecA247335 (j + 3) (by omega)
    simp only [show 0 ≤ j + 3 by omega, show 1 ≤ j + 3 by omega, show 2 ≤ j + 3 by omega,
      show 3 ≤ j + 3 by omega, show j + 3 - 0 = j + 3 by omega,
      show j + 3 - 1 = j + 2 by omega, show j + 3 - 2 = j + 1 by omega,
      show j + 3 - 3 = j by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 3 = 1) by omega,
      show ¬ (j + 3 = 2) by omega, if_true, if_false] at hr ⊢
    linear_combination (-1 : ℝ) * hr

open PowerSeries in
theorem forallPartA247335 (u v R : ℕ → ℝ) (hc : IsChain u v R) :
    (∀ n, 3 ≤ n → 1 / R n = 39 * (1 / R (n - 1)) - 39 * (1 / R (n - 2)) + 1 / R (n - 3)) ∧
      PowerSeries.mk (fun n => 1 / R n) * ((X - 1) * (X ^ 2 - 38 * X + 1)) =
        -(10 * X ^ 2 - 29 * X + 1) := by
  have h := chainCurvA247335 hc
  refine ⟨fun n hn => ?_, ?_⟩
  · simp only [h]
    exact curvRecA247335 n hn
  · have e : (fun n => 1 / R n) = curvA247335 := funext h
    rw [e]
    exact curvGenFunA247335


/-- An explicit chain: `R n = v n = 1 / c n` and `u n = (2/3) sqrt (1 - 1 / c n)`. -/
theorem existsChainA247335 : ∃ u v R : ℕ → ℝ, IsChain u v R := by
  refine ⟨fun n => 2 / 3 * Real.sqrt (1 - 1 / curvA247335 n), fun n => 1 / curvA247335 n,
    fun n => 1 / curvA247335 n, ?_, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨c1, -, -, -⟩ := curvFactsA247335 n
    have hpos : 0 < curvA247335 n := by linarith
    have hr : 0 < 1 / curvA247335 n := by positivity
    have hr1 : 1 / curvA247335 n ≤ 1 := by rw [div_le_one hpos]; exact c1
    have hs0 : 0 ≤ 1 - 1 / curvA247335 n := by linarith
    have hsq := Real.sq_sqrt hs0
    have hsn := Real.sqrt_nonneg (1 - 1 / curvA247335 n)
    have hs1 : Real.sqrt (1 - 1 / curvA247335 n) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    refine ⟨hr, rfl, by linarith, by linarith, by linarith, ?_⟩
    linear_combination (4 / 9) * hsq
  · show 1 / curvA247335 0 = 1
    norm_num [curvA247335]
  · intro n
    obtain ⟨c1, c2, c0, c3⟩ := curvFactsA247335 n
    have hpos : 0 < curvA247335 n := by linarith
    have hpos' : 0 < curvA247335 (n + 1) := by linarith
    have hs0 : 0 ≤ 1 - 1 / curvA247335 n := by
      have : 1 / curvA247335 n ≤ 1 := by rw [div_le_one hpos]; exact c1
      linarith
    have hs0' : 0 ≤ 1 - 1 / curvA247335 (n + 1) := by
      have : 1 / curvA247335 (n + 1) ≤ 1 := by rw [div_le_one hpos']; linarith
      linarith
    have hsq := Real.sq_sqrt hs0
    have hsq' := Real.sq_sqrt hs0'
    have hid : ((2 - 1 / curvA247335 n - 1 / curvA247335 (n + 1) -
        9 * (1 / curvA247335 n) * (1 / curvA247335 (n + 1))) / 2) ^ 2 -
        (1 - 1 / curvA247335 n) * (1 - 1 / curvA247335 (n + 1)) =
        (curvA247335 n ^ 2 + curvA247335 (n + 1) ^ 2 - 38 * curvA247335 n * curvA247335 (n + 1) +
          18 * (curvA247335 n + curvA247335 (n + 1)) + 81) /
          (4 * curvA247335 n ^ 2 * curvA247335 (n + 1) ^ 2) := by
      field_simp
      ring
    rw [c3, zero_div] at hid
    have hnum : (2 - 1 / curvA247335 n - 1 / curvA247335 (n + 1) -
        9 * (1 / curvA247335 n) * (1 / curvA247335 (n + 1))) / 2 =
        (2 * curvA247335 n * curvA247335 (n + 1) - curvA247335 n - curvA247335 (n + 1) - 9) /
          (2 * curvA247335 n * curvA247335 (n + 1)) := by
      field_simp
      ring
    have hnn : 0 ≤ (2 - 1 / curvA247335 n - 1 / curvA247335 (n + 1) -
        9 * (1 / curvA247335 n) * (1 / curvA247335 (n + 1))) / 2 := by
      rw [hnum]
      apply div_nonneg _ (by positivity)
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * curvA247335 n - 1 by linarith)
        (show (0 : ℝ) ≤ curvA247335 (n + 1) - 10 by linarith)]
    have hss : Real.sqrt (1 - 1 / curvA247335 n) * Real.sqrt (1 - 1 / curvA247335 (n + 1)) =
        (2 - 1 / curvA247335 n - 1 / curvA247335 (n + 1) -
          9 * (1 / curvA247335 n) * (1 / curvA247335 (n + 1))) / 2 := by
      rw [← Real.sqrt_mul hs0, Real.sqrt_eq_iff_eq_sq (mul_nonneg hs0 hs0') hnn]
      linarith
    refine ⟨?_, Or.inl ?_⟩
    · intro h
      have e : 1 / curvA247335 (n + 1) = 1 / curvA247335 n := congrArg (fun p => p.2.2) h
      have := inv_inj.1 (by simpa only [one_div] using e)
      linarith
    · show (2 / 3 * Real.sqrt (1 - 1 / curvA247335 (n + 1)) -
          2 / 3 * Real.sqrt (1 - 1 / curvA247335 n)) ^ 2 +
          (1 / curvA247335 (n + 1) - 1 / curvA247335 n) ^ 2 =
          (1 / curvA247335 n + 1 / curvA247335 (n + 1)) ^ 2
      linear_combination (4 / 9) * hsq' + (4 / 9) * hsq - (8 / 9) * hss
  · intro n h
    obtain ⟨c1, c2, -, -⟩ := curvFactsA247335 n
    obtain ⟨-, d2, -, -⟩ := curvFactsA247335 (n + 1)
    have e : 1 / curvA247335 (n + 2) = 1 / curvA247335 n := congrArg (fun p => p.2.2) h
    have := inv_inj.1 (by simpa only [one_div] using e)
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a247335.main :=
  ⟨OMA.Helpers.existsChainA247335, OMA.Helpers.forallPartA247335⟩
