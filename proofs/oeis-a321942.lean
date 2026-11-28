import OMAStatements.S_oeis_a321942

/-!
# Proof of Bala's integral conjecture for OEIS A321942

Source: https://oeis.org/A321942
Credit: @bmendonca3

For `n ≥ 1`, `∫_{x ≥ 0} (x / (1 + x))^n exp(-x) dx = (a(n) - A000262(n) G) / (n-1)!`.

Outline. Write `I(n)` for the integral and `b = A000262`.
* `b(m+3) = (2 m + 5) b(m+2) - (m+2) (m+1) b(m+1)`. With `t(m,k) = k! C(m,k) C(m+1,k)` and
  `g(m,k) = k ((m+2-k)^2 - (m+3)) t(m+2,k) / ((m+2) (m+3))`, the identity
  `t(m+2,k) - (2 m + 5) t(m+1,k) + (m+1) (m+2) t(m,k) = g(m,k+1) - g(m,k)` holds for all `k`.
  The sum over `k < m + 3` telescopes to `g(m,m+3) - g(m,0) = 0`.
* `(n+1) I(n+2) = (2 n + 3) I(n+1) - (n+1) I(n)`: integrate the derivative of
  `(x / (1 + x))^(n+1) exp(-x)`, with `d/dx (x / (1 + x)) = (1 - x / (1 + x))^2`.
* `I(0) = 1` and `I(1) = 1 - G`, so `I(2) = 2 - 3 G`.
* `n! I(n+1)` and `a(n+1) - b(n+1) G` satisfy the same recurrence with the same two initial
  values.
-/

namespace OMA.A321942Proof

open OMA.S_oeis_a321942 MeasureTheory Set Filter Topology

/-- The term of the sum that defines `A000262 (m + 1)`. -/
noncomputable def t (m k : ℕ) : ℝ :=
  (k.factorial : ℝ) * (m.choose k : ℝ) * ((m + 1).choose k : ℝ)

/-- The telescoping certificate. -/
noncomputable def g (m k : ℕ) : ℝ :=
  (k : ℝ) * (((m : ℝ) + 2 - k) ^ 2 - ((m : ℝ) + 3)) * t (m + 2) k / (((m : ℝ) + 2) * ((m : ℝ) + 3))

lemma choose_succ_right_cast (n k : ℕ) :
    (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) = ((n : ℝ) - k) * (n.choose k : ℝ) := by
  rcases le_or_gt k n with h | h
  · have h1 : ((n.choose (k + 1) * (k + 1) : ℕ) : ℝ) = ((n.choose k * (n - k) : ℕ) : ℝ) := by
      rw [Nat.choose_succ_right_eq]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h] at h1
    push_cast at h1
    linarith
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma choose_mul_succ_cast (n k : ℕ) :
    (n.choose k : ℝ) * ((n : ℝ) + 1) = ((n : ℝ) + 1 - k) * ((n + 1).choose k : ℝ) := by
  rcases le_or_gt k (n + 1) with h | h
  · have h1 : ((n.choose k * (n + 1) : ℕ) : ℝ) = (((n + 1).choose k * (n + 1 - k) : ℕ) : ℝ) := by
      rw [Nat.choose_mul_succ_eq]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h] at h1
    push_cast at h1
    linarith
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- The telescoping identity for the terms. -/
lemma term_identity (m k : ℕ) :
    t (m + 2) k - (2 * (m : ℝ) + 5) * t (m + 1) k + ((m : ℝ) + 1) * ((m : ℝ) + 2) * t m k
      = g m (k + 1) - g m k := by
  have e1 := choose_mul_succ_cast (m + 2) k
  have e2 := choose_mul_succ_cast (m + 1) k
  have e3 := choose_mul_succ_cast m k
  have e4 := choose_succ_right_cast (m + 3) k
  have e5 := choose_succ_right_cast (m + 2) k
  push_cast at e1 e2 e3 e4 e5
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  have hm3 : ((m : ℝ) + 3) ≠ 0 := by positivity
  set x : ℝ := ((m + 3).choose k : ℝ) with hx
  have f1 : ((m + 2).choose k : ℝ) = ((m : ℝ) + 3 - k) * x / ((m : ℝ) + 3) := by
    rw [eq_div_iff hm3]; linarith
  have f2 : ((m + 1).choose k : ℝ)
      = ((m : ℝ) + 2 - k) * (((m : ℝ) + 3 - k) * x / ((m : ℝ) + 3)) / ((m : ℝ) + 2) := by
    rw [eq_div_iff hm2, ← f1]; linarith
  have f3 : (m.choose k : ℝ)
      = ((m : ℝ) + 1 - k) * (((m : ℝ) + 2 - k) * (((m : ℝ) + 3 - k) * x / ((m : ℝ) + 3))
        / ((m : ℝ) + 2)) / ((m : ℝ) + 1) := by
    rw [eq_div_iff hm1, ← f2]; linarith
  have f4 : ((m + 3).choose (k + 1) : ℝ) = ((m : ℝ) + 3 - k) * x / ((k : ℝ) + 1) := by
    rw [eq_div_iff hk]; linarith
  have f5 : ((m + 2).choose (k + 1) : ℝ)
      = ((m : ℝ) + 2 - k) * (((m : ℝ) + 3 - k) * x / ((m : ℝ) + 3)) / ((k : ℝ) + 1) := by
    rw [eq_div_iff hk, ← f1]; linarith
  have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  simp only [g, t]
  rw [show m + 2 + 1 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl, hfac, f4, f5, f3, f2, f1]
  push_cast
  field_simp
  ring

lemma t_eq_zero {m k : ℕ} (h : m < k) : t m k = 0 := by
  simp [t, Nat.choose_eq_zero_of_lt h]

/-- The defining sum, with the range extended. -/
lemma A000262_succ_eq (m N : ℕ) (hN : m + 1 ≤ N) :
    (A000262 (m + 1) : ℝ) = ∑ k ∈ Finset.range N, t m k := by
  have hsub : Finset.range (m + 1) ⊆ Finset.range N := Finset.range_subset_range.mpr hN
  rw [← Finset.sum_subset hsub]
  · simp [A000262, t]
  · intro k _ hk
    exact t_eq_zero (by simpa using hk)

/-- The recurrence of A000262. -/
lemma A000262_rec (m : ℕ) :
    (A000262 (m + 3) : ℝ) = (2 * (m : ℝ) + 5) * (A000262 (m + 2) : ℝ)
      - ((m : ℝ) + 2) * ((m : ℝ) + 1) * (A000262 (m + 1) : ℝ) := by
  have h := Finset.sum_range_sub (g m) (m + 3)
  have h0 : g m 0 = 0 := by simp [g]
  have h1 : g m (m + 3) = 0 := by
    simp [g, t_eq_zero (show m + 2 < m + 3 by omega)]
  rw [h0, h1, sub_zero] at h
  have hs : ∑ k ∈ Finset.range (m + 3), (t (m + 2) k - (2 * (m : ℝ) + 5) * t (m + 1) k
      + ((m : ℝ) + 1) * ((m : ℝ) + 2) * t m k) = 0 := by
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => term_identity m k
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← A000262_succ_eq (m + 2) (m + 3) le_rfl, ← A000262_succ_eq (m + 1) (m + 3) (by omega),
    ← A000262_succ_eq m (m + 3) (by omega)] at hs
  linarith

/-- For `x ≥ 0`, `0 ≤ x / (1 + x) ≤ 1`. -/
lemma ratio_mem {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x / (1 + x) ∧ x / (1 + x) ≤ 1 := by
  have h : (0 : ℝ) < 1 + x := by linarith
  exact ⟨div_nonneg hx h.le, (div_le_one h).mpr (by linarith)⟩

/-- The integrand is integrable on `(0, ∞)`. -/
lemma integrableOn_pow (n : ℕ) :
    IntegrableOn (fun x : ℝ => (x / (1 + x)) ^ n * Real.exp (-x)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg_Ioi 0)
    (by fun_prop : Measurable _).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
  obtain ⟨h0, h1⟩ := ratio_mem hx0
  rw [Real.norm_of_nonneg (by positivity)]
  have h2 : (x / (1 + x)) ^ n ≤ 1 := pow_le_one₀ h0 h1
  nlinarith [Real.exp_pos (-x)]

/-- The integrand of `G` is integrable on `(0, ∞)`. -/
lemma integrableOn_G : IntegrableOn (fun x : ℝ => Real.exp (-x) / (1 + x)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg_Ioi 0)
    (by fun_prop : Measurable _).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
  nlinarith [Real.exp_pos (-x)]

/-- The reduction formula `(n+1) I(n+2) = (2 n + 3) I(n+1) - (n+1) I(n)`. -/
lemma integral_rec (n : ℕ) :
    ((n : ℝ) + 1) * ∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ (n + 2) * Real.exp (-x)
      = (2 * (n : ℝ) + 3) * (∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ (n + 1) * Real.exp (-x))
        - ((n : ℝ) + 1) * ∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ n * Real.exp (-x) := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun x : ℝ => (x / (1 + x)) ^ (n + 1) * Real.exp (-x))
      (((n : ℝ) + 1) * ((x / (1 + x)) ^ n * Real.exp (-x))
        - (2 * (n : ℝ) + 3) * ((x / (1 + x)) ^ (n + 1) * Real.exp (-x))
        + ((n : ℝ) + 1) * ((x / (1 + x)) ^ (n + 2) * Real.exp (-x))) x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    have hne : (1 + x) ≠ 0 := by linarith
    have hd : HasDerivAt (fun x : ℝ => x / (1 + x)) ((1 * (1 + x) - x * 1) / (1 + x) ^ 2) x :=
      (hasDerivAt_id' x).fun_div ((hasDerivAt_id' x).const_add 1) hne
    have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * (-1)) x :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have hu : (1 * (1 + x) - x * 1) / (1 + x) ^ 2 = (1 - x / (1 + x)) ^ 2 := by
      field_simp
      ring
    refine ((hd.fun_pow (n + 1)).fun_mul he).congr_deriv ?_
    rw [hu, Nat.add_sub_cancel]
    push_cast
    ring
  have i0 : IntegrableOn (fun x : ℝ => ((n : ℝ) + 1) * ((x / (1 + x)) ^ n * Real.exp (-x)))
      (Ioi 0) := (integrableOn_pow n).const_mul _
  have i1 : IntegrableOn (fun x : ℝ => (2 * (n : ℝ) + 3)
      * ((x / (1 + x)) ^ (n + 1) * Real.exp (-x))) (Ioi 0) := (integrableOn_pow (n + 1)).const_mul _
  have i2 : IntegrableOn (fun x : ℝ => ((n : ℝ) + 1)
      * ((x / (1 + x)) ^ (n + 2) * Real.exp (-x))) (Ioi 0) := (integrableOn_pow (n + 2)).const_mul _
  have i01 : IntegrableOn (fun x : ℝ => ((n : ℝ) + 1) * ((x / (1 + x)) ^ n * Real.exp (-x))
      - (2 * (n : ℝ) + 3) * ((x / (1 + x)) ^ (n + 1) * Real.exp (-x))) (Ioi 0) := i0.sub i1
  have hint : IntegrableOn (fun x : ℝ => ((n : ℝ) + 1) * ((x / (1 + x)) ^ n * Real.exp (-x))
        - (2 * (n : ℝ) + 3) * ((x / (1 + x)) ^ (n + 1) * Real.exp (-x))
        + ((n : ℝ) + 1) * ((x / (1 + x)) ^ (n + 2) * Real.exp (-x))) (Ioi 0) := i01.add i2
  have hlim : Tendsto (fun x : ℝ => (x / (1 + x)) ^ (n + 1) * Real.exp (-x)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (Real.tendsto_exp_neg_atTop_nhds_zero) ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      obtain ⟨h0, -⟩ := ratio_mem hx
      positivity
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      obtain ⟨h0, h1⟩ := ratio_mem hx
      have h2 : (x / (1 + x)) ^ (n + 1) ≤ 1 := pow_le_one₀ h0 h1
      nlinarith [Real.exp_pos (-x)]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  have hsplit : ∫ x in Ioi (0 : ℝ), (((n : ℝ) + 1) * ((x / (1 + x)) ^ n * Real.exp (-x))
        - (2 * (n : ℝ) + 3) * ((x / (1 + x)) ^ (n + 1) * Real.exp (-x))
        + ((n : ℝ) + 1) * ((x / (1 + x)) ^ (n + 2) * Real.exp (-x)))
      = ((n : ℝ) + 1) * (∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ n * Real.exp (-x))
        - (2 * (n : ℝ) + 3) * (∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ (n + 1) * Real.exp (-x))
        + ((n : ℝ) + 1) * ∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ (n + 2) * Real.exp (-x) := by
    rw [integral_add i01 i2, integral_sub i0 i1, integral_const_mul, integral_const_mul,
      integral_const_mul]
  rw [hsplit] at h
  simp only [zero_div, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, zero_mul, sub_zero] at h
  linarith

/-- `I(0) = 1`. -/
lemma integral_zero : ∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ 0 * Real.exp (-x) = 1 := by
  simp only [pow_zero, one_mul]
  exact integral_exp_neg_Ioi_zero

/-- `I(1) = 1 - G`. -/
lemma integral_one : ∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ 1 * Real.exp (-x) = 1 - G := by
  have h : ∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ 1 * Real.exp (-x)
      = ∫ x in Ioi (0 : ℝ), (Real.exp (-x) - Real.exp (-x) / (1 + x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hne : (1 + x) ≠ 0 := by linarith
    simp only [pow_one]
    field_simp
    ring
  rw [h, integral_sub (integrableOn_exp_neg_Ioi 0) integrableOn_G, integral_exp_neg_Ioi_zero]
  rfl

/-- The closed form, for two consecutive indices. -/
lemma integral_eq (n : ℕ) :
    ((n.factorial : ℝ) * ∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ (n + 1) * Real.exp (-x)
        = (a (n + 1) : ℝ) - (A000262 (n + 1) : ℝ) * G) ∧
      (((n + 1).factorial : ℝ) * ∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ (n + 2) * Real.exp (-x)
        = (a (n + 2) : ℝ) - (A000262 (n + 2) : ℝ) * G) := by
  induction n with
  | zero =>
    have h := integral_rec 0
    rw [integral_zero, integral_one] at h
    refine ⟨?_, ?_⟩
    · rw [integral_one]
      simp [a, A000262]
    · simp only [zero_add, Nat.factorial_one, Nat.cast_one, one_mul]
      simp only [Nat.cast_zero, zero_add, one_mul, mul_zero] at h
      rw [h]
      simp [a, A000262, Finset.sum_range_succ]
      ring
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have h := integral_rec (n + 1)
    have hb := A000262_rec n
    have ha : (a (n + 3) : ℝ) = (2 * ((n : ℝ) + 3) - 1) * (a (n + 2) : ℝ)
        - (((n : ℝ) + 3) - 1) * (((n : ℝ) + 3) - 2) * (a (n + 1) : ℝ) := by
      rw [a]
      push_cast
      ring
    have hf2 : ((n + 1 + 1).factorial : ℝ) = ((n : ℝ) + 2) * ((n + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hf1 : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [show n + 1 + 2 = n + 3 from rfl, hf2, ha, hb]
    rw [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at h
    push_cast at h
    rw [hf1] at h2 ⊢
    linear_combination ((n : ℝ) + 1) * (n.factorial : ℝ) * h + (2 * (n : ℝ) + 5) * h2
      - ((n : ℝ) + 2) * ((n : ℝ) + 1) * h1

end OMA.A321942Proof

open OMA.S_oeis_a321942 OMA.A321942Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a321942.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := (integral_eq m).1
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  rw [Nat.add_sub_cancel, ← h]
  field_simp
