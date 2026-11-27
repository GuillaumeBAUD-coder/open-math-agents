import OMAReductions.R_Erdos1129_erdos_1129_variants_erdos_lower_bound_R1

-- Step Erdos1129.erdos_1129.variants.erdos_lower_bound.R1.H2: hypothesis H2 of reduction Erdos1129.erdos_1129.variants.erdos_lower_bound.R1
-- Credit: @koolkao
-- H2 := ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →     IsCanonical (fun k : Fin n => -Real.cos ((2 * k + 1) * π / (2 * n)) / Real.cos (π / (2 * n))) ∧     ∀ j ∈ Finset.Icc 1 (n - 1), 2 / π * Real.log n - C <       gapMax (fun k : Fin n => -Real.cos ((2 * k + 1) * π / (2 * n)) / Real.cos (π / (2 * n))) j

-- Proof: the nodes are -cos(t_k)/cos(pi/(2n)) with t_k = (2k+1) pi/(2n); they increase from -1 to 1.
-- By affine invariance, at the point -cos(j pi/n)/cos(pi/(2n)) of the j-th gap the Lebesgue function
-- equals that of the zeros cos t_k of T_n at the extremum cos(j pi/n), which is
-- (1/n) sum_k sin t_k / |cos(j pi/n) - cos t_k| (Brutman 1978; Rivlin, The Chebyshev Polynomials).
-- Each term is a sum of two half-angle cotangents; bounding cot x below by 1/x - 2 and above by 1/x
-- and summing odd harmonic series gives (2/pi) log n - 3 for j <= n/2, and j -> n - j is a symmetry.

namespace OMA.E1129H2

open Erdos1129 Finset Real Polynomial

lemma cot_lb {x : ℝ} (h0 : 0 < x) (h1 : x ≤ π / 2) : 1 / x - 1 ≤ cos x / sin x := by
  have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
  have hsx : sin x ≤ x := sin_le h0.le
  have hc := one_sub_sq_div_two_le_cos (x := x)
  have hpi : π < 4 := pi_lt_four
  rw [le_div_iff₀ hs]
  have e : (1 / x - 1) * sin x = sin x / x - sin x := by ring
  rw [e]
  have h2 : sin x / x ≤ 1 := (div_le_one h0).mpr hsx
  have h3 : 1 - x ^ 2 / 2 ≥ 1 - x := by nlinarith
  have h4 : 1 - x ≤ cos x := by linarith
  have h5 : sin x / x - sin x ≤ 1 - sin x := by linarith
  by_cases hx1 : x ≤ 1
  · have h6 : sin x / x - sin x = sin x * (1 - x) / x := by field_simp
    rw [h6]
    have h7 : sin x * (1 - x) / x ≤ 1 - x := by
      rw [div_le_iff₀ h0]; nlinarith
    linarith
  · rw [not_le] at hx1
    have h8 : sin x / x - sin x ≤ 0 := by
      have : sin x / x ≤ sin x := by
        rw [div_le_iff₀ h0]; nlinarith
      linarith
    have h9 : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith, h1⟩
    linarith

lemma cot_ub {x : ℝ} (h0 : 0 < x) (h1 : x < π / 2) : cos x / sin x ≤ 1 / x := by
  have ht := lt_tan h0 h1
  have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
  have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  rw [tan_eq_sin_div_cos] at ht
  rw [div_le_div_iff₀ hs h0]
  rw [lt_div_iff₀ hc] at ht
  linarith

lemma cot_lb2 {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 3 * π / 4) : 1 / x - 2 ≤ cos x / sin x := by
  by_cases hx : x ≤ π / 2
  · have := cot_lb h0 hx; linarith
  · rw [not_le] at hx
    have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
    -- w = x - pi/2 in (0, pi/4]; cos x = - sin w, sin x = cos w, tan w <= 1
    set w := x - π / 2 with hw
    have hw0 : 0 < w := by linarith
    have hw1 : w ≤ π / 4 := by linarith
    have hcw : 0 < cos w := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have htw : tan w ≤ 1 := by
      rw [← tan_pi_div_four]
      exact strictMonoOn_tan.monotoneOn ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
        ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ hw1
    rw [tan_eq_sin_div_cos, div_le_one hcw] at htw
    have ex : x = w + π / 2 := by rw [hw]; ring
    have hcx : cos x = -sin w := by rw [ex, cos_add_pi_div_two]
    have hsx : sin x = cos w := by rw [ex, sin_add_pi_div_two]
    have h2 : -1 ≤ cos x / sin x := by
      rw [le_div_iff₀ hs, hcx, hsx]; linarith
    have h3 : 1 / x ≤ 1 := by
      rw [div_le_one h0]; linarith [pi_gt_three]
    linarith

lemma harm_lb (a N : ℕ) :
    (Real.log (2 * ((a + N : ℕ) : ℝ) + 1) - Real.log (2 * (a : ℝ) + 1)) / 2 ≤
      ∑ m ∈ range N, (1 : ℝ) / (2 * ((a + m : ℕ) : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hpos : (0 : ℝ) < 2 * ((a + N : ℕ) : ℝ) + 1 := by positivity
    have key : Real.log (2 * ((a + (N + 1) : ℕ) : ℝ) + 1) - Real.log (2 * ((a + N : ℕ) : ℝ) + 1)
        ≤ 2 / (2 * ((a + N : ℕ) : ℝ) + 1) := by
      rw [← Real.log_div (by positivity) hpos.ne']
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
      field_simp
      push_cast
      ring
    have : (1 : ℝ) / (2 * ((a + N : ℕ) : ℝ) + 1) = (2 / (2 * ((a + N : ℕ) : ℝ) + 1)) / 2 := by
      ring
    rw [this]
    linarith


lemma ratio_right {u v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ π / 2) (hu0 : 0 < u) (hu1 : u ≤ 3 * π / 4) :
    (1 / v - 1 + (1 / u - 2)) / 2 ≤ sin (u + v) / |cos (u - v) - cos (u + v)| := by
  have hsu : 0 < sin u := sin_pos_of_pos_of_lt_pi hu0 (by linarith [pi_pos])
  have hsv : 0 < sin v := sin_pos_of_pos_of_lt_pi hv0 (by linarith [pi_pos])
  have e1 : cos (u - v) - cos (u + v) = 2 * sin u * sin v := by
    rw [cos_sub_cos]
    have : (u - v + (u + v)) / 2 = u := by ring
    have h2 : (u - v - (u + v)) / 2 = -v := by ring
    rw [this, h2, sin_neg]; ring
  rw [e1, abs_of_pos (by positivity), sin_add]
  have e2 : (sin u * cos v + cos u * sin v) / (2 * sin u * sin v) =
      (cos v / sin v + cos u / sin u) / 2 := by
    field_simp
  rw [e2]
  have := cot_lb hv0 hv1
  have := cot_lb2 hu0 hu1
  linarith

lemma ratio_left {u v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ π / 2) (hu0 : 0 < u) (hu1 : u < π / 2) :
    (1 / v - 1 - 1 / u) / 2 ≤ sin (u - v) / |cos (u + v) - cos (u - v)| := by
  have hsu : 0 < sin u := sin_pos_of_pos_of_lt_pi hu0 (by linarith [pi_pos])
  have hsv : 0 < sin v := sin_pos_of_pos_of_lt_pi hv0 (by linarith [pi_pos])
  have e1 : cos (u + v) - cos (u - v) = -(2 * sin u * sin v) := by
    rw [cos_sub_cos]
    have : (u + v + (u - v)) / 2 = u := by ring
    have h2 : (u + v - (u - v)) / 2 = v := by ring
    rw [this, h2]; ring
  rw [e1, abs_neg, abs_of_pos (by positivity), sin_sub]
  have e2 : (sin u * cos v - cos u * sin v) / (2 * sin u * sin v) =
      (cos v / sin v - cos u / sin u) / 2 := by
    field_simp
  rw [e2]
  have := cot_lb hv0 hv1
  have := cot_ub hu0 hu1
  linarith


noncomputable def th (n k : ℕ) : ℝ := (2 * k + 1) * π / (2 * n)

noncomputable def F (n j : ℕ) : ℝ :=
  ∑ k ∈ range n, sin (th n k) / (n * |cos (j * π / n) - cos (th n k)|)

lemma term_right {n j k : ℕ} (hjk : j ≤ k) (hkn : k < n) (hj : 2 * j ≤ n) :
    2 / (π * (2 * ((k : ℝ) - j) + 1)) + 2 / (π * (2 * ((k : ℝ) + j) + 1)) - 3 / (2 * n) ≤
      sin (th n k) / (n * |cos (j * π / n) - cos (th n k)|) := by
  have hpi := pi_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hkn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
  have hj' : 2 * (j : ℝ) ≤ n := by exact_mod_cast hj
  set u := (2 * ((k : ℝ) + j) + 1) * π / (4 * n) with hu
  set v := (2 * ((k : ℝ) - j) + 1) * π / (4 * n) with hv
  have hth : th n k = u + v := by rw [th, hu, hv]; field_simp; ring
  have hphi : (j : ℝ) * π / n = u - v := by rw [hu, hv]; field_simp; ring
  have hv0 : 0 < v := by rw [hv]; apply div_pos _ (by positivity); nlinarith
  have hv1 : v ≤ π / 2 := by
    rw [hv, div_le_iff₀ (by positivity)]; nlinarith
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u ≤ 3 * π / 4 := by
    rw [hu, div_le_iff₀ (by positivity)]; nlinarith
  have hr := ratio_right hv0 hv1 hu0 hu1
  rw [hth, hphi]
  have e : sin (u + v) / (n * |cos (u - v) - cos (u + v)|) =
      (sin (u + v) / |cos (u - v) - cos (u + v)|) / n := by
    rw [div_div, mul_comm]
  rw [e]
  have e2 : 2 / (π * (2 * ((k : ℝ) - j) + 1)) + 2 / (π * (2 * ((k : ℝ) + j) + 1)) - 3 / (2 * n) =
      ((1 / v - 1 + (1 / u - 2)) / 2) / n := by
    have h1 : (0 : ℝ) < 2 * ((k : ℝ) - j) + 1 := by linarith
    have h2 : (0 : ℝ) < 2 * ((k : ℝ) + j) + 1 := by positivity
    rw [hu, hv]
    field_simp
    ring
  rw [e2]
  exact div_le_div_of_nonneg_right hr hn.le

lemma term_left {n j k : ℕ} (hkj : k < j) (hj : 2 * j ≤ n) :
    2 / (π * (2 * ((j : ℝ) - k) - 1)) - 1 / (2 * n) - 2 / (π * (2 * (j : ℝ) + 1)) ≤
      sin (th n k) / (n * |cos (j * π / n) - cos (th n k)|) := by
  have hpi := pi_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkj' : (k : ℝ) + 1 ≤ j := by exact_mod_cast hkj
  have hj' : 2 * (j : ℝ) ≤ n := by exact_mod_cast hj
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set u := (2 * ((k : ℝ) + j) + 1) * π / (4 * n) with hu
  set v := (2 * ((j : ℝ) - k) - 1) * π / (4 * n) with hv
  have hth : th n k = u - v := by rw [th, hu, hv]; field_simp; ring
  have hphi : (j : ℝ) * π / n = u + v := by rw [hu, hv]; field_simp; ring
  have hv0 : 0 < v := by rw [hv]; apply div_pos _ (by positivity); nlinarith
  have hv1 : v ≤ π / 2 := by
    rw [hv, div_le_iff₀ (by positivity)]; nlinarith
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < π / 2 := by
    rw [hu, div_lt_iff₀ (by positivity)]; nlinarith
  have hr := ratio_left hv0 hv1 hu0 hu1
  rw [hth, hphi]
  have e : sin (u - v) / (n * |cos (u + v) - cos (u - v)|) =
      (sin (u - v) / |cos (u + v) - cos (u - v)|) / n := by
    rw [div_div, mul_comm]
  rw [e]
  have h1 : (0 : ℝ) < 2 * ((j : ℝ) - k) - 1 := by linarith
  have e2 : 2 / (π * (2 * ((j : ℝ) - k) - 1)) - 1 / (2 * n) - 2 / (π * (2 * ((k : ℝ) + j) + 1)) =
      ((1 / v - 1 - 1 / u) / 2) / n := by
    have h2 : (0 : ℝ) < 2 * ((k : ℝ) + j) + 1 := by positivity
    rw [hu, hv]
    field_simp
    ring
  have h3 : 2 / (π * (2 * ((k : ℝ) + j) + 1)) ≤ 2 / (π * (2 * (j : ℝ) + 1)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have := div_le_div_of_nonneg_right hr hn.le
  rw [← e2] at this
  linarith


lemma F_bound {n j : ℕ} (hj1 : 1 ≤ j) (hj : 2 * j ≤ n) : 2 / π * Real.log n - 3 < F n j := by
  have hpi := pi_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hjn : j ≤ n := by omega
  unfold F
  rw [← sum_range_add_sum_Ico _ hjn]
  -- left part
  have hL : ∑ k ∈ range j, (2 / (π * (2 * ((j : ℝ) - k) - 1)) - 1 / (2 * n) -
      2 / (π * (2 * (j : ℝ) + 1))) ≤
      ∑ k ∈ range j, sin (th n k) / (n * |cos (j * π / n) - cos (th n k)|) :=
    sum_le_sum fun k hk => term_left (mem_range.mp hk) hj
  have hR : ∑ k ∈ Ico j n, (2 / (π * (2 * ((k : ℝ) - j) + 1)) +
      2 / (π * (2 * ((k : ℝ) + j) + 1)) - 3 / (2 * n)) ≤
      ∑ k ∈ Ico j n, sin (th n k) / (n * |cos (j * π / n) - cos (th n k)|) :=
    sum_le_sum fun k hk => term_right (mem_Ico.mp hk).1 (mem_Ico.mp hk).2 hj
  -- evaluate the left lower sum
  have hL1 : ∑ k ∈ range j, (2 / (π * (2 * ((j : ℝ) - k) - 1)) - 1 / (2 * n) -
      2 / (π * (2 * (j : ℝ) + 1))) =
      2 / π * ∑ m ∈ range j, (1 : ℝ) / (2 * ((0 + m : ℕ) : ℝ) + 1) -
        j * (1 / (2 * n) + 2 / (π * (2 * (j : ℝ) + 1))) := by
    rw [sum_sub_distrib, sum_sub_distrib, sum_const, sum_const, card_range, mul_sum,
      ← sum_range_reflect]
    have : ∀ m ∈ range j, 2 / (π * (2 * ((j : ℝ) - ((j - 1 - m : ℕ) : ℝ)) - 1)) =
        2 / π * (1 / (2 * ((0 + m : ℕ) : ℝ) + 1)) := by
      intro m hm
      have hm' := mem_range.mp hm
      have e : ((j - 1 - m : ℕ) : ℝ) = (j : ℝ) - 1 - m := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
      rw [e, show (2 : ℝ) * ((j : ℝ) - ((j : ℝ) - 1 - m)) - 1 = 2 * ((0 + m : ℕ) : ℝ) + 1 by
        push_cast; ring, mul_one_div, div_div]
    rw [sum_congr rfl this]
    simp only [nsmul_eq_mul]
    ring
  have hR1 : ∑ k ∈ Ico j n, (2 / (π * (2 * ((k : ℝ) - j) + 1)) +
      2 / (π * (2 * ((k : ℝ) + j) + 1)) - 3 / (2 * n)) =
      2 / π * ∑ m ∈ range (n - j), (1 : ℝ) / (2 * ((0 + m : ℕ) : ℝ) + 1) +
      2 / π * ∑ m ∈ range (n - j), (1 : ℝ) / (2 * ((2 * j + m : ℕ) : ℝ) + 1) -
        ((n - j : ℕ) : ℝ) * (3 / (2 * n)) := by
    rw [sum_Ico_eq_sum_range, sum_sub_distrib, sum_add_distrib, sum_const, card_range, mul_sum,
      mul_sum]
    simp only [nsmul_eq_mul]
    congr 2
    · refine sum_congr rfl fun m _ => ?_
      rw [show (2 : ℝ) * (((j + m : ℕ) : ℝ) - j) + 1 = 2 * ((0 + m : ℕ) : ℝ) + 1 by
        push_cast; ring, mul_one_div, div_div]
    · refine sum_congr rfl fun m _ => ?_
      rw [show (2 : ℝ) * (((j + m : ℕ) : ℝ) + j) + 1 = 2 * ((2 * j + m : ℕ) : ℝ) + 1 by
        push_cast; ring, mul_one_div, div_div]
  have hA := harm_lb 0 j
  have hB := harm_lb 0 (n - j)
  have hC := harm_lb (2 * j) (n - j)
  simp only [Nat.cast_zero, mul_zero, zero_add, Real.log_one, sub_zero] at hA hB hC
  have e1 : ((2 * j + (n - j) : ℕ) : ℝ) = n + j := by
    rw [show 2 * j + (n - j) = n + j by omega]; push_cast; ring
  rw [e1] at hC
  have e2 : ((n - j : ℕ) : ℝ) = n - j := by rw [Nat.cast_sub hjn]
  rw [e2] at hB
  rw [e2] at hR1
  simp only [zero_add] at hL1 hR1
  -- log comparisons
  have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hj' : 2 * (j : ℝ) ≤ n := by exact_mod_cast hj
  have l1 : Real.log n ≤ Real.log (2 * ((n : ℝ) - j) + 1) :=
    Real.log_le_log hn (by linarith)
  have l2 : Real.log n ≤ Real.log (2 * ((n : ℝ) + j) + 1) :=
    Real.log_le_log hn (by linarith)
  have l3 : Real.log (2 * ((2 * j : ℕ) : ℝ) + 1) ≤ Real.log 2 + Real.log (2 * (j : ℝ) + 1) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast; linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have c1 : (j : ℝ) * (1 / (2 * n) + 2 / (π * (2 * (j : ℝ) + 1))) ≤ 1 / 4 + 1 / π := by
    rw [mul_add]
    have : (j : ℝ) * (1 / (2 * n)) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
    have : (j : ℝ) * (2 / (π * (2 * (j : ℝ) + 1))) ≤ 1 / π := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hpi]; nlinarith
    linarith
  have c2 : ((n : ℝ) - j) * (3 / (2 * n)) ≤ 3 / 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hpi3 : 3 < π := pi_gt_three
  have c3 : 1 / π < 1 / 3 := by
    rw [div_lt_div_iff₀ hpi (by norm_num)]; linarith
  have c4 : Real.log 2 / π < 1 / 3 := by
    rw [div_lt_div_iff₀ hpi (by norm_num)]; nlinarith [Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]
  have key : 2 / π * Real.log n - 2 * (Real.log 2 / π) ≤
      2 / π * ∑ m ∈ range j, (1 : ℝ) / (2 * (m : ℝ) + 1) +
      2 / π * ∑ m ∈ range (n - j), (1 : ℝ) / (2 * (m : ℝ) + 1) +
      2 / π * ∑ m ∈ range (n - j), (1 : ℝ) / (2 * ((2 * j + m : ℕ) : ℝ) + 1) := by
    have hp : 0 < 2 / π := by positivity
    have s1 := mul_le_mul_of_nonneg_left hA hp.le
    have s2 := mul_le_mul_of_nonneg_left hB hp.le
    have s3 := mul_le_mul_of_nonneg_left hC hp.le
    have : 2 / π * Real.log n - 2 * (Real.log 2 / π) ≤
        2 / π * (Real.log (2 * (j : ℝ) + 1) / 2) +
        2 / π * (Real.log (2 * ((n : ℝ) - j) + 1) / 2) +
        2 / π * ((Real.log (2 * ((n : ℝ) + j) + 1) -
          Real.log (2 * ((2 * j : ℕ) : ℝ) + 1)) / 2) := by
      have : 2 / π * Real.log n ≤ 2 / π * ((Real.log (2 * ((n : ℝ) - j) + 1) +
          Real.log (2 * ((n : ℝ) + j) + 1)) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hp.le
      have e : 2 * (Real.log 2 / π) = 2 / π * Real.log 2 := by ring
      have : 2 / π * Real.log (2 * ((2 * j : ℕ) : ℝ) + 1) ≤
          2 / π * (Real.log 2 + Real.log (2 * (j : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left l3 hp.le
      have : 0 ≤ Real.log 2 / π := div_nonneg (Real.log_nonneg (by norm_num)) hpi.le
      linarith
    linarith
  linarith


lemma T_eq_nodal {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (hT : ∀ j, (Chebyshev.T ℝ (n : ℤ)).eval (x j) = 0) :
    Chebyshev.T ℝ (n : ℤ) =
      Polynomial.C (Chebyshev.T ℝ (n : ℤ)).leadingCoeff * Lagrange.nodal univ x := by
  have hdeg : (Chebyshev.T ℝ (n : ℤ)).degree = n := by
    rw [Chebyshev.degree_T ℝ]; simp
  have hne : Chebyshev.T ℝ (n : ℤ) ≠ 0 := by
    intro h; rw [h, degree_zero] at hdeg; exact WithBot.bot_ne_coe hdeg
  have hlc : (Chebyshev.T ℝ (n : ℤ)).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (univ.image x)
  · rw [card_image_of_injective _ hx, card_univ, Fintype.card_fin]
    calc _ < (Chebyshev.T ℝ (n : ℤ)).degree := by
          apply Polynomial.degree_sub_lt_left
          · rw [Polynomial.degree_C_mul hlc, Lagrange.degree_nodal, hdeg, card_univ,
              Fintype.card_fin]
          · exact hne
          · rw [leadingCoeff_mul, leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff, mul_one]
      _ = n := hdeg
  · intro z hz
    obtain ⟨j, -, rfl⟩ := mem_image.mp hz
    rw [hT j, eval_mul, eval_C, Lagrange.eval_nodal_at_node (mem_univ j), mul_zero]

lemma basis_formula {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (hT : ∀ j, (Chebyshev.T ℝ (n : ℤ)).eval (x j) = 0) (y : ℝ) (hy : ∀ j, y ≠ x j)
    (k : Fin n) :
    (Lagrange.basis univ x k).eval y =
      (Chebyshev.T ℝ (n : ℤ)).eval y /
        ((y - x k) * (derivative (Chebyshev.T ℝ (n : ℤ))).eval (x k)) := by
  have hfac := T_eq_nodal x hx hT
  have hne : Chebyshev.T ℝ (n : ℤ) ≠ 0 := by
    intro h; have := hT; rw [h] at hfac
    have hdeg : (Chebyshev.T ℝ (n : ℤ)).degree = n := by
      rw [Chebyshev.degree_T ℝ]; simp
    rw [h, degree_zero] at hdeg; exact WithBot.bot_ne_coe hdeg
  have ha : (Chebyshev.T ℝ (n : ℤ)).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  set a := (Chebyshev.T ℝ (n : ℤ)).leadingCoeff with ha_def
  rw [hfac, derivative_mul, derivative_C, zero_mul, zero_add]
  simp only [eval_mul, eval_C]
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ k), Lagrange.eval_nodal,
    Lagrange.eval_nodal, ← mul_prod_erase univ (fun i => y - x i) (mem_univ k)]
  rw [Lagrange.basis, eval_prod]
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  rw [prod_mul_distrib, prod_inv_distrib]
  have hy' : y - x k ≠ 0 := sub_ne_zero.mpr (hy k)
  have hp : ∏ i ∈ univ.erase k, (x k - x i) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun i hi => sub_ne_zero.mpr (fun h => (ne_of_mem_erase hi) (hx h).symm))
  field_simp

lemma deriv_T_cos (n : ℕ) (φ : ℝ) :
    (derivative (Chebyshev.T ℝ (n : ℤ))).eval (cos φ) * sin φ = n * sin (n * φ) := by
  have h1 : HasDerivAt (fun φ => (Chebyshev.T ℝ (n : ℤ)).eval (cos φ))
      ((derivative (Chebyshev.T ℝ (n : ℤ))).eval (cos φ) * (-sin φ)) φ :=
    ((Chebyshev.T ℝ (n : ℤ)).hasDerivAt (cos φ)).comp φ (hasDerivAt_cos φ)
  have h2 : HasDerivAt (fun φ => cos ((n : ℝ) * φ)) (-sin ((n : ℝ) * φ) * ((n : ℝ) * 1)) φ :=
    ((hasDerivAt_id' φ).const_mul (n : ℝ)).cos
  have e : (fun φ => (Chebyshev.T ℝ (n : ℤ)).eval (cos φ)) = fun φ => cos ((n : ℝ) * φ) := by
    funext φ; rw [Chebyshev.T_real_cos]; push_cast; rfl
  rw [e] at h1
  have := h1.unique h2
  linarith


lemma F_symm {n j : ℕ} (hj : j ≤ n) : F n (n - j) = F n j := by
  have hpi := pi_pos
  unfold F
  rw [← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have e1 : th n (n - 1 - k) = π - th n k := by
    unfold th
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    field_simp
    ring
  have e2 : ((n - j : ℕ) : ℝ) * π / n = π - j * π / n := by
    rw [Nat.cast_sub hj]
    field_simp
  rw [e1, e2, sin_pi_sub, cos_pi_sub, cos_pi_sub]
  congr 2
  rw [show -cos (↑j * π / ↑n) - -cos (th n k) = -(cos (↑j * π / ↑n) - cos (th n k)) by ring,
    abs_neg]

lemma th_pos (n k : ℕ) (hn : 0 < n) : 0 < th n k := by
  unfold th
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

lemma th_lt_pi {n k : ℕ} (hk : k < n) : th n k < π := by
  unfold th
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have : (0 : ℝ) < n := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pi_pos]

/-- The Lebesgue function of the zeros cos(th n k) of T_n at the extremum cos(j pi/n). -/
lemma L_cheb_eq {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) :
    lebesgueFunction (fun k : Fin n => cos (th n k)) (cos (j * π / n)) = F n j := by
  have hpi := pi_pos
  have hn0 : 0 < n := by omega
  have hn : (0 : ℝ) < n := by exact_mod_cast hn0
  set c : Fin n → ℝ := fun k => cos (th n k) with hc
  have hmem : ∀ k : ℕ, k < n → th n k ∈ Set.Icc 0 π := fun k hk =>
    ⟨(th_pos n k hn0).le, (th_lt_pi hk).le⟩
  have hφmem : (j : ℝ) * π / n ∈ Set.Icc 0 π := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hn]
    have : (j : ℝ) ≤ n := by exact_mod_cast hjn.le
    nlinarith
  have hinj : Function.Injective c := by
    intro a b h
    have := injOn_cos (hmem a a.2) (hmem b b.2) h
    unfold th at this
    have h2 : (a : ℝ) = b := by
      field_simp at this
      linarith
    exact Fin.ext (by exact_mod_cast h2)
  have hT : ∀ k, (Chebyshev.T ℝ (n : ℤ)).eval (c k) = 0 := by
    intro k
    simp only [hc]
    rw [Chebyshev.T_real_cos]
    apply cos_eq_zero_iff.mpr
    refine ⟨k, ?_⟩
    unfold th
    push_cast
    field_simp
  have hne : ∀ k, cos (j * π / n) ≠ c k := by
    intro k h
    have := injOn_cos hφmem (hmem k k.2) h
    unfold th at this
    have h2 : (2 * j : ℝ) = 2 * k + 1 := by
      field_simp at this
      linarith
    have h3 : (2 * j : ℕ) = 2 * (k : ℕ) + 1 := by exact_mod_cast h2
    omega
  unfold lebesgueFunction F
  rw [← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun k _ => ?_
  rw [basis_formula c hinj hT _ hne k]
  have hTφ : |(Chebyshev.T ℝ (n : ℤ)).eval (cos (j * π / n))| = 1 := by
    rw [Chebyshev.T_real_cos]
    have : ((n : ℤ) : ℝ) * (j * π / n) = (j : ℕ) * π := by
      push_cast; field_simp
    rw [this, cos_nat_mul_pi, abs_pow, abs_neg, abs_one, one_pow]
  have hθ0 := th_pos n k hn0
  have hθπ := th_lt_pi k.2
  have hsθ : 0 < sin (th n k) := sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hd := deriv_T_cos n (th n k)
  have hsin1 : |sin (n * th n k)| = 1 := by
    have hcos : cos (n * th n k) = 0 := by
      have := hT k
      simp only [hc] at this
      rw [Chebyshev.T_real_cos] at this
      push_cast at this
      exact this
    have h := sin_sq_add_cos_sq (n * th n k)
    rw [hcos] at h
    rw [← pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero, sq_abs]
    linarith
  set D := (derivative (Chebyshev.T ℝ (n : ℤ))).eval (c k) with hD
  have hDabs : |D| * sin (th n k) = n := by
    have : |D * sin (th n k)| = n := by
      simp only [hD, hc]
      rw [hd, abs_mul, hsin1, mul_one, abs_of_pos hn]
    rw [abs_mul, abs_of_pos hsθ] at this
    exact this
  have hD0 : |D| ≠ 0 := by
    intro h; rw [h, zero_mul] at hDabs; linarith
  have hx0 : |cos (j * π / n) - c k| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr (hne k))
  rw [abs_div, abs_mul, hTφ]
  have hD' : |D| = n / sin (th n k) := by
    rw [eq_div_iff hsθ.ne']; exact hDabs
  rw [hD']
  simp only [hc]
  field_simp


lemma a_pos {n : ℕ} (hn : 2 ≤ n) : 0 < cos (π / (2 * n)) := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply cos_pos_of_mem_Ioo
  constructor
  · have := pi_pos; linarith [show 0 < π / (2 * n) by positivity]
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [pi_pos]

lemma L_affine_eq {n : ℕ} (hn : 2 ≤ n) (φ : ℝ) :
    lebesgueFunction (fun k : Fin n => -cos ((2 * k + 1) * π / (2 * n)) / cos (π / (2 * n)))
      (-cos φ / cos (π / (2 * n))) =
    lebesgueFunction (fun k : Fin n => cos (th n k)) (cos φ) := by
  have ha := (a_pos hn).ne'
  rw [lebesgueFunction_eq, lebesgueFunction_eq]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  refine prod_congr rfl fun i _ => ?_
  unfold th
  rw [div_sub_div_same, div_sub_div_same, div_div_div_cancel_right₀ ha]
  rw [show -cos φ - -cos ((2 * (i : ℝ) + 1) * π / (2 * n)) =
      -(cos φ - cos ((2 * (i : ℝ) + 1) * π / (2 * n))) by ring,
    show -cos ((2 * (k : ℝ) + 1) * π / (2 * n)) - -cos ((2 * (i : ℝ) + 1) * π / (2 * n)) =
      -(cos ((2 * (k : ℝ) + 1) * π / (2 * n)) - cos ((2 * (i : ℝ) + 1) * π / (2 * n))) by ring,
    neg_div_neg_eq]

lemma y_first {n : ℕ} (hn : 2 ≤ n) : -cos (th n 0) / cos (π / (2 * n)) = -1 := by
  have ha := (a_pos hn).ne'
  unfold th
  rw [show (2 * ((0 : ℕ) : ℝ) + 1) * π / (2 * n) = π / (2 * n) by push_cast; ring, neg_div,
    div_self ha]

lemma y_last {n : ℕ} (hn : 2 ≤ n) : -cos (th n (n - 1)) / cos (π / (2 * n)) = 1 := by
  have ha := (a_pos hn).ne'
  unfold th
  have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  rw [Nat.cast_sub (show 1 ≤ n by omega), show (2 * ((n : ℝ) - ((1 : ℕ) : ℝ)) + 1) * π / (2 * n) = π - π / (2 * n) by
    field_simp; push_cast; ring, cos_pi_sub, neg_neg, div_self ha]

theorem H2_proof : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    IsCanonical (fun k : Fin n => -Real.cos ((2 * k + 1) * π / (2 * n)) / Real.cos (π / (2 * n))) ∧
    ∀ j ∈ Finset.Icc 1 (n - 1), 2 / π * Real.log n - C <
      gapMax (fun k : Fin n => -Real.cos ((2 * k + 1) * π / (2 * n)) / Real.cos (π / (2 * n))) j := by
  refine ⟨3, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  set y : Fin n → ℝ := fun k => -Real.cos ((2 * k + 1) * π / (2 * n)) / Real.cos (π / (2 * n))
    with hy
  have hyk : ∀ k : Fin n, y k = -cos (th n k) / cos (π / (2 * n)) := fun k => rfl
  have hmono : StrictMono y := by
    intro k l hkl
    rw [hyk, hyk]
    have ha := a_pos hn
    apply div_lt_div_of_pos_right _ ha
    have : cos (th n l) < cos (th n k) := by
      apply cos_lt_cos_of_nonneg_of_le_pi (th_pos n k (by omega)).le (th_lt_pi l.2).le
      unfold th
      have : (k : ℝ) < l := by exact_mod_cast hkl
      have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      apply div_lt_div_of_pos_right _ (by positivity)
      nlinarith [pi_pos]
    linarith
  have hfirst : y ⟨0, by omega⟩ = -1 := by rw [hyk]; exact y_first hn
  have hlast : y ⟨n - 1, by omega⟩ = 1 := by rw [hyk]; exact y_last hn
  refine ⟨⟨⟨hmono, fun k => ?_⟩, ⟨_, hfirst⟩, ⟨_, hlast⟩⟩, ?_⟩
  · constructor
    · rw [← hfirst]; exact hmono.monotone (Fin.le_def.mpr (Nat.zero_le _))
    · rw [← hlast]; exact hmono.monotone (Fin.le_def.mpr (by simp only; omega))
  · intro j hj
    obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.mp hj
    have hjn' : j < n := by omega
    -- the value at the extremum
    have hval : lebesgueFunction y (-cos (j * π / n) / cos (π / (2 * n))) = F n j := by
      rw [hy, L_affine_eq hn, L_cheb_eq hj1 hjn']
    have hF : 2 / π * Real.log n - 3 < F n j := by
      by_cases h2 : 2 * j ≤ n
      · exact F_bound hj1 h2
      · rw [← F_symm hjn'.le]
        exact F_bound (by omega) (by omega)
    -- the extremum lies in the gap
    have hlo : extendedNodes y j = -cos (th n (j - 1)) / cos (π / (2 * n)) := by
      unfold extendedNodes
      rw [dif_pos ⟨hj1, by omega⟩]
      rfl
    have hhi : extendedNodes y (j + 1) = -cos (th n j) / cos (π / (2 * n)) := by
      unfold extendedNodes
      rw [dif_pos ⟨by omega, by omega⟩]
      rfl
    have ha := a_pos hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hφ0 : 0 ≤ (j : ℝ) * π / n := by positivity
    have hmem : -cos (j * π / n) / cos (π / (2 * n)) ∈
        Set.Icc (extendedNodes y j) (extendedNodes y (j + 1)) := by
      rw [hlo, hhi]
      constructor
      · apply div_le_div_of_nonneg_right _ ha.le
        have : cos (j * π / n) ≤ cos (th n (j - 1)) := by
          apply cos_le_cos_of_nonneg_of_le_pi (th_pos n _ (by omega)).le
          · rw [div_le_iff₀ hn']
            have : (j : ℝ) ≤ n := by exact_mod_cast hjn'.le
            nlinarith [pi_pos]
          · unfold th
            rw [Nat.cast_sub hj1, div_le_div_iff₀ (by positivity) hn']
            push_cast
            nlinarith [pi_pos]
        linarith
      · apply div_le_div_of_nonneg_right _ ha.le
        have : cos (th n j) ≤ cos (j * π / n) := by
          apply cos_le_cos_of_nonneg_of_le_pi hφ0 (th_lt_pi hjn').le
          unfold th
          rw [div_le_div_iff₀ hn' (by positivity)]
          nlinarith [pi_pos]
        linarith
    have hbdd : BddAbove (lebesgueFunction y '' Set.Icc (extendedNodes y j) (extendedNodes y (j + 1))) := by
      refine (isCompact_Icc.image ?_).bddAbove
      unfold lebesgueFunction
      exact continuous_finsetSum _ fun k _ => (Polynomial.continuous _).abs
    have hle := le_csSup hbdd (Set.mem_image_of_mem _ hmem)
    unfold gapMax
    rw [hval] at hle
    linarith

end OMA.E1129H2

theorem OMA.solution : OMA.R_Erdos1129_erdos_1129_variants_erdos_lower_bound_R1.H2 :=
  OMA.E1129H2.H2_proof
