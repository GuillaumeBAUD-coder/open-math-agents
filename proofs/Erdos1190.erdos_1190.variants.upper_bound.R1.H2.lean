import OMAReductions.R_Erdos1190_erdos_1190_variants_upper_bound_R1

-- Step Erdos1190.erdos_1190.variants.upper_bound.R1.H2: hypothesis H2 of reduction Erdos1190.erdos_1190.variants.upper_bound.R1
-- Credit: @loremcdmx
-- H2 := ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ᶠ m : ℕ in atTop, ∃ B : ℝ,     B < scaleL m ^ (-(sqrt 3 / 2) + δ) ∧ ∀ K : ℕ,       (∑ k ∈ range K, 2 * scaleL (2 ^ (k + 1) * m) ^ (-(sqrt 3 / 2) + δ / 2)) ≤ B

namespace OMA.Aux
open Filter Real Finset

noncomputable def tt (M : ℕ) : ℝ := sqrt (log M * log (log M))

lemma rpow_scale (M : ℕ) (x : ℝ) : scaleL M ^ x = Real.exp (x * tt M) := by
  unfold scaleL tt
  rw [← Real.exp_mul, mul_comm]

lemma exp1_le_log16 (m : ℕ) (hm : 16 ≤ m) : Real.exp 1 ≤ log m := by
  have h1 : log 16 = 4 * log 2 := by
    rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have h2 : log 16 ≤ log m := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hm
  have := Real.log_two_gt_d9
  have := Real.exp_one_lt_d9
  linarith

lemma mono_aux (a b : ℝ) (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    a * log a ≤ b * log b ∧ b ≤ b * log b := by
  have hapos : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hbpos : 0 < b := lt_of_lt_of_le hapos hab
  have hla : 1 ≤ log a := by
    rw [Real.le_log_iff_exp_le hapos]; exact ha
  have hlab : log a ≤ log b := Real.log_le_log hapos hab
  constructor
  · calc a * log a ≤ b * log a := by nlinarith
      _ ≤ b * log b := by nlinarith
  · nlinarith

lemma stepA (m k : ℕ) (hm : 16 ≤ m) :
    tt m ≤ tt (2 ^ (k+1) * m) ∧ sqrt (((k:ℝ)+1) * log 2) ≤ tt (2 ^ (k+1) * m) := by
  have hm0 : (0:ℝ) < m := by positivity
  have hlogM : log ((2 ^ (k+1) * m : ℕ) : ℝ) = ((k:ℝ)+1) * log 2 + log m := by
    push_cast
    rw [Real.log_mul (by positivity) hm0.ne', Real.log_pow]; push_cast; ring
  have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hge := exp1_le_log16 m hm
  have hle : log m ≤ log ((2 ^ (k+1) * m : ℕ) : ℝ) := by
    rw [hlogM]; nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)+1) hl2.le]
  obtain ⟨h1, h2⟩ := mono_aux _ _ hge hle
  constructor
  · exact Real.sqrt_le_sqrt h1
  · apply Real.sqrt_le_sqrt
    rw [hlogM] at h2 ⊢
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)+1) hl2.le, Real.exp_pos 1, hge]

lemma stepA' (m k : ℕ) (hm : 16 ≤ m) (c θ : ℝ) (hc : 0 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.exp (-c * tt (2 ^ (k+1) * m)) ≤
      Real.exp (-c * (1 - θ) * tt m) * Real.exp (-(c * θ) * sqrt (((k:ℝ)+1) * log 2)) := by
  obtain ⟨h1, h2⟩ := stepA m k hm
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have a1 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hθ1)
  have a2 := mul_le_mul_of_nonneg_left h2 hθ0
  have : (1 - θ) * tt m + θ * sqrt (((k:ℝ)+1) * log 2) ≤ tt (2 ^ (k+1) * m) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hc.le]

lemma stepB (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    Summable (fun k : ℕ => Real.exp (-a * sqrt (((k:ℝ)+1) * L))) := by
  have hs : Summable (fun k : ℕ => 1 / (((k+1 : ℕ) : ℝ)) ^ 2) :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le)
    (fun k => ?_) (hs.mul_left (24 / ((a^2 * L)^2)))
  have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
  set y := a * sqrt (((k:ℝ)+1) * L) with hy
  have hypos : 0 < y := by positivity
  have hy2 : y ^ 2 = a^2 * (((k:ℝ)+1) * L) := by
    rw [hy, mul_pow, Real.sq_sqrt (by positivity)]
  have hy4 : y ^ 4 = (a^2 * L)^2 * ((k:ℝ)+1)^2 := by
    have : y ^ 4 = (y^2)^2 := by ring
    rw [this, hy2]; ring
  have hexp := Real.pow_div_factorial_le_exp y hypos.le 4
  have hf : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at hexp
  have hmain : Real.exp (-y) ≤ 24 / y ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    have : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    have h24 : y ^ 4 / 24 ≤ Real.exp y := hexp
    nlinarith [Real.exp_pos (-y), mul_le_mul_of_nonneg_left h24 (Real.exp_pos (-y)).le]
  have : -a * sqrt (((k:ℝ)+1) * L) = -y := by rw [hy]; ring
  rw [this]
  refine hmain.trans (le_of_eq ?_)
  rw [hy4]
  push_cast
  field_simp

lemma rho_facts (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) :
    0 < sqrt 3 / 2 - δ / 2 ∧ 0 ≤ δ / (4 * (sqrt 3 / 2 - δ / 2)) ∧
    δ / (4 * (sqrt 3 / 2 - δ / 2)) ≤ 1 ∧
    (sqrt 3 / 2 - δ / 2) * (δ / (4 * (sqrt 3 / 2 - δ / 2))) = δ / 4 := by
  have h3 : 1 ≤ sqrt 3 := by
    rw [show (1:ℝ) = sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hc : 0 < sqrt 3 / 2 - δ / 2 := by linarith
  have hc' : sqrt 3 - δ ≠ 0 := by intro h; linarith
  refine ⟨hc, by positivity, ?_, by field_simp⟩
  rw [div_le_one (by positivity)]; linarith

theorem main (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) :
    ∀ᶠ m : ℕ in atTop, ∃ B : ℝ,
      B < scaleL m ^ (-(sqrt 3 / 2) + δ) ∧ ∀ K : ℕ,
        (∑ k ∈ range K, 2 * scaleL (2 ^ (k + 1) * m) ^ (-(sqrt 3 / 2) + δ / 2)) ≤ B := by
  obtain ⟨hc, hθ0, hθ1, hcθ⟩ := rho_facts δ hδ hδ2
  set c := sqrt 3 / 2 - δ / 2 with hcdef
  set θ := δ / (4 * c) with hθdef
  have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hsum := stepB (δ/4) (log 2) (by positivity) hl2
  set G := ∑' k : ℕ, Real.exp (-(δ/4) * sqrt (((k:ℝ)+1) * log 2)) with hG
  have hG0 : 0 ≤ G := tsum_nonneg (fun k => (Real.exp_pos _).le)
  set N1 : ℕ := Nat.ceil (Real.exp ((8 * G / δ)^2)) + 16 with hN1
  filter_upwards [eventually_ge_atTop N1] with m hm
  have hm16 : 16 ≤ m := by omega
  have hm0 : (0:ℝ) < m := by positivity
  set E := Real.exp (-c * (1 - θ) * tt m) with hE
  have hEpos : 0 < E := Real.exp_pos _
  refine ⟨2 * G * E, ?_, ?_⟩
  · -- smallness
    have hge := exp1_le_log16 m hm16
    have hlm : (8 * G / δ)^2 ≤ log m := by
      rw [Real.le_log_iff_exp_le hm0]
      have h1 := Nat.le_ceil (Real.exp ((8 * G / δ)^2))
      have h2 : (Nat.ceil (Real.exp ((8 * G / δ)^2)) : ℝ) ≤ m := by
        exact_mod_cast (by omega : Nat.ceil (Real.exp ((8 * G / δ)^2)) ≤ m)
      linarith
    have hlogpos : 0 < log m := lt_of_lt_of_le (Real.exp_pos 1) hge
    have hll : 1 ≤ log (log m) := by
      rw [Real.le_log_iff_exp_le hlogpos]; exact hge
    have ht1 : sqrt (log m) ≤ tt m := by
      unfold tt
      apply Real.sqrt_le_sqrt
      nlinarith
    have ht2 : 8 * G / δ ≤ sqrt (log m) :=
      (le_abs_self _).trans (Real.abs_le_sqrt hlm)
    have ht3 : 2 * G ≤ δ / 4 * tt m := by
      have : 8 * G / δ ≤ tt m := ht2.trans ht1
      rw [div_le_iff₀ hδ] at this
      nlinarith
    have ht4 : 2 * G < Real.exp (δ / 4 * tt m) := by
      have := Real.add_one_le_exp (δ / 4 * tt m)
      linarith
    rw [rpow_scale]
    have e1 : -c * (1 - θ) = -c + δ / 4 := by linear_combination hcθ
    have e2 : (-(sqrt 3 / 2) + δ) * tt m = -c * (1 - θ) * tt m + δ / 4 * tt m := by
      rw [e1, hcdef]; ring
    rw [e2, Real.exp_add]
    rw [← hE]
    nlinarith
  · intro K
    have hterm : ∀ k : ℕ, 2 * scaleL (2 ^ (k + 1) * m) ^ (-(sqrt 3 / 2) + δ / 2) ≤
        2 * E * Real.exp (-(δ/4) * sqrt (((k:ℝ)+1) * log 2)) := by
      intro k
      rw [rpow_scale]
      have e : (-(sqrt 3 / 2) + δ / 2) = -c := by rw [hcdef]; ring
      rw [e]
      have := stepA' m k hm16 c θ hc hθ0 hθ1
      rw [hcθ] at this
      nlinarith
    calc _ ≤ ∑ k ∈ range K, 2 * E * Real.exp (-(δ/4) * sqrt (((k:ℝ)+1) * log 2)) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = 2 * E * ∑ k ∈ range K, Real.exp (-(δ/4) * sqrt (((k:ℝ)+1) * log 2)) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * E * G := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hsum.sum_le_tsum _ (fun i _ => (Real.exp_pos _).le)
      _ = 2 * G * E := by ring

end OMA.Aux

theorem OMA.solution : OMA.R_Erdos1190_erdos_1190_variants_upper_bound_R1.H2 := by
  intro δ hδ hδ2
  exact OMA.Aux.main δ hδ hδ2
