import OMAReductions.R_Erdos233_erdos_233_variants_upper_bound_R1

-- Reduction Erdos233.erdos_233.variants.upper_bound.R1.H2.R1 of step Erdos233.erdos_233.variants.upper_bound.R1.H2
-- Credit: @green-notes

/-!
Split Selberg's conditional mean-square estimate for the zero sum into two independent lemmas:
1. `H1`: Riemann-von Mangoldt unit-interval zero-counting bound `N(T + 1) - N(T) ≤ C * log(T + 2)`.
2. `H2`: Gaussian-majorized Plancherel bound over `[x, 4x]` for any countable frequency sum
   `∑' i, a i * y ^ (3/2 + i * γ i)` with `Summable (fun i ↦ ‖a i‖)`.
`main` combines them with the second-difference bound `‖c_ρ(δ)‖ ≤ min (δ^2) (13 / max (3/4) γ^2)`
and dyadic/tail summation over unit intervals.
-/

open Complex MeasureTheory Filter
open scoped Real

namespace OMA.R_Erdos233_erdos_233_variants_upper_bound_R1_H2_R1

def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T →
    Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} =>
      if T ≤ |ρ.1.im| ∧ |ρ.1.im| < T + 1 then
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
      else 0) ∧
    (∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
      if T ≤ |ρ.1.im| ∧ |ρ.1.im| < T + 1 then
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
      else 0) ≤ C * Real.log (T + 2)

def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type} (γ : ι → ℝ) (a : ι → ℂ),
      Summable (fun i ↦ ‖a i‖) →
      ∀ x : ℝ, 1 ≤ x →
        IntervalIntegrable (fun y : ℝ =>
          ‖∑' i : ι, a i * (y : ℂ) ^ ((3 / 2 : ℂ) + (γ i : ℂ) * I)‖ ^ 2)
          MeasureTheory.volume x (4 * x) ∧
        ∫ y in x..4 * x,
          ‖∑' i : ι, a i * (y : ℂ) ^ ((3 / 2 : ℂ) + (γ i : ℂ) * I)‖ ^ 2
          ≤ C * x ^ 4 * ∑' k : ℕ,
              (∑' i : ι, if (k : ℝ) ≤ |γ i| ∧ |γ i| < (k : ℝ) + 1 then ‖a i‖ else 0) ^ 2

lemma rh_re_eq_half (hRH : RiemannHypothesis) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.re = 1 / 2 := by
  refine hRH ρ hζ ?_ ?_
  · rintro ⟨n, rfl⟩
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [hre] at h0
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h
    rw [h] at h1
    simp at h1

lemma cpow_one_add_re_half {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ρ + 1 = (3 / 2 : ℂ) + (ρ.im : ℂ) * I := by
  apply Complex.ext
  · simp [hre]; norm_num
  · simp

lemma hasDerivAt_one_add_cpow (a : ℝ) (ha : 0 < a) {s : ℂ} (hs : s ≠ 0) (v : ℝ) (hv : 0 ≤ v) :
    HasDerivAt (fun t : ℝ ↦ ((a + t : ℝ) : ℂ) ^ s) (s * ((a + v : ℝ) : ℂ) ^ (s - 1)) v := by
  have hav : a + v ≠ 0 := by linarith
  have h1 := hasDerivAt_ofReal_cpow_const hav hs
  have h2 : HasDerivAt (fun t : ℝ ↦ a + t) 1 v := (hasDerivAt_id v).const_add a
  simpa [Function.comp_def] using h1.scomp v h2

lemma second_diff_bound {ρ : ℂ} (hre : ρ.re = 1 / 2) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ‖(((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) + 1) /
        (ρ * (ρ + 1))‖ ≤ δ ^ 2 := by
  have hρ0 : ρ ≠ 0 := fun h ↦ by rw [h] at hre; norm_num at hre
  have hρ1 : ρ + 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h
    simp [hre] at this
    norm_num at this
  have hprod0 : 0 < ‖ρ * (ρ + 1)‖ := norm_pos_iff.mpr (mul_ne_zero hρ0 hρ1)
  let f : ℝ → ℂ := fun t ↦ ((1 + t : ℝ) : ℂ) ^ (ρ + 1)
  let f' : ℝ → ℂ := fun t ↦ (ρ + 1) * ((1 + t : ℝ) : ℂ) ^ ρ
  let g : ℝ → ℂ := fun t ↦ f (t + δ) - f t
  let g' : ℝ → ℂ := fun t ↦ f' (t + δ) - f' t
  have hf_deriv : ∀ t : ℝ, 0 ≤ t → HasDerivAt f (f' t) t := fun t ht ↦ by
    simpa [f, f'] using hasDerivAt_one_add_cpow 1 one_pos hρ1 t ht
  have hf'_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt f' ((ρ + 1) * (ρ * ((1 + t : ℝ) : ℂ) ^ (ρ - 1))) t := fun t ht ↦
    (hasDerivAt_one_add_cpow 1 one_pos hρ0 t ht).const_mul (ρ + 1)
  have hf'_bound : ∀ t ∈ Set.Icc (0 : ℝ) δ, ‖g' t‖ ≤ ‖ρ * (ρ + 1)‖ * δ := by
    intro t ht
    have hwin : ∀ v ∈ Set.Icc t (t + δ),
        HasDerivWithinAt f' ((ρ + 1) * (ρ * ((1 + v : ℝ) : ℂ) ^ (ρ - 1))) (Set.Icc t (t + δ)) v :=
      fun v hv ↦ (hf'_deriv v (by linarith [ht.1, hv.1])).hasDerivWithinAt
    have hbd : ∀ v ∈ Set.Ico t (t + δ),
        ‖(ρ + 1) * (ρ * ((1 + v : ℝ) : ℂ) ^ (ρ - 1))‖ ≤ ‖ρ * (ρ + 1)‖ := by
      intro v hv
      have hv1 : 1 ≤ 1 + v := by linarith [ht.1, hv.1]
      have hnv : ‖((1 + v : ℝ) : ℂ) ^ (ρ - 1)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
        have hsub : (ρ - 1).re = -1 / 2 := by simp [hre]; norm_num
        rw [hsub]
        exact Real.rpow_le_one_of_one_le_of_nonpos hv1 (by norm_num)
      calc ‖(ρ + 1) * (ρ * ((1 + v : ℝ) : ℂ) ^ (ρ - 1))‖
          = ‖ρ * (ρ + 1)‖ * ‖((1 + v : ℝ) : ℂ) ^ (ρ - 1)‖ := by
            rw [← mul_assoc, mul_comm (ρ + 1) ρ, norm_mul]
        _ ≤ ‖ρ * (ρ + 1)‖ * 1 := mul_le_mul_of_nonneg_left hnv (norm_nonneg _)
        _ = ‖ρ * (ρ + 1)‖ := mul_one _
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hwin hbd (t + δ)
      (Set.right_mem_Icc.mpr (by linarith))
    simpa [g', add_sub_cancel_left] using hmv
  have hg_deriv : ∀ t ∈ Set.Icc (0 : ℝ) δ, HasDerivWithinAt g (g' t) (Set.Icc 0 δ) t := by
    intro t ht
    have htd : 0 ≤ t + δ := by linarith [ht.1]
    have hd1 : HasDerivAt (fun u ↦ f (u + δ)) (f' (t + δ)) t := by
      have hcomp := (hf_deriv (t + δ) htd).scomp t ((hasDerivAt_id t).add_const δ)
      simpa [Function.comp_def] using hcomp
    have hd2 : HasDerivAt f (f' t) t := hf_deriv t ht.1
    exact (hd1.sub hd2).hasDerivWithinAt
  have hmv2 := norm_image_sub_le_of_norm_deriv_le_segment' hg_deriv
    (fun t ht ↦ hf'_bound t (Set.Ico_subset_Icc_self ht)) δ (Set.right_mem_Icc.mpr hδ0.le)
  have hdiff : g δ - g 0 =
      ((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) + 1 := by
    have hf0 : f 0 = 1 := by simp [f]
    have hf2 : f (δ + δ) = ((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1) := by simp [f, two_mul]
    have hf1 : f (0 + δ) = ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) := by simp [f]
    have hfd : f δ = ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) := rfl
    calc g δ - g 0 = (f (δ + δ) - f δ) - (f (0 + δ) - f 0) := rfl
      _ = ((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) + 1 := by
          rw [hf2, hf1, hfd, hf0]; ring
  rw [sub_zero] at hmv2
  rw [hdiff] at hmv2
  rw [norm_div, div_le_iff₀ hprod0]
  calc ‖(((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) + 1)‖
      ≤ ‖ρ * (ρ + 1)‖ * δ * δ := hmv2
    _ = δ ^ 2 * ‖ρ * (ρ + 1)‖ := by ring

lemma tail_coeff_bound {ρ : ℂ} (hre : ρ.re = 1 / 2) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ‖(((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) + 1) /
        (ρ * (ρ + 1))‖ ≤ 13 / max (3 / 4) (ρ.im ^ 2) := by
  have h12 : ‖((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1)‖ ≤ 4 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    have hre1 : (ρ + 1).re = 3 / 2 := by simp [hre]; norm_num
    rw [hre1]
    have hle2 : 1 + 2 * δ ≤ 2 := by linarith
    have h1le : 1 ≤ 1 + 2 * δ := by linarith
    calc (1 + 2 * δ) ^ (3 / 2 : ℝ) ≤ (1 + 2 * δ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1le (by norm_num)
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow (by linarith) hle2 (by norm_num)
      _ = 4 := by norm_num
  have h11 : ‖((1 + δ : ℝ) : ℂ) ^ (ρ + 1)‖ ≤ 4 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    have hre1 : (ρ + 1).re = 3 / 2 := by simp [hre]; norm_num
    rw [hre1]
    have hle2 : 1 + δ ≤ 2 := by linarith
    have h1le : 1 ≤ 1 + δ := by linarith
    calc (1 + δ) ^ (3 / 2 : ℝ) ≤ (1 + δ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1le (by norm_num)
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow (by linarith) hle2 (by norm_num)
      _ = 4 := by norm_num
  have hnum : ‖((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) + 1‖ ≤ 13 := by
    calc ‖((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) + 1‖
        ≤ ‖((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1)‖ + ‖(1 : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ (‖((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1)‖ + ‖2 * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1)‖) + 1 := by
          gcongr
          · exact norm_sub_le _ _
          · simp
      _ = ‖((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1)‖ + 2 * ‖((1 + δ : ℝ) : ℂ) ^ (ρ + 1)‖ + 1 := by
          rw [norm_mul]; norm_num
      _ ≤ 4 + 2 * 4 + 1 := by linarith
      _ = 13 := by norm_num
  have hn0 : 1 / 2 ≤ ‖ρ‖ := by
    calc (1 / 2 : ℝ) = |ρ.re| := by rw [hre]; norm_num
      _ ≤ ‖ρ‖ := abs_re_le_norm ρ
  have hn1 : 3 / 2 ≤ ‖ρ + 1‖ := by
    calc (3 / 2 : ℝ) = |(ρ + 1).re| := by simp [hre]; norm_num
      _ ≤ ‖ρ + 1‖ := abs_re_le_norm (ρ + 1)
  have him0 : |ρ.im| ≤ ‖ρ‖ := abs_im_le_norm ρ
  have him1 : |ρ.im| ≤ ‖ρ + 1‖ := by
    have := abs_im_le_norm (ρ + 1)
    simpa using this
  have hden : max (3 / 4) (ρ.im ^ 2) ≤ ‖ρ * (ρ + 1)‖ := by
    rw [norm_mul, max_le_iff]
    constructor
    · calc (3 / 4 : ℝ) = (1 / 2) * (3 / 2) := by norm_num
        _ ≤ ‖ρ‖ * ‖ρ + 1‖ := mul_le_mul hn0 hn1 (by norm_num) (norm_nonneg _)
    · calc ρ.im ^ 2 = |ρ.im| * |ρ.im| := by rw [← sq_abs, sq]
        _ ≤ ‖ρ‖ * ‖ρ + 1‖ := mul_le_mul him0 him1 (abs_nonneg _) (norm_nonneg _)
  have hmax_pos : 0 < max (3 / 4 : ℝ) (ρ.im ^ 2) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  rw [norm_div]
  exact div_le_div₀ (by norm_num) hnum hmax_pos hden

lemma tsum_inv_sq_shift_le (K : ℕ) (hK : 2 ≤ K) :
    Summable (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + K) ^ 2) ∧
    ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + K) ^ 2 ≤ 2 / (K : ℝ) := by
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + K) ^ 2 ≤
      1 / ((K : ℝ) - 1) - 1 / ((n : ℝ) + K - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hp1 : (0 : ℝ) < (n : ℝ) + K - 1 := by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      have hp2 : (0 : ℝ) < (n : ℝ) + K := by positivity
      have hp3 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + K - 1 := by push_cast; linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      have hstep : (1 : ℝ) / ((n : ℝ) + K) ^ 2 ≤
          1 / ((n : ℝ) + K - 1) - 1 / (((n + 1 : ℕ) : ℝ) + K - 1) := by
        have e1 : ((n + 1 : ℕ) : ℝ) + K - 1 = (n : ℝ) + K := by push_cast; ring
        rw [e1]
        field_simp
        nlinarith
      linarith
  have hbd : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + K) ^ 2 ≤ 2 / (K : ℝ) := by
    intro n
    have h1 : 0 < 1 / ((n : ℝ) + K - 1) := div_pos zero_lt_one (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    have h2 : 1 / ((K : ℝ) - 1) ≤ 2 / (K : ℝ) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    linarith [hpart n]
  exact ⟨summable_of_sum_range_le (fun _ ↦ by positivity) hbd,
    Real.tsum_le_of_sum_range_le (fun _ ↦ by positivity) hbd⟩

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hx.le] at h1
  linarith

lemma summable_log_tail (C₁ : ℝ) (hC₁ : 0 ≤ C₁) {δ : ℝ} (hδ0 : 0 < δ) :
    Summable (fun k : ℕ ↦ C₁ * Real.log ((k : ℝ) + 2) *
      min (δ ^ 2) (13 / max (3 / 4) ((k : ℝ) ^ 2))) := by
  have hp : Summable (fun k : ℕ ↦ (C₁ * (13 * (2 * Real.sqrt 3))) * (((k + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    ((Real.summable_nat_rpow.mpr (by norm_num)).comp_injective (add_left_injective 2)).mul_left _
  rw [← summable_nat_add_iff 2]
  refine Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg
      (mul_nonneg hC₁ (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])))
      (le_min (sq_nonneg δ) (by positivity)))
    (fun k ↦ ?_) hp
  have hk2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 2)
  have hk0 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by linarith
  have hlog : Real.log (((k + 2 : ℕ) : ℝ) + 2) ≤ 2 * Real.sqrt 3 * ((k + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
    calc Real.log (((k + 2 : ℕ) : ℝ) + 2) ≤ 2 * Real.sqrt (((k + 2 : ℕ) : ℝ) + 2) :=
          log_le_two_sqrt (by linarith)
      _ ≤ 2 * Real.sqrt (3 * ((k + 2 : ℕ) : ℝ)) := by gcongr; linarith
      _ = 2 * (Real.sqrt 3 * Real.sqrt ((k + 2 : ℕ) : ℝ)) := by rw [Real.sqrt_mul (by norm_num)]
      _ = 2 * Real.sqrt 3 * ((k + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow]; ring
  have hmin : min (δ ^ 2) (13 / max (3 / 4 : ℝ) (((k + 2 : ℕ) : ℝ) ^ 2)) ≤
      13 / ((k + 2 : ℕ) : ℝ) ^ 2 := by
    refine (min_le_right _ _).trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hk0) (le_max_right _ _)
  have hlog_nn : 0 ≤ Real.log (((k + 2 : ℕ) : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hrpow : ((k + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 =
      ((k + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast ((k + 2 : ℕ) : ℝ) 2, ← Real.rpow_sub hk0]
    norm_num
  calc C₁ * Real.log (((k + 2 : ℕ) : ℝ) + 2) *
        min (δ ^ 2) (13 / max (3 / 4 : ℝ) (((k + 2 : ℕ) : ℝ) ^ 2))
      ≤ C₁ * (2 * Real.sqrt 3 * ((k + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) * (13 / ((k + 2 : ℕ) : ℝ) ^ 2) := by
        gcongr
    _ = C₁ * (13 * (2 * Real.sqrt 3)) * (((k + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) := by ring
    _ = (C₁ * (13 * (2 * Real.sqrt 3))) * (((k + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by rw [hrpow]

lemma tail_sum_sq_bound {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    Summable (fun k : ℕ ↦
      (Real.log ((k : ℝ) + 2) * min (δ ^ 2) (13 / max (3 / 4) ((k : ℝ) ^ 2))) ^ 2) ∧
    ∑' k : ℕ, (Real.log ((k : ℝ) + 2) * min (δ ^ 2) (13 / max (3 / 4) ((k : ℝ) ^ 2))) ^ 2 ≤
      120000 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by
  let f : ℕ → ℝ := fun k ↦
    (Real.log ((k : ℝ) + 2) * min (δ ^ 2) (13 / max (3 / 4) ((k : ℝ) ^ 2))) ^ 2
  have hf_nn : ∀ k, 0 ≤ f k := fun _ ↦ sq_nonneg _
  let K : ℕ := ⌊1 / δ⌋₊
  have hK2 : 2 ≤ K := by
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hδ0]
    norm_num
    linarith
  have hK_le : (K : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
  have hK_lt : 1 / δ < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK_pos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK_half : 1 / (2 * δ) ≤ (K : ℝ) := by
    have hK2r : (2 : ℝ) ≤ K := by exact_mod_cast hK2
    have h1 : 1 / δ ≤ (3 / 2 : ℝ) * K := by linarith
    have : 1 / (2 * δ) = (1 / 2) * (1 / δ) := by ring
    linarith
  have hinvK : 1 / (K : ℝ) ≤ 2 * δ := by
    rw [div_le_iff₀ hK_pos]
    have := mul_le_mul_of_nonneg_right hK_half (show 0 ≤ 2 * δ by positivity)
    have e : 1 / (2 * δ) * (2 * δ) = 1 := by field_simp
    linarith
  have hL : 1 ≤ Real.log (2 / δ) := by
    have h4 : (4 : ℝ) ≤ 2 / δ := by rw [le_div_iff₀ hδ0]; linarith
    have hexp : Real.exp 1 ≤ 2 / δ := by linarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr hexp
  have hlogK : Real.log ((K : ℝ) + 2) ≤ 2 * Real.log (2 / δ) := by
    have h1 : (K : ℝ) + 2 ≤ (2 / δ) ^ 2 := by
      have h2d : 2 ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
      have h4d : (4 : ℝ) ≤ 2 / δ := by rw [le_div_iff₀ hδ0]; linarith
      calc (K : ℝ) + 2 ≤ 1 / δ + 2 := by linarith
        _ ≤ 1 / δ + 1 / δ := by linarith
        _ = 2 / δ := by ring
        _ ≤ (2 / δ) * (2 / δ) := by nlinarith
        _ = (2 / δ) ^ 2 := (sq _).symm
    calc Real.log ((K : ℝ) + 2) ≤ Real.log ((2 / δ) ^ 2) := Real.log_le_log (by positivity) h1
      _ = 2 * Real.log (2 / δ) := by rw [Real.log_pow]; push_cast; ring
  have hhead : ∑ k ∈ Finset.range K, f k ≤ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by
    have hterm : ∀ k ∈ Finset.range K, f k ≤ 4 * δ ^ 4 * Real.log (2 / δ) ^ 2 := by
      intro k hk
      have hk_lt : k < K := Finset.mem_range.mp hk
      have hlk : Real.log ((k : ℝ) + 2) ≤ Real.log ((K : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (by omega : k + 2 ≤ K + 2))
      have hlk0 : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
      have hmin : min (δ ^ 2) (13 / max (3 / 4 : ℝ) ((k : ℝ) ^ 2)) ≤ δ ^ 2 := min_le_left _ _
      have hmin0 : 0 ≤ min (δ ^ 2) (13 / max (3 / 4 : ℝ) ((k : ℝ) ^ 2)) :=
        le_min (sq_nonneg δ) (by positivity)
      have hprod : Real.log ((k : ℝ) + 2) * min (δ ^ 2) (13 / max (3 / 4 : ℝ) ((k : ℝ) ^ 2)) ≤
          2 * Real.log (2 / δ) * δ ^ 2 :=
        mul_le_mul (hlk.trans hlogK) hmin hmin0 (by positivity)
      calc f k ≤ (2 * Real.log (2 / δ) * δ ^ 2) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg hlk0 hmin0) hprod 2
        _ = 4 * δ ^ 4 * Real.log (2 / δ) ^ 2 := by ring
    calc ∑ k ∈ Finset.range K, f k
        ≤ ∑ _ ∈ Finset.range K, (4 * δ ^ 4 * Real.log (2 / δ) ^ 2) := Finset.sum_le_sum hterm
      _ = (K : ℝ) * (4 * δ ^ 4 * Real.log (2 / δ) ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (1 / δ) * (4 * δ ^ 4 * Real.log (2 / δ) ^ 2) := by gcongr
      _ = 4 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by field_simp
  obtain ⟨hsum_inv2, htsum_inv2⟩ := tsum_inv_sq_shift_le K hK2
  have htail_bound : ∀ k : ℕ, f (k + K) ≤
      (2 * 169 * (2 * Real.log (2 / δ)) ^ 2 / K ^ 2 +
        2 * 169 * 8 / K ^ 2) * (1 / ((k : ℝ) + K) ^ 2) := by
    intro k
    have hm_ge : (K : ℝ) ≤ (k : ℝ) + K := by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
    have hm_pos : 0 < (k : ℝ) + K := by linarith
    have hlog_split : Real.log (((k + K : ℕ) : ℝ) + 2) =
        Real.log ((K : ℝ) + 2) + Real.log ((((k + K : ℕ) : ℝ) + 2) / ((K : ℝ) + 2)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hratio : (((k + K : ℕ) : ℝ) + 2) / ((K : ℝ) + 2) ≤ 2 * (((k : ℝ) + K) / (K : ℝ)) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hK_pos]
      push_cast
      nlinarith
    have hlog_ratio_sq :
        (Real.log ((((k + K : ℕ) : ℝ) + 2) / ((K : ℝ) + 2))) ^ 2 ≤
          8 * (((k : ℝ) + K) / (K : ℝ)) := by
      have hr0 : 0 < (((k + K : ℕ) : ℝ) + 2) / ((K : ℝ) + 2) := by positivity
      have h1 : Real.log ((((k + K : ℕ) : ℝ) + 2) / ((K : ℝ) + 2)) ≤
          2 * Real.sqrt ((((k + K : ℕ) : ℝ) + 2) / ((K : ℝ) + 2)) := log_le_two_sqrt hr0
      have h0 : 0 ≤ Real.log ((((k + K : ℕ) : ℝ) + 2) / ((K : ℝ) + 2)) := by
        refine Real.log_nonneg ?_
        rw [one_le_div (by positivity)]
        push_cast
        linarith
      calc (Real.log ((((k + K : ℕ) : ℝ) + 2) / ((K : ℝ) + 2))) ^ 2
          ≤ (2 * Real.sqrt ((((k + K : ℕ) : ℝ) + 2) / ((K : ℝ) + 2))) ^ 2 :=
            pow_le_pow_left₀ h0 h1 2
        _ = 4 * ((((k + K : ℕ) : ℝ) + 2) / ((K : ℝ) + 2)) := by
            rw [mul_pow, Real.sq_sqrt hr0.le]; norm_num
        _ ≤ 4 * (2 * (((k : ℝ) + K) / (K : ℝ))) := by gcongr
        _ = 8 * (((k : ℝ) + K) / (K : ℝ)) := by ring
    have hlog_sq : (Real.log (((k + K : ℕ) : ℝ) + 2)) ^ 2 ≤
        2 * (2 * Real.log (2 / δ)) ^ 2 + 2 * (8 * (((k : ℝ) + K) / (K : ℝ))) := by
      rw [hlog_split]
      have hsq2 : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b ↦ by
        nlinarith [sq_nonneg (a - b)]
      have hlogK0 : 0 ≤ Real.log ((K : ℝ) + 2) := Real.log_nonneg (by linarith)
      have hKsq : (Real.log ((K : ℝ) + 2)) ^ 2 ≤ (2 * Real.log (2 / δ)) ^ 2 :=
        pow_le_pow_left₀ hlogK0 hlogK 2
      linarith [hsq2 (Real.log ((K : ℝ) + 2)) (Real.log ((((k + K : ℕ) : ℝ) + 2) / ((K : ℝ) + 2)))]
    have hmin_sq : (min (δ ^ 2) (13 / max (3 / 4 : ℝ) (((k + K : ℕ) : ℝ) ^ 2))) ^ 2 ≤
        169 / ((k : ℝ) + K) ^ 4 := by
      have hmin : min (δ ^ 2) (13 / max (3 / 4 : ℝ) (((k + K : ℕ) : ℝ) ^ 2)) ≤
          13 / ((k : ℝ) + K) ^ 2 := by
        refine (min_le_right _ _).trans ?_
        have hcast : (((k + K : ℕ) : ℝ) ^ 2) = ((k : ℝ) + K) ^ 2 := by push_cast; ring
        rw [hcast]
        exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hm_pos) (le_max_right _ _)
      have hmin0 : 0 ≤ min (δ ^ 2) (13 / max (3 / 4 : ℝ) (((k + K : ℕ) : ℝ) ^ 2)) :=
        le_min (sq_nonneg δ) (by positivity)
      calc (min (δ ^ 2) (13 / max (3 / 4 : ℝ) (((k + K : ℕ) : ℝ) ^ 2))) ^ 2
          ≤ (13 / ((k : ℝ) + K) ^ 2) ^ 2 := pow_le_pow_left₀ hmin0 hmin 2
        _ = 169 / ((k : ℝ) + K) ^ 4 := by rw [div_pow, ← pow_mul]; norm_num
    have hinv_m : 1 / ((k : ℝ) + K) ^ 2 ≤ 1 / (K : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hK_pos) (pow_le_pow_left₀ hK_pos.le hm_ge 2)
    have hinv_m1 : 1 / ((k : ℝ) + K) ≤ 1 / (K : ℝ) :=
      div_le_div_of_nonneg_left zero_le_one hK_pos hm_ge
    calc f (k + K)
        = (Real.log (((k + K : ℕ) : ℝ) + 2)) ^ 2 *
            (min (δ ^ 2) (13 / max (3 / 4 : ℝ) (((k + K : ℕ) : ℝ) ^ 2))) ^ 2 := by
          dsimp [f]; push_cast; ring
      _ ≤ (2 * (2 * Real.log (2 / δ)) ^ 2 + 2 * (8 * (((k : ℝ) + K) / (K : ℝ)))) *
            (169 / ((k : ℝ) + K) ^ 4) :=
          mul_le_mul hlog_sq hmin_sq (sq_nonneg _) (by positivity)
      _ = 2 * 169 * (2 * Real.log (2 / δ)) ^ 2 * (1 / ((k : ℝ) + K) ^ 2) * (1 / ((k : ℝ) + K) ^ 2) +
            2 * 169 * 8 / K * (1 / ((k : ℝ) + K)) * (1 / ((k : ℝ) + K) ^ 2) := by
          field_simp
      _ ≤ 2 * 169 * (2 * Real.log (2 / δ)) ^ 2 * (1 / (K : ℝ) ^ 2) * (1 / ((k : ℝ) + K) ^ 2) +
            2 * 169 * 8 / K * (1 / (K : ℝ)) * (1 / ((k : ℝ) + K) ^ 2) := by
          gcongr
      _ = (2 * 169 * (2 * Real.log (2 / δ)) ^ 2 / K ^ 2 + 2 * 169 * 8 / K ^ 2) *
            (1 / ((k : ℝ) + K) ^ 2) := by ring
  have hsum_tail : Summable (fun k : ℕ ↦ f (k + K)) := by
    refine Summable.of_nonneg_of_le (fun k ↦ hf_nn (k + K)) htail_bound ?_
    exact hsum_inv2.mul_left _
  have hsum_all : Summable f := (summable_nat_add_iff K).mp hsum_tail
  have htsum_tail : ∑' k : ℕ, f (k + K) ≤
      (2 * 169 * (2 * Real.log (2 / δ)) ^ 2 / K ^ 2 + 2 * 169 * 8 / K ^ 2) * (2 / (K : ℝ)) := by
    calc ∑' k : ℕ, f (k + K)
        ≤ ∑' k : ℕ, (2 * 169 * (2 * Real.log (2 / δ)) ^ 2 / K ^ 2 + 2 * 169 * 8 / K ^ 2) *
            (1 / ((k : ℝ) + K) ^ 2) :=
          hsum_tail.tsum_le_tsum htail_bound (hsum_inv2.mul_left _)
      _ = (2 * 169 * (2 * Real.log (2 / δ)) ^ 2 / K ^ 2 + 2 * 169 * 8 / K ^ 2) *
            ∑' k : ℕ, (1 / ((k : ℝ) + K) ^ 2) := tsum_mul_left
      _ ≤ (2 * 169 * (2 * Real.log (2 / δ)) ^ 2 / K ^ 2 + 2 * 169 * 8 / K ^ 2) * (2 / (K : ℝ)) :=
          mul_le_mul_of_nonneg_left htsum_inv2 (by positivity)
  have htail_final : ∑' k : ℕ, f (k + K) ≤ 100000 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by
    have hinv3 : 1 / (K : ℝ) ^ 3 ≤ 8 * δ ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hinvK 3
      calc 1 / (K : ℝ) ^ 3 = (1 / (K : ℝ)) ^ 3 := by ring
        _ ≤ (2 * δ) ^ 3 := this
        _ = 8 * δ ^ 3 := by ring
    have h1_le_L2 : 1 ≤ Real.log (2 / δ) ^ 2 := one_le_pow₀ hL
    have hK_eq : (2 * 169 * (2 * Real.log (2 / δ)) ^ 2 / K ^ 2 + 2 * 169 * 8 / K ^ 2) * (2 / (K : ℝ)) =
        2704 * Real.log (2 / δ) ^ 2 * (1 / (K : ℝ) ^ 3) + 5408 * (1 / (K : ℝ) ^ 3) := by ring
    calc ∑' k : ℕ, f (k + K)
        ≤ 2704 * Real.log (2 / δ) ^ 2 * (1 / (K : ℝ) ^ 3) + 5408 * (1 / (K : ℝ) ^ 3) := by
          linarith [htsum_tail, hK_eq]
      _ ≤ 2704 * Real.log (2 / δ) ^ 2 * (8 * δ ^ 3) + 5408 * (8 * δ ^ 3) := by gcongr
      _ ≤ 2704 * Real.log (2 / δ) ^ 2 * (8 * δ ^ 3) + 5408 * (8 * δ ^ 3) * Real.log (2 / δ) ^ 2 := by
          have : 0 ≤ 5408 * (8 * δ ^ 3) := by positivity
          nlinarith
      _ ≤ 100000 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by
          have : 0 ≤ δ ^ 3 * Real.log (2 / δ) ^ 2 := by positivity
          linarith
  have hsplit := hsum_all.sum_add_tsum_nat_add K
  refine ⟨hsum_all, ?_⟩
  have : (4 : ℝ) * δ ^ 3 * Real.log (2 / δ) ^ 2 + 100000 * δ ^ 3 * Real.log (2 / δ) ^ 2 ≤
      120000 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by
    have : 0 ≤ δ ^ 3 * Real.log (2 / δ) ^ 2 := by positivity
    linarith
  linarith

lemma summable_zero_weighted {C₁ : ℝ}
    (h1 : ∀ T : ℝ, 0 ≤ T →
      Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} =>
        if T ≤ |ρ.1.im| ∧ |ρ.1.im| < T + 1 then
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
        else 0) ∧
      (∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
        if T ≤ |ρ.1.im| ∧ |ρ.1.im| < T + 1 then
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
        else 0) ≤ C₁ * Real.log (T + 2))
    (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hw_sum : Summable (fun k : ℕ ↦ C₁ * Real.log ((k : ℝ) + 2) * w k))
    (g : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} → ℝ)
    (hg0 : ∀ ρ, 0 ≤ g ρ)
    (hg_le : ∀ ρ, g ρ ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * w ⌊|ρ.1.im|⌋₊) :
    Summable g := by
  refine summable_of_sum_le (c := ∑' k : ℕ, C₁ * Real.log ((k : ℝ) + 2) * w k) hg0 fun u ↦ ?_
  let M : ℕ := u.sup fun ρ ↦ ⌊|ρ.1.im|⌋₊
  have hmap : ∀ ρ ∈ u, ⌊|ρ.1.im|⌋₊ ∈ Finset.range (M + 1) := fun ρ hρ ↦
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := fun ρ ↦ ⌊|ρ.1.im|⌋₊) hρ))
  rw [← Finset.sum_fiberwise_of_maps_to hmap g]
  have hterm : ∀ k ∈ Finset.range (M + 1),
      ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k, g ρ ≤ C₁ * Real.log ((k : ℝ) + 2) * w k := by
    intro k _
    obtain ⟨hsum_k, hbd_k⟩ := h1 k (Nat.cast_nonneg k)
    have h1' : ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k, g ρ ≤
        w k * ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k,
          (if (k : ℝ) ≤ |ρ.1.im| ∧ |ρ.1.im| < (k : ℝ) + 1 then
            (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
          else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ρ hρ ↦ ?_
      have hk_eq : ⌊|ρ.1.im|⌋₊ = k := (Finset.mem_filter.mp hρ).2
      have hcond : (k : ℝ) ≤ |ρ.1.im| ∧ |ρ.1.im| < (k : ℝ) + 1 :=
        (Nat.floor_eq_iff (abs_nonneg _)).mp hk_eq
      rw [if_pos hcond, mul_comm]
      simpa [hk_eq] using hg_le ρ
    have h2' : ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k,
        (if (k : ℝ) ≤ |ρ.1.im| ∧ |ρ.1.im| < (k : ℝ) + 1 then
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
        else 0) ≤ C₁ * Real.log ((k : ℝ) + 2) := by
      refine (hsum_k.sum_le_tsum _ fun ρ _ ↦ ?_).trans hbd_k
      split_ifs <;> positivity
    calc ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k, g ρ
        ≤ w k * ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k,
            (if (k : ℝ) ≤ |ρ.1.im| ∧ |ρ.1.im| < (k : ℝ) + 1 then
              (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
            else 0) := h1'
      _ ≤ w k * (C₁ * Real.log ((k : ℝ) + 2)) := mul_le_mul_of_nonneg_left h2' (hw k)
      _ = C₁ * Real.log ((k : ℝ) + 2) * w k := by ring
  calc ∑ k ∈ Finset.range (M + 1), ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k, g ρ
      ≤ ∑ k ∈ Finset.range (M + 1), C₁ * Real.log ((k : ℝ) + 2) * w k := Finset.sum_le_sum hterm
    _ ≤ ∑' k : ℕ, C₁ * Real.log ((k : ℝ) + 2) * w k := by
        refine hw_sum.sum_le_tsum (Finset.range (M + 1)) fun k _ ↦ ?_
        have hC₁ : 0 ≤ C₁ := by
          have := (h1 0 le_rfl).2
          have hnn : 0 ≤ ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
              (if (0 : ℝ) ≤ |ρ.1.im| ∧ |ρ.1.im| < (0 : ℝ) + 1 then
                (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
              else 0) := tsum_nonneg fun _ ↦ by split_ifs <;> positivity
          have hl2 : 0 < Real.log ((0 : ℝ) + 2) := Real.log_pos (by norm_num)
          nlinarith [this, hnn, hl2]
        have hl : 0 ≤ Real.log ((k : ℝ) + 2) :=
          Real.log_nonneg (by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])
        exact mul_nonneg (mul_nonneg hC₁ hl) (hw k)

theorem main : H1 → H2 → OMA.R_Erdos233_erdos_233_variants_upper_bound_R1.H2 := by
  intro h1 h2 hRH
  obtain ⟨C₁, hC₁, h1_bd⟩ := h1
  obtain ⟨C₂, hC₂, h2_bd⟩ := h2
  refine ⟨C₂ * (C₁ ^ 2 * 120000), by positivity, fun x hx δ hδ0 hδ1 ↦ ?_⟩
  let ι := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}
  let γ : ι → ℝ := fun ρ ↦ ρ.1.im
  let c : ι → ℂ := fun ρ ↦
    (((1 + 2 * δ : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) + 1) /
      ((ρ : ℂ) * ((ρ : ℂ) + 1))
  let a : ι → ℂ := fun ρ ↦ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * c ρ
  let w : ℕ → ℝ := fun k ↦ min (δ ^ 2) (13 / max (3 / 4) ((k : ℝ) ^ 2))
  have hw0 : ∀ k, 0 ≤ w k := fun k ↦ le_min (sq_nonneg δ) (by positivity)
  have hre_half : ∀ ρ : ι, ρ.1.re = 1 / 2 := fun ρ ↦
    rh_re_eq_half hRH ρ.2.1 ρ.2.2.1 ρ.2.2.2
  have hc_le : ∀ ρ : ι, ‖c ρ‖ ≤ w ⌊|γ ρ|⌋₊ := fun ρ ↦ by
    refine le_min (second_diff_bound (hre_half ρ) hδ0 hδ1) ?_
    refine (tail_coeff_bound (hre_half ρ) hδ0 hδ1).trans ?_
    have hfl : (⌊|γ ρ|⌋₊ : ℝ) ≤ |γ ρ| := Nat.floor_le (abs_nonneg _)
    have hsq : (⌊|γ ρ|⌋₊ : ℝ) ^ 2 ≤ (γ ρ) ^ 2 := by
      calc (⌊|γ ρ|⌋₊ : ℝ) ^ 2 ≤ |γ ρ| ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hfl 2
        _ = (γ ρ) ^ 2 := sq_abs _
    have hmax : max (3 / 4 : ℝ) ((⌊|γ ρ|⌋₊ : ℝ) ^ 2) ≤ max (3 / 4) ((γ ρ) ^ 2) :=
      max_le_max le_rfl hsq
    exact div_le_div_of_nonneg_left (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) hmax
  have ha_le : ∀ ρ : ι, ‖a ρ‖ ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * w ⌊|γ ρ|⌋₊ := by
    intro ρ
    rw [show a ρ = (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * c ρ from rfl, norm_mul,
      Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hc_le ρ) (Nat.cast_nonneg _)
  have ha_sum : Summable (fun ρ : ι ↦ ‖a ρ‖) :=
    summable_zero_weighted h1_bd w hw0 (summable_log_tail C₁ hC₁.le hδ0)
      (fun ρ ↦ ‖a ρ‖) (fun _ ↦ norm_nonneg _) ha_le
  have hfun_eq : (fun y : ℝ =>
      ‖∑' ρ : ι, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * ((y : ℂ) ^ ((ρ : ℂ) + 1) * c ρ)‖ ^ 2) =
      (fun y : ℝ => ‖∑' ρ : ι, a ρ * (y : ℂ) ^ ((3 / 2 : ℂ) + (γ ρ : ℂ) * I)‖ ^ 2) := by
    funext y
    congr 2
    refine tsum_congr fun ρ ↦ ?_
    rw [cpow_one_add_re_half (hre_half ρ)]
    dsimp [a, γ]
    ring
  obtain ⟨hint, hms⟩ := h2_bd γ a ha_sum x hx
  rw [hfun_eq]
  refine ⟨hint, hms.trans ?_⟩
  obtain ⟨hsq_sum, hsq_bd⟩ := tail_sum_sq_bound hδ0 hδ1
  have hk_bd : ∀ k : ℕ,
      (∑' ρ : ι, if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then ‖a ρ‖ else 0) ^ 2 ≤
        C₁ ^ 2 * (Real.log ((k : ℝ) + 2) * w k) ^ 2 := by
    intro k
    obtain ⟨hsum_k, hbd_k⟩ := h1_bd k (Nat.cast_nonneg k)
    have hle_k : ∀ ρ : ι,
        (if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then ‖a ρ‖ else 0) ≤
          w k * (if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then
            (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0) := by
      intro ρ
      split_ifs with h
      · have hfl : ⌊|γ ρ|⌋₊ = k := (Nat.floor_eq_iff (abs_nonneg _)).mpr h
        rw [mul_comm]
        simpa [hfl] using ha_le ρ
      · rw [mul_zero]
    have hsum_ak : Summable (fun ρ : ι ↦
        if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then ‖a ρ‖ else 0) :=
      Summable.of_nonneg_of_le (fun _ ↦ by split_ifs <;> positivity) hle_k (hsum_k.mul_left _)
    have htsum_k : (∑' ρ : ι, if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then ‖a ρ‖ else 0) ≤
        C₁ * Real.log ((k : ℝ) + 2) * w k := by
      calc (∑' ρ : ι, if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then ‖a ρ‖ else 0)
          ≤ ∑' ρ : ι, w k * (if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then
              (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0) :=
            hsum_ak.tsum_le_tsum hle_k (hsum_k.mul_left _)
        _ = w k * ∑' ρ : ι, (if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then
              (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0) := tsum_mul_left
        _ ≤ w k * (C₁ * Real.log ((k : ℝ) + 2)) := mul_le_mul_of_nonneg_left hbd_k (hw0 k)
        _ = C₁ * Real.log ((k : ℝ) + 2) * w k := by ring
    have hnn_k : 0 ≤ ∑' ρ : ι, if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then ‖a ρ‖ else 0 :=
      tsum_nonneg fun _ ↦ by split_ifs <;> positivity
    calc (∑' ρ : ι, if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then ‖a ρ‖ else 0) ^ 2
        ≤ (C₁ * Real.log ((k : ℝ) + 2) * w k) ^ 2 := pow_le_pow_left₀ hnn_k htsum_k 2
      _ = C₁ ^ 2 * (Real.log ((k : ℝ) + 2) * w k) ^ 2 := by ring
  have hsum_lhs : Summable (fun k : ℕ ↦
      (∑' ρ : ι, if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then ‖a ρ‖ else 0) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) hk_bd (hsq_sum.mul_left _)
  have htsum_all : (∑' k : ℕ,
      (∑' ρ : ι, if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then ‖a ρ‖ else 0) ^ 2) ≤
      C₁ ^ 2 * (120000 * δ ^ 3 * Real.log (2 / δ) ^ 2) := by
    calc (∑' k : ℕ,
          (∑' ρ : ι, if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then ‖a ρ‖ else 0) ^ 2)
        ≤ ∑' k : ℕ, C₁ ^ 2 * (Real.log ((k : ℝ) + 2) * w k) ^ 2 :=
          hsum_lhs.tsum_le_tsum hk_bd (hsq_sum.mul_left _)
      _ = C₁ ^ 2 * ∑' k : ℕ, (Real.log ((k : ℝ) + 2) * w k) ^ 2 := tsum_mul_left
      _ ≤ C₁ ^ 2 * (120000 * δ ^ 3 * Real.log (2 / δ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq_bd (sq_nonneg C₁)
  calc C₂ * x ^ 4 * ∑' k : ℕ,
        (∑' ρ : ι, if (k : ℝ) ≤ |γ ρ| ∧ |γ ρ| < (k : ℝ) + 1 then ‖a ρ‖ else 0) ^ 2
      ≤ C₂ * x ^ 4 * (C₁ ^ 2 * (120000 * δ ^ 3 * Real.log (2 / δ) ^ 2)) := by
        gcongr
    _ = C₂ * (C₁ ^ 2 * 120000) * x ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by ring

end OMA.R_Erdos233_erdos_233_variants_upper_bound_R1_H2_R1

