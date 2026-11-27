import FormalConjectures.ErdosProblems.«5»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The three normalized averages are obtained from the two sieve moments and
Gallagher's mean singular series in Section 3 of Goldston, Motohashi,
Pintz and Yıldırım, arXiv:math/0505300. The joint normalization includes
the factor for unordered tuples. The proof chooses a fixed sieve exponent
below 1/4, derives a positive average, and changes the logarithmic
normalization from the lower prime to its index using Chebyshev's bound.
-/

-- Credit: @dk8827

open Filter Finset Real
open scoped Topology BigOperators ArithmeticFunction.Moebius

namespace OMA.R_Erdos5_erdos_5_variants_goldston_pintz_yildirim_R1

private theorem log_le_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ √x := by
  have h : 0 < √x / 2 := by positivity
  have heq : Real.log (√x / 2) = Real.log x / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx.le]
  linarith only [Real.log_le_sub_one_of_pos h, heq, Real.log_two_lt_d9]

private theorem prime_count_lower {x : ℝ} (hx : 256 ≤ x) :
    x / (4 * Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx1 : 1 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hlogx : Real.log (x + 2) ≤ x / 8 := by
    apply (log_le_sqrt (by linarith : 0 < x + 2)).trans
    apply Real.sqrt_le_iff.2
    refine ⟨by linarith, ?_⟩
    nlinarith only [hx, mul_nonneg (show 0 ≤ x - 256 by linarith) (show 0 ≤ x by linarith)]
  have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
    (show 0 ≤ x - 1 by linarith)
  have hnum : x / 4 ≤ (x - 1) * Real.log 2 - Real.log (x + 2) :=
    by linarith only [hmul, hlogx, hx]
  calc
    x / (4 * Real.log x) = (x / 4) / Real.log x := by ring
    _ ≤ _ := (div_le_div_of_nonneg_right hnum hL.le).trans (Chebyshev.pi_ge' hx1)

private theorem nth_prime_polynomial {i : ℕ} (hi : 16 ≤ i) :
    i.nth Nat.Prime ≤ i ^ 4 := by
  let x : ℝ := (i : ℝ) ^ 4
  have hir : (16 : ℝ) ≤ i := by exact_mod_cast hi
  have hix : 256 ≤ x := by
    dsimp [x]
    calc
      _ ≤ (16 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := by gcongr
  have hxfloor : ⌊x⌋₊ = i ^ 4 := by rw [show x = ((i ^ 4 : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]
  have hl0 : 0 < log x := Real.log_pos (by linarith)
  have hsq : √x = (i : ℝ) ^ 2 := by
    rw [show x = ((i : ℝ) ^ 2) ^ 2 by dsimp [x]; ring, Real.sqrt_sq (by positivity)]
  have hlog : log x ≤ (i : ℝ) ^ 2 := hsq ▸ log_le_sqrt (by linarith : 0 < x)
  have hstart : (i : ℝ) + 1 ≤ (i : ℝ) ^ 2 / 4 := by
    nlinarith only [hir, mul_nonneg (show 0 ≤ (i : ℝ) - 16 by linarith) (show 0 ≤ (i : ℝ) by positivity)]
  have hfrac : (i : ℝ) ^ 2 / 4 ≤ x / (4 * log x) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * log x)).2
    calc
      _ = (i : ℝ) ^ 2 * log x := by ring
      _ ≤ (i : ℝ) ^ 2 * (i : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = x := by dsimp [x]; ring
  have hcnt := hstart.trans (hfrac.trans (prime_count_lower hix))
  rw [hxfloor] at hcnt
  have hcard : i + 1 ≤ Nat.primeCounting (i ^ 4) := by exact_mod_cast hcnt
  have h := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := i ^ 4 + 1) (by
    rw [← Nat.primeCounting', ← Nat.primeCounting]
    omega : i < Nat.count Nat.Prime (i ^ 4 + 1))
  omega

private theorem coefficients (η : ℝ) (hη : 0 < η) :
    ∃ (k l : ℕ) (r : ℝ), 0 < k ∧ 0 < l ∧ 0 < r ∧ r < 1 / 4 ∧
      0 < η + (k : ℝ) / (k + 2 * l + 1) * (2 * (2 * l + 1) / (l + 1)) * r - 1 := by
  obtain ⟨t, ht⟩ := exists_nat_gt (4 / η + 1)
  have ht₀ : (0 : ℝ) < t := by linarith only [ht, div_pos (by norm_num : (0 : ℝ) < 4) hη]
  let u : ℝ := t / ((t : ℝ) + 1)
  have hu₀ : 0 < u := by dsimp only [u]; positivity
  have hu₁ : u < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have hs : 4 / ((t : ℝ) + 1) < η := by
    apply (div_lt_iff₀ (by positivity)).2
    have hh := (div_lt_iff₀ hη).1 (show 4 / η < (t : ℝ) + 1 by linarith only [ht])
    simpa only [mul_comm] using hh
  have hgap : (1 - u) = 1 / ((t : ℝ) + 1) := by dsimp only [u]; field_simp; ring
  have hu4 : 1 - u ^ 4 ≤ 4 * (1 - u) := by
    have hu2 : u ^ 2 ≤ 1 := pow_le_one₀ hu₀.le hu₁.le
    have hu3 : u ^ 3 ≤ 1 := pow_le_one₀ hu₀.le hu₁.le
    calc
      _ = (1 - u) * (1 + u + u ^ 2 + u ^ 3) := by ring
      _ ≤ _ := by rw [mul_comm 4]; gcongr; linarith only [hu₁, hu2, hu3]
  have hv : u ≤ (2 * (t : ℝ) + 1) / (2 * ((t : ℝ) + 1)) := by
    dsimp only [u]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [ht₀]
  have hk : (t : ℝ) ^ 2 / ((t : ℝ) ^ 2 + 2 * t + 1) = u ^ 2 := by
    dsimp only [u]
    rw [div_pow]
    congr 1
    ring
  have he : (t : ℝ) ^ 2 / ((t : ℝ) ^ 2 + 2 * t + 1) *
      (2 * (2 * t + 1) / (t + 1)) * (u / 4) =
      u ^ 3 * ((2 * (t : ℝ) + 1) / (2 * ((t : ℝ) + 1))) := by
    rw [hk]
    field_simp
    ring
  have hterm := mul_le_mul_of_nonneg_left hv (pow_nonneg hu₀.le 3)
  have hterm' : u ^ 4 ≤ u ^ 3 * ((2 * (t : ℝ) + 1) / (2 * ((t : ℝ) + 1))) := by
    rwa [← pow_succ] at hterm
  refine ⟨t ^ 2, t, u / 4, pow_pos (by exact_mod_cast ht₀) _, by exact_mod_cast ht₀, by positivity, by linarith, ?_⟩
  push_cast
  rw [he]
  rw [hgap, ← mul_div_assoc] at hu4
  norm_num at hu4
  linarith only [hs, hu4, hterm']

private theorem log_multiplier :
    Tendsto (fun N : ℕ => log (3 * (N : ℝ)) / log (N : ℝ)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun N : ℕ => log 3 / log (N : ℝ)) atTop (𝓝 0) :=
    by simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := log 3)).mul (tendsto_inv_atTop_zero.comp hlog)
  apply (by simpa using tendsto_const_nhds.add hs :
    Tendsto (fun N : ℕ => 1 + log 3 / log (N : ℝ)) atTop (𝓝 1)).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  rw [Real.log_mul (by norm_num) (by positivity), add_div, div_self (Real.log_pos hN').ne']
  ring

/-- The unweighted second moment, averaged over all tuples. -/
def H1 : Prop :=
  ∀ (η r : ℝ), 0 < η → η ≤ 1 → 0 < r → r < 1 / 4 →
  ∀ k l : ℕ, 0 < k → 0 < l →
  let h (N : ℕ) : ℕ := ⌊η * log (N : ℝ)⌋₊
  let R (N : ℕ) : ℝ := (N : ℝ) ^ r
  let T (N : ℕ) := (Icc 1 (h N)).powersetCard k
  let w (N n : ℕ) (S : Finset ℕ) : ℝ :=
    ((∑ d ∈ (Icc 1 ⌊R N⌋₊).filter (fun d => d ∣ ∏ a ∈ S, (n + a)),
        (μ d : ℝ) * (log (R N / d)) ^ (k + l)) / (Nat.factorial (k + l) : ℝ)) ^ 2
  let C (N : ℕ) : ℝ := (N : ℝ) * (h N : ℝ) ^ k * (log (R N)) ^ (k + 2 * l) *
    (Nat.choose (2 * l) l : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (k + 2 * l) : ℝ))
  Tendsto (fun N => (∑ S ∈ T N, ∑ n ∈ Ioc N (2 * N), w N n S) / C N) atTop (𝓝 1)

/-- The prime-weighted moment for shifts outside the tuple. -/
def H2 : Prop :=
  ∀ (η r : ℝ), 0 < η → η ≤ 1 → 0 < r → r < 1 / 4 →
  ∀ k l : ℕ, 0 < k → 0 < l →
  let h (N : ℕ) : ℕ := ⌊η * log (N : ℝ)⌋₊
  let R (N : ℕ) : ℝ := (N : ℝ) ^ r
  let T (N : ℕ) := (Icc 1 (h N)).powersetCard k
  let w (N n : ℕ) (S : Finset ℕ) : ℝ :=
    ((∑ d ∈ (Icc 1 ⌊R N⌋₊).filter (fun d => d ∣ ∏ a ∈ S, (n + a)),
        (μ d : ℝ) * (log (R N / d)) ^ (k + l)) / (Nat.factorial (k + l) : ℝ)) ^ 2
  let C (N : ℕ) : ℝ := (N : ℝ) * (h N : ℝ) ^ k * (log (R N)) ^ (k + 2 * l) *
    (Nat.choose (2 * l) l : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (k + 2 * l) : ℝ))
  Tendsto (fun N => (∑ S ∈ T N, ∑ n ∈ Ioc N (2 * N),
      (∑ a ∈ Icc 1 (h N) \ S, if (n + a).Prime then log ((n + a : ℕ) : ℝ) else 0) *
         w N n S) / (C N * log (N : ℝ))) atTop (𝓝 η)

/-- The prime-weighted moment for shifts inside the tuple. -/
def H3 : Prop :=
  ∀ (η r : ℝ), 0 < η → η ≤ 1 → 0 < r → r < 1 / 4 →
  ∀ k l : ℕ, 0 < k → 0 < l →
  let h (N : ℕ) : ℕ := ⌊η * log (N : ℝ)⌋₊
  let R (N : ℕ) : ℝ := (N : ℝ) ^ r
  let T (N : ℕ) := (Icc 1 (h N)).powersetCard k
  let w (N n : ℕ) (S : Finset ℕ) : ℝ :=
    ((∑ d ∈ (Icc 1 ⌊R N⌋₊).filter (fun d => d ∣ ∏ a ∈ S, (n + a)),
        (μ d : ℝ) * (log (R N / d)) ^ (k + l)) / (Nat.factorial (k + l) : ℝ)) ^ 2
  let C (N : ℕ) : ℝ := (N : ℝ) * (h N : ℝ) ^ k * (log (R N)) ^ (k + 2 * l) *
    (Nat.choose (2 * l) l : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (k + 2 * l) : ℝ))
  Tendsto (fun N => (∑ S ∈ T N, ∑ n ∈ Ioc N (2 * N),
      (∑ a ∈ S, if (n + a).Prime then log ((n + a : ℕ) : ℝ) else 0) *
         w N n S) / (C N * log (N : ℝ))) atTop
      (𝓝 ((k : ℝ) / (k + 2 * l + 1) * (2 * (2 * l + 1) / (l + 1)) * r))

set_option maxHeartbeats 1400000 in
theorem main : H1 → H2 → H3 → type_of% @Erdos5.erdos_5.variants.goldston_pintz_yildirim := by
  classical
  intro mass outside inside
  change MapClusterPt 0 atTop Erdos5.normalizedGap
  rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently]
  intro ε hε
  rw [frequently_atTop]
  intro i₀
  let η : ℝ := min 1 (ε / 8)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη₁ : η ≤ 1 := min_le_left _ _
  obtain ⟨k, l, r, hk, hl, hr, hr₄, hcoeff⟩ := coefficients η hη
  let h (N : ℕ) : ℕ := ⌊η * log (N : ℝ)⌋₊
  let R (N : ℕ) : ℝ := (N : ℝ) ^ r
  let T (N : ℕ) := (Icc 1 (h N)).powersetCard k
  let w (N n : ℕ) (S : Finset ℕ) : ℝ :=
    ((∑ d ∈ (Icc 1 ⌊R N⌋₊).filter (fun d => d ∣ ∏ a ∈ S, (n + a)),
        (μ d : ℝ) * (log (R N / d)) ^ (k + l)) / (Nat.factorial (k + l) : ℝ)) ^ 2
  let C (N : ℕ) : ℝ := (N : ℝ) * (h N : ℝ) ^ k * (log (R N)) ^ (k + 2 * l) *
    (Nat.choose (2 * l) l : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (k + 2 * l) : ℝ))
  let θ (n a : ℕ) : ℝ := if (n + a).Prime then log ((n + a : ℕ) : ℝ) else 0
  let A (N : ℕ) : ℝ := ∑ S ∈ T N, ∑ n ∈ Ioc N (2 * N), w N n S
  let B (N : ℕ) : ℝ := ∑ S ∈ T N, ∑ n ∈ Ioc N (2 * N),
    (∑ a ∈ Icc 1 (h N) \ S, θ n a) * w N n S
  let D (N : ℕ) : ℝ := ∑ S ∈ T N, ∑ n ∈ Ioc N (2 * N),
    (∑ a ∈ S, θ n a) * w N n S
  have hA : Tendsto (fun N => A N / C N) atTop (𝓝 1) := mass η r hη hη₁ hr hr₄ k l hk hl
  have hB : Tendsto (fun N => B N / (C N * log (N : ℝ))) atTop (𝓝 η) :=
    outside η r hη hη₁ hr hr₄ k l hk hl
  have hD : Tendsto (fun N => D N / (C N * log (N : ℝ))) atTop
      (𝓝 ((k : ℝ) / (k + 2 * l + 1) * (2 * (2 * l + 1) / (l + 1)) * r)) :=
    inside η r hη hη₁ hr hr₄ k l hk hl
  have hlim := (hB.add hD).sub (hA.mul log_multiplier)
  rw [mul_one] at hlim
  have hpositive := hlim.eventually (Ioi_mem_nhds hcoeff)
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let iMin := max 16 i₀
  obtain ⟨N, hN₂, hNlarge, hNlog, hNpos⟩ :=
    ((eventually_ge_atTop (2 : ℕ)).and ((eventually_ge_atTop (iMin.nth Nat.Prime)).and
      ((hlogTop.eventually_ge_atTop (1 / η)).and hpositive))).exists
  have hN₁ : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNlog₀ := Real.log_pos hN₁
  have hH₀ : 0 < h N := by
    have hs : (1 : ℝ) ≤ η * log (N : ℝ) := by
      have hh := (div_le_iff₀ hη).1 hNlog
      rwa [mul_comm] at hh
    exact (Nat.le_floor (by simpa only [Nat.cast_one] using hs) : 1 ≤ h N)
  have hHle : (h N : ℝ) ≤ η * log (N : ℝ) := Nat.floor_le (by positivity)
  have hHN : h N ≤ N := by
    have hx := mul_le_mul_of_nonneg_right hη₁ hNlog₀.le
    have hy := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by positivity)
    exact_mod_cast (show (h N : ℝ) ≤ N by linarith only [hHle, hx, hy])
  have hR₁ : 1 < R N := Real.one_lt_rpow hN₁ hr
  have hlogR := Real.log_pos hR₁
  have hchoose : 0 < Nat.choose (2 * l) l := Nat.choose_pos (by omega)
  have hC : 0 < C N := by dsimp only [C]; positivity
  have hnorm : 0 < C N * log (N : ℝ) := mul_pos hC hNlog₀
  have hNpos' : 0 < B N + D N - log (3 * (N : ℝ)) * A N := by
    change 0 < B N / (C N * log (N : ℝ)) + D N / (C N * log (N : ℝ)) -
      A N / C N * (log (3 * (N : ℝ)) / log (N : ℝ)) at hNpos
    rw [← add_div, div_mul_div_comm, ← sub_div, mul_comm (A N)] at hNpos
    exact (div_pos_iff_of_pos_right hnorm).1 hNpos
  have hparts (S : Finset ℕ) (hS : S ∈ T N) (n : ℕ) :
      (∑ a ∈ Icc 1 (h N) \ S, θ n a) + (∑ a ∈ S, θ n a)
        = ∑ a ∈ Icc 1 (h N), θ n a :=
    sum_sdiff (mem_powersetCard.1 hS).1
  have hsum : B N + D N - log (3 * (N : ℝ)) * A N =
      ∑ S ∈ T N, ∑ n ∈ Ioc N (2 * N),
        ((∑ a ∈ Icc 1 (h N), θ n a) - log (3 * (N : ℝ))) * w N n S := by
    simp only [A, B, D]
    simp_rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib, ← add_mul, ← sub_mul]
    refine sum_congr rfl fun S hS => sum_congr rfl fun n _ => ?_
    rw [hparts S hS n]
  rw [hsum] at hNpos'
  obtain ⟨S, hS, hSn⟩ := exists_lt_of_sum_lt (s := T N) (f := fun _ => (0 : ℝ))
    (by simpa only [sum_const_zero] using hNpos')
  obtain ⟨n, hn, hnp⟩ := exists_lt_of_sum_lt (s := Ioc N (2 * N)) (f := fun _ => (0 : ℝ))
    (by simpa only [sum_const_zero] using hSn)
  have hpositive_shift : log (3 * (N : ℝ)) < ∑ a ∈ Icc 1 (h N), θ n a := by
    by_contra! hle
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hle)
      (show 0 ≤ w N n S by dsimp only [w]; positivity)
    have hpos : 0 < ((∑ a ∈ Icc 1 (h N), θ n a) - log (3 * (N : ℝ))) * w N n S := by
      simpa using hnp
    exact (not_lt_of_ge hnonpos) hpos
  let P := (Icc 1 (h N)).filter (fun a => (n + a).Prime)
  have hPcard : 1 < P.card := by
    have hp_sum : ∑ a ∈ P, log ((n + a : ℕ) : ℝ) =
        ∑ a ∈ Icc 1 (h N), θ n a := sum_filter _ _
    have hs : ∑ a ∈ P, log ((n + a : ℕ) : ℝ) ≤ (P.card : ℝ) * log (3 * (N : ℝ)) := by
      calc
        _ ≤ ∑ _ ∈ P, log (3 * (N : ℝ)) := by
          apply sum_le_sum
          intro a ha
          have ha' := mem_Icc.1 (mem_filter.1 ha).1
          have hna : n + a ≤ 3 * N := by
            have := (mem_Ioc.1 hn).2
            omega
          have hna₀ : (0 : ℝ) < ((n + a : ℕ) : ℝ) := by
            have := (mem_Ioc.1 hn).1
            exact_mod_cast (show 0 < n + a by omega)
          apply Real.log_le_log hna₀
          exact_mod_cast hna
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    by_contra! hle
    have hle' : (P.card : ℝ) ≤ 1 := by exact_mod_cast hle
    have hlog₃ : 0 ≤ log (3 * (N : ℝ)) := Real.log_nonneg (by linarith)
    have hh := mul_le_mul_of_nonneg_right hle' hlog₃
    rw [hp_sum] at hs
    linarith only [hs, hh, hpositive_shift]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 hPcard
  wlog hab' : a < b generalizing a b
  · exact this b hb a ha hab.symm (by omega)
  have ha' := mem_Icc.1 (mem_filter.1 ha).1
  have hb' := mem_Icc.1 (mem_filter.1 hb).1
  have hpa := (mem_filter.1 ha).2
  have hpb := (mem_filter.1 hb).2
  obtain ⟨i, hi⟩ : ∃ i : ℕ, i.nth Nat.Prime = n + a :=
    Nat.subset_range_nth hpa
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j.nth Nat.Prime = n + b :=
    Nat.subset_range_nth hpb
  have hnth := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hiaj : i < j := hnth.lt_iff_lt.1 (by rw [hi, hj]; omega)
  have hnext : (i + 1).nth Nat.Prime ≤ n + b := hj ▸ hnth.monotone (by omega)
  have hiM : iMin < i := hnth.lt_iff_lt.1 (show iMin.nth Nat.Prime < i.nth Nat.Prime by
    rw [hi]
    have := (mem_Ioc.1 hn).1
    omega)
  have hi₁ : 16 ≤ i := (le_max_left 16 i₀).trans hiM.le
  have hi₀ : i₀ ≤ i := (le_max_right 16 i₀).trans hiM.le
  have hgap : primeGap i ≤ h N := by
    unfold primeGap
    omega
  have hNle : N ≤ i ^ 4 := by
    have hh := nth_prime_polynomial hi₁
    rw [hi] at hh
    have := (mem_Ioc.1 hn).1
    omega
  have hlogi : 0 < log (i : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < i by omega))
  have hNlogi : log (N : ℝ) ≤ 4 * log (i : ℝ) := by
    have hle : (N : ℝ) ≤ (i : ℝ) ^ 4 := by exact_mod_cast hNle
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (show (0 : ℝ) < N by positivity) hle
  have hnormalized : Erdos5.normalizedGap i ≤ 4 * η := by
    apply (div_le_iff₀ hlogi).2
    have hgap' : (primeGap i : ℝ) ≤ h N := by exact_mod_cast hgap
    have hh := mul_le_mul_of_nonneg_left hNlogi hη.le
    linarith only [hgap', hHle, hh]
  refine ⟨i, hi₀, ?_⟩
  have hηε : η ≤ ε / 8 := min_le_right _ _
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (Erdos5.normalizedGap_nonneg i)]
  linarith only [hnormalized, hηε, hε]

end OMA.R_Erdos5_erdos_5_variants_goldston_pintz_yildirim_R1
