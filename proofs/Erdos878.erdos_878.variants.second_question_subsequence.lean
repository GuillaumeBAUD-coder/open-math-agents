import FormalConjectures.ErdosProblems.«878»

/-!
# A subsequence for the maximal order of the prime-power sum

Specialize the full endpoint limit to the identity sequence. The proof of that limit is
adapted and dependency-pruned from Kenta Kitamura's Apache-2.0 formalization:
https://github.com/KitaKen1/erdos-878-lean/blob/d4a8eecf0606b3eee7342c2040a31c8c30eb5d76/lean4web/PartsIILean4Web.lean .

Copyright (c) 2026 Kenta Kitamura, Gershon Bialer, Arend Mellendijk, Math Inc., Evan Chen,
Kenny Lau, Seewoo Lee, Ken Ono, and Jujian Zhang. Released under the Apache License 2.0.
-/
open Filter

open scoped BigOperators Topology
section

namespace Local878.TrackB

open Set Filter

open scoped Topology

noncomputable section

def reciprocalLogPhase (a n x : ℝ) : ℝ := a / Real.log (n * x)

def reciprocalLogSlope (a n x : ℝ) : ℝ := -a / (x * Real.log (n * x) ^ 2)

def logCurvature (z : ℝ) : ℝ := 1 / z ^ 2 + 2 / z ^ 3

def logCurvatureRate (z : ℝ) : ℝ := 2 / z ^ 3 + 6 / z ^ 4

def reciprocalLogCorrelation (a n₁ n₂ x : ℝ) : ℝ :=
  reciprocalLogPhase a n₁ x - reciprocalLogPhase a n₂ x

theorem hasDerivAt_log_mul (n x : ℝ) (hn : n ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (fun y ↦ Real.log (n * y)) (1 / x) x := by
  have h := ((hasDerivAt_id x).const_mul n).log (mul_ne_zero hn hx)
  convert h using 1 <;> first | rfl | (dsimp only [id_eq]; field_simp)

theorem hasDerivAt_reciprocalLogPhase (a n x : ℝ) (hn : 0 < n)
    (hx : 0 < x) (hnx : 1 < n * x) :
    HasDerivAt (reciprocalLogPhase a n) (reciprocalLogSlope a n x) x := by
  have hl : Real.log (n * x) ≠ 0 := (Real.log_pos hnx).ne'
  have h := (hasDerivAt_const x a).div (hasDerivAt_log_mul n x hn.ne' hx.ne') hl
  convert h using 1 <;> first | rfl | (unfold reciprocalLogSlope; ring)

theorem hasDerivAt_reciprocalLogSlope (a n x : ℝ) (hn : 0 < n)
    (hx : 0 < x) (hnx : 1 < n * x) :
    HasDerivAt (reciprocalLogSlope a n)
      (a / x ^ 2 * logCurvature (Real.log (n * x))) x := by
  have hl : Real.log (n * x) ≠ 0 := (Real.log_pos hnx).ne'
  have hden := (hasDerivAt_id x).mul ((hasDerivAt_log_mul n x hn.ne' hx.ne').pow 2)
  have h := (hasDerivAt_const x (-a)).div hden (mul_ne_zero hx.ne' (pow_ne_zero 2 hl))
  convert h using 1 <;> first | rfl |
    (unfold logCurvature; dsimp; field_simp; ring)

theorem deriv2_reciprocalLogCorrelation (a n₁ n₂ x : ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hx : 0 < x)
    (hprod₁ : 1 < n₁ * x) (hprod₂ : 1 < n₂ * x) :
    deriv (deriv (reciprocalLogCorrelation a n₁ n₂)) x =
      a / x ^ 2 * (logCurvature (Real.log (n₁ * x)) -
        logCurvature (Real.log (n₂ * x))) := by
  have hs := (hasDerivAt_reciprocalLogSlope a n₁ x hn₁ hx hprod₁).sub
    (hasDerivAt_reciprocalLogSlope a n₂ x hn₂ hx hprod₂)
  have heq : deriv (reciprocalLogCorrelation a n₁ n₂) =ᶠ[𝓝 x]
      (fun y ↦ reciprocalLogSlope a n₁ y - reciprocalLogSlope a n₂ y) := by
    have hp₁ : ∀ᶠ y in 𝓝 x, 1 < n₁ * y :=
      (continuousAt_const.mul continuousAt_id).eventually_const_lt hprod₁
    have hp₂ : ∀ᶠ y in 𝓝 x, 1 < n₂ * y :=
      (continuousAt_const.mul continuousAt_id).eventually_const_lt hprod₂
    filter_upwards [eventually_gt_nhds hx, hp₁, hp₂] with y hy h₁ h₂
    exact ((hasDerivAt_reciprocalLogPhase a n₁ y hn₁ hy h₁).sub
      (hasDerivAt_reciprocalLogPhase a n₂ y hn₂ hy h₂)).deriv
  rw [heq.deriv_eq]
  calc
    _ = a / x ^ 2 * logCurvature (Real.log (n₁ * x)) -
        a / x ^ 2 * logCurvature (Real.log (n₂ * x)) := hs.deriv
    _ = _ := by ring

theorem hasDerivAt_logCurvature (z : ℝ) (hz : 0 < z) :
    HasDerivAt logCurvature (-logCurvatureRate z) z := by
  have h₂ := (hasDerivAt_const z (1 : ℝ)).div ((hasDerivAt_id z).pow 2)
    (pow_ne_zero 2 hz.ne')
  have h₃ := (hasDerivAt_const z (2 : ℝ)).div ((hasDerivAt_id z).pow 3)
    (pow_ne_zero 3 hz.ne')
  convert h₂.add h₃ using 1 <;> first | rfl |
    (unfold logCurvatureRate; dsimp; field_simp; ring)

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Set

noncomputable section

theorem logCurvature_bounds (L z : ℝ) (hL : 1 ≤ L) (hzL : L ≤ z)
    (hzU : z ≤ 2 * L) :
    1 / (4 * L ^ 2) ≤ logCurvature z ∧ logCurvature z ≤ 3 / L ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hzpos : 0 < z := hLpos.trans_le hzL
  have hl : 1 / (2 * L) ^ 2 ≤ 1 / z ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hzpos 2)
      (pow_le_pow_left₀ hzpos.le hzU 2)
  have hu₂ : 1 / z ^ 2 ≤ 1 / L ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos 2)
      (pow_le_pow_left₀ hLpos.le hzL 2)
  have hu₃ : 2 / z ^ 3 ≤ 2 / L ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos 2)
      ((pow_le_pow_right₀ hL (show 2 ≤ 3 by norm_num)).trans
        (pow_le_pow_left₀ hLpos.le hzL 3))
  constructor
  · calc
      1 / (4 * L ^ 2) = 1 / (2 * L) ^ 2 := by ring
      _ ≤ 1 / z ^ 2 := hl
      _ ≤ logCurvature z := le_add_of_nonneg_right (by positivity)
  · unfold logCurvature
    calc
      1 / z ^ 2 + 2 / z ^ 3 ≤ 1 / L ^ 2 + 2 / L ^ 2 := add_le_add hu₂ hu₃
      _ = 3 / L ^ 2 := by ring

theorem logCurvatureRate_bounds (L z : ℝ) (hL : 1 ≤ L) (hzL : L ≤ z)
    (hzU : z ≤ 2 * L) :
    1 / (4 * L ^ 3) ≤ logCurvatureRate z ∧ logCurvatureRate z ≤ 8 / L ^ 3 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hzpos : 0 < z := hLpos.trans_le hzL
  have hlower : 2 / (2 * L) ^ 3 ≤ 2 / z ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hzpos 3)
      (pow_le_pow_left₀ hzpos.le hzU 3)
  have hu₃ : 2 / z ^ 3 ≤ 2 / L ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos 3)
      (pow_le_pow_left₀ hLpos.le hzL 3)
  have hu₄ : 6 / z ^ 4 ≤ 6 / L ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos 3)
      ((pow_le_pow_right₀ hL (show 3 ≤ 4 by norm_num)).trans
        (pow_le_pow_left₀ hLpos.le hzL 4))
  constructor
  · calc
      1 / (4 * L ^ 3) = 2 / (2 * L) ^ 3 := by ring
      _ ≤ 2 / z ^ 3 := hlower
      _ ≤ logCurvatureRate z := le_add_of_nonneg_right (by positivity)
  · unfold logCurvatureRate
    calc
      2 / z ^ 3 + 6 / z ^ 4 ≤ 2 / L ^ 3 + 6 / L ^ 3 := add_le_add hu₃ hu₄
      _ = 8 / L ^ 3 := by ring

theorem logCurvature_sub_bounds (L s t : ℝ) (hL : 1 ≤ L) (hs : L ≤ s)
    (hst : s ≤ t) (ht : t ≤ 2 * L) :
    (t - s) / (4 * L ^ 3) ≤ logCurvature s - logCurvature t ∧
      logCurvature s - logCurvature t ≤ 8 * (t - s) / L ^ 3 := by
  rcases lt_or_eq_of_le hst with hst' | rfl
  · have hspos : 0 < s := (lt_of_lt_of_le zero_lt_one hL).trans_le hs
    have hcont : ContinuousOn logCurvature (Icc s t) := by
      intro z hz
      exact (hasDerivAt_logCurvature z (hspos.trans_le hz.1)).continuousAt.continuousWithinAt
    obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope logCurvature
      (fun z ↦ -logCurvatureRate z) hst' hcont
      (fun z hz ↦ hasDerivAt_logCurvature z (hspos.trans hz.1))
    have heq : logCurvature s - logCurvature t = logCurvatureRate z * (t - s) := by
      have hh := (eq_div_iff (sub_ne_zero.mpr hst'.ne')).mp he
      nlinarith [hh]
    have hb := logCurvatureRate_bounds L z hL (hs.trans hz.1.le) (hz.2.le.trans ht)
    rw [heq]
    constructor
    · convert mul_le_mul_of_nonneg_right hb.1 (sub_nonneg.mpr hst) using 1 <;> first | rfl | ring
    · convert mul_le_mul_of_nonneg_right hb.2 (sub_nonneg.mpr hst) using 1 <;> first | rfl | ring
  · simp

theorem log_sub_bounds (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (v - u) / v ≤ Real.log v - Real.log u ∧
      Real.log v - Real.log u ≤ (v - u) / u := by
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hv hu)
  have hr := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne'] at hl hr
  have hleft : 1 - (v / u)⁻¹ = (v - u) / v := by field_simp
  have hright : v / u - 1 = (v - u) / u := by field_simp
  exact ⟨hleft ▸ hl, hright ▸ hr⟩

theorem log_sub_bounds_on_dyadic (N u v : ℝ) (hN : 0 < N) (hu : N ≤ u)
    (huv : u ≤ v) (hv : v ≤ 2 * N) :
    (v - u) / (2 * N) ≤ Real.log v - Real.log u ∧
      Real.log v - Real.log u ≤ (v - u) / N := by
  have hupos := hN.trans_le hu
  have hvpos := hupos.trans_le huv
  have hb := log_sub_bounds u v hupos hvpos
  exact ⟨(div_le_div_of_nonneg_left (sub_nonneg.mpr huv) hvpos hv).trans hb.1,
    hb.2.trans (div_le_div_of_nonneg_left (sub_nonneg.mpr huv) hN hu)⟩

theorem logCurvature_log_gap_bounds (L N n₁ n₂ x : ℝ) (hL : 1 ≤ L)
    (hN : 0 < N) (hn₁ : N ≤ n₁) (hn₁₂ : n₁ ≤ n₂) (hn₂ : n₂ ≤ 2 * N)
    (hx : 0 < x) (hlow : L ≤ Real.log (n₁ * x)) (hhigh : Real.log (n₂ * x) ≤ 2 * L) :
    (n₂ - n₁) / (8 * N * L ^ 3) ≤
        logCurvature (Real.log (n₁ * x)) - logCurvature (Real.log (n₂ * x)) ∧
      logCurvature (Real.log (n₁ * x)) - logCurvature (Real.log (n₂ * x)) ≤
        8 * (n₂ - n₁) / (N * L ^ 3) := by
  have hn₁pos := hN.trans_le hn₁
  have hn₂pos := hn₁pos.trans_le hn₁₂
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlogs : Real.log (n₁ * x) ≤ Real.log (n₂ * x) :=
    Real.log_le_log (mul_pos hn₁pos hx) (mul_le_mul_of_nonneg_right hn₁₂ hx.le)
  have hdiff : Real.log (n₂ * x) - Real.log (n₁ * x) = Real.log n₂ - Real.log n₁ := by
    rw [Real.log_mul hn₂pos.ne' hx.ne', Real.log_mul hn₁pos.ne' hx.ne']
    ring
  have hw := logCurvature_sub_bounds L _ _ hL hlow hlogs hhigh
  rw [hdiff] at hw
  have hg := log_sub_bounds_on_dyadic N n₁ n₂ hN hn₁ hn₁₂ hn₂
  constructor
  · calc
      (n₂ - n₁) / (8 * N * L ^ 3) = ((n₂ - n₁) / (2 * N)) / (4 * L ^ 3) := by ring
      _ ≤ (Real.log n₂ - Real.log n₁) / (4 * L ^ 3) :=
        div_le_div_of_nonneg_right hg.1 (by positivity)
      _ ≤ _ := hw.1
  · calc
      _ ≤ 8 * (Real.log n₂ - Real.log n₁) / L ^ 3 := hw.2
      _ ≤ 8 * ((n₂ - n₁) / N) / L ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg.2 (by norm_num)) (by positivity)
      _ = _ := by ring

theorem deriv2_reciprocalLogCorrelation_bounds (a L M N n₁ n₂ x : ℝ)
    (ha : 0 ≤ a) (hL : 1 ≤ L) (hM : 0 < M) (hN : 0 < N)
    (hxlo : M ≤ x) (hxhi : x ≤ 2 * M)
    (hnlo : N ≤ n₁) (hnord : n₁ ≤ n₂) (hnhi : n₂ ≤ 2 * N)
    (hloglo : L ≤ Real.log (n₁ * x)) (hloghi : Real.log (n₂ * x) ≤ 2 * L) :
    a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3) ≤
        deriv (deriv (reciprocalLogCorrelation a n₁ n₂)) x ∧
      deriv (deriv (reciprocalLogCorrelation a n₁ n₂)) x ≤
        8 * a * (n₂ - n₁) / (N * M ^ 2 * L ^ 3) := by
  have hx := hM.trans_le hxlo
  have hn₁ := hN.trans_le hnlo
  have hn₂ := hn₁.trans_le hnord
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hprod₁ : 1 < n₁ * x :=
    (Real.log_pos_iff (mul_nonneg hn₁.le hx.le)).mp (hLpos.trans_le hloglo)
  have hprod₂ : 1 < n₂ * x := hprod₁.trans_le (mul_le_mul_of_nonneg_right hnord hx.le)
  rw [deriv2_reciprocalLogCorrelation a n₁ n₂ x hn₁ hn₂ hx hprod₁ hprod₂]
  have hw := logCurvature_log_gap_bounds L N n₁ n₂ x hL hN hnlo hnord hnhi hx hloglo hloghi
  have hd : 0 ≤ n₂ - n₁ := sub_nonneg.mpr hnord
  have hwpos : 0 ≤ logCurvature (Real.log (n₁ * x)) - logCurvature (Real.log (n₂ * x)) :=
    (by positivity : 0 ≤ (n₂ - n₁) / (8 * N * L ^ 3)).trans hw.1
  have hl : a / (4 * M ^ 2) ≤ a / x ^ 2 := by
    calc
      a / (4 * M ^ 2) = a / (2 * M) ^ 2 := by ring
      _ ≤ a / x ^ 2 := div_le_div_of_nonneg_left ha (pow_pos hx 2)
        (pow_le_pow_left₀ hx.le hxhi 2)
  have hu : a / x ^ 2 ≤ a / M ^ 2 := div_le_div_of_nonneg_left ha (pow_pos hM 2)
    (pow_le_pow_left₀ hM.le hxlo 2)
  constructor
  · convert mul_le_mul hl hw.1 (by positivity) (by positivity) using 1 <;> first | rfl | ring
  · convert mul_le_mul hu hw.2 hwpos (by positivity) using 1 <;> first | rfl | ring

end

end Local878.TrackB

end

section

namespace Local878

namespace TrackB

open scoped ArithmeticFunction BigOperators

noncomputable def lambdaLE (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n ≤ V then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

noncomputable def lambdaGT (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if V < n then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

noncomputable def muLE (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

noncomputable def muGT (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if U < n then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

@[simp] theorem lambdaLE_apply (V n : ℕ) :
    lambdaLE V n = if n ≤ V then ArithmeticFunction.vonMangoldt n else 0 :=
  rfl

@[simp] theorem lambdaGT_apply (V n : ℕ) :
    lambdaGT V n = if V < n then ArithmeticFunction.vonMangoldt n else 0 :=
  rfl

@[simp] theorem muLE_apply (U n : ℕ) :
    muLE U n = if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0 :=
  rfl

@[simp] theorem muGT_apply (U n : ℕ) :
    muGT U n = if U < n then (ArithmeticFunction.moebius n : ℝ) else 0 :=
  rfl

theorem muLE_add_muGT (U : ℕ) :
    muLE U + muGT U = (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
  ext n
  by_cases hn : n ≤ U
  · have hnot : ¬ U < n := not_lt.mpr hn
    simp [hn, hnot]
  · have hlt : U < n := lt_of_not_ge hn
    simp [hn, hlt]

theorem lambdaLE_add_lambdaGT (V : ℕ) :
    lambdaLE V + lambdaGT V =
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) := by
  ext n
  by_cases hn : n ≤ V
  · have hnot : ¬ V < n := not_lt.mpr hn
    simp [hn, hnot]
  · have hlt : V < n := lt_of_not_ge hn
    simp [hn, hlt]

noncomputable def vaughanTypeILog (U : ℕ) : ArithmeticFunction ℝ :=
  muLE U * ArithmeticFunction.log

noncomputable def vaughanTypeILambda (U V : ℕ) : ArithmeticFunction ℝ :=
  muLE U * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLE V)

noncomputable def vaughanTypeII (U V : ℕ) : ArithmeticFunction ℝ :=
  lambdaGT V * (muGT U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))

theorem vaughan_identity_function (U V : ℕ) :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      lambdaLE V + vaughanTypeILog U - vaughanTypeILambda U V + vaughanTypeII U V := by
  have hMuZeta :
      (muLE U + muGT U) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 := by
    rw [muLE_add_muGT, ArithmeticFunction.coe_moebius_mul_coe_zeta]
  have hLambdaHigh :
      lambdaGT V = vaughanTypeILog U - vaughanTypeILambda U V + vaughanTypeII U V := by
    have hExpand :
        lambdaGT V = lambdaGT V *
            ((muLE U + muGT U) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
      rw [hMuZeta, mul_one]
    have hDistribute :
        lambdaGT V *
            ((muLE U + muGT U) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
          muLE U * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaGT V) +
            vaughanTypeII U V := by
      unfold vaughanTypeII
      ring
    have hLambdaHighEq :
        lambdaGT V =
          (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - lambdaLE V := by
      have hsplit := lambdaLE_add_lambdaGT V
      rw [← hsplit]
      abel
    have hFirst :
        muLE U * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaGT V) =
          vaughanTypeILog U - vaughanTypeILambda U V := by
      rw [hLambdaHighEq, mul_sub, ArithmeticFunction.zeta_mul_vonMangoldt]
      unfold vaughanTypeILog vaughanTypeILambda
      ring
    rw [hExpand, hDistribute, hFirst]
  rw [← lambdaLE_add_lambdaGT V, hLambdaHigh]
  abel

theorem vaughan_identity (U V n : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      lambdaLE V n + vaughanTypeILog U n - vaughanTypeILambda U V n +
        vaughanTypeII U V n := by
  have h := congrArg (fun a : ArithmeticFunction ℝ ↦ a n)
    (vaughan_identity_function U V)
  simpa only [ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, sub_eq_add_neg] using h

noncomputable def weightedArithmeticSum
    (I : Finset ℕ) (w : ℕ → ℂ) (a : ArithmeticFunction ℝ) : ℂ :=
  ∑ n ∈ I, (a n : ℂ) * w n

theorem vaughan_weighted_sum (U V : ℕ) (I : Finset ℕ) (w : ℕ → ℂ) :
    weightedArithmeticSum I w
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      weightedArithmeticSum I w (lambdaLE V) +
        weightedArithmeticSum I w (vaughanTypeILog U) -
        weightedArithmeticSum I w (vaughanTypeILambda U V) +
        weightedArithmeticSum I w (vaughanTypeII U V) := by
  unfold weightedArithmeticSum
  calc
    (∑ n ∈ I, ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n : ℂ) * w n) =
        ∑ n ∈ I,
          ((lambdaLE V n : ℂ) * w n +
            (vaughanTypeILog U n : ℂ) * w n -
            (vaughanTypeILambda U V n : ℂ) * w n +
            (vaughanTypeII U V n : ℂ) * w n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      have hreal := vaughan_identity U V n
      have hcomplex :
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) =
            (lambdaLE V n : ℂ) + (vaughanTypeILog U n : ℂ) -
              (vaughanTypeILambda U V n : ℂ) + (vaughanTypeII U V n : ℂ) := by
        exact_mod_cast hreal
      rw [hcomplex]
      ring
    _ = (∑ n ∈ I, (lambdaLE V n : ℂ) * w n) +
          (∑ n ∈ I, (vaughanTypeILog U n : ℂ) * w n) -
          (∑ n ∈ I, (vaughanTypeILambda U V n : ℂ) * w n) +
          (∑ n ∈ I, (vaughanTypeII U V n : ℂ) * w n) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

end TrackB

end Local878

end

section

namespace Local878.TrackB

open Finset

noncomputable section

theorem sum_Icc_inv_le_one_add_log (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, ((d : ℝ))⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have heq : ((harmonic N : ℚ) : ℝ) = ∑ d ∈ Finset.Icc 1 N, ((d : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  linarith [heq ▸ h]

theorem sum_Icc_ite_dvd_inv_le (N g : ℕ) (hg : 1 ≤ g) :
    ∑ d ∈ Finset.Icc 1 N, (if g ∣ d then ((d : ℝ))⁻¹ else 0) ≤
      ((g : ℝ))⁻¹ * ∑ e ∈ Finset.Icc 1 N, ((e : ℝ))⁻¹ := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hsub : {d ∈ Finset.Icc 1 N | g ∣ d} ⊆
      (Finset.Icc 1 N).image (fun e => g * e) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdN⟩, hgd⟩ := hd
    refine Finset.mem_image.mpr ⟨d / g, ?_, Nat.mul_div_cancel' hgd⟩
    rw [Finset.mem_Icc]
    refine ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hgd),
      (Nat.div_le_self d g).trans hdN⟩
  calc ∑ d ∈ {d ∈ Finset.Icc 1 N | g ∣ d}, ((d : ℝ))⁻¹
      ≤ ∑ d ∈ (Finset.Icc 1 N).image (fun e => g * e), ((d : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ = ∑ e ∈ Finset.Icc 1 N, (((g * e : ℕ) : ℝ))⁻¹ :=
        Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)
    _ = ((g : ℝ))⁻¹ * ∑ e ∈ Finset.Icc 1 N, ((e : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        push_cast
        rw [mul_inv]

theorem sum_Ioc_card_divisors_sq_le (N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ) ^ 2 ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  classical
  set H : ℝ := ∑ e ∈ Finset.Icc 1 N, ((e : ℝ))⁻¹ with hH
  have hH_nonneg : 0 ≤ H := Finset.sum_nonneg fun e _ => by positivity
  have hH_le : H ≤ 1 + Real.log N := sum_Icc_inv_le_one_add_log N
  
  set A : ℕ → ℝ := fun g => ∑ d ∈ Finset.Icc 1 N,
    (if g ∣ d then ((d : ℝ))⁻¹ else 0) with hA
  have hA_nonneg : ∀ g, 0 ≤ A g := fun g =>
    Finset.sum_nonneg fun d _ => by by_cases h : g ∣ d <;> simp [h]
  have hA_le : ∀ g, 1 ≤ g → A g ≤ ((g : ℝ))⁻¹ * H := fun g hg =>
    sum_Icc_ite_dvd_inv_le N g hg
  
  have hcard : ∀ m ∈ Finset.Ioc 0 N,
      ((m.divisors.card : ℕ) : ℝ) =
        ∑ d ∈ Finset.Icc 1 N, (if d ∣ m then (1 : ℝ) else 0) := by
    intro m hm
    obtain ⟨hm0, hmN⟩ := Finset.mem_Ioc.mp hm
    have hset : m.divisors = {d ∈ Finset.Icc 1 N | d ∣ m} := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, _⟩
        have hd0 : d ≠ 0 := by
          rintro rfl
          exact absurd (zero_dvd_iff.mp hdvd) (by omega)
        exact ⟨⟨by omega, (Nat.le_of_dvd hm0 hdvd).trans hmN⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩
        exact ⟨hdvd, by omega⟩
    rw [hset, Finset.sum_boole]
  
  have hmain : ∑ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ) ^ 2 =
      ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
        ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) := by
    calc ∑ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ) ^ 2
        = ∑ m ∈ Finset.Ioc 0 N, ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            (if d₁ ∣ m then (1 : ℝ) else 0) * (if d₂ ∣ m then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [hcard m hm, sq, Finset.sum_mul_sum]
      _ = ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Ioc 0 N,
            (if d₁ ∣ m then (1 : ℝ) else 0) * (if d₂ ∣ m then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm
      _ = ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
          have hpt : ∀ m : ℕ,
              (if d₁ ∣ m then (1 : ℝ) else 0) * (if d₂ ∣ m then (1 : ℝ) else 0) =
                (if Nat.lcm d₁ d₂ ∣ m then (1 : ℝ) else 0) := by
            intro m
            by_cases h1 : d₁ ∣ m <;> by_cases h2 : d₂ ∣ m
            · simp [h1, h2, Nat.lcm_dvd h1 h2]
            · have : ¬ Nat.lcm d₁ d₂ ∣ m := fun h =>
                h2 ((Nat.dvd_lcm_right d₁ d₂).trans h)
              simp [h1, h2, this]
            · have : ¬ Nat.lcm d₁ d₂ ∣ m := fun h =>
                h1 ((Nat.dvd_lcm_left d₁ d₂).trans h)
              simp [h1, h2, this]
            · have : ¬ Nat.lcm d₁ d₂ ∣ m := fun h =>
                h1 ((Nat.dvd_lcm_left d₁ d₂).trans h)
              simp [h1, h2, this]
          simp_rw [hpt]
          rw [Finset.sum_boole]
          norm_cast
          exact Nat.Ioc_filter_dvd_card_eq_div N (Nat.lcm d₁ d₂)
  rw [hmain]
  
  have hstep4 : ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
      ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) ≤
        ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
          (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) := by
    refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
    obtain ⟨h11, _⟩ := Finset.mem_Icc.mp hd₁
    obtain ⟨h21, _⟩ := Finset.mem_Icc.mp hd₂
    have hlcm0 : 0 < Nat.lcm d₁ d₂ :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
    have h1 : ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) ≤ (N : ℝ) / ((Nat.lcm d₁ d₂ : ℕ) : ℝ) :=
      Nat.cast_div_le
    refine h1.trans (le_of_eq ?_)
    have hgl : ((Nat.gcd d₁ d₂ : ℕ) : ℝ) * ((Nat.lcm d₁ d₂ : ℕ) : ℝ) =
        (d₁ : ℝ) * (d₂ : ℝ) := by exact_mod_cast Nat.gcd_mul_lcm d₁ d₂
    have hgpos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ (by omega)
    have hgcd0 : ((Nat.gcd d₁ d₂ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [← hgl, mul_comm (N : ℝ) ((Nat.gcd d₁ d₂ : ℕ) : ℝ),
      mul_div_mul_left _ _ hgcd0]
  refine hstep4.trans ?_
  
  have hgcd_le : ∀ d₁ ∈ Finset.Icc 1 N, ∀ d₂ ∈ Finset.Icc 1 N,
      ((Nat.gcd d₁ d₂ : ℕ) : ℝ) ≤
        ∑ g ∈ Finset.Icc 1 N, (if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0) := by
    intro d₁ hd₁ d₂ hd₂
    obtain ⟨h11, h1N⟩ := Finset.mem_Icc.mp hd₁
    have hgpos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ (by omega)
    have hgle : Nat.gcd d₁ d₂ ≤ d₁ := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left d₁ d₂)
    have hgmem : Nat.gcd d₁ d₂ ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hsingle := Finset.single_le_sum
      (f := fun g => if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0)
      (fun g _ => by by_cases h : g ∣ d₁ ∧ g ∣ d₂ <;> simp [h]) hgmem
    simpa [Nat.gcd_dvd_left, Nat.gcd_dvd_right] using hsingle
  
  have hstep6 : ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
      (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) ≤
        (N : ℝ) * ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g) := by
    have hpoint : ∀ d₁ ∈ Finset.Icc 1 N, ∀ d₂ ∈ Finset.Icc 1 N,
        (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) ≤
          ∑ g ∈ Finset.Icc 1 N, (N : ℝ) *
            ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
              (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) := by
      intro d₁ hd₁ d₂ hd₂
      obtain ⟨h11, _⟩ := Finset.mem_Icc.mp hd₁
      obtain ⟨h21, _⟩ := Finset.mem_Icc.mp hd₂
      have hfact : ∀ g : ℕ,
          (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
            (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) =
          (N : ℝ) * (if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0) /
            ((d₁ : ℝ) * (d₂ : ℝ)) := by
        intro g
        by_cases h1 : g ∣ d₁
        · by_cases h2 : g ∣ d₂
          · simp only [h1, h2, and_self, ite_true, div_eq_mul_inv, mul_inv]
            ring
          · simp [h1, h2]
        · simp [h1]
      simp_rw [hfact]
      rw [← Finset.sum_div, ← Finset.mul_sum]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgcd_le d₁ hd₁ d₂ hd₂) (Nat.cast_nonneg N))
        (by positivity)
    calc ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
          (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ))
        ≤ ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            ∑ g ∈ Finset.Icc 1 N, (N : ℝ) *
              ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
                (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) :=
          Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ =>
            hpoint d₁ hd₁ d₂ hd₂
      _ = ∑ d₁ ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
              (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) :=
          Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm
      _ = ∑ g ∈ Finset.Icc 1 N, ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
              (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) :=
          Finset.sum_comm
      _ = (N : ℝ) * ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          simp only [hA]
          have hterm : ∀ d₁ d₂ : ℕ,
              (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
                (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) =
              ((N : ℝ) * (g : ℝ) * (if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0)) *
                (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) := fun _ _ => by ring
          simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul]
          rw [← Finset.mul_sum]
          ring
  refine hstep6.trans ?_
  
  have hstep7 : ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g) ≤ H * H * H := by
    have hterm : ∀ g ∈ Finset.Icc 1 N,
        (g : ℝ) * (A g * A g) ≤ ((g : ℝ))⁻¹ * (H * H) := by
      intro g hg
      obtain ⟨hg1, _⟩ := Finset.mem_Icc.mp hg
      have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hg1
      have hAg := hA_le g hg1
      have hAg0 := hA_nonneg g
      have hinvH : 0 ≤ ((g : ℝ))⁻¹ * H := mul_nonneg (by positivity) hH_nonneg
      calc (g : ℝ) * (A g * A g)
          ≤ (g : ℝ) * ((((g : ℝ))⁻¹ * H) * (((g : ℝ))⁻¹ * H)) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hgpos)
            exact mul_le_mul hAg hAg hAg0 hinvH
        _ = ((g : ℝ))⁻¹ * (H * H) := by
            field_simp
    calc ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g)
        ≤ ∑ g ∈ Finset.Icc 1 N, ((g : ℝ))⁻¹ * (H * H) := Finset.sum_le_sum hterm
      _ = H * (H * H) := by rw [← Finset.sum_mul, ← hH]
      _ = H * H * H := by ring
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc (N : ℝ) * ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g)
      ≤ (N : ℝ) * (H * H * H) := mul_le_mul_of_nonneg_left hstep7 hN0
    _ ≤ (N : ℝ) * ((1 + Real.log N) * (1 + Real.log N) * (1 + Real.log N)) := by
        have h1 : H * H * H ≤ (1 + Real.log N) * (1 + Real.log N) * (1 + Real.log N) := by
          have hl0 : (0 : ℝ) ≤ 1 + Real.log N := hH_nonneg.trans hH_le
          exact mul_le_mul (mul_le_mul hH_le hH_le hH_nonneg hl0) hH_le hH_nonneg
            (mul_nonneg hl0 hl0)
        exact mul_le_mul_of_nonneg_left h1 hN0
    _ = (N : ℝ) * (1 + Real.log N) ^ 3 := by ring

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open scoped ArithmeticFunction BigOperators

noncomputable def typeICoeff (U V : ℕ) : ArithmeticFunction ℝ :=
  muLE U * lambdaLE V

noncomputable def typeIICoeff (U : ℕ) : ArithmeticFunction ℝ :=
  muGT U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

theorem abs_muLE_le_one (U n : ℕ) : |muLE U n| ≤ 1 := by
  by_cases h : n ≤ U
  · simp only [muLE_apply, if_pos h]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · simp [h]

theorem abs_muGT_le_one (U n : ℕ) : |muGT U n| ≤ 1 := by
  by_cases h : U < n
  · simp only [muGT_apply, if_pos h]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · simp [h]

theorem lambdaLE_nonneg (V n : ℕ) : 0 ≤ lambdaLE V n := by
  simp only [lambdaLE_apply]
  split_ifs <;> positivity

theorem lambdaGT_nonneg (V n : ℕ) : 0 ≤ lambdaGT V n := by
  simp only [lambdaGT_apply]
  split_ifs <;> positivity

theorem lambdaLE_le_vonMangoldt (V n : ℕ) :
    lambdaLE V n ≤ ArithmeticFunction.vonMangoldt n := by
  simp only [lambdaLE_apply]
  split_ifs <;> first | exact le_rfl | exact ArithmeticFunction.vonMangoldt_nonneg

theorem lambdaGT_le_log (V n : ℕ) : lambdaGT V n ≤ Real.log n := by
  simp only [lambdaGT_apply]
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_le_log
  · exact Real.log_natCast_nonneg n

theorem vaughanTypeILambda_eq (U V : ℕ) :
    vaughanTypeILambda U V =
      typeICoeff U V * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  unfold vaughanTypeILambda typeICoeff
  ring

theorem abs_typeICoeff_le_log (U V n : ℕ) : |typeICoeff U V n| ≤ Real.log n := by
  rw [typeICoeff, ArithmeticFunction.mul_apply]
  calc
    |∑ ab ∈ n.divisorsAntidiagonal, muLE U ab.1 * lambdaLE V ab.2|
        ≤ ∑ ab ∈ n.divisorsAntidiagonal, |muLE U ab.1 * lambdaLE V ab.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt ab.2 := by
      apply Finset.sum_le_sum
      intro ab _
      rw [abs_mul, abs_of_nonneg (lambdaLE_nonneg V ab.2)]
      exact (mul_le_mul_of_nonneg_right (abs_muLE_le_one U ab.1)
        (lambdaLE_nonneg V ab.2)).trans (by simpa using lambdaLE_le_vonMangoldt V ab.2)
    _ = Real.log n := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ b ↦ ArithmeticFunction.vonMangoldt b)]
      exact ArithmeticFunction.vonMangoldt_sum

theorem typeICoeff_eq_zero_of_mul_lt (U V n : ℕ) (hn : U * V < n) :
    typeICoeff U V n = 0 := by
  rw [typeICoeff, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  have heq := (Nat.mem_divisorsAntidiagonal.mp hab).1
  by_cases ha : ab.1 ≤ U
  · have hb : ¬ ab.2 ≤ V := by
      intro hb
      have := Nat.mul_le_mul ha hb
      omega
    simp [hb]
  · simp [ha]

theorem abs_typeIICoeff_le_card_divisors (U n : ℕ) :
    |typeIICoeff U n| ≤ (n.divisors.card : ℝ) := by
  rw [typeIICoeff, ArithmeticFunction.coe_mul_zeta_apply]
  calc
    |∑ d ∈ n.divisors, muGT U d| ≤ ∑ d ∈ n.divisors, |muGT U d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) :=
      Finset.sum_le_sum fun d _ ↦ abs_muGT_le_one U d
    _ = _ := by simp

theorem typeIICoeff_eq_zero_of_le (U n : ℕ) (hn : n ≤ U) :
    typeIICoeff U n = 0 := by
  rw [typeIICoeff, ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdu : d ≤ U := (Nat.divisor_le hd).trans hn
  simp [not_lt.mpr hdu]

theorem weightedArithmeticSum_lambdaLE_eq_zero
    (V : ℕ) (I : Finset ℕ) (w : ℕ → ℂ) (hI : ∀ n ∈ I, V < n) :
    weightedArithmeticSum I w (lambdaLE V) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  simp [not_le.mpr (hI n hn)]

theorem sum_typeIICoeff_sq_le (U N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, typeIICoeff U n ^ 2) ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  apply le_trans _ (sum_Ioc_card_divisors_sq_le N)
  apply Finset.sum_le_sum
  intro n _
  simpa only [sq_abs] using
    pow_le_pow_left₀ (abs_nonneg _) (abs_typeIICoeff_le_card_divisors U n) 2

theorem sum_typeIICoeff_sq_le_on_dyadic
    (U M : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.Ioc M (2 * M)) :
    (∑ n ∈ I, typeIICoeff U n ^ 2) ≤
      2 * (M : ℝ) * (1 + Real.log (2 * (M : ℝ))) ^ 3 := by
  have hsub : I ⊆ Finset.Ioc 0 (2 * M) :=
    hI.trans (Finset.Ioc_subset_Ioc (Nat.zero_le M) le_rfl)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ sq_nonneg _)).trans ?_
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using sum_typeIICoeff_sq_le U (2 * M)

theorem sum_lambdaGT_sq_le_on_dyadic
    (V M : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.Ioc M (2 * M)) :
    (∑ n ∈ I, lambdaGT V n ^ 2) ≤
      (M : ℝ) * Real.log (2 * (M : ℝ) + 1) ^ 2 := by
  calc
    (∑ n ∈ I, lambdaGT V n ^ 2) ≤
        ∑ n ∈ Finset.Ioc M (2 * M), lambdaGT V n ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ ↦ sq_nonneg _)
    _ ≤ ∑ _n ∈ Finset.Ioc M (2 * M), Real.log (2 * (M : ℝ) + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0, hnM⟩ := Finset.mem_Ioc.mp hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le M).trans_lt hn0
      apply pow_le_pow_left₀ (lambdaGT_nonneg V n) _ 2
      refine (lambdaGT_le_log V n).trans (Real.log_le_log hnpos ?_)
      exact_mod_cast (show n ≤ 2 * M + 1 by omega)
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      congr 2
      omega

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

noncomputable section

theorem dyadicBoxCount_le_three_log (n : ℕ) (hn : 2 ≤ n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * Real.log n := by
  have hn0 : n ≠ 0 := by omega
  have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hpowR : (2 : ℝ) ^ (Nat.log 2 n : ℕ) ≤ (n : ℝ) := by exact_mod_cast hpow
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hcpos : (0 : ℝ) < Real.log 2 := by linarith
  have hlogpow : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity) hpowR
    rwa [Real.log_pow] at h
  have hlogn : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hX_pos : (0 : ℝ) < Real.log n := lt_of_lt_of_le hcpos hlogn
  have key : ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤ 2 * Real.log n := by
    have : ((Nat.log 2 n : ℝ) + 1) * Real.log 2 =
        (Nat.log 2 n : ℝ) * Real.log 2 + Real.log 2 := by ring
    rw [this]
    linarith
  have key2 : 2 * Real.log n ≤ 3 * Real.log n * Real.log 2 := by nlinarith
  have h1 : ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤
      3 * Real.log n * Real.log 2 := key.trans key2
  have h2 : ((Nat.log 2 n : ℝ) + 1) ≤ 3 * Real.log n :=
    le_of_mul_le_mul_right h1 hcpos
  push_cast
  exact h2

theorem Ioc_zero_eq_dyadic_biUnion (N : ℕ) (hN : 1 ≤ N) :
    Finset.Ioc 0 N =
      insert 1 ((Finset.range (Nat.log 2 N + 1)).biUnion
        (fun j => Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N))) := by
  ext m
  simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_range,
    le_min_iff]
  constructor
  · rintro ⟨hm0, hmN⟩
    by_cases hm1 : m = 1
    · exact Or.inl hm1
    · refine Or.inr ⟨Nat.log 2 (m - 1), ?_, ?_, ?_, hmN⟩
      · have hle : m - 1 ≤ N := by omega
        exact Nat.lt_succ_of_le (Nat.log_mono_right hle)
      · have h := Nat.pow_log_le_self 2 (x := m - 1) (by omega)
        omega
      · have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (m - 1)
        omega
  · rintro (rfl | ⟨j, _, hjm, hm2, hmN⟩)
    · exact ⟨one_pos, hN⟩
    · exact ⟨lt_of_le_of_lt (Nat.zero_le _) hjm, hmN⟩

theorem dyadic_blocks_pairwiseDisjoint (N : ℕ) :
    Set.PairwiseDisjoint ↑(Finset.range (Nat.log 2 N + 1))
      (fun j => Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N)) := by
  have key : ∀ i j : ℕ, i < j →
      Disjoint (Finset.Ioc (2 ^ i) (min (2 ^ (i + 1)) N))
        (Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N)) := by
    intro i j hij
    refine Finset.disjoint_left.mpr ?_
    intro m hm hm'
    obtain ⟨_, hm2⟩ := Finset.mem_Ioc.mp hm
    obtain ⟨hm3, _⟩ := Finset.mem_Ioc.mp hm'
    have hpow : (2 : ℕ) ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hij
    have := le_min_iff.mp hm2
    omega
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem sum_Ioc_eq_one_add_dyadic {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Ioc 0 N, f n) = f 1 +
      ∑ j ∈ range (Nat.log 2 N + 1),
        ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n := by
  classical
  have hnot : 1 ∉ (range (Nat.log 2 N + 1)).biUnion
      (fun j ↦ Ioc (2 ^ j) (min (2 ^ (j + 1)) N)) := by
    intro h
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp h
    have := (mem_Ioc.mp hj).1
    have := Nat.one_le_two_pow (n := j)
    omega
  rw [Ioc_zero_eq_dyadic_biUnion N hN, sum_insert hnot,
    sum_biUnion (dyadic_blocks_pairwiseDisjoint N)]

theorem sum_Ioc_eq_dyadic_of_one_eq_zero {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (N : ℕ) (hf : f 1 = 0) :
    (∑ n ∈ Ioc 0 N, f n) =
      ∑ j ∈ range (Nat.log 2 N + 1),
        ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [sum_Ioc_eq_one_add_dyadic f N hN, hf, zero_add]

theorem sum_sum_Ioc_eq_dyadic (f : ℕ → ℕ → ℂ) (X Y : ℕ)
    (hleft : ∀ n, f 1 n = 0) (hright : ∀ m, f m 1 = 0) :
    (∑ m ∈ Ioc 0 X, ∑ n ∈ Ioc 0 Y, f m n) =
      ∑ i ∈ range (Nat.log 2 X + 1), ∑ j ∈ range (Nat.log 2 Y + 1),
        ∑ m ∈ Ioc (2 ^ i) (min (2 ^ (i + 1)) X),
          ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) Y), f m n := by
  rw [sum_Ioc_eq_dyadic_of_one_eq_zero (fun m ↦ ∑ n ∈ Ioc 0 Y, f m n)
    X (by simp [hleft])]
  apply sum_congr rfl
  intro i _
  simp_rw [sum_Ioc_eq_dyadic_of_one_eq_zero (f _) Y (hright _)]
  rw [sum_comm]

theorem correlation_product_filter_eq_Ioc (M B P Y n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    {m ∈ Ioc M B | P < m * n₁ ∧ m * n₁ ≤ Y ∧ P < m * n₂ ∧ m * n₂ ≤ Y} =
      Ioc (max M (max (P / n₁) (P / n₂)))
        (min B (min (Y / n₁) (Y / n₂))) := by
  ext m
  simp only [mem_filter, mem_Ioc, max_lt_iff, le_min_iff,
    Nat.div_lt_iff_lt_mul hn₁, Nat.div_lt_iff_lt_mul hn₂,
    Nat.le_div_iff_mul_le hn₁, Nat.le_div_iff_mul_le hn₂]
  tauto

theorem sum_correlation_product_filter_eq_Ioc (M B P Y n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (f : ℕ → ℂ) :
    (∑ m ∈ Ioc M B,
      if P < m * n₁ ∧ m * n₁ ≤ Y ∧ P < m * n₂ ∧ m * n₂ ≤ Y then f m else 0) =
      ∑ m ∈ Ioc (max M (max (P / n₁) (P / n₂)))
        (min B (min (Y / n₁) (Y / n₂))), f m := by
  rw [← sum_filter, correlation_product_filter_eq_Ioc M B P Y n₁ n₂ hn₁ hn₂]

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

open scoped ArithmeticFunction

noncomputable section

theorem sum_Ioc_divisors_swap (M : ℕ) (F : ℕ → ℕ → ℂ) :
    ∑ m ∈ Finset.Ioc 0 M, ∑ e ∈ m.divisors, F e m =
      ∑ e ∈ Finset.Ioc 0 M, ∑ f ∈ Finset.Ioc 0 (M / e), F e (e * f) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun p => ⟨p.2, p.1 / p.2⟩)
    (j := fun p => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨hm0, hmM⟩, hdvd, hne⟩ := hp
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos hdvd hm0
    refine ⟨⟨he0, le_trans (Nat.le_of_dvd hm0 hdvd) hmM⟩, ?_, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd hm0 hdvd) he0
    · exact Nat.div_le_div_right hmM
  · rintro ⟨e, f⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨he0, heM⟩, hf0, hfM⟩ := hp
    have hefM : e * f ≤ M := by
      have hfe := (Nat.le_div_iff_mul_le he0).mp hfM
      calc e * f = f * e := Nat.mul_comm e f
        _ ≤ M := hfe
    exact ⟨⟨by positivity, hefM⟩, Dvd.intro f rfl, by positivity⟩
  · rintro ⟨m, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp
    obtain ⟨_, hdvd, _⟩ := hp
    simp [Nat.mul_div_cancel' hdvd]
  · rintro ⟨e, f⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc] at hp
    obtain ⟨⟨he0, _⟩, _, _⟩ := hp
    simp [Nat.mul_div_cancel_left f he0]
  · rintro ⟨m, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp
    obtain ⟨_, hdvd, _⟩ := hp
    simp [Nat.mul_div_cancel' hdvd]

theorem weightedArithmeticSum_convolution_Ioc
    (a b : ArithmeticFunction ℝ) (Y : ℕ) (w : ℕ → ℂ) :
    weightedArithmeticSum (Ioc 0 Y) w (a * b) =
      ∑ m ∈ Ioc 0 Y, ∑ n ∈ Ioc 0 (Y / m),
        (a m : ℂ) * (b n : ℂ) * w (m * n) := by
  unfold weightedArithmeticSum
  have hexpand :
      (∑ r ∈ Ioc 0 Y, ((a * b) r : ℂ) * w r) =
        ∑ r ∈ Ioc 0 Y, ∑ m ∈ r.divisors,
          (a m : ℂ) * (b (r / m) : ℂ) * w r := by
    apply sum_congr rfl
    intro r _
    simp only [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
      Finset.sum_mul]
    exact Nat.sum_divisorsAntidiagonal (fun m n ↦ (a m : ℂ) * (b n : ℂ) * w r)
  rw [hexpand]
  rw [sum_Ioc_divisors_swap]
  apply sum_congr rfl
  intro m hm
  have hmpos := (mem_Ioc.mp hm).1
  apply sum_congr rfl
  intro n _
  rw [Nat.mul_div_cancel_left n hmpos]

theorem Ioc_div_eq_product_filter (Y m : ℕ) (hm : 0 < m) :
    Ioc 0 (Y / m) = {n ∈ Ioc 0 Y | m * n ≤ Y} := by
  ext n
  simp only [mem_Ioc, mem_filter]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨⟨hn, h.trans (Nat.div_le_self Y m)⟩, ?_⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).mp h
  · rintro ⟨⟨hn, _⟩, h⟩
    exact ⟨hn, (Nat.le_div_iff_mul_le hm).mpr (by simpa [Nat.mul_comm] using h)⟩

def productBandTerm (a b : ArithmeticFunction ℝ) (P Y : ℕ) (w : ℕ → ℂ)
    (m n : ℕ) : ℂ :=
  if P < m * n ∧ m * n ≤ Y then (a m : ℂ) * (b n : ℂ) * w (m * n) else 0

theorem productBandTerm_swap (a b : ArithmeticFunction ℝ) (P Y : ℕ)
    (w : ℕ → ℂ) (m n : ℕ) :
    productBandTerm a b P Y w m n = productBandTerm b a P Y w n m := by
  unfold productBandTerm
  rw [Nat.mul_comm n m]
  split_ifs <;> ring

theorem sum_productBandTerm_swap (a b : ArithmeticFunction ℝ) (P Y : ℕ)
    (w : ℕ → ℂ) (I J : Finset ℕ) :
    (∑ m ∈ I, ∑ n ∈ J, productBandTerm a b P Y w m n) =
      ∑ n ∈ J, ∑ m ∈ I, productBandTerm b a P Y w n m := by
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro m _
  exact productBandTerm_swap a b P Y w m n

theorem weightedArithmeticSum_convolution_band
    (a b : ArithmeticFunction ℝ) (P Y : ℕ) (w : ℕ → ℂ) :
    weightedArithmeticSum (Ioc P Y) w (a * b) =
      ∑ m ∈ Ioc 0 Y, ∑ n ∈ Ioc 0 Y, productBandTerm a b P Y w m n := by
  have hband : {n ∈ Ioc 0 Y | P < n} = Ioc P Y := by
    ext n
    simp only [mem_filter, mem_Ioc]
    omega
  have hweight :
      weightedArithmeticSum (Ioc P Y) w (a * b) =
        weightedArithmeticSum (Ioc 0 Y) (fun n ↦ if P < n then w n else 0) (a * b) := by
    unfold weightedArithmeticSum
    rw [← hband, sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hn : P < n <;> simp only [hn, ite_true, ite_false, mul_zero]
  rw [hweight, weightedArithmeticSum_convolution_Ioc]
  apply sum_congr rfl
  intro m hm
  rw [Ioc_div_eq_product_filter Y m (mem_Ioc.mp hm).1, sum_filter]
  apply sum_congr rfl
  intro n _
  unfold productBandTerm
  by_cases hlo : P < m * n <;> by_cases hhi : m * n ≤ Y <;> simp [hlo, hhi]

theorem weightedArithmeticSum_typeII_eq_dyadic (U V P Y : ℕ) (hU : 1 ≤ U)
    (w : ℕ → ℂ) :
    weightedArithmeticSum (Ioc P Y) w (vaughanTypeII U V) =
      ∑ i ∈ range (Nat.log 2 Y + 1), ∑ j ∈ range (Nat.log 2 Y + 1),
        ∑ m ∈ Ioc (2 ^ i) (min (2 ^ (i + 1)) Y),
          ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) Y),
            productBandTerm (lambdaGT V) (typeIICoeff U) P Y w m n := by
  change weightedArithmeticSum (Ioc P Y) w (lambdaGT V * typeIICoeff U) = _
  rw [weightedArithmeticSum_convolution_band]
  apply sum_sum_Ioc_eq_dyadic
  · intro n
    simp [productBandTerm, lambdaGT_apply]
  · intro m
    simp [productBandTerm, typeIICoeff_eq_zero_of_le U 1 hU]

theorem norm_weightedArithmeticSum_typeII_le_dyadic (U V P Y : ℕ) (hU : 1 ≤ U)
    (w : ℕ → ℂ) :
    ‖weightedArithmeticSum (Ioc P Y) w (vaughanTypeII U V)‖ ≤
      ∑ i ∈ range (Nat.log 2 Y + 1), ∑ j ∈ range (Nat.log 2 Y + 1),
        ‖∑ m ∈ Ioc (2 ^ i) (min (2 ^ (i + 1)) Y),
          ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) Y),
            productBandTerm (lambdaGT V) (typeIICoeff U) P Y w m n‖ := by
  rw [weightedArithmeticSum_typeII_eq_dyadic U V P Y hU w]
  exact (norm_sum_le _ _).trans (sum_le_sum fun _ _ ↦ norm_sum_le _ _)

theorem norm_weightedArithmeticSum_typeII_le_of_box_bound
    (U V P Y : ℕ) (hU : 1 ≤ U) (hY : 2 ≤ Y) (w : ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hbox : ∀ i ∈ range (Nat.log 2 Y + 1), ∀ j ∈ range (Nat.log 2 Y + 1),
      ‖∑ m ∈ Ioc (2 ^ i) (min (2 ^ (i + 1)) Y),
        ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) Y),
          productBandTerm (lambdaGT V) (typeIICoeff U) P Y w m n‖ ≤ B) :
    ‖weightedArithmeticSum (Ioc P Y) w (vaughanTypeII U V)‖ ≤
      9 * Real.log (Y : ℝ) ^ 2 * B := by
  calc
    ‖weightedArithmeticSum (Ioc P Y) w (vaughanTypeII U V)‖ ≤
        ∑ _i ∈ range (Nat.log 2 Y + 1), ∑ _j ∈ range (Nat.log 2 Y + 1), B :=
      (norm_weightedArithmeticSum_typeII_le_dyadic U V P Y hU w).trans
        (sum_le_sum fun i hi ↦ sum_le_sum fun j hj ↦ hbox i hi j hj)
    _ = ((Nat.log 2 Y + 1 : ℕ) : ℝ) ^ 2 * B := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      ring
    _ ≤ (3 * Real.log (Y : ℝ)) ^ 2 * B :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (dyadicBoxCount_le_three_log Y hY) 2) hB
    _ = _ := by ring

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

open scoped ComplexConjugate

noncomputable section

def phaseCharacter (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

def reciprocalLogWeight (a : ℝ) (n : ℕ) : ℂ := phaseCharacter (a / Real.log (n : ℝ))

@[simp] theorem norm_phaseCharacter (t : ℝ) : ‖phaseCharacter t‖ = 1 := by
  simp [phaseCharacter, Complex.norm_exp]

@[simp] theorem norm_reciprocalLogWeight (a : ℝ) (n : ℕ) : ‖reciprocalLogWeight a n‖ = 1 :=
  norm_phaseCharacter _

theorem phaseCharacter_mul_conj (s t : ℝ) :
    phaseCharacter s * conj (phaseCharacter t) = phaseCharacter (s - t) := by
  unfold phaseCharacter
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub,
    Complex.ofReal_mul]
  ring

theorem reciprocalLogWeight_mul_conj (a : ℝ) (m n₁ n₂ : ℕ) :
    reciprocalLogWeight a (m * n₁) * conj (reciprocalLogWeight a (m * n₂)) =
      phaseCharacter (reciprocalLogCorrelation a (n₁ : ℝ) (n₂ : ℝ) (m : ℝ)) := by
  unfold reciprocalLogWeight reciprocalLogCorrelation reciprocalLogPhase
  rw [phaseCharacter_mul_conj]
  simp only [Nat.cast_mul, mul_comm (m : ℝ)]

def bandPhase (a : ℝ) (P Y m n : ℕ) : ℂ :=
  if P < m * n ∧ m * n ≤ Y then reciprocalLogWeight a (m * n) else 0

theorem bandPhase_mul_conj (a : ℝ) (P Y m n₁ n₂ : ℕ) :
    bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂) =
      if P < m * n₁ ∧ m * n₁ ≤ Y ∧ P < m * n₂ ∧ m * n₂ ≤ Y then
        phaseCharacter (reciprocalLogCorrelation a (n₁ : ℝ) (n₂ : ℝ) (m : ℝ)) else 0 := by
  have hcond : (P < m * n₁ ∧ m * n₁ ≤ Y ∧ P < m * n₂ ∧ m * n₂ ≤ Y) =
      ((P < m * n₁ ∧ m * n₁ ≤ Y) ∧ (P < m * n₂ ∧ m * n₂ ≤ Y)) :=
    propext and_assoc.symm
  simp only [hcond]
  by_cases h₁ : P < m * n₁ ∧ m * n₁ ≤ Y <;>
    by_cases h₂ : P < m * n₂ ∧ m * n₂ ≤ Y <;>
    simp [bandPhase, h₁, h₂, reciprocalLogWeight_mul_conj]

theorem sum_bandPhase_correlation (a : ℝ) (M B P Y n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    (∑ m ∈ Ioc M B, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)) =
      ∑ m ∈ Ioc (max M (max (P / n₁) (P / n₂)))
        (min B (min (Y / n₁) (Y / n₂))),
          phaseCharacter (reciprocalLogCorrelation a (n₁ : ℝ) (n₂ : ℝ) (m : ℝ)) := by
  simp_rw [bandPhase_mul_conj]
  exact sum_correlation_product_filter_eq_Ioc M B P Y n₁ n₂ hn₁ hn₂ _

theorem real_product_bounds_of_div_hull (P Y n : ℕ) (hn : 0 < n) (x : ℝ)
    (hlo : ((P / n + 1 : ℕ) : ℝ) ≤ x) (hhi : x ≤ ((Y / n : ℕ) : ℝ)) :
    (P : ℝ) < (n : ℝ) * x ∧ (n : ℝ) * x ≤ (Y : ℝ) := by
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · have hnat : P < n * (P / n + 1) := Nat.lt_mul_div_succ P hn
    have hreal : (P : ℝ) < (n : ℝ) * ((P / n + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    exact hreal.trans_le (mul_le_mul_of_nonneg_left hlo hnR)
  · have hnat : n * (Y / n) ≤ Y := Nat.mul_div_le Y n
    have hreal : (n : ℝ) * ((Y / n : ℕ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hnat
    exact (mul_le_mul_of_nonneg_left hhi hnR).trans hreal

theorem correlation_real_hull_bounds (M B P Y n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (x : ℝ)
    (hlo : ((max M (max (P / n₁) (P / n₂)) + 1 : ℕ) : ℝ) ≤ x)
    (hhi : x ≤ ((min B (min (Y / n₁) (Y / n₂)) : ℕ) : ℝ)) :
    (M : ℝ) < x ∧ x ≤ (B : ℝ) ∧
      (P : ℝ) < (n₁ : ℝ) * x ∧ (n₁ : ℝ) * x ≤ (Y : ℝ) ∧
      (P : ℝ) < (n₂ : ℝ) * x ∧ (n₂ : ℝ) * x ≤ (Y : ℝ) := by
  have hlo₁ : ((P / n₁ + 1 : ℕ) : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Nat.add_le_add_right ((le_max_left _ _).trans (le_max_right _ _)) 1)).trans hlo
  have hlo₂ : ((P / n₂ + 1 : ℕ) : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Nat.add_le_add_right ((le_max_right _ _).trans (le_max_right _ _)) 1)).trans hlo
  have hhi₁ : x ≤ ((Y / n₁ : ℕ) : ℝ) :=
    hhi.trans (Nat.cast_le.mpr ((min_le_right _ _).trans (min_le_left _ _)))
  have hhi₂ : x ≤ ((Y / n₂ : ℕ) : ℝ) :=
    hhi.trans (Nat.cast_le.mpr ((min_le_right _ _).trans (min_le_right _ _)))
  have hb₁ := real_product_bounds_of_div_hull P Y n₁ hn₁ x hlo₁ hhi₁
  have hb₂ := real_product_bounds_of_div_hull P Y n₂ hn₂ x hlo₂ hhi₂
  refine ⟨?_, hhi.trans (Nat.cast_le.mpr (min_le_left _ _)), hb₁.1, hb₁.2, hb₂.1, hb₂.2⟩
  have hnat : M < max M (max (P / n₁) (P / n₂)) + 1 :=
    Nat.lt_succ_of_le (le_max_left _ _)
  exact (Nat.cast_lt.mpr hnat).trans_le hlo

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

noncomputable section

theorem phaseCharacter_add (s t : ℝ) :
    phaseCharacter (s + t) = phaseCharacter s * phaseCharacter t := by
  unfold phaseCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def phaseResolvent (t : ℝ) : ℂ := (1 - phaseCharacter t)⁻¹

def halfCotPhase (t : ℝ) : ℝ := Real.cos (Real.pi * t) / (2 * Real.sin (Real.pi * t))

theorem sin_pi_pos_of_unit (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    0 < Real.sin (Real.pi * t) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht)
    (by nlinarith [Real.pi_pos])

theorem norm_one_sub_phaseCharacter (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    ‖1 - phaseCharacter t‖ = 2 * Real.sin (Real.pi * t) := by
  rw [norm_sub_rev]
  unfold phaseCharacter
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  have he : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [he, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num)
    (sin_pi_pos_of_unit t ht ht1))]

theorem one_sub_phaseCharacter_ne_zero (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    1 - phaseCharacter t ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_one_sub_phaseCharacter t ht ht1]
  exact mul_pos (by norm_num) (sin_pi_pos_of_unit t ht ht1)

theorem phaseResolvent_eq (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    phaseResolvent t = (1 / 2 : ℂ) + (halfCotPhase t : ℂ) * Complex.I := by
  have hs := (sin_pi_pos_of_unit t ht ht1).ne'
  have he : 2 * Real.pi * t = 2 * (Real.pi * t) := by ring
  apply (mul_eq_one_iff_inv_eq₀ (one_sub_phaseCharacter_ne_zero t ht ht1)).mp
  unfold phaseCharacter halfCotPhase
  rw [Complex.exp_ofReal_mul_I, he, Real.cos_two_mul, Real.sin_two_mul]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      mul_zero, add_zero, zero_add, mul_one, sub_zero, zero_sub]
  all_goals field_simp
  all_goals
    have hcircle := Real.sin_sq_add_cos_sq (Real.pi * t)
    have hprod := congrArg (fun r : ℝ => Real.cos (Real.pi * t) * r) hcircle
    nlinarith

theorem halfCotPhase_antitone (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) :
    halfCotPhase t ≤ halfCotPhase s := by
  have hs1 : s < 1 := hst.trans_lt ht
  have ht0 : 0 < t := hs.trans_le hst
  have hsin_s := sin_pi_pos_of_unit s hs hs1
  have hsin_t := sin_pi_pos_of_unit t ht0 ht
  have hd : 0 ≤ Real.sin (Real.pi * t - Real.pi * s) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
  rw [Real.sin_sub] at hd
  unfold halfCotPhase
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem two_mul_le_sin_pi (δ t : ℝ) (hδ : 0 < δ) (hlo : δ ≤ t) (hhi : t ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * t) := by
  have hpi := Real.pi_pos
  have ht0 : 0 < t := hδ.trans_le hlo
  by_cases ht : t ≤ 1 / 2
  · have h := Real.mul_le_sin (x := Real.pi * t) (by positivity) (by nlinarith)
    have he : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    rw [he] at h
    linarith
  · have h := Real.mul_le_sin (x := Real.pi * (1 - t)) (by nlinarith) (by nlinarith)
    have he : 2 / Real.pi * (Real.pi * (1 - t)) = 2 * (1 - t) := by field_simp
    rw [he, show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring,
      Real.sin_pi_sub] at h
    linarith

theorem norm_phaseResolvent_le (δ t : ℝ) (hδ : 0 < δ)
    (hlo : δ ≤ t) (hhi : t ≤ 1 - δ) : ‖phaseResolvent t‖ ≤ 1 / (4 * δ) := by
  have ht0 := hδ.trans_le hlo
  have ht1 : t < 1 := by linarith
  rw [phaseResolvent, norm_inv, norm_one_sub_phaseCharacter t ht0 ht1, ← one_div]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  linarith [two_mul_le_sin_pi δ t hδ hlo hhi]

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

noncomputable section

theorem sum_range_mul_sub_identity (c z : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ range (N + 1), c k * (z k - z (k + 1))) =
      c 0 * z 0 - c N * z (N + 1) +
        ∑ k ∈ range N, (c (k + 1) - c k) * z (k + 1) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

theorem norm_phaseResolvent_sub (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) :
    ‖phaseResolvent t - phaseResolvent s‖ = halfCotPhase s - halfCotPhase t := by
  rw [phaseResolvent_eq t (hs.trans_le hst) ht,
    phaseResolvent_eq s hs (hst.trans_lt ht)]
  have he : (1 / 2 : ℂ) + (halfCotPhase t : ℂ) * Complex.I -
      ((1 / 2 : ℂ) + (halfCotPhase s : ℂ) * Complex.I) =
      ((halfCotPhase t - halfCotPhase s : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (halfCotPhase_antitone s t hs hst ht))]
  ring

theorem sum_norm_phaseResolvent_sub (d : ℕ → ℝ) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < d k) (hlt : ∀ k ≤ N, d k < 1)
    (hmono : MonotoneOn d (Set.Icc 0 N)) :
    (∑ k ∈ range N, ‖phaseResolvent (d (k + 1)) - phaseResolvent (d k)‖) =
      halfCotPhase (d 0) - halfCotPhase (d N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih (fun k hk => hpos k (by omega))
      (fun k hk => hlt k (by omega))
      (fun i hi j hj hij => hmono ⟨hi.1, Nat.le_succ_of_le hi.2⟩
        ⟨hj.1, Nat.le_succ_of_le hj.2⟩ hij)]
    rw [norm_phaseResolvent_sub (d N) (d (N + 1)) (hpos N (by omega))
      (hmono ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)) (hlt _ le_rfl)]
    ring

theorem phaseCharacter_eq_resolvent_mul_sub (s t : ℝ)
    (hpos : 0 < t - s) (hlt : t - s < 1) :
    phaseCharacter s = phaseResolvent (t - s) * (phaseCharacter s - phaseCharacter t) := by
  have hstep : phaseCharacter t = phaseCharacter s * phaseCharacter (t - s) := by
    rw [← phaseCharacter_add]
    congr 1
    ring
  rw [hstep, phaseResolvent, ← mul_one_sub]
  rw [mul_left_comm, inv_mul_cancel₀ (one_sub_phaseCharacter_ne_zero _ hpos hlt), mul_one]

theorem norm_sum_phaseCharacter_le_of_monotone_increments
    (u : ℕ → ℝ) (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hlo : ∀ k ≤ N, δ ≤ u (k + 1) - u k)
    (hhi : ∀ k ≤ N, u (k + 1) - u k ≤ 1 - δ)
    (hmono : MonotoneOn (fun k => u (k + 1) - u k) (Set.Icc 0 N)) :
    ‖∑ k ∈ range (N + 1), phaseCharacter (u k)‖ ≤ 1 / δ := by
  let d : ℕ → ℝ := fun k => u (k + 1) - u k
  have hpos (k : ℕ) (hk : k ≤ N) : 0 < d k := hδ.trans_le (hlo k hk)
  have hlt (k : ℕ) (hk : k ≤ N) : d k < 1 := by dsimp [d]; linarith [hhi k hk]
  have he : (∑ k ∈ range (N + 1), phaseCharacter (u k)) =
      phaseResolvent (d 0) * phaseCharacter (u 0) -
        phaseResolvent (d N) * phaseCharacter (u (N + 1)) +
        ∑ k ∈ range N, (phaseResolvent (d (k + 1)) - phaseResolvent (d k)) *
          phaseCharacter (u (k + 1)) := by
    calc
      _ = ∑ k ∈ range (N + 1), phaseResolvent (d k) *
          (phaseCharacter (u k) - phaseCharacter (u (k + 1))) := by
        apply sum_congr rfl
        intro k hk
        exact phaseCharacter_eq_resolvent_mul_sub _ _ (hpos k (by simpa using hk))
          (hlt k (by simpa using hk))
      _ = _ := sum_range_mul_sub_identity _ _ N
  have hvar := sum_norm_phaseResolvent_sub d N hpos hlt hmono
  have hq (k : ℕ) (hk : k ≤ N) : |halfCotPhase (d k)| ≤ ‖phaseResolvent (d k)‖ := by
    have h := Complex.abs_im_le_norm (phaseResolvent (d k))
    simpa [phaseResolvent_eq _ (hpos k hk) (hlt k hk)] using h
  have hvarle : halfCotPhase (d 0) - halfCotPhase (d N) ≤
      ‖phaseResolvent (d 0)‖ + ‖phaseResolvent (d N)‖ := by
    have h0 := (abs_le.mp (hq 0 (Nat.zero_le N))).2
    have hN := (abs_le.mp (hq N le_rfl)).1
    linarith
  rw [he]
  calc
    _ ≤ ‖phaseResolvent (d 0) * phaseCharacter (u 0) -
          phaseResolvent (d N) * phaseCharacter (u (N + 1))‖ +
        ‖∑ k ∈ range N, (phaseResolvent (d (k + 1)) - phaseResolvent (d k)) *
          phaseCharacter (u (k + 1))‖ := norm_add_le _ _
    _ ≤ (‖phaseResolvent (d 0)‖ + ‖phaseResolvent (d N)‖) +
        ∑ k ∈ range N, ‖phaseResolvent (d (k + 1)) - phaseResolvent (d k)‖ := by
      apply add_le_add
      · simpa only [norm_mul, norm_phaseCharacter, mul_one] using norm_sub_le
          (phaseResolvent (d 0) * phaseCharacter (u 0))
          (phaseResolvent (d N) * phaseCharacter (u (N + 1)))
      · simpa only [norm_mul, norm_phaseCharacter, mul_one] using norm_sum_le (range N)
          (fun k => (phaseResolvent (d (k + 1)) - phaseResolvent (d k)) *
            phaseCharacter (u (k + 1)))
    _ = (‖phaseResolvent (d 0)‖ + ‖phaseResolvent (d N)‖) +
        (halfCotPhase (d 0) - halfCotPhase (d N)) := by rw [hvar]
    _ ≤ 2 * (‖phaseResolvent (d 0)‖ + ‖phaseResolvent (d N)‖) := by linarith
    _ ≤ 2 * (1 / (4 * δ) + 1 / (4 * δ)) := by
      gcongr
      · exact norm_phaseResolvent_le δ _ hδ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
      · exact norm_phaseResolvent_le δ _ hδ (hlo N le_rfl) (hhi N le_rfl)
    _ = 1 / δ := by ring

theorem norm_sum_phaseCharacter_le_of_monotone_increments_closed
    (u : ℕ → ℝ) (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hlo : ∀ k < N, δ ≤ u (k + 1) - u k)
    (hhi : ∀ k < N, u (k + 1) - u k ≤ 1 - δ)
    (hmono : MonotoneOn (fun k => u (k + 1) - u k) (Set.Ico 0 N)) :
    ‖∑ k ∈ range (N + 1), phaseCharacter (u k)‖ ≤ 1 + 1 / δ := by
  cases N with
  | zero => simpa using (show (1 : ℝ) ≤ 1 + 1 / δ from le_add_of_nonneg_right (by positivity))
  | succ N =>
    have h := norm_sum_phaseCharacter_le_of_monotone_increments u N δ hδ
      (fun k hk => hlo k (by omega)) (fun k hk => hhi k (by omega))
      (fun i hi j hj hij => hmono ⟨hi.1, Nat.lt_succ_of_le hi.2⟩
        ⟨hj.1, Nat.lt_succ_of_le hj.2⟩ hij)
    rw [sum_range_succ]
    calc
      _ ≤ ‖∑ k ∈ range (N + 1), phaseCharacter (u k)‖ +
          ‖phaseCharacter (u (N + 1))‖ := norm_add_le _ _
      _ ≤ 1 / δ + 1 := add_le_add h (le_of_eq (norm_phaseCharacter _))
      _ = 1 + 1 / δ := add_comm _ _

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset Set

noncomputable section

@[simp] theorem phaseCharacter_int (z : ℤ) : phaseCharacter (z : ℝ) = 1 := by
  unfold phaseCharacter
  convert Complex.exp_int_mul_two_pi_mul_I z using 1
  congr 1
  push_cast
  ring

theorem phaseCharacter_sub_int (s : ℝ) (z : ℤ) :
    phaseCharacter (s - z) = phaseCharacter s := by
  have h := (phaseCharacter_add (s - z) z).symm
  simpa only [sub_add_cancel, phaseCharacter_int, mul_one] using h

theorem norm_sum_phaseCharacter_le_of_monotone_deriv
    (f f' : ℝ → ℝ) (a : ℝ) (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (f' x) x)
    (hm : MonotoneOn f' (Set.Ioo a (a + N)))
    (hlo : ∀ x ∈ Set.Ioo a (a + N), δ ≤ f' x)
    (hhi : ∀ x ∈ Set.Ioo a (a + N), f' x ≤ 1 - δ) :
    ‖∑ k ∈ Finset.range (N + 1), phaseCharacter (f (a + k))‖ ≤ 1 + 1 / δ := by
  have hw (k : ℕ) (hk : k < N) : ∃ x ∈ Set.Ioo (a + k) (a + (k + 1 : ℕ)),
      f' x = f (a + (k + 1 : ℕ)) - f (a + k) := by
    have hkn : (k + 1 : ℝ) ≤ N := by exact_mod_cast hk
    have hsub : Set.Icc (a + k) (a + (k + 1 : ℕ)) ⊆ Set.Icc a (a + N) := by
      intro x hx
      simp only [Nat.cast_add, Nat.cast_one, Set.mem_Icc] at hx ⊢
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f f'
      (show a + (k : ℝ) < a + ((k + 1 : ℕ) : ℝ) by push_cast; linarith)
      (hc.mono hsub) (fun x hx => hd x (by
        simp only [Nat.cast_add, Nat.cast_one, Set.mem_Ioo] at hx ⊢
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k]))
    refine ⟨x, hx, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_add_left_eq_sub,
      add_sub_cancel_left, div_one] using he
  have hmem (k : ℕ) (hk : k < N) {x : ℝ}
      (hx : x ∈ Set.Ioo (a + k) (a + (k + 1 : ℕ))) : x ∈ Set.Ioo a (a + N) := by
    have hkn : (k + 1 : ℝ) ≤ N := by exact_mod_cast hk
    simp only [Nat.cast_add, Nat.cast_one, Set.mem_Ioo] at hx ⊢
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k]
  apply norm_sum_phaseCharacter_le_of_monotone_increments_closed
    (fun k => f (a + k)) N δ hδ
  · intro k hk
    obtain ⟨x, hx, he⟩ := hw k hk
    exact he ▸ hlo x (hmem k hk hx)
  · intro k hk
    obtain ⟨x, hx, he⟩ := hw k hk
    exact he ▸ hhi x (hmem k hk hx)
  · intro i hi j hj hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    obtain ⟨x, hx, he⟩ := hw i hi.2
    obtain ⟨y, hy, he'⟩ := hw j hj.2
    have hijR : (i + 1 : ℝ) ≤ j := by exact_mod_cast hij
    have hxy : x ≤ y := by
      simp only [Nat.cast_add, Nat.cast_one, Set.mem_Ioo] at hx hy
      linarith
    dsimp only
    rw [← he, ← he']
    exact hm (hmem i hi.2 hx) (hmem j hj.2 hy) hxy

theorem norm_sum_phaseCharacter_le_of_monotone_deriv_strip
    (f f' : ℝ → ℝ) (a : ℝ) (N : ℕ) (δ : ℝ) (z : ℤ) (hδ : 0 < δ)
    (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (f' x) x)
    (hm : MonotoneOn f' (Set.Ioo a (a + N)))
    (hlo : ∀ x ∈ Set.Ioo a (a + N), (z : ℝ) + δ ≤ f' x)
    (hhi : ∀ x ∈ Set.Ioo a (a + N), f' x ≤ (z : ℝ) + 1 - δ) :
    ‖∑ k ∈ Finset.range (N + 1), phaseCharacter (f (a + k))‖ ≤ 1 + 1 / δ := by
  have h := norm_sum_phaseCharacter_le_of_monotone_deriv
    (fun x => f x - (z : ℝ) * (x - a)) (fun x => f' x - z) a N δ hδ
    (hc.sub (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn)
    (fun x hx => by
      convert (hd x hx).sub (((hasDerivAt_id x).sub_const a).const_mul (z : ℝ)) using 1 <;>
        first | rfl | simp only [mul_one])
    (fun x hx y hy hxy => sub_le_sub_right (hm hx hy hxy) _)
    (fun x hx => by linarith [hlo x hx]) (fun x hx => by linarith [hhi x hx])
  have he (k : ℕ) : phaseCharacter (f (a + k) - (z : ℝ) * (a + k - a)) =
      phaseCharacter (f (a + k)) := by
    rw [add_sub_cancel_left]
    simpa only [Int.cast_mul, Int.cast_natCast] using
      phaseCharacter_sub_int (f (a + k)) (z * (k : ℤ))
  simpa only [he] using h

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset Set

noncomputable section

theorem sub_bounds_of_hasDerivAt_bounds (h h' : ℝ → ℝ) (a b l v s t : ℝ)
    (hc : ContinuousOn h (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt h (h' x) x)
    (hb : ∀ x ∈ Set.Ioo a b, l ≤ h' x ∧ h' x ≤ v)
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    l * (t - s) ≤ h t - h s ∧ h t - h s ≤ v * (t - s) := by
  rcases lt_or_eq_of_le hst with hst | rfl
  · have hsub : Set.Ioo s t ⊆ Set.Ioo a b := fun x hx =>
      ⟨hs.1.trans_lt hx.1, hx.2.trans_le ht.2⟩
    obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope h h' hst
      (hc.mono (Set.Icc_subset_Icc hs.1 ht.2)) (fun x hx => hd x (hsub hx))
    have heq := (eq_div_iff (sub_ne_zero.mpr hst.ne')).mp he
    have hxbound := hb x (hsub hx)
    constructor
    · simpa only [heq] using mul_le_mul_of_nonneg_right hxbound.1 (sub_nonneg.mpr hst.le)
    · simpa only [heq] using mul_le_mul_of_nonneg_right hxbound.2 (sub_nonneg.mpr hst.le)
  · simp

theorem card_nat_le_real_diameter (S : Finset ℕ) (hS : S.Nonempty) :
    (S.card : ℝ) ≤ (S.max' hS : ℝ) - (S.min' hS : ℝ) + 1 := by
  have hsub : S ⊆ Finset.Icc (S.min' hS) (S.max' hS) := fun k hk =>
    Finset.mem_Icc.mpr ⟨S.min'_le k hk, S.le_max' k hk⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hminmax := S.min'_le_max' hS
  have hcast : ((S.max' hS + 1 - S.min' hS : ℕ) : ℝ) =
      (S.max' hS : ℝ) - (S.min' hS : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    ring
  exact (Nat.cast_le.mpr hcard).trans_eq hcast

theorem card_le_of_separated_band (S : Finset ℕ) (d : ℕ → ℝ) (l A B : ℝ)
    (hl : 0 < l) (hAB : A ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → l * ((j : ℝ) - i) ≤ d j - d i)
    (hband : ∀ i ∈ S, A ≤ d i ∧ d i ≤ B) :
    (S.card : ℝ) ≤ (B - A) / l + 1 := by
  obtain hS | hS := S.eq_empty_or_nonempty
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hs := hsep _ (S.min'_mem hS) _ (S.max'_mem hS) (S.min'_le_max' hS)
    have ha := (hband _ (S.min'_mem hS)).1
    have hb := (hband _ (S.max'_mem hS)).2
    have hwidth : (S.max' hS : ℝ) - (S.min' hS : ℝ) ≤ (B - A) / l := by
      apply (le_div_iff₀ hl).mpr
      nlinarith
    linarith [card_nat_le_real_diameter S hS]

theorem card_int_le_real_diameter (S : Finset ℤ) (hS : S.Nonempty) :
    (S.card : ℝ) ≤ (S.max' hS : ℝ) - (S.min' hS : ℝ) + 1 := by
  have hsub : S ⊆ Finset.Icc (S.min' hS) (S.max' hS) := fun k hk =>
    Finset.mem_Icc.mpr ⟨S.min'_le k hk, S.le_max' k hk⟩
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hminmax := S.min'_le_max' hS
  have hcast : (((S.max' hS + 1 - S.min' hS).toNat : ℕ) : ℝ) =
      (S.max' hS : ℝ) - (S.min' hS : ℝ) + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  exact (Nat.cast_le.mpr hcard).trans_eq hcast

theorem card_image_floor_le (S : Finset ℕ) (d : ℕ → ℝ) (δ A B : ℝ)
    (hAB : A ≤ B) (hd : ∀ i ∈ S, A ≤ d i ∧ d i ≤ B) :
    ((S.image (fun i => ⌊d i + δ⌋)).card : ℝ) ≤ B - A + 2 := by
  let K := S.image (fun i => ⌊d i + δ⌋)
  obtain hK | hK := K.eq_empty_or_nonempty
  · change (K.card : ℝ) ≤ _
    rw [hK, Finset.card_empty, Nat.cast_zero]
    linarith
  · obtain ⟨i, hi, hei⟩ := Finset.mem_image.mp (K.min'_mem hK)
    obtain ⟨j, hj, hej⟩ := Finset.mem_image.mp (K.max'_mem hK)
    have hlo := Int.lt_floor_add_one (d i + δ)
    have hhi := Int.floor_le (d j + δ)
    rw [hei] at hlo
    rw [hej] at hhi
    have hwidth : (K.max' hK : ℝ) - (K.min' hK : ℝ) + 1 ≤ B - A + 2 := by
      linarith [(hd i hi).1, (hd j hj).2]
    exact (card_int_le_real_diameter K hK).trans hwidth

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset Set

noncomputable section

def derivativeNear (d : ℕ → ℝ) (N : ℕ) (δ : ℝ) (z : ℤ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun k => ⌊d k + δ⌋ = z ∧ d k < (z : ℝ) + δ)

def derivativeFar (d : ℕ → ℝ) (N : ℕ) (δ : ℝ) (z : ℤ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun k => ⌊d k + δ⌋ = z ∧ (z : ℝ) + δ ≤ d k)

theorem derivativeNear_bounds (d : ℕ → ℝ) (N : ℕ) (δ : ℝ) (z : ℤ)
    {k : ℕ} (hk : k ∈ derivativeNear d N δ z) :
    k ≤ N ∧ (z : ℝ) - δ ≤ d k ∧ d k < (z : ℝ) + δ := by
  obtain ⟨hk, he, hlt⟩ := Finset.mem_filter.mp hk
  have hfloor := Int.floor_le (d k + δ)
  rw [he] at hfloor
  exact ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), by linarith, hlt⟩

theorem derivativeFar_eq_band (d : ℕ → ℝ) (N : ℕ) (δ : ℝ) (z : ℤ) (hδ : 0 ≤ δ) :
    derivativeFar d N δ z = (Finset.range (N + 1)).filter
      (fun k => (z : ℝ) + δ ≤ d k ∧ d k < (z : ℝ) + 1 - δ) := by
  ext k
  simp only [derivativeFar, Finset.mem_filter]
  constructor
  · rintro ⟨hk, he, hlo⟩
    have hfloor := Int.lt_floor_add_one (d k + δ)
    rw [he] at hfloor
    exact ⟨hk, hlo, by linarith⟩
  · rintro ⟨hk, hlo, hhi⟩
    refine ⟨hk, Int.floor_eq_iff.mpr ⟨?_, ?_⟩, hlo⟩ <;> linarith

theorem monotone_band_eq_Icc (d : ℕ → ℝ) (N : ℕ) (A B : ℝ)
    (hm : MonotoneOn d (Set.Icc 0 N))
    (hne : ((Finset.range (N + 1)).filter (fun k => A ≤ d k ∧ d k < B)).Nonempty) :
    let S := (Finset.range (N + 1)).filter (fun k => A ≤ d k ∧ d k < B)
    S = Finset.Icc (S.min' hne) (S.max' hne) := by
  let S := (Finset.range (N + 1)).filter (fun k => A ≤ d k ∧ d k < B)
  change S = _
  have hmin := Finset.mem_filter.mp (S.min'_mem hne)
  have hmax := Finset.mem_filter.mp (S.max'_mem hne)
  have hlo : S.min' hne ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmin.1)
  have hhi : S.max' hne ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmax.1)
  ext k
  constructor
  · intro hk
    exact Finset.mem_Icc.mpr ⟨S.min'_le k hk, S.le_max' k hk⟩
  · intro hk
    obtain ⟨hkl, hkr⟩ := Finset.mem_Icc.mp hk
    have hkN := hkr.trans hhi
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hkN), ?_, ?_⟩
    · exact hmin.2.1.trans (hm ⟨Nat.zero_le _, hlo⟩ ⟨Nat.zero_le _, hkN⟩ hkl)
    · exact (hm ⟨Nat.zero_le _, hkN⟩ ⟨Nat.zero_le _, hhi⟩ hkr).trans_lt hmax.2.2

theorem sum_eq_derivative_near_add_far (d : ℕ → ℝ) (N : ℕ) (δ : ℝ) (w : ℕ → ℂ) :
    (∑ k ∈ Finset.range (N + 1), w k) =
      ∑ z ∈ (Finset.range (N + 1)).image (fun k => ⌊d k + δ⌋),
        ((∑ k ∈ derivativeNear d N δ z, w k) + (∑ k ∈ derivativeFar d N δ z, w k)) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun k hk =>
    Finset.mem_image_of_mem (fun k => ⌊d k + δ⌋) hk) w]
  apply Finset.sum_congr rfl
  intro z hz
  have h := Finset.sum_filter_add_sum_filter_not
    ((Finset.range (N + 1)).filter (fun k => ⌊d k + δ⌋ = z))
    (fun k => d k < (z : ℝ) + δ) w
  simpa only [Finset.filter_filter, not_lt, derivativeNear, derivativeFar] using h.symm

theorem card_derivativeNear_le (d : ℕ → ℝ) (N : ℕ) (δ l : ℝ) (z : ℤ)
    (hδ : 0 ≤ δ) (hl : 0 < l)
    (hsep : ∀ i ≤ N, ∀ j ≤ N, i ≤ j → l * ((j : ℝ) - i) ≤ d j - d i) :
    ((derivativeNear d N δ z).card : ℝ) ≤ 2 * δ / l + 1 := by
  have h := card_le_of_separated_band (derivativeNear d N δ z) d l
    ((z : ℝ) - δ) ((z : ℝ) + δ) hl (by linarith)
    (fun i hi j hj hij => hsep i (derivativeNear_bounds d N δ z hi).1
      j (derivativeNear_bounds d N δ z hj).1 hij)
    (fun i hi => ⟨(derivativeNear_bounds d N δ z hi).2.1,
      (derivativeNear_bounds d N δ z hi).2.2.le⟩)
  convert h using 1
  ring

theorem norm_sum_derivativeFar_le (f h : ℝ → ℝ) (a : ℝ) (N : ℕ) (δ : ℝ) (z : ℤ)
    (hδ : 0 < δ) (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (h x) x)
    (hm : MonotoneOn h (Set.Icc a (a + N))) :
    ‖∑ k ∈ derivativeFar (fun k => h (a + k)) N δ z, phaseCharacter (f (a + k))‖ ≤
      1 + 1 / δ := by
  rw [derivativeFar_eq_band _ _ _ _ hδ.le]
  let S := (Finset.range (N + 1)).filter
    (fun k : ℕ => (z : ℝ) + δ ≤ h (a + k) ∧ h (a + k) < (z : ℝ) + 1 - δ)
  change ‖∑ k ∈ S, _‖ ≤ _
  obtain hS | hS := S.eq_empty_or_nonempty
  · rw [hS, Finset.sum_empty, norm_zero]
    positivity
  · have hsamp (k : ℕ) (hk : k ≤ N) : a + (k : ℝ) ∈ Set.Icc a (a + N) :=
      ⟨by linarith [Nat.cast_nonneg (α := ℝ) k], by linarith [show (k : ℝ) ≤ N by exact_mod_cast hk]⟩
    have hmono : MonotoneOn (fun k : ℕ => h (a + k)) (Set.Icc 0 N) := by
      intro i hi j hj hij
      exact hm (hsamp i hi.2) (hsamp j hj.2) (by linarith [show (i : ℝ) ≤ j by exact_mod_cast hij])
    have he := monotone_band_eq_Icc (fun k => h (a + k)) N ((z : ℝ) + δ)
      ((z : ℝ) + 1 - δ) hmono hS
    let L := S.min' hS
    let R := S.max' hS
    have hL := Finset.mem_filter.mp (S.min'_mem hS)
    have hR := Finset.mem_filter.mp (S.max'_mem hS)
    have hLN : L ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hL.1)
    have hRN : R ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hR.1)
    have hLR : L ≤ R := S.min'_le_max' hS
    have hright : a + (L : ℝ) + ((R - L : ℕ) : ℝ) = a + R := by
      rw [Nat.cast_sub hLR]
      ring
    have hsub : Set.Icc (a + L) (a + L + (R - L : ℕ)) ⊆ Set.Icc a (a + N) := by
      rw [hright]
      exact Set.Icc_subset_Icc (hsamp L hLN).1 (hsamp R hRN).2
    have hsubopen : Set.Ioo (a + L) (a + L + (R - L : ℕ)) ⊆ Set.Ioo a (a + N) := by
      rw [hright]
      exact fun x hx => ⟨(hsamp L hLN).1.trans_lt hx.1, hx.2.trans_le (hsamp R hRN).2⟩
    have hbound := norm_sum_phaseCharacter_le_of_monotone_deriv_strip f h (a + L) (R - L) δ z
      hδ (hc.mono hsub) (fun x hx => hd x (hsubopen hx))
      (fun x hx y hy hxy => hm (hsub (Set.Ioo_subset_Icc_self hx))
        (hsub (Set.Ioo_subset_Icc_self hy)) hxy)
      (fun x hx => hL.2.1.trans (hm (hsamp L hLN)
        (hsub (Set.Ioo_subset_Icc_self hx)) hx.1.le))
      (fun x hx => by
        have hxR : x ≤ a + R := hx.2.le.trans_eq hright
        exact ((hm (hsub (Set.Ioo_subset_Icc_self hx)) (hsamp R hRN) hxR).trans_lt hR.2.2).le)
    have hI : Finset.Icc L R = Finset.Ico L (R + 1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    change S = Finset.Icc L R at he
    rw [he, hI, Finset.sum_Ico_eq_sum_range]
    have hlen : R + 1 - L = R - L + 1 := by omega
    simpa only [hlen, Nat.cast_add, add_assoc] using hbound

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset Set

noncomputable section

theorem norm_sum_phaseCharacter_le_card (S : Finset ℕ) (u : ℕ → ℝ) :
    ‖∑ k ∈ S, phaseCharacter (u k)‖ ≤ (S.card : ℝ) := by
  simpa only [norm_phaseCharacter, Finset.sum_const, nsmul_eq_mul, mul_one] using
    norm_sum_le S (fun k => phaseCharacter (u k))

theorem norm_sum_le_of_derivative_separation (f h : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (δ l A B : ℝ) (hδ : 0 < δ) (hl : 0 < l) (hAB : A ≤ B)
    (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (h x) x)
    (hm : MonotoneOn h (Set.Icc a (a + N)))
    (hsep : ∀ i ≤ N, ∀ j ≤ N, i ≤ j →
      l * ((j : ℝ) - i) ≤ h (a + j) - h (a + i))
    (hband : ∀ k ≤ N, A ≤ h (a + k) ∧ h (a + k) ≤ B) :
    ‖∑ k ∈ Finset.range (N + 1), phaseCharacter (f (a + k))‖ ≤
      (B - A + 2) * (2 * δ / l + 2 + 1 / δ) := by
  let d : ℕ → ℝ := fun k => h (a + k)
  let K := (Finset.range (N + 1)).image (fun k => ⌊d k + δ⌋)
  have hcount : (K.card : ℝ) ≤ B - A + 2 :=
    card_image_floor_le (Finset.range (N + 1)) d δ A B hAB
      (fun k hk => hband k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  have hfiber (z : ℤ) :
      ‖(∑ k ∈ derivativeNear d N δ z, phaseCharacter (f (a + k))) +
        (∑ k ∈ derivativeFar d N δ z, phaseCharacter (f (a + k)))‖ ≤
        2 * δ / l + 2 + 1 / δ := by
    have hn := (norm_sum_phaseCharacter_le_card (derivativeNear d N δ z)
      (fun k => f (a + k))).trans (card_derivativeNear_le d N δ l z hδ.le hl hsep)
    have hf := norm_sum_derivativeFar_le f h a N δ z hδ hc hd hm
    exact (norm_add_le _ _).trans (by linarith)
  rw [sum_eq_derivative_near_add_far d N δ]
  calc
    _ ≤ ∑ z ∈ K, ‖(∑ k ∈ derivativeNear d N δ z, phaseCharacter (f (a + k))) +
        (∑ k ∈ derivativeFar d N δ z, phaseCharacter (f (a + k)))‖ := norm_sum_le _ _
    _ ≤ ∑ _z ∈ K, (2 * δ / l + 2 + 1 / δ) := Finset.sum_le_sum (fun z _ => hfiber z)
    _ = (K.card : ℝ) * (2 * δ / l + 2 + 1 / δ) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (by positivity)

theorem second_derivative_test_parameterized (f h h' : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (δ l v : ℝ) (hδ : 0 < δ) (hl : 0 < l)
    (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (h x) x)
    (hhc : ContinuousOn h (Set.Icc a (a + N)))
    (hhd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt h (h' x) x)
    (hcurv : ∀ x ∈ Set.Ioo a (a + N), l ≤ h' x ∧ h' x ≤ v) :
    ‖∑ k ∈ Finset.range (N + 1), phaseCharacter (f (a + k))‖ ≤
      (v * N + 2) * (2 * δ / l + 2 + 1 / δ) := by
  have hab : a ≤ a + (N : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hsamp (k : ℕ) (hk : k ≤ N) : a + (k : ℝ) ∈ Set.Icc a (a + N) :=
    ⟨by linarith [Nat.cast_nonneg (α := ℝ) k], by linarith [show (k : ℝ) ≤ N by exact_mod_cast hk]⟩
  have hmono : MonotoneOn h (Set.Icc a (a + N)) := by
    intro s hs t ht hst
    have hb := (sub_bounds_of_hasDerivAt_bounds h h' a (a + N) l v s t hhc hhd hcurv hs ht hst).1
    have hh := mul_nonneg hl.le (sub_nonneg.mpr hst)
    linarith
  have hbound := norm_sum_le_of_derivative_separation f h a N δ l (h a) (h (a + N)) hδ hl
    (hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab) hc hd hmono
    (fun i hi j hj hij => by
      have hb := (sub_bounds_of_hasDerivAt_bounds h h' a (a + N) l v (a + i) (a + j)
        hhc hhd hcurv (hsamp i hi) (hsamp j hj) (by linarith [show (i : ℝ) ≤ j by exact_mod_cast hij])).1
      simpa only [add_sub_add_left_eq_sub] using hb)
    (fun k hk => ⟨hmono ⟨le_rfl, hab⟩ (hsamp k hk) (hsamp k hk).1,
      hmono (hsamp k hk) ⟨hab, le_rfl⟩ (hsamp k hk).2⟩)
  have hspan := (sub_bounds_of_hasDerivAt_bounds h h' a (a + N) l v a (a + N)
    hhc hhd hcurv ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab).2
  rw [add_sub_cancel_left] at hspan
  exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

theorem second_derivative_parameter_bound (l A n : ℝ)
    (hl : 0 < l) (hl1 : l ≤ 1) (hA : 0 ≤ A) (hn : 0 ≤ n) :
    (A * l * n + 2) * (2 * Real.sqrt l / l + 2 + 1 / Real.sqrt l) ≤
      10 * (A * n * Real.sqrt l + 1 / Real.sqrt l) := by
  let r := Real.sqrt l
  have hr : 0 < r := Real.sqrt_pos.mpr hl
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr hl1
  have hrsq : r ^ 2 = l := Real.sq_sqrt hl.le
  have hlr : l ≤ r := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hlr (mul_nonneg hA hn)
  have hinv : 1 ≤ 1 / r := (le_div_iff₀ hr).mpr (by linarith)
  have he : (A * l * n + 2) * (2 * r / l + 2 + 1 / r) =
      3 * A * n * r + 2 * A * n * l + 6 / r + 4 := by
    rw [← hrsq]
    field_simp
    ring
  change (A * l * n + 2) * (2 * r / l + 2 + 1 / r) ≤ 10 * (A * n * r + 1 / r)
  rw [he]
  have hpos := mul_nonneg (mul_nonneg hA hn) hr.le
  simp only [div_eq_mul_inv, one_mul] at hinv ⊢
  nlinarith only [hscale, hinv, hpos]

theorem second_derivative_test_small (f h h' : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (l A : ℝ) (hl : 0 < l) (hl1 : l ≤ 1) (hA : 0 ≤ A)
    (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (h x) x)
    (hhc : ContinuousOn h (Set.Icc a (a + N)))
    (hhd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt h (h' x) x)
    (hcurv : ∀ x ∈ Set.Ioo a (a + N), l ≤ h' x ∧ h' x ≤ A * l) :
    ‖∑ k ∈ Finset.range (N + 1), phaseCharacter (f (a + k))‖ ≤
      10 * (A * N * Real.sqrt l + 1 / Real.sqrt l) := by
  exact (second_derivative_test_parameterized f h h' a N (Real.sqrt l) l (A * l)
    (Real.sqrt_pos.mpr hl) hl hc hd hhc hhd hcurv).trans
      (second_derivative_parameter_bound l A N hl hl1 hA (Nat.cast_nonneg N))

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset Set

noncomputable section

theorem sum_Icc_eq_sum_range_shift {R : Type*} [AddCommMonoid R]
    (u : ℕ → R) (A B : ℕ) (hAB : A ≤ B) :
    (∑ k ∈ Finset.Icc A B, u k) = ∑ k ∈ Finset.range (B - A + 1), u (A + k) := by
  calc
    _ = ∑ k ∈ Finset.Ico A (B + 1), u k := by
      apply Finset.sum_congr
      · ext k
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      · intro k hk
        rfl
    _ = ∑ k ∈ Finset.range (B + 1 - A), u (A + k) :=
      Finset.sum_Ico_eq_sum_range u A (B + 1)
    _ = _ := by rw [show B + 1 - A = B - A + 1 by omega]

theorem norm_sum_reciprocalLogCorrelation_Icc_le
    (a L M N n₁ n₂ : ℝ) (A B : ℕ)
    (ha : 0 < a) (hL : 1 ≤ L) (hM : 0 < M) (hN : 0 < N)
    (hnlo : N ≤ n₁) (hnord : n₁ < n₂) (hnhi : n₂ ≤ 2 * N) (hAB : A ≤ B)
    (hlam : a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3) ≤ 1)
    (hbox : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ), M ≤ x ∧ x ≤ 2 * M)
    (hlog : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ),
      L ≤ Real.log (n₁ * x) ∧ Real.log (n₂ * x) ≤ 2 * L) :
    ‖∑ k ∈ Finset.Icc A B,
        phaseCharacter (reciprocalLogCorrelation a n₁ n₂ k)‖ ≤
      10 * (256 * (B - A : ℕ) *
          Real.sqrt (a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3)) +
        1 / Real.sqrt (a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3))) := by
  let lam := a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3)
  have hn₁ : 0 < n₁ := hN.trans_le hnlo
  have hn₂ : 0 < n₂ := hn₁.trans hnord
  have hlampos : 0 < lam := by dsimp [lam]; positivity
  have hend : (A : ℝ) + (B - A : ℕ) = B := by
    rw [Nat.cast_sub hAB]
    ring
  have hmem {x : ℝ} (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      x ∈ Set.Icc (A : ℝ) (B : ℝ) := by rwa [hend] at hx
  let slope : ℝ → ℝ := fun x => reciprocalLogSlope a n₁ x - reciprocalLogSlope a n₂ x
  let curve : ℝ → ℝ := fun x => a / x ^ 2 *
    (logCurvature (Real.log (n₁ * x)) - logCurvature (Real.log (n₂ * x)))
  have hdomain (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      0 < x ∧ 1 < n₁ * x ∧ 1 < n₂ * x := by
    have hm := (hbox x (hmem hx)).1
    have hxp : 0 < x := hM.trans_le hm
    have hl := (hlog x (hmem hx)).1
    have hp₁ : 1 < n₁ * x :=
      (Real.log_pos_iff (mul_nonneg hn₁.le hxp.le)).mp
        ((lt_of_lt_of_le zero_lt_one hL).trans_le hl)
    exact ⟨hxp, hp₁, hp₁.trans_le (mul_le_mul_of_nonneg_right hnord.le hxp.le)⟩
  have hfirst (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      HasDerivAt (reciprocalLogCorrelation a n₁ n₂) (slope x) x := by
    have hd := hdomain x hx
    exact (hasDerivAt_reciprocalLogPhase a n₁ x hn₁ hd.1 hd.2.1).sub
      (hasDerivAt_reciprocalLogPhase a n₂ x hn₂ hd.1 hd.2.2)
  have hsecond (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      HasDerivAt slope (curve x) x := by
    have hd := hdomain x hx
    convert (hasDerivAt_reciprocalLogSlope a n₁ x hn₁ hd.1 hd.2.1).sub
      (hasDerivAt_reciprocalLogSlope a n₂ x hn₂ hd.1 hd.2.2) using 1 <;>
      first | rfl | (dsimp [slope, curve]; ring)
  have hcurv (x : ℝ) (hx : x ∈ Set.Ioo (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      lam ≤ curve x ∧ curve x ≤ 256 * lam := by
    have hm := hbox x (hmem (Set.Ioo_subset_Icc_self hx))
    have hlg := hlog x (hmem (Set.Ioo_subset_Icc_self hx))
    have hb := deriv2_reciprocalLogCorrelation_bounds a L M N n₁ n₂ x ha.le hL hM hN
      hm.1 hm.2 hnlo hnord.le hnhi hlg.1 hlg.2
    have hd := hdomain x (Set.Ioo_subset_Icc_self hx)
    rw [deriv2_reciprocalLogCorrelation a n₁ n₂ x hn₁ hn₂ hd.1 hd.2.1 hd.2.2] at hb
    dsimp [lam, curve]
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    ring
  have ht := second_derivative_test_small (reciprocalLogCorrelation a n₁ n₂)
    slope curve (A : ℝ) (B - A) lam 256 hlampos hlam (by norm_num)
    (fun x hx => (hfirst x hx).continuousAt.continuousWithinAt)
    (fun x hx => hfirst x (Set.Ioo_subset_Icc_self hx))
    (fun x hx => (hsecond x hx).continuousAt.continuousWithinAt)
    (fun x hx => hsecond x (Set.Ioo_subset_Icc_self hx)) hcurv
  rw [sum_Icc_eq_sum_range_shift _ A B hAB]
  simpa only [Nat.cast_add] using ht

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset Set

open scoped ComplexConjugate

noncomputable section

theorem sum_Ioc_eq_sum_Icc_succ {R : Type*} [AddCommMonoid R]
    (u : ℕ → R) (A B : ℕ) :
    (∑ k ∈ Finset.Ioc A B, u k) = ∑ k ∈ Finset.Icc (A + 1) B, u k := by
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  · intro k hk
    rfl

theorem norm_sum_bandPhase_correlation_le
    (a C : ℝ) (M B P Y N n₁ n₂ : ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hnlo : N ≤ n₁) (hnord : n₁ < n₂) (hnhi : n₂ ≤ 2 * N)
    (hlam : a * ((n₂ : ℝ) - n₁) /
      (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) ≤ 1) :
    let lo := max M (max (P / n₁) (P / n₂))
    let hi := min B (min (Y / n₁) (Y / n₂))
    let lam := a * ((n₂ : ℝ) - n₁) /
      (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
    ‖∑ m ∈ Finset.Ioc M B,
        bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ ≤
      10 * (256 * (hi - (lo + 1) : ℕ) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  dsimp only
  let lo := max M (max (P / n₁) (P / n₂))
  let hi := min B (min (Y / n₁) (Y / n₂))
  let lam := a * ((n₂ : ℝ) - n₁) /
    (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
  have hn₁ : 0 < n₁ := hN.trans_le hnlo
  have hn₂ : 0 < n₂ := hn₁.trans hnord
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hPreal : (0 : ℝ) < P := by exact_mod_cast hP
  have hnordreal : (n₁ : ℝ) < n₂ := by exact_mod_cast hnord
  have hlogPpos : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hPlog
  have hlampos : 0 < lam := by
    dsimp [lam]
    exact div_pos (mul_pos ha (sub_pos.mpr hnordreal)) (by positivity)
  rw [sum_bandPhase_correlation a M B P Y n₁ n₂ hn₁ hn₂]
  change ‖∑ m ∈ Finset.Ioc lo hi,
    phaseCharacter (reciprocalLogCorrelation a (n₁ : ℝ) (n₂ : ℝ) (m : ℝ))‖ ≤ _
  by_cases hli : lo < hi
  · rw [sum_Ioc_eq_sum_Icc_succ]
    apply norm_sum_reciprocalLogCorrelation_Icc_le a (Real.log (P : ℝ))
      (M : ℝ) (N : ℝ) (n₁ : ℝ) (n₂ : ℝ) (lo + 1) hi
      ha hPlog hMreal hNreal
      (by exact_mod_cast hnlo) (by exact_mod_cast hnord) (by exact_mod_cast hnhi)
      (by omega) hlam
    · intro x hx
      have hxlo : ((max M (max (P / n₁) (P / n₂)) + 1 : ℕ) : ℝ) ≤ x := by
        simpa only [lo] using hx.1
      have hxhi : x ≤ ((min B (min (Y / n₁) (Y / n₂)) : ℕ) : ℝ) := by
        simpa only [hi] using hx.2
      rcases correlation_real_hull_bounds M B P Y n₁ n₂ hn₁ hn₂ x hxlo hxhi with
        ⟨hxM, hxB, hp₁lo, hp₁hi, hp₂lo, hp₂hi⟩
      refine ⟨hxM.le, hxB.trans ?_⟩
      exact_mod_cast hB
    · intro x hx
      have hxlo : ((max M (max (P / n₁) (P / n₂)) + 1 : ℕ) : ℝ) ≤ x := by
        simpa only [lo] using hx.1
      have hxhi : x ≤ ((min B (min (Y / n₁) (Y / n₂)) : ℕ) : ℝ) := by
        simpa only [hi] using hx.2
      rcases correlation_real_hull_bounds M B P Y n₁ n₂ hn₁ hn₂ x hxlo hxhi with
        ⟨hxM, hxB, hp₁lo, hp₁hi, hp₂lo, hp₂hi⟩
      constructor
      · exact Real.log_le_log hPreal hp₁lo.le
      · calc
          Real.log ((n₂ : ℝ) * x) ≤ Real.log (C * P) :=
            Real.log_le_log (mul_pos (by exact_mod_cast hn₂) (hMreal.trans hxM))
              (hp₂hi.trans hY)
          _ = Real.log C + Real.log (P : ℝ) := Real.log_mul hC.ne' hPreal.ne'
          _ ≤ 2 * Real.log (P : ℝ) := by
            linarith [Real.log_le_log hC hCP]
  · rw [Finset.Ioc_eq_empty hli, Finset.sum_empty, norm_zero]
    positivity

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

noncomputable section

theorem norm_sum_range_smul_le_two_mul_endpoint
    (f : ℕ → ℝ) (g : ℕ → ℂ) (n : ℕ) (B : ℝ)
    (hf0 : 0 ≤ f 0) (hf : Monotone f) (hB : 0 ≤ B)
    (hpartial : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, g i‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, f i • g i‖ ≤ 2 * f n * B := by
  rw [Finset.sum_range_by_parts]
  have hflast : 0 ≤ f (n - 1) := hf0.trans (hf (Nat.zero_le _))
  have hfirst :
      ‖f (n - 1) • ∑ i ∈ Finset.range n, g i‖ ≤ f (n - 1) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hflast]
    exact mul_le_mul_of_nonneg_left (hpartial n le_rfl) hflast
  have hsecond :
      ‖∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j‖ ≤
        (f (n - 1) - f 0) * B := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n - 1),
          ‖(f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i) * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hdiff : 0 ≤ f (i + 1) - f i := sub_nonneg.mpr (hf (Nat.le_succ i))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
        apply mul_le_mul_of_nonneg_left _ hdiff
        apply hpartial
        have : i < n - 1 := Finset.mem_range.mp hi
        omega
      _ = (f (n - 1) - f 0) * B := by
        rw [← Finset.sum_mul, Finset.sum_range_sub]
  calc
    ‖f (n - 1) • ∑ i ∈ Finset.range n, g i -
        ∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j‖ ≤
        ‖f (n - 1) • ∑ i ∈ Finset.range n, g i‖ +
          ‖∑ i ∈ Finset.range (n - 1),
            (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j‖ :=
      norm_sub_le _ _
    _ ≤ f (n - 1) * B + (f (n - 1) - f 0) * B := add_le_add hfirst hsecond
    _ = 2 * f (n - 1) * B - f 0 * B := by ring
    _ ≤ 2 * f (n - 1) * B := sub_le_self _ (mul_nonneg hf0 hB)
    _ ≤ 2 * f n * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hf (Nat.sub_le n 1)) (by norm_num)) hB

theorem norm_sum_range_log_mul_le
    (Q n : ℕ) (g : ℕ → ℂ) (B : ℝ) (hQ : 1 ≤ Q) (hB : 0 ≤ B)
    (hpartial : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, g i‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, (Real.log (Q + i : ℕ) : ℂ) * g i‖ ≤
      2 * Real.log (Q + n : ℕ) * B := by
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog0 : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg hQreal
  have hmono : Monotone (fun i : ℕ => Real.log (Q + i : ℕ)) := by
    intro i j hij
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.add_le_add_left hij Q
  have h := norm_sum_range_smul_le_two_mul_endpoint
    (fun i : ℕ => Real.log (Q + i : ℕ)) g n B hlog0 hmono hB hpartial
  simpa only [Complex.real_smul] using h

theorem norm_sum_Icc_log_mul_le
    (u : ℕ → ℂ) (A B : ℕ) (E : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hE : 0 ≤ E)
    (hpartial : ∀ r ≤ B - A + 1,
      ‖∑ i ∈ Finset.range r, u (A + i)‖ ≤ E) :
    ‖∑ k ∈ Finset.Icc A B, (Real.log (k : ℝ) : ℂ) * u k‖ ≤
      2 * Real.log (B + 1 : ℕ) * E := by
  rw [sum_Icc_eq_sum_range_shift _ A B hAB]
  have h := norm_sum_range_log_mul_le A (B - A + 1) (fun i => u (A + i)) E
    hA hE hpartial
  convert h using 1
  rw [show A + (B - A + 1) = B + 1 by omega]

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

open scoped ComplexConjugate

noncomputable section

theorem ofReal_sum_norm_sq_eq_sum_correlation
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (J : Finset β) (b : β → ℝ) (phi878 : α → β → ℂ) :
    ((∑ m ∈ I, ‖∑ n ∈ J, (b n : ℂ) * phi878 m n‖ ^ 2) : ℂ) =
      ∑ n₁ ∈ J, ∑ n₂ ∈ J, ((b n₁ * b n₂ : ℝ) : ℂ) *
        ∑ m ∈ I, phi878 m n₁ * conj (phi878 m n₂) := by
  simp_rw [← Complex.mul_conj']
  simp_rw [map_sum, map_mul, Complex.conj_ofReal]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₁ hn₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₂ hn₂
  apply Finset.sum_congr rfl
  intro m hm
  rw [Complex.ofReal_mul]
  ring

theorem sum_norm_sq_inner_le_sum_abs_mul_norm_correlation
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (J : Finset β) (b : β → ℝ) (phi878 : α → β → ℂ) :
    (∑ m ∈ I, ‖∑ n ∈ J, (b n : ℂ) * phi878 m n‖ ^ 2) ≤
      ∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
        ‖∑ m ∈ I, phi878 m n₁ * conj (phi878 m n₂)‖ := by
  let R : ℝ := ∑ m ∈ I, ‖∑ n ∈ J, (b n : ℂ) * phi878 m n‖ ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexpand := ofReal_sum_norm_sq_eq_sum_correlation I J b phi878
  change R ≤ _
  calc
    R = ‖(R : ℂ)‖ := by simp [abs_of_nonneg hR]
    _ = ‖∑ n₁ ∈ J, ∑ n₂ ∈ J, ((b n₁ * b n₂ : ℝ) : ℂ) *
        ∑ m ∈ I, phi878 m n₁ * conj (phi878 m n₂)‖ :=
      congrArg norm (by simpa [R] using hexpand)
    _ ≤ ∑ n₁ ∈ J, ‖∑ n₂ ∈ J, ((b n₁ * b n₂ : ℝ) : ℂ) *
        ∑ m ∈ I, phi878 m n₁ * conj (phi878 m n₂)‖ := norm_sum_le _ _
    _ ≤ ∑ n₁ ∈ J, ∑ n₂ ∈ J, ‖((b n₁ * b n₂ : ℝ) : ℂ) *
        ∑ m ∈ I, phi878 m n₁ * conj (phi878 m n₂)‖ := by
      apply Finset.sum_le_sum
      intro n₁ hn₁
      exact norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n₁ hn₁
      apply Finset.sum_congr rfl
      intro n₂ hn₂
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_sq_sum_mul_sum_le_sq_sum_mul_correlation
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (J : Finset β) (a : α → ℝ) (b : β → ℝ) (phi878 : α → β → ℂ) :
    ‖∑ m ∈ I, (a m : ℂ) * ∑ n ∈ J, (b n : ℂ) * phi878 m n‖ ^ 2 ≤
      (∑ m ∈ I, a m ^ 2) *
        ∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
          ‖∑ m ∈ I, phi878 m n₁ * conj (phi878 m n₂)‖ := by
  let v : α → ℂ := fun m => ∑ n ∈ J, (b n : ℂ) * phi878 m n
  have htri :
      ‖∑ m ∈ I, (a m : ℂ) * v m‖ ≤ ∑ m ∈ I, |a m| * ‖v m‖ := by
    calc
      _ ≤ ∑ m ∈ I, ‖(a m : ℂ) * v m‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsquare :
      ‖∑ m ∈ I, (a m : ℂ) * v m‖ ^ 2 ≤ (∑ m ∈ I, |a m| * ‖v m‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq I (fun m => |a m|) (fun m => ‖v m‖)
  have hcorr := sum_norm_sq_inner_le_sum_abs_mul_norm_correlation I J b phi878
  change ‖∑ m ∈ I, (a m : ℂ) * v m‖ ^ 2 ≤ _
  calc
    _ ≤ (∑ m ∈ I, |a m| * ‖v m‖) ^ 2 := hsquare
    _ ≤ (∑ m ∈ I, a m ^ 2) * ∑ m ∈ I, ‖v m‖ ^ 2 := by
      simpa only [sq_abs] using hcauchy
    _ ≤ (∑ m ∈ I, a m ^ 2) *
        ∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
          ‖∑ m ∈ I, phi878 m n₁ * conj (phi878 m n₂)‖ :=
      mul_le_mul_of_nonneg_left hcorr (Finset.sum_nonneg fun _ _ => sq_nonneg _)

@[simp] theorem norm_bandPhase_le_one (a : ℝ) (P Y m n : ℕ) :
    ‖bandPhase a P Y m n‖ ≤ 1 := by
  unfold bandPhase
  split_ifs <;> simp

theorem norm_sum_bandPhase_correlation_le_card
    (a : ℝ) (P Y n₁ n₂ : ℕ) (I : Finset ℕ) :
    ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ ≤ I.card := by
  calc
    _ ≤ ∑ m ∈ I, ‖bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, Complex.norm_conj]
      simpa using mul_le_mul (norm_bandPhase_le_one a P Y m n₁)
        (norm_bandPhase_le_one a P Y m n₂) (norm_nonneg _) zero_le_one
    _ = I.card := by simp

theorem norm_sum_bandPhase_correlation_comm
    (a : ℝ) (P Y n₁ n₂ : ℕ) (I : Finset ℕ) :
    ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ =
      ‖∑ m ∈ I, bandPhase a P Y m n₂ * conj (bandPhase a P Y m n₁)‖ := by
  have hconj :
      conj (∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)) =
        ∑ m ∈ I, bandPhase a P Y m n₂ * conj (bandPhase a P Y m n₁) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [map_mul, Complex.conj_conj]
    ring
  calc
    _ = ‖conj (∑ m ∈ I,
        bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂))‖ :=
      (Complex.norm_conj _).symm
    _ = _ := congrArg norm hconj

noncomputable def typeIICorrelationBound
    (a : ℝ) (M B P Y N n₁ n₂ : ℕ) : ℝ :=
  let p := min n₁ n₂
  let q := max n₁ n₂
  let lo := max M (max (P / p) (P / q))
  let hi := min B (min (Y / p) (Y / q))
  let lam := a * ((q : ℝ) - p) /
    (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
  10 * (256 * (hi - (lo + 1) : ℕ) * Real.sqrt lam + 1 / Real.sqrt lam)

theorem norm_sum_bandPhase_correlation_le_symmetric
    (a C : ℝ) (M B P Y N n₁ n₂ : ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hn₁lo : N ≤ n₁) (hn₁hi : n₁ ≤ 2 * N)
    (hn₂lo : N ≤ n₂) (hn₂hi : n₂ ≤ 2 * N) (hne : n₁ ≠ n₂)
    (hlam : a * (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) /
      (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) ≤ 1) :
    ‖∑ m ∈ Finset.Ioc M B,
        bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ ≤
      typeIICorrelationBound a M B P Y N n₁ n₂ := by
  have hord : min n₁ n₂ < max n₁ n₂ := min_lt_max.mpr hne
  have hlo : N ≤ min n₁ n₂ := le_min hn₁lo hn₂lo
  have hhi : max n₁ n₂ ≤ 2 * N := max_le hn₁hi hn₂hi
  have ht := norm_sum_bandPhase_correlation_le a C M B P Y N
    (min n₁ n₂) (max n₁ n₂) ha hC hP hPlog hCP hY hM hB hN hlo hord hhi hlam
  by_cases h : n₁ ≤ n₂
  · simpa [typeIICorrelationBound, min_eq_left h, max_eq_right h] using ht
  · have hrev : n₂ ≤ n₁ := le_of_not_ge h
    rw [norm_sum_bandPhase_correlation_comm a P Y n₁ n₂]
    simpa [typeIICorrelationBound, min_eq_right hrev, max_eq_left hrev] using ht

theorem sum_abs_mul_norm_bandPhase_correlation_le_ite
    (a : ℝ) (P Y : ℕ) (I J : Finset ℕ) (b : ℕ → ℝ) (K : ℕ → ℕ → ℝ)
    (hoff : ∀ n₁ ∈ J, ∀ n₂ ∈ J, n₁ ≠ n₂ →
      ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ ≤ K n₁ n₂) :
    (∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
        ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖) ≤
      ∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
        (if n₁ = n₂ then (I.card : ℝ) else K n₁ n₂) := by
  apply Finset.sum_le_sum
  intro n₁ hn₁
  apply Finset.sum_le_sum
  intro n₂ hn₂
  split_ifs with h
  · subst n₂
    exact mul_le_mul_of_nonneg_left
      (norm_sum_bandPhase_correlation_le_card a P Y n₁ n₁ I)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  ·
    exact mul_le_mul_of_nonneg_left (hoff n₁ hn₁ n₂ hn₂ h)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem sum_abs_mul_ite_eq_diagonal_add_offDiagonal
    (J : Finset ℕ) (b : ℕ → ℝ) (D : ℝ) (K : ℕ → ℕ → ℝ) :
    (∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
        (if n₁ = n₂ then D else K n₁ n₂)) =
      D * (∑ n ∈ J, b n ^ 2) +
        ∑ n₁ ∈ J, ∑ n₂ ∈ J,
          if n₁ = n₂ then 0 else |b n₁| * |b n₂| * K n₁ n₂ := by
  calc
    _ = ∑ n₁ ∈ J, (|b n₁| ^ 2 * D +
        ∑ n₂ ∈ J, if n₁ = n₂ then 0 else |b n₁| * |b n₂| * K n₁ n₂) := by
      apply Finset.sum_congr rfl
      intro n₁ hn₁
      calc
        _ = (∑ n₂ ∈ J, if n₁ = n₂ then |b n₁| * |b n₂| * D else 0) +
            ∑ n₂ ∈ J, if n₁ = n₂ then 0 else |b n₁| * |b n₂| * K n₁ n₂ := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro n₂ hn₂
          split_ifs <;> ring
        _ = _ := by simp [hn₁, pow_two]
    _ = (∑ n ∈ J, |b n| ^ 2 * D) +
        ∑ n₁ ∈ J, ∑ n₂ ∈ J,
          if n₁ = n₂ then 0 else |b n₁| * |b n₂| * K n₁ n₂ := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [← Finset.sum_mul]
      simp_rw [sq_abs]
      ring

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

noncomputable section

def typeIIUpperPairs (J : Finset ℕ) : Finset (ℕ × ℕ) :=
  (J ×ˢ J).filter fun p => p.1 < p.2

def typeIIShiftPairs (N : ℕ) (J : Finset ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc 0 N ×ˢ J).filter fun p => p.2 + p.1 ∈ J

theorem sum_typeIIUpperPairs_eq_sum_typeIIShiftPairs
    {R : Type*} [AddCommMonoid R] (N : ℕ) (J : Finset ℕ)
    (F : ℕ → ℕ → R) (hJ : J ⊆ Finset.Ioc N (2 * N)) :
    ∑ p ∈ typeIIUpperPairs J, F p.1 p.2 =
      ∑ p ∈ typeIIShiftPairs N J, F p.2 (p.2 + p.1) := by
  refine Finset.sum_nbij'
    (i := fun p : ℕ × ℕ => (p.2 - p.1, p.1))
    (j := fun p : ℕ × ℕ => (p.2, p.2 + p.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n₁, n₂⟩ hp
    simp only [typeIIUpperPairs, typeIIShiftPairs, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨hn₁, hn₂⟩, hlt⟩ := hp
    have hn₁Ioc := Finset.mem_Ioc.mp (hJ hn₁)
    have hn₂Ioc := Finset.mem_Ioc.mp (hJ hn₂)
    refine ⟨⟨⟨Nat.sub_pos_iff_lt.mpr hlt, ?_⟩, hn₁⟩, ?_⟩
    · omega
    · simpa [Nat.add_sub_of_le hlt.le] using hn₂
  · rintro ⟨d, n⟩ hp
    simp only [typeIIUpperPairs, typeIIShiftPairs, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨hd, hn⟩, hnd⟩ := hp
    exact ⟨⟨hn, hnd⟩, by omega⟩
  · rintro ⟨n₁, n₂⟩ hp
    simp only [typeIIUpperPairs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨_, hlt⟩ := hp
    simp [Nat.add_sub_of_le hlt.le]
  · rintro ⟨d, n⟩ hp
    simp
  · rintro ⟨n₁, n₂⟩ hp
    simp only [typeIIUpperPairs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨_, hlt⟩ := hp
    simp [Nat.add_sub_of_le hlt.le]

theorem sum_typeIIUpperPairs_eq_sum_lt
    {R : Type*} [AddCommMonoid R] (J : Finset ℕ) (F : ℕ → ℕ → R) :
    ∑ p ∈ typeIIUpperPairs J, F p.1 p.2 =
      ∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ < n₂ then F n₁ n₂ else 0 := by
  rw [typeIIUpperPairs, Finset.sum_filter, Finset.sum_product]

theorem sum_offDiagonal_eq_two_mul_sum_typeIIUpperPairs
    {R : Type*} [CommSemiring R] (J : Finset ℕ) (F : ℕ → ℕ → R)
    (hsymm : ∀ n₁ ∈ J, ∀ n₂ ∈ J, F n₁ n₂ = F n₂ n₁) :
    (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else F n₁ n₂) =
      2 * ∑ p ∈ typeIIUpperPairs J, F p.1 p.2 := by
  have hsplit :
      (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else F n₁ n₂) =
        (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ < n₂ then F n₁ n₂ else 0) +
        (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₂ < n₁ then F n₁ n₂ else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n₁ hn₁
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n₂ hn₂
    rcases lt_trichotomy n₁ n₂ with hlt | heq | hgt
    · have hnot : ¬n₂ < n₁ := Nat.not_lt.mpr hlt.le
      simp [hlt, hlt.ne, hnot]
    · subst n₂
      simp
    · have hnot : ¬n₁ < n₂ := Nat.not_lt.mpr hgt.le
      simp [hgt, hgt.ne', hnot]
  have hlower :
      (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₂ < n₁ then F n₁ n₂ else 0) =
        ∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ < n₂ then F n₁ n₂ else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n₁ hn₁
    apply Finset.sum_congr rfl
    intro n₂ hn₂
    by_cases hlt : n₁ < n₂
    · simp [hlt, hsymm n₂ hn₂ n₁ hn₁]
    · simp [hlt]
  rw [hsplit, hlower, ← sum_typeIIUpperPairs_eq_sum_lt J F]
  ring

theorem sum_typeIIShiftPairs_eq_sum_shift
    {R : Type*} [AddCommMonoid R] (N : ℕ) (J : Finset ℕ)
    (G : ℕ → ℕ → R) :
    ∑ p ∈ typeIIShiftPairs N J, G p.1 p.2 =
      ∑ d ∈ Finset.Ioc 0 N, ∑ n ∈ J,
        if n + d ∈ J then G d n else 0 := by
  rw [typeIIShiftPairs, Finset.sum_filter, Finset.sum_product]

theorem sum_offDiagonal_eq_two_mul_sum_shifts
    {R : Type*} [CommSemiring R] (N : ℕ) (J : Finset ℕ)
    (F : ℕ → ℕ → R) (hJ : J ⊆ Finset.Ioc N (2 * N))
    (hsymm : ∀ n₁ ∈ J, ∀ n₂ ∈ J, F n₁ n₂ = F n₂ n₁) :
    (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else F n₁ n₂) =
      2 * ∑ d ∈ Finset.Ioc 0 N, ∑ n ∈ J,
        if n + d ∈ J then F n (n + d) else 0 := by
  rw [sum_offDiagonal_eq_two_mul_sum_typeIIUpperPairs J F hsymm]
  rw [sum_typeIIUpperPairs_eq_sum_typeIIShiftPairs N J F hJ]
  rw [sum_typeIIShiftPairs_eq_sum_shift N J
    (fun d n => F n (n + d))]

theorem sum_sq_shift_le_sum_sq (J : Finset ℕ) (b : ℕ → ℝ) (d : ℕ) :
    (∑ n ∈ J.filter (fun n => n + d ∈ J), b (n + d) ^ 2) ≤
      ∑ n ∈ J, b n ^ 2 := by
  let S := J.filter fun n => n + d ∈ J
  have hinj : Set.InjOn (fun n : ℕ => n + d) (↑S : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ h
    exact Nat.add_right_cancel h
  have himage : Finset.image (fun n : ℕ => n + d) S ⊆ J := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hn).2
  change (∑ n ∈ S, b (n + d) ^ 2) ≤ _
  calc
    _ = ∑ k ∈ Finset.image (fun n : ℕ => n + d) S, b k ^ 2 := by
      symm
      exact Finset.sum_image hinj
    _ ≤ ∑ n ∈ J, b n ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun n hnJ hnimage => sq_nonneg (b n))

theorem sum_abs_mul_shift_le_sum_sq (J : Finset ℕ) (b : ℕ → ℝ) (d : ℕ) :
    (∑ n ∈ J.filter (fun n => n + d ∈ J), |b n| * |b (n + d)|) ≤
      ∑ n ∈ J, b n ^ 2 := by
  let S := J.filter fun n => n + d ∈ J
  have hfirst : (∑ n ∈ S, b n ^ 2) ≤ ∑ n ∈ J, b n ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n hnJ hnS
    exact sq_nonneg (b n)
  have hsecond : (∑ n ∈ S, b (n + d) ^ 2) ≤ ∑ n ∈ J, b n ^ 2 := by
    simpa [S] using sum_sq_shift_le_sum_sq J b d
  change (∑ n ∈ S, |b n| * |b (n + d)|) ≤ _
  calc
    _ ≤ ∑ n ∈ S, (b n ^ 2 + b (n + d) ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have h := two_mul_le_add_sq |b n| |b (n + d)|
      rw [sq_abs, sq_abs] at h
      linarith
    _ = ((∑ n ∈ S, b n ^ 2) + ∑ n ∈ S, b (n + d) ^ 2) / 2 := by
      calc
        _ = (∑ n ∈ S, b n ^ 2 / 2) +
            ∑ n ∈ S, b (n + d) ^ 2 / 2 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := by
          rw [← Finset.sum_div, ← Finset.sum_div]
          ring
    _ ≤ ((∑ n ∈ J, b n ^ 2) + ∑ n ∈ J, b n ^ 2) / 2 := by
      gcongr
    _ = ∑ n ∈ J, b n ^ 2 := by ring

theorem sum_shift_kernel_le_moment_mul_sum
    (N : ℕ) (J : Finset ℕ) (b : ℕ → ℝ) (K : ℕ → ℝ)
    (hK : ∀ d ∈ Finset.Ioc 0 N, 0 ≤ K d) :
    (∑ d ∈ Finset.Ioc 0 N, ∑ n ∈ J,
        if n + d ∈ J then |b n| * |b (n + d)| * K d else 0) ≤
      (∑ n ∈ J, b n ^ 2) * ∑ d ∈ Finset.Ioc 0 N, K d := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [← Finset.sum_filter]
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_abs_mul_shift_le_sum_sq J b d) (hK d hd)

theorem sum_offDiagonal_distanceKernel_le
    (N : ℕ) (J : Finset ℕ) (b : ℕ → ℝ) (K : ℕ → ℝ)
    (hJ : J ⊆ Finset.Ioc N (2 * N))
    (hK : ∀ d ∈ Finset.Ioc 0 N, 0 ≤ K d) :
    (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else
        |b n₁| * |b n₂| * K (max n₁ n₂ - min n₁ n₂)) ≤
      2 * (∑ n ∈ J, b n ^ 2) * ∑ d ∈ Finset.Ioc 0 N, K d := by
  let F : ℕ → ℕ → ℝ := fun n₁ n₂ =>
    |b n₁| * |b n₂| * K (max n₁ n₂ - min n₁ n₂)
  have hsymm : ∀ n₁ ∈ J, ∀ n₂ ∈ J, F n₁ n₂ = F n₂ n₁ := by
    intro n₁ hn₁ n₂ hn₂
    dsimp [F]
    rw [max_comm, min_comm]
    ring
  rw [show (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else
      |b n₁| * |b n₂| * K (max n₁ n₂ - min n₁ n₂)) =
      ∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else F n₁ n₂ by rfl]
  rw [sum_offDiagonal_eq_two_mul_sum_shifts N J F hJ hsymm]
  have hshift := sum_shift_kernel_le_moment_mul_sum N J b K hK
  calc
    2 * (∑ d ∈ Finset.Ioc 0 N, ∑ n ∈ J,
        if n + d ∈ J then F n (n + d) else 0) ≤
        2 * ((∑ n ∈ J, b n ^ 2) * ∑ d ∈ Finset.Ioc 0 N, K d) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [F] using hshift
      · norm_num
    _ = 2 * (∑ n ∈ J, b n ^ 2) * ∑ d ∈ Finset.Ioc 0 N, K d := by ring

noncomputable def typeIIDistanceBound
    (a : ℝ) (M P N d : ℕ) : ℝ :=
  let lam := a * (d : ℝ) /
    (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
  10 * (512 * (M : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam)

theorem typeIIDistanceBound_nonneg
    (a : ℝ) (M P N d : ℕ) :
    0 ≤ typeIIDistanceBound a M P N d := by
  dsimp [typeIIDistanceBound]
  exact mul_nonneg (by norm_num)
    (add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg M)) (Real.sqrt_nonneg _))
      (div_nonneg zero_le_one (Real.sqrt_nonneg _)))

theorem typeIICorrelationBound_le_typeIIDistanceBound
    (a : ℝ) (M B P Y N n₁ n₂ : ℕ) (hB : B ≤ 2 * M) :
    typeIICorrelationBound a M B P Y N n₁ n₂ ≤
      typeIIDistanceBound a M P N (max n₁ n₂ - min n₁ n₂) := by
  let p := min n₁ n₂
  let q := max n₁ n₂
  let lo := max M (max (P / p) (P / q))
  let hi := min B (min (Y / p) (Y / q))
  let lam := a * ((q : ℝ) - p) /
    (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
  have hpq : p ≤ q := by simp [p, q]
  have hlen : hi - (lo + 1) ≤ 2 * M := by
    exact (Nat.sub_le hi (lo + 1)).trans ((min_le_left _ _).trans hB)
  have hlenReal : ((hi - (lo + 1) : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
    exact_mod_cast hlen
  have hlam :
      a * ((max n₁ n₂ - min n₁ n₂ : ℕ) : ℝ) /
          (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) = lam := by
    rw [Nat.cast_sub (show min n₁ n₂ ≤ max n₁ n₂ from min_le_max)]
  dsimp [typeIICorrelationBound, typeIIDistanceBound]
  rw [hlam]
  have hsqrt : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  nlinarith

theorem sum_sqrt_Ioc_le_mul_sqrt (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N, Real.sqrt (d : ℝ)) ≤
      (N : ℝ) * Real.sqrt (N : ℝ) := by
  calc
    _ ≤ ∑ _d ∈ Finset.Ioc 0 N, Real.sqrt (N : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Ioc.mp hd).2)
    _ = (N : ℝ) * Real.sqrt (N : ℝ) := by
      simp [Nat.card_Ioc]

theorem sum_Ioc_sub_eq (f : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N, (f d - f (d - 1))) = f N - f 0 := by
  calc
    _ = ∑ k ∈ Finset.range N, (f (k + 1) - f k) := by
      refine Finset.sum_nbij'
        (i := fun d : ℕ => d - 1) (j := fun k : ℕ => k + 1) ?_ ?_ ?_ ?_ ?_
      · intro d hd
        simp only [Finset.mem_Ioc, Finset.mem_range] at hd ⊢
        omega
      · intro k hk
        simp only [Finset.mem_range, Finset.mem_Ioc] at hk ⊢
        omega
      · intro d hd
        simp only [Finset.mem_Ioc] at hd
        omega
      · intro k hk
        simp
      · intro d hd
        simp only [Finset.mem_Ioc] at hd
        rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
    _ = _ := Finset.sum_range_sub f N

theorem one_div_sqrt_le_two_mul_sqrt_sub (d : ℕ) (hd : 0 < d) :
    1 / Real.sqrt (d : ℝ) ≤
      2 * (Real.sqrt (d : ℝ) - Real.sqrt ((d - 1 : ℕ) : ℝ)) := by
  let x := Real.sqrt (d : ℝ)
  let y := Real.sqrt ((d - 1 : ℕ) : ℝ)
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : 1 ≤ d := hd
  have hxpos : 0 < x := Real.sqrt_pos.2 hdreal
  have hx0 : 0 ≤ x := hxpos.le
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hyx : y ≤ x := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Nat.sub_le d 1))
  have hx2 : x ^ 2 = (d : ℝ) := Real.sq_sqrt hdreal.le
  have hy2 : y ^ 2 = ((d - 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd1]
    norm_num
  have hprod : (x - y) * (x + y) = 1 := by
    nlinarith
  have hsum : x + y ≤ 2 * x := by linarith
  have hmul : (x - y) * (x + y) ≤ (x - y) * (2 * x) :=
    mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hyx)
  change 1 / x ≤ 2 * (x - y)
  rw [div_le_iff₀ hxpos]
  nlinarith

theorem sum_inv_sqrt_Ioc_le_two_mul_sqrt (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N, 1 / Real.sqrt (d : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) := by
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 N,
        2 * (Real.sqrt (d : ℝ) - Real.sqrt ((d - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact one_div_sqrt_le_two_mul_sqrt_sub d (Finset.mem_Ioc.mp hd).1
    _ = 2 * (Real.sqrt (N : ℝ) - Real.sqrt (0 : ℝ)) := by
      rw [← Finset.mul_sum, sum_Ioc_sub_eq (fun d => Real.sqrt (d : ℝ)) N]
      simp
    _ = 2 * Real.sqrt (N : ℝ) := by simp

noncomputable def typeIILambdaScale (a : ℝ) (M P N : ℕ) : ℝ :=
  a / (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)

theorem typeIILambdaScale_pos
    (a : ℝ) (M P N : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    0 < typeIILambdaScale a M P N := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hPlog
  unfold typeIILambdaScale
  positivity

theorem typeIIDistanceBound_eq_scale
    (a : ℝ) (M P N d : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hd : 0 < d) :
    typeIIDistanceBound a M P N d =
      5120 * (M : ℝ) * Real.sqrt (typeIILambdaScale a M P N) *
          Real.sqrt (d : ℝ) +
        (10 / Real.sqrt (typeIILambdaScale a M P N)) *
          (1 / Real.sqrt (d : ℝ)) := by
  have hscale := typeIILambdaScale_pos a M P N ha hM hN hPlog
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrtScale : Real.sqrt (typeIILambdaScale a M P N) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hscale)
  have hsqrtD : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdreal)
  have hlam :
      a * (d : ℝ) /
          (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) =
        typeIILambdaScale a M P N * (d : ℝ) := by
    unfold typeIILambdaScale
    ring
  dsimp [typeIIDistanceBound]
  rw [hlam, Real.sqrt_mul hscale.le]
  field_simp
  ring

theorem sum_typeIIDistanceBound_eq_scale
    (a : ℝ) (M P N : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    (∑ d ∈ Finset.Ioc 0 N, typeIIDistanceBound a M P N d) =
      5120 * (M : ℝ) * Real.sqrt (typeIILambdaScale a M P N) *
          (∑ d ∈ Finset.Ioc 0 N, Real.sqrt (d : ℝ)) +
        (10 / Real.sqrt (typeIILambdaScale a M P N)) *
          ∑ d ∈ Finset.Ioc 0 N, 1 / Real.sqrt (d : ℝ) := by
  calc
    _ = ∑ d ∈ Finset.Ioc 0 N, (
        (5120 * (M : ℝ) * Real.sqrt (typeIILambdaScale a M P N)) *
            Real.sqrt (d : ℝ) +
          (10 / Real.sqrt (typeIILambdaScale a M P N)) *
            (1 / Real.sqrt (d : ℝ))) := by
      apply Finset.sum_congr rfl
      intro d hd
      simpa [mul_assoc] using typeIIDistanceBound_eq_scale
        a M P N d ha hM hN hPlog (Finset.mem_Ioc.mp hd).1
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem sum_typeIIDistanceBound_le_explicit_sqrt
    (a : ℝ) (M P N : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    (∑ d ∈ Finset.Ioc 0 N, typeIIDistanceBound a M P N d) ≤
      5120 * (M : ℝ) * Real.sqrt (typeIILambdaScale a M P N) *
          ((N : ℝ) * Real.sqrt (N : ℝ)) +
        (10 / Real.sqrt (typeIILambdaScale a M P N)) *
          (2 * Real.sqrt (N : ℝ)) := by
  rw [sum_typeIIDistanceBound_eq_scale a M P N ha hM hN hPlog]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (sum_sqrt_Ioc_le_mul_sqrt N)
      (mul_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg M))
        (Real.sqrt_nonneg _))
  · exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_Ioc_le_two_mul_sqrt N)
      (div_nonneg (by norm_num) (Real.sqrt_nonneg _))

theorem typeII_lambda_le_one_of_scale
    (a : ℝ) (M P N n₁ n₂ : ℕ)
    (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ))
    (hn₁lo : N ≤ n₁) (hn₁hi : n₁ ≤ 2 * N)
    (hn₂lo : N ≤ n₂) (hn₂hi : n₂ ≤ 2 * N)
    (hscale : a ≤ 32 * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) :
    a * (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) /
        (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) ≤ 1 := by
  have hminmax : min n₁ n₂ ≤ max n₁ n₂ := min_le_max
  have hdiffNat : max n₁ n₂ - min n₁ n₂ ≤ N := by
    have hlo : N ≤ min n₁ n₂ := le_min hn₁lo hn₂lo
    have hhi : max n₁ n₂ ≤ 2 * N := max_le hn₁hi hn₂hi
    omega
  have hdiffReal :
      (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) ≤ (N : ℝ) := by
    rw [← Nat.cast_sub hminmax]
    exact_mod_cast hdiffNat
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hPlog
  have hden :
      0 < 32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3 := by
    positivity
  apply (div_le_one hden).2
  calc
    a * (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) ≤ a * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hdiffReal ha.le
    _ ≤ (32 * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hscale hNreal.le
    _ = 32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3 := by ring

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

open scoped ComplexConjugate

noncomputable section

theorem norm_sq_productBand_box_le_moments
    (A D : ArithmeticFunction ℝ) (a C : ℝ) (M B P Y N : ℕ) (J : Finset ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hJ : J ⊆ Ioc N (2 * N))
    (hscale : a ≤ 32 * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) :
    ‖∑ m ∈ Ioc M B, ∑ n ∈ J,
        productBandTerm A D P Y (reciprocalLogWeight a) m n‖ ^ 2 ≤
      (∑ m ∈ Ioc M B, A m ^ 2) * (∑ n ∈ J, D n ^ 2) *
        ((M : ℝ) + 2 * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d) := by
  let I := Ioc M B
  let K := fun n₁ n₂ => typeIIDistanceBound a M P N (max n₁ n₂ - min n₁ n₂)
  have hcauchy := norm_sq_sum_mul_sum_le_sq_sum_mul_correlation I J A D
    (bandPhase a P Y)
  have hrewrite :
      (∑ m ∈ I, ∑ n ∈ J, productBandTerm A D P Y (reciprocalLogWeight a) m n) =
        ∑ m ∈ I, (A m : ℂ) * ∑ n ∈ J, (D n : ℂ) * bandPhase a P Y m n := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    unfold productBandTerm bandPhase
    split_ifs <;> simp [mul_assoc]
  have hoff : ∀ n₁ ∈ J, ∀ n₂ ∈ J, n₁ ≠ n₂ →
      ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ ≤ K n₁ n₂ := by
    intro n₁ hn₁ n₂ hn₂ hne
    have h₁ := Finset.mem_Ioc.mp (hJ hn₁)
    have h₂ := Finset.mem_Ioc.mp (hJ hn₂)
    exact (norm_sum_bandPhase_correlation_le_symmetric a C M B P Y N n₁ n₂
      ha hC hP hPlog hCP hY hM hB hN h₁.1.le h₁.2 h₂.1.le h₂.2 hne
      (typeII_lambda_le_one_of_scale a M P N n₁ n₂ ha hM hN hPlog
        h₁.1.le h₁.2 h₂.1.le h₂.2 hscale)).trans
      (typeIICorrelationBound_le_typeIIDistanceBound a M B P Y N n₁ n₂ hB)
  have hcorr := sum_abs_mul_norm_bandPhase_correlation_le_ite a P Y I J D K hoff
  rw [sum_abs_mul_ite_eq_diagonal_add_offDiagonal] at hcorr
  have hdist := sum_offDiagonal_distanceKernel_le N J D (typeIIDistanceBound a M P N)
    hJ (fun d hd => typeIIDistanceBound_nonneg a M P N d)
  have hcard : (I.card : ℝ) ≤ M := by
    simp only [I, Nat.card_Ioc]
    exact_mod_cast (show B - M ≤ M by omega)
  have hinner :
      (∑ n₁ ∈ J, ∑ n₂ ∈ J, |D n₁| * |D n₂| *
        ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖) ≤
        (∑ n ∈ J, D n ^ 2) *
          ((M : ℝ) + 2 * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d) := by
    refine hcorr.trans ?_
    calc
      _ ≤ (M : ℝ) * (∑ n ∈ J, D n ^ 2) +
          2 * (∑ n ∈ J, D n ^ 2) * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d :=
        add_le_add (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun n hn => sq_nonneg _))
          hdist
      _ = _ := by ring
  change ‖∑ m ∈ I, ∑ n ∈ J, productBandTerm A D P Y (reciprocalLogWeight a) m n‖ ^ 2 ≤ _
  rw [hrewrite]
  refine hcauchy.trans ?_
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinner
    (Finset.sum_nonneg fun m hm => sq_nonneg (A m))

def typeIICommonLog (Y : ℕ) : ℝ := 1 + Real.log (2 * (Y : ℝ) + 1)

theorem one_le_typeIICommonLog (Y : ℕ) : 1 ≤ typeIICommonLog Y := by
  have h : 0 ≤ Real.log (2 * (Y : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) Y])
  dsimp [typeIICommonLog]
  linarith

theorem sum_typeIICoeff_sq_le_common
    (U M Y : ℕ) (I : Finset ℕ) (hI : I ⊆ Ioc M (2 * M)) (hMY : M ≤ Y) :
    (∑ m ∈ I, typeIICoeff U m ^ 2) ≤ 2 * (M : ℝ) * typeIICommonLog Y ^ 3 := by
  have hlog : 1 + Real.log (2 * (M : ℝ)) ≤ typeIICommonLog Y := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simpa [typeIICommonLog] using one_le_typeIICommonLog Y
    · have hMr : (0 : ℝ) < M := by exact_mod_cast hM
      have hMYr : (M : ℝ) ≤ Y := by exact_mod_cast hMY
      have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * M)
        (show 2 * (M : ℝ) ≤ 2 * Y + 1 by linarith)
      dsimp [typeIICommonLog]
      linarith
  have hnonneg : 0 ≤ 1 + Real.log (2 * (M : ℝ)) := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * M by exact_mod_cast (show 1 ≤ 2*M by omega))
      linarith
  exact (sum_typeIICoeff_sq_le_on_dyadic U M I hI).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hlog 3) (by positivity))

theorem sum_lambdaGT_sq_le_common
    (V M Y : ℕ) (I : Finset ℕ) (hI : I ⊆ Ioc M (2 * M)) (hMY : M ≤ Y) :
    (∑ m ∈ I, lambdaGT V m ^ 2) ≤ 2 * (M : ℝ) * typeIICommonLog Y ^ 3 := by
  have hMYr : (M : ℝ) ≤ Y := by exact_mod_cast hMY
  have hlog0 : 0 ≤ Real.log (2 * (M : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
  have hlog : Real.log (2 * (M : ℝ) + 1) ≤ typeIICommonLog Y := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * M + 1)
      (show 2 * (M : ℝ) + 1 ≤ 2 * Y + 1 by linarith)
    dsimp [typeIICommonLog]
    linarith
  have hH := one_le_typeIICommonLog Y
  have hsquare := pow_le_pow_left₀ hlog0 hlog 2
  have hcube : typeIICommonLog Y ^ 2 ≤ typeIICommonLog Y ^ 3 := by
    nlinarith [sq_nonneg (typeIICommonLog Y),
      mul_nonneg (sq_nonneg (typeIICommonLog Y)) (show 0 ≤ typeIICommonLog Y - 1 by linarith)]
  have hbound : Real.log (2 * (M : ℝ) + 1) ^ 2 ≤ 2 * typeIICommonLog Y ^ 3 := by
    nlinarith
  calc
    _ ≤ (M : ℝ) * Real.log (2 * (M : ℝ) + 1) ^ 2 := sum_lambdaGT_sq_le_on_dyadic V M I hI
    _ ≤ (M : ℝ) * (2 * typeIICommonLog Y ^ 3) :=
      mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = _ := by ring

def typeIIFrequencyRoot (a : ℝ) (P : ℕ) : ℝ :=
  Real.sqrt (a / (32 * Real.log (P : ℝ) ^ 3))

theorem typeIIFrequencyRoot_pos (a : ℝ) (P : ℕ)
    (ha : 0 < a) (hPlog : 1 ≤ Real.log (P : ℝ)) :
    0 < typeIIFrequencyRoot a P := by
  have hlog : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hPlog
  unfold typeIIFrequencyRoot
  positivity

theorem sqrt_typeIILambdaScale_eq (a : ℝ) (M P N : ℕ)
    (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    Real.sqrt (typeIILambdaScale a M P N) =
      typeIIFrequencyRoot a P / ((M : ℝ) * Real.sqrt (N : ℝ)) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hPlog
  have heq : typeIILambdaScale a M P N =
      (a / (32 * Real.log (P : ℝ) ^ 3)) / ((M : ℝ) ^ 2 * N) := by
    unfold typeIILambdaScale
    ring
  rw [heq, Real.sqrt_div (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hMr.le]
  rfl

theorem sum_typeIIDistanceBound_le_frequency
    (a : ℝ) (M P N : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    (∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d) ≤
      5120 * (N : ℝ) * typeIIFrequencyRoot a P +
        20 * (M : ℝ) * N / typeIIFrequencyRoot a P := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hNr)
  have hg := typeIIFrequencyRoot_pos a P ha hPlog
  have hsquare := Real.sq_sqrt hNr.le
  refine (sum_typeIIDistanceBound_le_explicit_sqrt a M P N ha hM hN hPlog).trans_eq ?_
  rw [sqrt_typeIILambdaScale_eq a M P N ha hM hN hPlog]
  field_simp
  nlinarith

theorem norm_sq_productBand_box_le_common_moments
    (A D : ArithmeticFunction ℝ) (a C : ℝ) (M B P Y N : ℕ) (J : Finset ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hJ : J ⊆ Ioc N (2 * N))
    (hscale : a ≤ 32 * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
    (hA : (∑ m ∈ Ioc M B, A m ^ 2) ≤ 2 * (M : ℝ) * typeIICommonLog Y ^ 3)
    (hD : (∑ n ∈ J, D n ^ 2) ≤ 2 * (N : ℝ) * typeIICommonLog Y ^ 3) :
    ‖∑ m ∈ Ioc M B, ∑ n ∈ J,
        productBandTerm A D P Y (reciprocalLogWeight a) m n‖ ^ 2 ≤
      4 * (M : ℝ) * N * typeIICommonLog Y ^ 6 *
        ((M : ℝ) + 10240 * N * typeIIFrequencyRoot a P +
          40 * (M : ℝ) * N / typeIIFrequencyRoot a P) := by
  have hbase := norm_sq_productBand_box_le_moments A D a C M B P Y N J
    ha hC hP hPlog hCP hY hM hB hN hJ hscale
  have hsum := sum_typeIIDistanceBound_le_frequency a M P N ha hM hN hPlog
  have hH : 0 ≤ typeIICommonLog Y := zero_le_one.trans (one_le_typeIICommonLog Y)
  have hS : 0 ≤ (M : ℝ) + 2 * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d := by
    exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun d hd => typeIIDistanceBound_nonneg a M P N d))
  calc
    _ ≤ (∑ m ∈ Ioc M B, A m ^ 2) * (∑ n ∈ J, D n ^ 2) *
        ((M : ℝ) + 2 * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d) := hbase
    _ ≤ (2 * (M : ℝ) * typeIICommonLog Y ^ 3) *
        (2 * (N : ℝ) * typeIICommonLog Y ^ 3) *
        ((M : ℝ) + 2 * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hA hD (Finset.sum_nonneg fun n hn => sq_nonneg _) (by positivity)) hS
    _ ≤ (2 * (M : ℝ) * typeIICommonLog Y ^ 3) *
        (2 * (N : ℝ) * typeIICommonLog Y ^ 3) *
        ((M : ℝ) + 2 * (5120 * (N : ℝ) * typeIIFrequencyRoot a P +
          20 * (M : ℝ) * N / typeIIFrequencyRoot a P)) := by
      apply mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) _)
      positivity
    _ = _ := by ring

def typeIIUniformError (a : ℝ) (P K : ℕ) : ℝ :=
  2 / (K : ℝ) + 20480 * typeIIFrequencyRoot a P / Real.sqrt (P : ℝ) +
    40 / typeIIFrequencyRoot a P

theorem typeIIUniformError_nonneg (a : ℝ) (P K : ℕ) :
    0 ≤ typeIIUniformError a P K := by
  unfold typeIIUniformError typeIIFrequencyRoot
  positivity

theorem typeII_scale_of_long_box (a : ℝ) (M P : ℕ)
    (haP : a ≤ (P : ℝ)) (hgeom : P ≤ 4 * M ^ 2)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    a ≤ 32 * (M : ℝ) ^ 2 * Real.log (P : ℝ) ^ 3 := by
  have hPr : (P : ℝ) ≤ 4 * (M : ℝ) ^ 2 := by exact_mod_cast hgeom
  have hpow : (1 : ℝ) ≤ Real.log (P : ℝ) ^ 3 := one_le_pow₀ hPlog
  have hmul := mul_le_mul_of_nonneg_left hpow (sq_nonneg (M : ℝ))
  nlinarith [sq_nonneg (M : ℝ)]

theorem typeII_normalized_error_le
    (a : ℝ) (M N P K : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hP : 0 < P) (hK : 0 < K) (hKN : K ≤ 2 * N) (hgeom : P ≤ 4 * M ^ 2) :
    1 / (N : ℝ) + 10240 * typeIIFrequencyRoot a P / M +
        40 / typeIIFrequencyRoot a P ≤ typeIIUniformError a P K := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hsP : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.2 hPr
  have hKNr : (K : ℝ) ≤ 2 * N := by exact_mod_cast hKN
  have hgeomr : (P : ℝ) ≤ 4 * (M : ℝ) ^ 2 := by exact_mod_cast hgeom
  have hsPM : Real.sqrt (P : ℝ) ≤ 2 * M := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hg : 0 ≤ typeIIFrequencyRoot a P := Real.sqrt_nonneg _
  have hdiag : 1 / (N : ℝ) ≤ 2 / K := by
    apply (div_le_div_iff₀ hNr hKr).2
    nlinarith
  have hcurv : 10240 * typeIIFrequencyRoot a P / M ≤
      20480 * typeIIFrequencyRoot a P / Real.sqrt (P : ℝ) := by
    apply (div_le_div_iff₀ hMr hsP).2
    nlinarith [mul_le_mul_of_nonneg_left hsPM (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10240) hg)]
  exact add_le_add (add_le_add hdiag hcurv) le_rfl

def typeIIUniformBoxBound (a : ℝ) (P Y K : ℕ) : ℝ :=
  Real.sqrt (4 * (Y : ℝ) ^ 2 * typeIICommonLog Y ^ 6 * typeIIUniformError a P K)

theorem typeIIUniformBoxBound_nonneg (a : ℝ) (P Y K : ℕ) :
    0 ≤ typeIIUniformBoxBound a P Y K := Real.sqrt_nonneg _

theorem norm_productBand_box_le_uniform
    (A D : ArithmeticFunction ℝ) (a C : ℝ) (M B P Y N K : ℕ) (J : Finset ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ))
    (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N) (hK : 0 < K)
    (hJ : J ⊆ Ioc N (2 * N)) (hKN : K ≤ 2 * N)
    (hgeom : P ≤ 4 * M ^ 2) (hprod : M * N ≤ Y)
    (hA : (∑ m ∈ Ioc M B, A m ^ 2) ≤ 2 * (M : ℝ) * typeIICommonLog Y ^ 3)
    (hD : (∑ n ∈ J, D n ^ 2) ≤ 2 * (N : ℝ) * typeIICommonLog Y ^ 3) :
    ‖∑ m ∈ Ioc M B, ∑ n ∈ J,
        productBandTerm A D P Y (reciprocalLogWeight a) m n‖ ≤
      typeIIUniformBoxBound a P Y K := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hprodR : (M : ℝ) * N ≤ Y := by exact_mod_cast hprod
  have hg := typeIIFrequencyRoot_pos a P ha hPlog
  have hbase := norm_sq_productBand_box_le_common_moments A D a C M B P Y N J
    ha hC hP hPlog hCP hY hM hB hN hJ
    (typeII_scale_of_long_box a M P haP hgeom hPlog) hA hD
  have heq :
      4 * (M : ℝ) * N * typeIICommonLog Y ^ 6 *
        ((M : ℝ) + 10240 * N * typeIIFrequencyRoot a P +
          40 * (M : ℝ) * N / typeIIFrequencyRoot a P) =
      4 * ((M : ℝ) * N) ^ 2 * typeIICommonLog Y ^ 6 *
        (1 / (N : ℝ) + 10240 * typeIIFrequencyRoot a P / M +
          40 / typeIIFrequencyRoot a P) := by
    field_simp
  rw [heq] at hbase
  have herr := typeII_normalized_error_le a M N P K hM hN hP hK hKN hgeom
  have hsq : ((M : ℝ) * N) ^ 2 ≤ (Y : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hprodR 2
  apply (Real.le_sqrt (norm_nonneg _) (by
    exact mul_nonneg (by positivity) (typeIIUniformError_nonneg a P K))).2
  refine hbase.trans ?_
  calc
    _ ≤ 4 * ((M : ℝ) * N) ^ 2 * typeIICommonLog Y ^ 6 * typeIIUniformError a P K :=
      mul_le_mul_of_nonneg_left herr (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (by positivity)) (typeIIUniformError_nonneg a P K)

theorem productBandTerm_typeII_ne_zero_properties
    (U V P Y m n : ℕ) (w : ℕ → ℂ)
    (ht : productBandTerm (lambdaGT V) (typeIICoeff U) P Y w m n ≠ 0) :
    (P < m * n ∧ m * n ≤ Y) ∧ V < m ∧ U < n := by
  have hb : P < m * n ∧ m * n ≤ Y := by
    by_contra h
    simp [productBandTerm, h] at ht
  have hm : V < m := by
    by_contra h
    simp [productBandTerm, lambdaGT_apply, h] at ht
  have hn : U < n := by
    by_contra h
    have hz := typeIICoeff_eq_zero_of_le U n (by omega)
    simp [productBandTerm, hz] at ht
  exact ⟨hb, hm, hn⟩

theorem norm_typeII_productBand_box_le_uniform
    (a C : ℝ) (U V M B N D P Y : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ))
    (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) (hN : 0 < N)
    (hB : B ≤ 2 * M) (hD : D ≤ 2 * N) :
    ‖∑ m ∈ Ioc M B, ∑ n ∈ Ioc N D,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y (reciprocalLogWeight a) m n‖ ≤
      typeIIUniformBoxBound a P Y (min U V) := by
  by_cases hactive : ∃ m ∈ Ioc M B, ∃ n ∈ Ioc N D,
      productBandTerm (lambdaGT V) (typeIICoeff U) P Y (reciprocalLogWeight a) m n ≠ 0
  · obtain ⟨m, hm, n, hn, ht⟩ := hactive
    obtain ⟨⟨hlo, hhi⟩, hVm, hUn⟩ :=
      productBandTerm_typeII_ne_zero_properties U V P Y m n (reciprocalLogWeight a) ht
    obtain ⟨hMm, hmB⟩ := Finset.mem_Ioc.mp hm
    obtain ⟨hNn, hnD⟩ := Finset.mem_Ioc.mp hn
    have hm2 : m ≤ 2 * M := hmB.trans hB
    have hn2 : n ≤ 2 * N := hnD.trans hD
    have hMN : M * N ≤ Y := (Nat.mul_le_mul hMm.le hNn.le).trans hhi
    have hPmn : P ≤ 4 * M * N := by
      have hh := Nat.mul_le_mul hm2 hn2
      nlinarith
    have hMY : M ≤ Y := (Nat.le_mul_of_pos_right M hN).trans hMN
    have hNY : N ≤ Y := (Nat.le_mul_of_pos_left N hM).trans hMN
    have hK : 0 < min U V := lt_min hU hV
    have hKN : min U V ≤ 2 * N := (min_le_left _ _).trans (hUn.le.trans hn2)
    have hKM : min U V ≤ 2 * M := (min_le_right _ _).trans (hVm.le.trans hm2)
    have hI : Ioc M B ⊆ Ioc M (2 * M) := Finset.Ioc_subset_Ioc le_rfl hB
    have hJ : Ioc N D ⊆ Ioc N (2 * N) := Finset.Ioc_subset_Ioc le_rfl hD
    by_cases hNM : N ≤ M
    · have hgeom : P ≤ 4 * M ^ 2 := by
        nlinarith [Nat.mul_le_mul_left M hNM]
      exact norm_productBand_box_le_uniform (lambdaGT V) (typeIICoeff U)
        a C M B P Y N (min U V) (Ioc N D) ha haP hC hP hPlog hCP hY
        hM hB hN hK hJ hKN hgeom hMN
        (sum_lambdaGT_sq_le_common V M Y (Ioc M B) hI hMY)
        (sum_typeIICoeff_sq_le_common U N Y (Ioc N D) hJ hNY)
    · have hMN' : M ≤ N := by omega
      have hgeom : P ≤ 4 * N ^ 2 := by
        nlinarith [Nat.mul_le_mul_left N hMN']
      rw [sum_productBandTerm_swap]
      exact norm_productBand_box_le_uniform (typeIICoeff U) (lambdaGT V)
        a C N D P Y M (min U V) (Ioc M B) ha haP hC hP hPlog hCP hY
        hN hD hM hK hI hKM hgeom (by simpa [Nat.mul_comm] using hMN)
        (sum_typeIICoeff_sq_le_common U N Y (Ioc N D) hJ hNY)
        (sum_lambdaGT_sq_le_common V M Y (Ioc M B) hI hMY)
  · have hz : (∑ m ∈ Ioc M B, ∑ n ∈ Ioc N D,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y (reciprocalLogWeight a) m n) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      apply Finset.sum_eq_zero
      intro n hn
      by_contra ht
      exact hactive ⟨m, hm, n, hn, ht⟩
    rw [hz, norm_zero]
    exact typeIIUniformBoxBound_nonneg a P Y (min U V)

theorem norm_weightedArithmeticSum_typeII_le_explicit
    (a C : ℝ) (U V P Y : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ))
    (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hU : 0 < U) (hV : 0 < V) (hY2 : 2 ≤ Y) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeII U V)‖ ≤
      9 * Real.log (Y : ℝ) ^ 2 * typeIIUniformBoxBound a P Y (min U V) := by
  apply norm_weightedArithmeticSum_typeII_le_of_box_bound U V P Y hU hY2
    (reciprocalLogWeight a) (typeIIUniformBoxBound a P Y (min U V))
    (typeIIUniformBoxBound_nonneg a P Y (min U V))
  intro i hi j hj
  apply norm_typeII_productBand_box_le_uniform a C U V
    (2 ^ i) (min (2 ^ (i + 1)) Y) (2 ^ j) (min (2 ^ (j + 1)) Y) P Y
    ha haP hC hP hPlog hCP hY hU hV (by positivity) (by positivity)
  · calc
      min (2 ^ (i + 1)) Y ≤ 2 ^ (i + 1) := min_le_left _ _
      _ = 2 * 2 ^ i := by rw [pow_succ]; omega
  · calc
      min (2 ^ (j + 1)) Y ≤ 2 ^ (j + 1) := min_le_left _ _
      _ = 2 * 2 ^ j := by rw [pow_succ]; omega

theorem typeIIUniformBoxBound_eq (a : ℝ) (P Y K : ℕ) :
    typeIIUniformBoxBound a P Y K =
      2 * (Y : ℝ) * typeIICommonLog Y ^ 3 * Real.sqrt (typeIIUniformError a P K) := by
  have hH : 0 ≤ typeIICommonLog Y := zero_le_one.trans (one_le_typeIICommonLog Y)
  have hfactor : 0 ≤ 2 * (Y : ℝ) * typeIICommonLog Y ^ 3 := by positivity
  unfold typeIIUniformBoxBound
  rw [show 4 * (Y : ℝ) ^ 2 * typeIICommonLog Y ^ 6 * typeIIUniformError a P K =
    (2 * (Y : ℝ) * typeIICommonLog Y ^ 3) ^ 2 * typeIIUniformError a P K by ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hfactor]

theorem norm_weightedArithmeticSum_typeII_le_normalized
    (a C : ℝ) (U V P Y : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ))
    (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hU : 0 < U) (hV : 0 < V) (hY2 : 2 ≤ Y) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeII U V)‖ ≤
      18 * (Y : ℝ) * Real.log (Y : ℝ) ^ 2 * typeIICommonLog Y ^ 3 *
        Real.sqrt (typeIIUniformError a P (min U V)) := by
  have h := norm_weightedArithmeticSum_typeII_le_explicit
    a C U V P Y ha haP hC hP hPlog hCP hY hU hV hY2
  rw [typeIIUniformBoxBound_eq] at h
  convert h using 1
  ring

theorem norm_weightedArithmeticSum_typeII_le_uniform_endpoint
    (a C : ℝ) (U V P Y X : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ))
    (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hX : (X : ℝ) ≤ C * P) (hYX : Y ≤ X)
    (hU : 0 < U) (hV : 0 < V) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeII U V)‖ ≤
      18 * (X : ℝ) * Real.log (X : ℝ) ^ 2 * typeIICommonLog X ^ 3 *
        Real.sqrt (typeIIUniformError a P (min U V)) := by
  have hHX : 0 ≤ typeIICommonLog X := zero_le_one.trans (one_le_typeIICommonLog X)
  by_cases hY2 : 2 ≤ Y
  · have hYXr : (Y : ℝ) ≤ X := by exact_mod_cast hYX
    have hYr : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
    have hlogY : 0 ≤ Real.log (Y : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
    have hlogs : Real.log (Y : ℝ) ≤ Real.log (X : ℝ) := Real.log_le_log hYr hYXr
    have hHY : 0 ≤ typeIICommonLog Y := zero_le_one.trans (one_le_typeIICommonLog Y)
    have hHs : typeIICommonLog Y ≤ typeIICommonLog X := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * Y + 1)
        (show 2 * (Y : ℝ) + 1 ≤ 2 * X + 1 by linarith)
      dsimp [typeIICommonLog]
      linarith
    refine (norm_weightedArithmeticSum_typeII_le_normalized a C U V P Y
      ha haP hC hP hPlog hCP (hYXr.trans hX) hU hV hY2).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul
    · exact mul_le_mul (mul_le_mul_of_nonneg_left hYXr (by norm_num))
        (pow_le_pow_left₀ hlogY hlogs 2) (sq_nonneg _) (by positivity)
    · exact pow_le_pow_left₀ hHY hHs 3
    · positivity
    · positivity
  · have hempty : Ioc P Y = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    simp only [hempty, weightedArithmeticSum, Finset.sum_empty, norm_zero]
    positivity

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

noncomputable section

theorem reciprocalLogPhase_curvature_of_ratio (a n L R C x : ℝ)
    (ha : 0 ≤ a) (_hn : 0 < n) (hL : 1 ≤ L) (hR : 0 < R) (hC : 0 < C)
    (hxlo : R ≤ x) (hxhi : x ≤ C * R)
    (hloglo : L ≤ Real.log (n * x)) (hloghi : Real.log (n * x) ≤ 2 * L) :
    a / (4 * (C * R) ^ 2 * L ^ 2) ≤
        a / x ^ 2 * logCurvature (Real.log (n * x)) ∧
      a / x ^ 2 * logCurvature (Real.log (n * x)) ≤
        (12 * C ^ 2) * (a / (4 * (C * R) ^ 2 * L ^ 2)) := by
  have hx : 0 < x := hR.trans_le hxlo
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hw := logCurvature_bounds L (Real.log (n * x)) hL hloglo hloghi
  have hw0 : 0 ≤ logCurvature (Real.log (n * x)) := (by positivity : 0 ≤ 1 / (4*L^2)).trans hw.1
  have hlo := div_le_div_of_nonneg_left ha (pow_pos hx 2)
    (pow_le_pow_left₀ hx.le hxhi 2)
  have hhi := div_le_div_of_nonneg_left ha (pow_pos hR 2)
    (pow_le_pow_left₀ hR.le hxlo 2)
  constructor
  · convert mul_le_mul hlo hw.1 (by positivity) (by positivity) using 1 <;> first | rfl | ring
  · calc
      _ ≤ (a / R ^ 2) * (3 / L ^ 2) := mul_le_mul hhi hw.2 hw0 (by positivity)
      _ = _ := by field_simp; ring

theorem norm_sum_reciprocalLogPhase_Icc_le_of_ratio
    (a n L R C : ℝ) (A B : ℕ) (ha : 0 < a) (hn : 0 < n)
    (hL : 1 ≤ L) (hR : 0 < R) (hC : 0 < C) (hAB : A ≤ B)
    (hlam : a / (4 * (C * R) ^ 2 * L ^ 2) ≤ 1)
    (hbox : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ), R ≤ x ∧ x ≤ C * R)
    (hlog : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ),
      L ≤ Real.log (n * x) ∧ Real.log (n * x) ≤ 2 * L) :
    ‖∑ k ∈ Icc A B, phaseCharacter (reciprocalLogPhase a n k)‖ ≤
      10 * ((12 * C ^ 2) * (B - A : ℕ) *
          Real.sqrt (a / (4 * (C * R) ^ 2 * L ^ 2)) +
        1 / Real.sqrt (a / (4 * (C * R) ^ 2 * L ^ 2))) := by
  let lam := a / (4 * (C * R) ^ 2 * L ^ 2)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlampos : 0 < lam := by dsimp [lam]; positivity
  have hend : (A : ℝ) + (B - A : ℕ) = B := by rw [Nat.cast_sub hAB]; ring
  have hmem {x : ℝ} (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      x ∈ Set.Icc (A : ℝ) (B : ℝ) := by rwa [hend] at hx
  have hdom (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      0 < x ∧ 1 < n * x := by
    have hxp := hR.trans_le (hbox x (hmem hx)).1
    exact ⟨hxp, (Real.log_pos_iff (mul_nonneg hn.le hxp.le)).mp
      (hLp.trans_le (hlog x (hmem hx)).1)⟩
  have hf (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :=
    hasDerivAt_reciprocalLogPhase a n x hn (hdom x hx).1 (hdom x hx).2
  have hh (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :=
    hasDerivAt_reciprocalLogSlope a n x hn (hdom x hx).1 (hdom x hx).2
  have ht := second_derivative_test_small (reciprocalLogPhase a n)
    (reciprocalLogSlope a n) (fun x => a / x ^ 2 * logCurvature (Real.log (n*x)))
    (A : ℝ) (B-A) lam (12*C^2) hlampos hlam (by positivity)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => hf x (Set.Ioo_subset_Icc_self hx))
    (fun x hx => (hh x hx).continuousAt.continuousWithinAt)
    (fun x hx => hh x (Set.Ioo_subset_Icc_self hx))
    (fun x hx => by
      have hx' := hmem (Set.Ioo_subset_Icc_self hx)
      exact reciprocalLogPhase_curvature_of_ratio a n L R C x ha.le hn hL hR hC
        (hbox x hx').1 (hbox x hx').2 (hlog x hx').1 (hlog x hx').2)
  rw [sum_Icc_eq_sum_range_shift _ A B hAB]
  simpa only [Nat.cast_add] using ht

def typeIInnerBound (a C : ℝ) (P n : ℕ) : ℝ :=
  60 * C ^ 2 * Real.sqrt a / Real.log (P : ℝ) +
    20 * C * P * Real.log (P : ℝ) / ((n : ℝ) * Real.sqrt a)

theorem typeIInnerBound_nonneg (a C : ℝ) (P n : ℕ) (hC : 0 ≤ C) :
    0 ≤ typeIInnerBound a C P n := by
  have hlog := Real.log_natCast_nonneg P
  unfold typeIInnerBound
  positivity

theorem typeI_lambda_le_one (a C : ℝ) (P n : ℕ)
    (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P) (hn : 0 < n)
    (hnP : n ^ 2 ≤ P) (hlog : 1 ≤ Real.log (P : ℝ)) :
    a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2) ≤ 1 := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnPr : (n : ℝ) ^ 2 ≤ P := by exact_mod_cast hnP
  have hCr : 0 < C := zero_lt_one.trans_le hC
  have hLr : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hlog
  have heq : a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2) =
      a * (n : ℝ) ^ 2 / (4 * C ^ 2 * (P : ℝ) ^ 2 * Real.log (P : ℝ) ^ 2) := by
    field_simp
  rw [heq]
  apply (div_le_one (by positivity)).2
  have hC2 : (1 : ℝ) ≤ C ^ 2 := one_le_pow₀ hC
  have hL2 : (1 : ℝ) ≤ Real.log (P : ℝ) ^ 2 := one_le_pow₀ hlog
  calc
    a * (n : ℝ) ^ 2 ≤ (P : ℝ) * n ^ 2 := mul_le_mul_of_nonneg_right haP (sq_nonneg _)
    _ ≤ (P : ℝ) ^ 2 := by nlinarith
    _ ≤ 4 * C ^ 2 * (P : ℝ) ^ 2 * Real.log (P : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hC2 (sq_nonneg (P : ℝ)),
        mul_le_mul_of_nonneg_left hL2 (show 0 ≤ 4*C^2*(P : ℝ)^2 by positivity)]

theorem sqrt_typeI_lambda (a C : ℝ) (P n : ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hn : 0 < n)
    (hlog : 1 ≤ Real.log (P : ℝ)) :
    Real.sqrt (a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2)) =
      Real.sqrt a / (2 * C * ((P : ℝ) / n) * Real.log (P : ℝ)) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hLr : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hlog
  rw [show 4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2 =
      (2 * C * ((P : ℝ) / n) * Real.log (P : ℝ)) ^ 2 by ring,
    Real.sqrt_div ha.le, Real.sqrt_sq (by positivity)]

theorem typeI_scalar_bound (a C t : ℝ) (P n : ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hn : 0 < n)
    (hlog : 1 ≤ Real.log (P : ℝ)) (ht : t ≤ C * ((P : ℝ) / n)) :
    10 * ((12*C^2) * t *
        Real.sqrt (a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2)) +
      1 / Real.sqrt (a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2))) ≤
      typeIInnerBound a C P n := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hLr : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hlog
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  calc
    _ ≤ 10 * ((12*C^2) * (C * ((P : ℝ) / n)) *
        Real.sqrt (a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2)) +
      1 / Real.sqrt (a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2))) := by
      gcongr
    _ = _ := by
      rw [sqrt_typeI_lambda a C P n ha hC hP hn hlog]
      unfold typeIInnerBound
      field_simp
      ring

theorem norm_sum_reciprocalLogWeight_subinterval_le
    (a C : ℝ) (P Y n A B : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hCP : C ≤ (P : ℝ))
    (hY : (Y : ℝ) ≤ C * P) (hn : 0 < n) (hnP : n ^ 2 ≤ P)
    (hA : P / n + 1 ≤ A) (hB : B ≤ Y / n) (hAB : A ≤ B) :
    ‖∑ k ∈ Icc A B, reciprocalLogWeight a (n*k)‖ ≤ typeIInnerBound a C P n := by
  have hCr : 0 < C := zero_lt_one.trans_le hC
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) (B : ℝ)) :
      (P : ℝ) < (n : ℝ)*x ∧ (n : ℝ)*x ≤ Y :=
    real_product_bounds_of_div_hull P Y n hn x
      ((show ((P/n+1 : ℕ) : ℝ) ≤ A by exact_mod_cast hA).trans hx.1)
      (hx.2.trans (by exact_mod_cast hB))
  have hbox (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) (B : ℝ)) :
      (P : ℝ)/n ≤ x ∧ x ≤ C*((P : ℝ)/n) := by
    have hb := hbound x hx
    constructor
    · exact (div_le_iff₀ hnr).2 (by nlinarith)
    · calc
        x ≤ (C*(P : ℝ))/n := (le_div_iff₀ hnr).2 (by nlinarith [hb.2.trans hY])
        _ = C*((P : ℝ)/n) := by ring
  have hlogs (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) (B : ℝ)) :
      Real.log (P : ℝ) ≤ Real.log ((n : ℝ)*x) ∧
        Real.log ((n : ℝ)*x) ≤ 2*Real.log (P : ℝ) := by
    have hb := hbound x hx
    constructor
    · exact Real.log_le_log hPr hb.1.le
    · calc
        Real.log ((n : ℝ)*x) ≤ Real.log (C*(P : ℝ)) :=
          Real.log_le_log (hPr.trans hb.1) (hb.2.trans hY)
        _ = Real.log C + Real.log (P : ℝ) := Real.log_mul hCr.ne' hPr.ne'
        _ ≤ _ := by linarith [Real.log_le_log hCr hCP]
  have ht := norm_sum_reciprocalLogPhase_Icc_le_of_ratio
    a (n : ℝ) (Real.log (P : ℝ)) ((P : ℝ)/n) C A B ha hnr hPlog
    (div_pos hPr hnr) hCr hAB (typeI_lambda_le_one a C P n haP hC hP hn hnP hPlog)
    hbox hlogs
  have hlen : ((B-A : ℕ) : ℝ) ≤ C*((P : ℝ)/n) := by
    calc
      _ ≤ (B : ℝ) := by exact_mod_cast (Nat.sub_le B A)
      _ ≤ ((Y / n : ℕ) : ℝ) := by exact_mod_cast hB
      _ ≤ (Y : ℝ)/n := Nat.cast_div_le
      _ ≤ (C*(P : ℝ))/n := div_le_div_of_nonneg_right hY hnr.le
      _ = _ := by ring
  have hs := ht.trans (typeI_scalar_bound a C ((B-A : ℕ) : ℝ) P n ha hCr hP hn hPlog hlen)
  simpa only [reciprocalLogWeight, reciprocalLogPhase, Nat.cast_mul] using hs

theorem norm_sum_reciprocalLogWeight_quotient_le
    (a C : ℝ) (P Y n : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hCP : C ≤ (P : ℝ))
    (hY : (Y : ℝ) ≤ C * P) (hn : 0 < n) (hnP : n ^ 2 ≤ P) :
    ‖∑ k ∈ Ioc (P/n) (Y/n), reciprocalLogWeight a (n*k)‖ ≤
      typeIInnerBound a C P n := by
  by_cases h : P/n < Y/n
  · rw [sum_Ioc_eq_sum_Icc_succ]
    exact norm_sum_reciprocalLogWeight_subinterval_le a C P Y n (P/n+1) (Y/n)
      ha haP hC hP hPlog hCP hY hn hnP le_rfl le_rfl (by omega)
  · rw [Ioc_eq_empty (by omega), sum_empty, norm_zero]
    exact typeIInnerBound_nonneg a C P n (by linarith)

theorem norm_sum_log_mul_reciprocalLogWeight_quotient_le
    (a C : ℝ) (P Y n : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hCP : C ≤ (P : ℝ))
    (hY : (Y : ℝ) ≤ C * P) (hn : 0 < n) (hnP : n ^ 2 ≤ P) :
    ‖∑ k ∈ Ioc (P/n) (Y/n), (Real.log (k : ℝ) : ℂ) *
      reciprocalLogWeight a (n*k)‖ ≤
      2 * Real.log (Y+1 : ℕ) * typeIInnerBound a C P n := by
  have hE := typeIInnerBound_nonneg a C P n (show 0 ≤ C by linarith)
  have hlogY := Real.log_natCast_nonneg (Y+1)
  by_cases h : P/n < Y/n
  · rw [sum_Ioc_eq_sum_Icc_succ]
    have ht := norm_sum_Icc_log_mul_le (fun k => reciprocalLogWeight a (n*k))
      (P/n+1) (Y/n) (typeIInnerBound a C P n) (Nat.le_add_left 1 (P/n))
      (Nat.succ_le_iff.mpr h) hE ?_
    · refine ht.trans ?_
      gcongr
      exact_mod_cast Nat.div_le_self Y n
    · intro r hr
      by_cases hr0 : r = 0
      · simpa [hr0] using hE
      · let B := P/n+1+r-1
        have hQ := Nat.zero_le (P/n)
        have hAB : P/n+1 ≤ B := by dsimp [B]; omega
        have hBY : B ≤ Y/n := by dsimp [B]; omega
        have hlen : B-(P/n+1)+1 = r := by dsimp [B]; omega
        rw [← hlen, ← sum_Icc_eq_sum_range_shift
          (fun k => reciprocalLogWeight a (n*k)) _ _ hAB]
        exact norm_sum_reciprocalLogWeight_subinterval_le a C P Y n (P/n+1) B
          ha haP hC hP hPlog hCP hY hn hnP le_rfl hBY hAB
  · rw [Ioc_eq_empty (by omega), sum_empty, norm_zero]
    positivity

def typeIOuterBound (a C : ℝ) (P D : ℕ) : ℝ :=
  60 * C ^ 2 * Real.sqrt a / Real.log (P : ℝ) * D +
    (20 * C * P * Real.log (P : ℝ) / Real.sqrt a) * (1 + Real.log (D : ℝ))

theorem typeIOuterBound_nonneg (a C : ℝ) (P D : ℕ) (hC : 0 ≤ C) :
    0 ≤ typeIOuterBound a C P D := by
  have hPlog := Real.log_natCast_nonneg P
  have hDlog := Real.log_natCast_nonneg D
  unfold typeIOuterBound
  positivity

theorem sum_typeIInnerBound_le (a C : ℝ) (P D : ℕ) (hC : 0 ≤ C) :
    (∑ n ∈ Ioc 0 D, typeIInnerBound a C P n) ≤ typeIOuterBound a C P D := by
  have hPlog := Real.log_natCast_nonneg P
  have hsum : (∑ n ∈ Ioc 0 D, (n : ℝ)⁻¹) ≤ 1+Real.log (D : ℝ) := by
    simpa only [sum_Ioc_eq_sum_Icc_succ, zero_add] using sum_Icc_inv_le_one_add_log D
  simp only [typeIInnerBound, sum_add_distrib,
    sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  have hsplit (n : ℕ) : 20*C*P*Real.log (P : ℝ)/((n : ℝ)*Real.sqrt a) =
      (20*C*P*Real.log (P : ℝ)/Real.sqrt a) * (n : ℝ)⁻¹ := by ring
  simp_rw [hsplit]
  rw [← mul_sum]
  unfold typeIOuterBound
  nlinarith [mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 20*C*P*Real.log (P : ℝ)/Real.sqrt a by positivity)]

theorem weightedArithmeticSum_convolution_band_eq_quotient
    (c b : ArithmeticFunction ℝ) (P Y : ℕ) (w : ℕ → ℂ) :
    weightedArithmeticSum (Ioc P Y) w (c*b) =
      ∑ n ∈ Ioc 0 Y, (c n : ℂ) *
        ∑ k ∈ Ioc (P/n) (Y/n), (b k : ℂ) * w (n*k) := by
  rw [weightedArithmeticSum_convolution_band]
  apply sum_congr rfl
  intro n hn
  have hn0 := (mem_Ioc.mp hn).1
  have hfilter : Ioc (P/n) (Y/n) =
      {k ∈ Ioc 0 Y | P < n*k ∧ n*k ≤ Y} := by
    ext k
    simp only [mem_Ioc, mem_filter]
    constructor
    · rintro ⟨hlo, hhi⟩
      refine ⟨⟨(Nat.zero_le _).trans_lt hlo, hhi.trans (Nat.div_le_self Y n)⟩, ?_, ?_⟩
      · simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hn0).mp hlo
      · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hn0).mp hhi
    · rintro ⟨_, hlo, hhi⟩
      exact ⟨(Nat.div_lt_iff_lt_mul hn0).mpr (by simpa [Nat.mul_comm] using hlo),
        (Nat.le_div_iff_mul_le hn0).mpr (by simpa [Nat.mul_comm] using hhi)⟩
  rw [hfilter, sum_filter, mul_sum]
  apply sum_congr rfl
  intro k _
  unfold productBandTerm
  split_ifs <;> simp [mul_assoc]

theorem norm_weightedArithmeticSum_short_convolution_le
    (c b : ArithmeticFunction ℝ) (a C K H : ℝ) (P Y D : ℕ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hsupport : ∀ n, D < n → c n = 0)
    (hcoeff : ∀ n ∈ Ioc 0 D, |c n| ≤ K)
    (hinner : ∀ n ∈ Ioc 0 D,
      ‖∑ k ∈ Ioc (P/n) (Y/n), (b k : ℂ) * reciprocalLogWeight a (n*k)‖ ≤
        H * typeIInnerBound a C P n) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (c*b)‖ ≤
      K * H * typeIOuterBound a C P D := by
  rw [weightedArithmeticSum_convolution_band_eq_quotient]
  calc
    _ ≤ ∑ n ∈ Ioc 0 Y, ‖(c n : ℂ) *
        ∑ k ∈ Ioc (P/n) (Y/n), (b k : ℂ) * reciprocalLogWeight a (n*k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc 0 Y, if n ≤ D then K*H*typeIInnerBound a C P n else 0 := by
      apply sum_le_sum
      intro n hn
      by_cases hnD : n ≤ D
      · rw [if_pos hnD, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hn' : n ∈ Ioc 0 D := mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, hnD⟩
        calc
          _ ≤ K * (H*typeIInnerBound a C P n) :=
            mul_le_mul (hcoeff n hn') (hinner n hn') (norm_nonneg _) hK
          _ = _ := by ring
      · simp [hnD, hsupport n (by omega)]
    _ = ∑ n ∈ {n ∈ Ioc 0 Y | n ≤ D}, K*H*typeIInnerBound a C P n :=
      (sum_filter _ _).symm
    _ ≤ ∑ n ∈ Ioc 0 D, K*H*typeIInnerBound a C P n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hnY, hnD⟩ := mem_filter.mp hn
        exact mem_Ioc.mpr ⟨(mem_Ioc.mp hnY).1, hnD⟩
      · intro n _ _
        exact mul_nonneg (mul_nonneg hK hH) (typeIInnerBound_nonneg a C P n hC)
    _ = K*H*∑ n ∈ Ioc 0 D, typeIInnerBound a C P n := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_typeIInnerBound_le a C P D hC)
      (mul_nonneg hK hH)

theorem norm_weightedArithmeticSum_typeILog_le
    (a C : ℝ) (U P Y : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hCP : C ≤ (P : ℝ))
    (hY : (Y : ℝ) ≤ C * P) (hUP : U ^ 2 ≤ P) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeILog U)‖ ≤
      2 * Real.log (Y+1 : ℕ) * typeIOuterBound a C P U := by
  have hH : 0 ≤ 2*Real.log (Y+1 : ℕ) := by positivity
  have ht := norm_weightedArithmeticSum_short_convolution_le
    (muLE U) ArithmeticFunction.log a C 1 (2*Real.log (Y+1 : ℕ)) P Y U
    (by linarith) zero_le_one hH
    (fun n hn => by simp [not_le.mpr hn])
    (fun n _ => abs_muLE_le_one U n) ?_
  · simpa only [one_mul, vaughanTypeILog] using ht
  · intro n hn
    obtain ⟨hn0, hnU⟩ := mem_Ioc.mp hn
    simpa only [ArithmeticFunction.log_apply] using
      norm_sum_log_mul_reciprocalLogWeight_quotient_le a C P Y n
        ha haP hC hP hPlog hCP hY hn0 ((Nat.pow_le_pow_left hnU 2).trans hUP)

theorem norm_weightedArithmeticSum_typeILambda_le
    (a C : ℝ) (U V P Y : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hCP : C ≤ (P : ℝ))
    (hY : (Y : ℝ) ≤ C * P) (hUVP : (U*V) ^ 2 ≤ P) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeILambda U V)‖ ≤
      Real.log (U*V : ℕ) * typeIOuterBound a C P (U*V) := by
  rw [vaughanTypeILambda_eq]
  have ht := norm_weightedArithmeticSum_short_convolution_le
    (typeICoeff U V) (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    a C (Real.log (U*V : ℕ)) 1 P Y (U*V)
    (by linarith) (Real.log_natCast_nonneg _) zero_le_one
    (typeICoeff_eq_zero_of_mul_lt U V) ?_ ?_
  · simpa only [mul_one] using ht
  · intro n hn
    obtain ⟨hn0, hnUV⟩ := mem_Ioc.mp hn
    exact (abs_typeICoeff_le_log U V n).trans
      (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnUV))
  · intro n hn
    obtain ⟨hn0, hnUV⟩ := mem_Ioc.mp hn
    have heq : (∑ k ∈ Ioc (P/n) (Y/n),
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) k : ℂ) *
          reciprocalLogWeight a (n*k)) =
        ∑ k ∈ Ioc (P/n) (Y/n), reciprocalLogWeight a (n*k) := by
      apply sum_congr rfl
      intro k hk
      have hk0 : k ≠ 0 := ne_of_gt ((Nat.zero_le _).trans_lt (mem_Ioc.mp hk).1)
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hk0]
    rw [heq, one_mul]
    exact norm_sum_reciprocalLogWeight_quotient_le a C P Y n
      ha haP hC hP hPlog hCP hY hn0 ((Nat.pow_le_pow_left hnUV 2).trans hUVP)

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

noncomputable section

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Filter

noncomputable section

def trackBCutoff (P : ℕ) : ℕ := ⌈Real.log (P : ℝ) ^ 64⌉₊

def trackBScaleCondition (P : ℕ) : Prop :=
  1 ≤ Real.log (P : ℝ) ∧ 16 * Real.log (P : ℝ) ^ 400 ≤ (P : ℝ)

theorem trackBCutoff_bounds (P : ℕ) (hL : 1 ≤ Real.log (P : ℝ)) :
    Real.log (P : ℝ) ^ 64 ≤ (trackBCutoff P : ℝ) ∧
      (trackBCutoff P : ℝ) ≤ 2 * Real.log (P : ℝ) ^ 64 := by
  have hpow : (1 : ℝ) ≤ Real.log (P : ℝ) ^ 64 := one_le_pow₀ hL
  refine ⟨Nat.le_ceil _, ?_⟩
  have ht := Nat.ceil_lt_add_one (show 0 ≤ Real.log (P : ℝ)^64 by positivity)
  dsimp [trackBCutoff]
  linarith

theorem trackBCutoff_pos (P : ℕ) (hL : 1 ≤ Real.log (P : ℝ)) :
    0 < trackBCutoff P := by
  have h := (one_le_pow₀ hL (n := 64)).trans (trackBCutoff_bounds P hL).1
  have : 1 ≤ trackBCutoff P := by exact_mod_cast h
  omega

theorem trackBScaleCondition_sixteen_le (P : ℕ) (h : trackBScaleCondition P) :
    16 ≤ P := by
  have hpow : (1 : ℝ) ≤ Real.log (P : ℝ)^400 := one_le_pow₀ h.1
  have : (16 : ℝ) ≤ P := by linarith [h.2]
  exact_mod_cast this

theorem trackBCutoff_sq_sq_le (P : ℕ) (h : trackBScaleCondition P) :
    (trackBCutoff P * trackBCutoff P)^2 ≤ P := by
  have hb := (trackBCutoff_bounds P h.1).2
  have he : (trackBCutoff P : ℝ)^4 ≤ (P : ℝ) := by
    calc
      _ ≤ (2*Real.log (P : ℝ)^64)^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hb 4
      _ = 16*Real.log (P : ℝ)^256 := by ring
      _ ≤ 16*Real.log (P : ℝ)^400 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ h.1 (by decide)) (by norm_num)
      _ ≤ _ := h.2
  have he' : ((trackBCutoff P : ℝ)*trackBCutoff P)^2 ≤ (P : ℝ) := by
    convert he using 1; ring
  exact_mod_cast he'

theorem trackBScaleCondition_sqrt_lower (P : ℕ) (h : trackBScaleCondition P) :
    4 * Real.log (P : ℝ)^200 ≤ Real.sqrt (P : ℝ) := by
  apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg P)).2
  convert h.2 using 1; ring

theorem eventually_trackBScaleCondition : ∀ᶠ P : ℕ in atTop, trackBScaleCondition P := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 400)).bound
    (show (0 : ℝ) < 1/16 by norm_num)
  have hn : Tendsto (fun P : ℕ => (P : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp hn).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hn.eventually hsmall, hlog] with P hp hL
  change 1 ≤ Real.log (P : ℝ) at hL
  refine ⟨hL, ?_⟩
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hL0 : 0 ≤ Real.log (P : ℝ) := by linarith
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hL0 _),
    id_eq, abs_of_nonneg hP0] at hp
  linarith

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Filter Finset

noncomputable section

theorem trackBFrequency_positive_le (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120) : 0 < a ∧ a ≤ (P : ℝ) := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by
    have := trackBScaleCondition_sixteen_le P h; omega)
  have hL : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le h.1
  exact ⟨(div_pos hP (pow_pos hL _)).trans_le hlo,
    hhi.trans (div_le_self hP.le (one_le_pow₀ h.1))⟩

theorem trackBFrequency_sqrt_lower (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (ha : 0 < a) (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a) :
    Real.sqrt (P : ℝ) ≤ Real.sqrt a * Real.log (P : ℝ)^65 := by
  have hL : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le h.1
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ a * Real.log (P : ℝ)^130 := (div_le_iff₀ (pow_pos hL _)).mp hlo
    _ = _ := by rw [mul_pow, Real.sq_sqrt ha.le]; ring

theorem trackBFrequencyRoot_upper (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (ha : 0 < a) (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120) :
    typeIIFrequencyRoot a P * Real.log (P : ℝ)^61 ≤ Real.sqrt (P : ℝ) := by
  let L := Real.log (P : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hg := typeIIFrequencyRoot_pos a P ha h.1
  have hg2 : typeIIFrequencyRoot a P ^ 2 = a/(32*L^3) := Real.sq_sqrt (by positivity)
  have he : (typeIIFrequencyRoot a P * L^61)^2 = a*L^119/32 := by
    rw [mul_pow, hg2]
    field_simp
  have ha120 : a*L^120 ≤ (P : ℝ) := (le_div_iff₀ (pow_pos hL _)).mp hhi
  have ha119 : a*L^119 ≤ (P : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h.1 (show 119 ≤ 120 by decide)) ha.le).trans ha120
  have hs := Real.sq_sqrt (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
  have hS := Real.sqrt_nonneg (P : ℝ)
  change typeIIFrequencyRoot a P * L^61 ≤ Real.sqrt (P : ℝ)
  nlinarith

theorem trackBFrequencyRoot_lower (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (ha : 0 < a) (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a) :
    Real.sqrt (P : ℝ) ≤ 6 * typeIIFrequencyRoot a P * Real.log (P : ℝ)^67 := by
  let L := Real.log (P : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hg := typeIIFrequencyRoot_pos a P ha h.1
  have hg2 : typeIIFrequencyRoot a P ^ 2 = a/(32*L^3) := Real.sq_sqrt (by positivity)
  have he : (6*typeIIFrequencyRoot a P * L^67)^2 = (36/32 : ℝ)*(a*L^130)*L := by
    rw [mul_pow, mul_pow, hg2]
    field_simp
    ring
  have ha130 : (P : ℝ) ≤ a*L^130 := (div_le_iff₀ (pow_pos hL _)).mp hlo
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  change (P : ℝ) ≤ (6*typeIIFrequencyRoot a P * L^67)^2
  rw [he]
  have hm := mul_le_mul_of_nonneg_left h.1 (show 0 ≤ a*L^130 by positivity)
  nlinarith

theorem typeIIUniformError_logSaving_le (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120) :
    typeIIUniformError a P (trackBCutoff P) ≤ 22500 / Real.log (P : ℝ)^60 := by
  let L := Real.log (P : ℝ)
  let g := typeIIFrequencyRoot a P
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have ha := (trackBFrequency_positive_le a P h hlo hhi).1
  have hg : 0 < g := typeIIFrequencyRoot_pos a P ha h.1
  have hP : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by
    have := trackBScaleCondition_sixteen_le P h; omega)
  have hS : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.mpr hP
  have hK : L^60 ≤ (trackBCutoff P : ℝ) :=
    (pow_le_pow_right₀ h.1 (show 60 ≤ 64 by decide)).trans (trackBCutoff_bounds P h.1).1
  have hd : 2/(trackBCutoff P : ℝ) ≤ 2/L^60 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hL _) hK
  have hgu : g*L^60 ≤ Real.sqrt (P : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h.1 (show 60 ≤ 61 by decide)) hg.le).trans
      (trackBFrequencyRoot_upper a P h ha hhi)
  have hu : 20480*g/Real.sqrt (P : ℝ) ≤ 20480/L^60 := by
    apply (div_le_div_iff₀ hS (pow_pos hL _)).2
    nlinarith
  have hp : 4*L^127 ≤ 6*g*L^67 := by
    calc
      _ ≤ 4*L^200 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ h.1 (by decide)) (by norm_num)
      _ ≤ Real.sqrt (P : ℝ) := trackBScaleCondition_sqrt_lower P h
      _ ≤ _ := trackBFrequencyRoot_lower a P h ha hlo
  have hp' : (4*L^60)*L^67 ≤ (6*g)*L^67 := by convert hp using 1; ring
  have hgl := le_of_mul_le_mul_right hp' (pow_pos hL 67)
  have hl : 40/g ≤ 60/L^60 := by
    apply (div_le_div_iff₀ hg (pow_pos hL _)).2
    nlinarith
  change 2/(trackBCutoff P : ℝ) + 20480*g/Real.sqrt (P : ℝ) + 40/g ≤ 22500/L^60
  have hsum := add_le_add (add_le_add hd hu) hl
  have hden : 0 < L^60 := pow_pos hL _
  calc
    _ ≤ 2/L^60 + 20480/L^60 + 60/L^60 := hsum
    _ ≤ _ := by rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hden.le

theorem sqrt_typeIIUniformError_logSaving_le (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120) :
    Real.sqrt (typeIIUniformError a P (trackBCutoff P)) ≤ 150/Real.log (P : ℝ)^30 := by
  have hL : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le h.1
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, (typeIIUniformError_logSaving_le a P h hlo hhi).trans_eq ?_⟩
  field_simp
  ring

theorem trackBEndpoint_log_bounds (C : ℝ) (P X : ℕ) (h : trackBScaleCondition P)
    (hCP : C ≤ (P : ℝ)) (hPX : P ≤ X) (hX : (X : ℝ) ≤ C*P) :
    Real.log (X : ℝ) ≤ 2*Real.log (P : ℝ) ∧
    Real.log (X+1 : ℕ) ≤ 3*Real.log (P : ℝ) ∧
    typeIICommonLog X ≤ 4*Real.log (P : ℝ) := by
  have hP16 : (16 : ℝ) ≤ P := by exact_mod_cast trackBScaleCondition_sixteen_le P h
  have hP1 : (1 : ℝ) ≤ P := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hX0 : (0 : ℝ) < X := hP0.trans_le (by exact_mod_cast hPX)
  have hXs : (X : ℝ) ≤ (P : ℝ)^2 := by nlinarith [mul_le_mul_of_nonneg_right hCP hP0.le]
  have hp2 : (1 : ℝ) ≤ (P : ℝ)^2 := one_le_pow₀ hP1
  have hp3 := mul_le_mul_of_nonneg_right hP16 (sq_nonneg (P : ℝ))
  have hX3 : (X+1 : ℕ) ≤ (P : ℝ)^3 := by push_cast; nlinarith
  have hX23 : 2*(X : ℝ)+1 ≤ (P : ℝ)^3 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ Real.log ((P : ℝ)^2) := Real.log_le_log hX0 hXs
      _ = _ := by rw [Real.log_pow]; norm_num
  · calc
      _ ≤ Real.log ((P : ℝ)^3) := Real.log_le_log (by positivity) hX3
      _ = _ := by rw [Real.log_pow]; norm_num
  · have ht := Real.log_le_log (by positivity : (0 : ℝ) < 2*X+1) hX23
    rw [Real.log_pow] at ht
    dsimp [typeIICommonLog]
    norm_num at ht
    linarith [h.1]

theorem norm_weightedArithmeticSum_typeII_le_logSaving
    (a C : ℝ) (P Y X : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120)
    (hC : 1 ≤ C) (hCP : C ≤ (P : ℝ))
    (hPX : P ≤ X) (hX : (X : ℝ) ≤ C*P) (hYX : Y ≤ X) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a)
      (vaughanTypeII (trackBCutoff P) (trackBCutoff P))‖ ≤
      691200 * C * P / Real.log (P : ℝ)^25 := by
  have ha := trackBFrequency_positive_le a P h hlo hhi
  have hL : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le h.1
  have hCr : 0 < C := zero_lt_one.trans_le hC
  have hP : 0 < P := by have := trackBScaleCondition_sixteen_le P h; omega
  have ht := norm_weightedArithmeticSum_typeII_le_uniform_endpoint a C
    (trackBCutoff P) (trackBCutoff P) P Y X ha.1 ha.2 hCr hP h.1 hCP hX hYX
    (trackBCutoff_pos P h.1) (trackBCutoff_pos P h.1)
  simp only [min_self] at ht
  obtain ⟨hlogX, hlogX1, hHX⟩ := trackBEndpoint_log_bounds C P X h hCP hPX hX
  have herr := sqrt_typeIIUniformError_logSaving_le a P h hlo hhi
  have hlogX0 := Real.log_natCast_nonneg X
  have hHX0 : 0 ≤ typeIICommonLog X := zero_le_one.trans (one_le_typeIICommonLog X)
  refine ht.trans ?_
  calc
    _ ≤ 18*(C*P)*(2*Real.log (P : ℝ))^2*(4*Real.log (P : ℝ))^3*
        (150/Real.log (P : ℝ)^30) := by gcongr
    _ = _ := by field_simp; ring

theorem typeIOuterBound_le_polylog (a C : ℝ) (P D : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120)
    (hC : 1 ≤ C) (hD : 0 < D) (hDP : D ≤ P)
    (hDb : (D : ℝ) ≤ 4*Real.log (P : ℝ)^128) :
    typeIOuterBound a C P D ≤
      280*C^2*Real.sqrt (P : ℝ)*Real.log (P : ℝ)^128 := by
  let L := Real.log (P : ℝ)
  let S := Real.sqrt (P : ℝ)
  have ha := trackBFrequency_positive_le a P h hlo hhi
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hCC : C ≤ C^2 := by nlinarith
  have hA : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha.1
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hAS : Real.sqrt a / L ≤ S :=
    (div_le_self (Real.sqrt_nonneg _) h.1).trans (Real.sqrt_le_sqrt ha.2)
  have hlogD : Real.log (D : ℝ) ≤ L :=
    Real.log_le_log (by exact_mod_cast hD) (by exact_mod_cast hDP)
  have hlogD0 := Real.log_natCast_nonneg D
  have hlogD1 : 1+Real.log (D : ℝ) ≤ 2*L := by linarith [h.1]
  have hPA : (P : ℝ)/Real.sqrt a ≤ S*L^65 := by
    apply (div_le_iff₀ hA).2
    calc
      _ = S*S := by dsimp [S]; nlinarith [Real.sq_sqrt (Nat.cast_nonneg P : (0 : ℝ) ≤ P)]
      _ ≤ S*(Real.sqrt a * L^65) := mul_le_mul_of_nonneg_left
        (trackBFrequency_sqrt_lower a P h ha.1 hlo) hS
      _ = _ := by ring
  have hfirst : 60*C^2*Real.sqrt a/L*D ≤ 240*C^2*S*L^128 := by
    calc
      _ = 60*C^2*(Real.sqrt a/L)*D := by ring
      _ ≤ 60*C^2*S*(4*L^128) := by gcongr
      _ = _ := by ring
  have hsecond : (20*C*P*L/Real.sqrt a)*(1+Real.log (D : ℝ)) ≤ 40*C^2*S*L^128 := by
    calc
      _ = 20*C*((P : ℝ)/Real.sqrt a)*L*(1+Real.log (D : ℝ)) := by ring
      _ ≤ 20*C*(S*L^65)*L*(2*L) := by gcongr
      _ = 40*C*S*L^67 := by ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCC (by norm_num)) hS)
        (pow_le_pow_right₀ h.1 (by decide)) (pow_nonneg hL.le _) (by positivity)
  calc
    _ ≤ 240*C^2*S*L^128 + 40*C^2*S*L^128 := add_le_add hfirst hsecond
    _ = _ := by ring

theorem sqrt_mul_log_pow_le_logSaving (P : ℕ) (h : trackBScaleCondition P) :
    Real.sqrt (P : ℝ)*Real.log (P : ℝ)^129 ≤ (P : ℝ)/Real.log (P : ℝ)^25 := by
  let L := Real.log (P : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hp : L^154 ≤ Real.sqrt (P : ℝ) := by
    calc
      _ ≤ L^200 := pow_le_pow_right₀ h.1 (by decide)
      _ ≤ 4*L^200 := by nlinarith [pow_nonneg hL.le 200]
      _ ≤ _ := trackBScaleCondition_sqrt_lower P h
  apply (le_div_iff₀ (pow_pos hL 25)).2
  calc
    _ = Real.sqrt (P : ℝ)*L^154 := by ring
    _ ≤ Real.sqrt (P : ℝ)^2 := by nlinarith [Real.sqrt_nonneg (P : ℝ)]
    _ = _ := Real.sq_sqrt (Nat.cast_nonneg P)

theorem norm_weightedArithmeticSum_typeI_le_logSaving
    (a C : ℝ) (P Y X : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120)
    (hC : 1 ≤ C) (hCP : C ≤ (P : ℝ))
    (hPX : P ≤ X) (hX : (X : ℝ) ≤ C*P) (hYX : Y ≤ X) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeILog (trackBCutoff P))‖ +
      ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a)
        (vaughanTypeILambda (trackBCutoff P) (trackBCutoff P))‖ ≤
      1960*C^2*P/Real.log (P : ℝ)^25 := by
  let K := trackBCutoff P
  let L := Real.log (P : ℝ)
  let B := 280*C^2*Real.sqrt (P : ℝ)*L^128
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have ha := trackBFrequency_positive_le a P h hlo hhi
  have hP : 0 < P := by have := trackBScaleCondition_sixteen_le P h; omega
  have hK : 0 < K := trackBCutoff_pos P h.1
  have hKK : 0 < K*K := Nat.mul_pos hK hK
  have hKKsq : (K*K)^2 ≤ P := trackBCutoff_sq_sq_le P h
  have hKKP : K*K ≤ P := (Nat.le_self_pow (by decide) (K*K)).trans hKKsq
  have hKK' : K^2 ≤ P := by simpa [pow_two] using hKKP
  have hKleKK : K ≤ K*K := Nat.le_mul_of_pos_right K hK
  have hKP : K ≤ P := hKleKK.trans hKKP
  have hKKb : (K*K : ℕ) ≤ 4*L^128 := by
    calc
      ((K*K : ℕ) : ℝ) = (K : ℝ)^2 := by push_cast; ring
      _ ≤ (2*L^64)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (trackBCutoff_bounds P h.1).2 2
      _ = _ := by ring
  have hKb : (K : ℝ) ≤ 4*L^128 := (by exact_mod_cast hKleKK : (K : ℝ) ≤ (K*K : ℕ)).trans hKKb
  have hB1 : typeIOuterBound a C P K ≤ B := typeIOuterBound_le_polylog a C P K
    h hlo hhi hC hK hKP hKb
  have hB2 : typeIOuterBound a C P (K*K) ≤ B := typeIOuterBound_le_polylog a C P (K*K)
    h hlo hhi hC hKK hKKP hKKb
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB10 := typeIOuterBound_nonneg a C P K hC0.le
  have hB20 := typeIOuterBound_nonneg a C P (K*K) hC0.le
  have hY : (Y : ℝ) ≤ C*P := (show (Y : ℝ) ≤ X by exact_mod_cast hYX).trans hX
  have hlogX1 := (trackBEndpoint_log_bounds C P X h hCP hPX hX).2.1
  have hlogY1 : Real.log (Y+1 : ℕ) ≤ 3*L :=
    (Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hYX 1)).trans hlogX1
  have hlogKK : Real.log (K*K : ℕ) ≤ L :=
    Real.log_le_log (by exact_mod_cast hKK) (by exact_mod_cast hKKP)
  have hlogY0 := Real.log_natCast_nonneg (Y+1)
  have hlogKK0 := Real.log_natCast_nonneg (K*K)
  have hI1 := norm_weightedArithmeticSum_typeILog_le a C K P Y
    ha.1 ha.2 hC hP h.1 hCP hY hKK'
  have hI2 := norm_weightedArithmeticSum_typeILambda_le a C K K P Y
    ha.1 ha.2 hC hP h.1 hCP hY hKKsq
  calc
    _ ≤ 2*Real.log (Y+1 : ℕ)*typeIOuterBound a C P K +
        Real.log (K*K : ℕ)*typeIOuterBound a C P (K*K) := add_le_add hI1 hI2
    _ ≤ 2*(3*L)*B + L*B := by gcongr
    _ = 1960*C^2*(Real.sqrt (P : ℝ)*L^129) := by dsimp [B]; ring
    _ ≤ 1960*C^2*((P : ℝ)/L^25) := mul_le_mul_of_nonneg_left
      (sqrt_mul_log_pow_le_logSaving P h) (by positivity)
    _ = _ := by ring

theorem norm_weightedArithmeticSum_vonMangoldt_le_logSaving
    (a C : ℝ) (P Y X : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120)
    (hC : 1 ≤ C) (hCP : C ≤ (P : ℝ))
    (hPX : P ≤ X) (hX : (X : ℝ) ≤ C*P) (hYX : Y ≤ X) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) ArithmeticFunction.vonMangoldt‖ ≤
      1000000*C^2*P/Real.log (P : ℝ)^25 := by
  let K := trackBCutoff P
  have hK : 0 < K := trackBCutoff_pos P h.1
  have hKKP : K*K ≤ P :=
    (Nat.le_self_pow (by decide) (K*K)).trans (trackBCutoff_sq_sq_le P h)
  have hKP : K ≤ P := (Nat.le_mul_of_pos_right K hK).trans hKKP
  have hlow := weightedArithmeticSum_lambdaLE_eq_zero K (Ioc P Y) (reciprocalLogWeight a)
    (fun n hn => hKP.trans_lt (mem_Ioc.mp hn).1)
  have hI := norm_weightedArithmeticSum_typeI_le_logSaving a C P Y X h hlo hhi hC hCP hPX hX hYX
  have hII := norm_weightedArithmeticSum_typeII_le_logSaving a C P Y X h hlo hhi hC hCP hPX hX hYX
  rw [vaughan_weighted_sum K K, hlow, zero_add]
  have ht := (norm_add_le
    (weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeILog K) -
      weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeILambda K K))
    (weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeII K K))).trans
    (add_le_add ((norm_sub_le _ _).trans hI) hII)
  refine ht.trans ?_
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hCC : C ≤ C^2 := by nlinarith
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hCC hP0, mul_nonneg (sq_nonneg C) hP0]

theorem eventually_vonMangoldt_logSaving (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ P : ℕ in atTop, ∀ a : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ a → a ≤ (P : ℝ)/Real.log (P : ℝ)^120 →
      ∀ Y X : ℕ, P ≤ X → (X : ℝ) ≤ C*P → Y ≤ X →
      ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) ArithmeticFunction.vonMangoldt‖ ≤
        1000000*C^2*P/Real.log (P : ℝ)^25 := by
  have hCP : ∀ᶠ P : ℕ in atTop, C ≤ (P : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop C)
  filter_upwards [eventually_trackBScaleCondition, hCP] with P hp hcp
  intro a hlo hhi Y X hPX hX hYX
  exact norm_weightedArithmeticSum_vonMangoldt_le_logSaving a C P Y X hp hlo hhi hC hcp hPX hX hYX

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Filter Finset

open scoped ComplexConjugate

noncomputable section

theorem phaseCharacter_neg_eq_conj (a : ℝ) : phaseCharacter (-a) = conj (phaseCharacter a) := by
  have h := (phaseCharacter_mul_conj 0 a).symm
  simpa only [show phaseCharacter 0 = 1 by simp [phaseCharacter], one_mul, zero_sub] using h

theorem weightedArithmeticSum_neg_frequency (A : ArithmeticFunction ℝ) (a : ℝ) (I : Finset ℕ) :
    weightedArithmeticSum I (reciprocalLogWeight (-a)) A =
      conj (weightedArithmeticSum I (reciprocalLogWeight a) A) := by
  unfold weightedArithmeticSum
  simp only [map_sum, map_mul, Complex.conj_ofReal, reciprocalLogWeight, neg_div,
    phaseCharacter_neg_eq_conj]

theorem norm_weightedArithmeticSum_abs_frequency (A : ArithmeticFunction ℝ) (a : ℝ) (I : Finset ℕ) :
    ‖weightedArithmeticSum I (reciprocalLogWeight |a|) A‖ =
      ‖weightedArithmeticSum I (reciprocalLogWeight a) A‖ := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
  · rw [abs_of_neg (lt_of_not_ge ha), weightedArithmeticSum_neg_frequency, Complex.norm_conj]

theorem eventually_vonMangoldt_signed_logSaving (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ P : ℕ in atTop, ∀ a : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ |a| → |a| ≤ (P : ℝ)/Real.log (P : ℝ)^120 →
      ∀ Y X : ℕ, P ≤ X → (X : ℝ) ≤ C*P → Y ≤ X →
      ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) ArithmeticFunction.vonMangoldt‖ ≤
        1000000*C^2*P/Real.log (P : ℝ)^25 := by
  filter_upwards [eventually_vonMangoldt_logSaving C hC] with P hp
  intro a hlo hhi Y X hPX hX hYX
  simpa only [norm_weightedArithmeticSum_abs_frequency] using hp |a| hlo hhi Y X hPX hX hYX

theorem eventually_vonMangoldt_harmonics_logSaving (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t → t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      ∀ k : ℤ, k ≠ 0 → |(k : ℝ)| ≤ Real.log (P : ℝ)^6 →
      ∀ Y X : ℕ, P ≤ X → (X : ℝ) ≤ C*P → Y ≤ X →
      ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight ((k : ℝ)*t))
        ArithmeticFunction.vonMangoldt‖ ≤ 1000000*C^2*P/Real.log (P : ℝ)^25 := by
  filter_upwards [eventually_vonMangoldt_signed_logSaving C hC,
    eventually_trackBScaleCondition] with P hp hs
  intro t htlo hthi k hk hkhi Y X hPX hX hYX
  have hP : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by
    have := trackBScaleCondition_sixteen_le P hs; omega)
  have hL : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hs.1
  have ht : 0 < t := (div_pos hP (pow_pos hL _)).trans_le htlo
  have hklo : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hprodlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ |(k : ℝ)*t| := by
    rw [abs_mul, abs_of_pos ht]
    exact htlo.trans (by nlinarith)
  have hprodhi : |(k : ℝ)*t| ≤ (P : ℝ)/Real.log (P : ℝ)^120 := by
    rw [abs_mul, abs_of_pos ht]
    calc
      _ ≤ Real.log (P : ℝ)^6 * ((P : ℝ)/Real.log (P : ℝ)^126) :=
        mul_le_mul hkhi hthi ht.le (by positivity)
      _ = _ := by field_simp
  exact hp ((k : ℝ)*t) hprodlo hprodhi Y X hPX hX hYX

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

open scoped ComplexConjugate

noncomputable section

def fejerPhaseSum (K : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ range K, phaseCharacter ((j : ℝ)*u)

def finiteFejerKernel (K : ℕ) (u : ℝ) : ℝ := ‖fejerPhaseSum K u‖^2 / (K : ℝ)^2

def inPhaseWindow (c b u : ℝ) : Prop :=
  Int.fract (u-c) ≤ b ∨ 1-b ≤ Int.fract (u-c)

instance (c b u : ℝ) : Decidable (inPhaseWindow c b u) :=
  inferInstanceAs (Decidable (Int.fract (u-c) ≤ b ∨ 1-b ≤ Int.fract (u-c)))

def fejerLeakage (K : ℕ) (b : ℝ) : ℝ := 1 / (4*(K : ℝ)^2*b^2)

def finiteFejerMinorant (K : ℕ) (c b u : ℝ) : ℝ :=
  finiteFejerKernel K (u-c) - fejerLeakage K b

theorem inPhaseWindow_iff_fract_mem (c b u : ℝ) (hb : 0 < b)
    (hlo : 0 < c-b) (hhi : c+b < 1) :
    inPhaseWindow c b u ↔ c-b ≤ Int.fract u ∧ Int.fract u ≤ c+b := by
  let f := Int.fract u
  have hf0 : 0 ≤ f := Int.fract_nonneg u
  have hf1 : f < 1 := Int.fract_lt_one u
  have hfract : Int.fract (u-c) = Int.fract (f-c) := by
    apply Int.fract_eq_fract.mpr
    refine ⟨⌊u⌋, ?_⟩
    change (u-c)-(Int.fract u-c) = (⌊u⌋ : ℝ)
    linarith [Int.fract_add_floor u]
  unfold inPhaseWindow
  rw [hfract]
  change Int.fract (f-c) ≤ b ∨ 1-b ≤ Int.fract (f-c) ↔ c-b ≤ f ∧ f ≤ c+b
  by_cases hfc : c ≤ f
  · rw [Int.fract_eq_self.mpr (show 0 ≤ f-c ∧ f-c < 1 by constructor <;> linarith)]
    constructor
    · rintro (hleft | hright) <;> constructor <;> linarith
    · rintro ⟨_, hupper⟩
      left
      linarith
  · have hfr : Int.fract (f-c) = f-c+1 := by
      rw [← Int.fract_add_one (f-c)]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hfr]
    constructor
    · rintro (hleft | hright) <;> constructor <;> linarith
    · rintro ⟨hlower, _⟩
      right
      linarith

theorem phaseCharacter_fract (u : ℝ) : phaseCharacter (Int.fract u) = phaseCharacter u := by
  exact phaseCharacter_sub_int u ⌊u⌋

theorem fejerPhaseSum_mul_one_sub (K : ℕ) (u : ℝ) :
    fejerPhaseSum K u * (1-phaseCharacter u) = 1-phaseCharacter ((K : ℝ)*u) := by
  induction K with
  | zero => simp [fejerPhaseSum, phaseCharacter]
  | succ K ih =>
    have hphase : phaseCharacter (((K+1 : ℕ) : ℝ)*u) =
        phaseCharacter ((K : ℝ)*u) * phaseCharacter u := by
      rw [show (((K+1 : ℕ) : ℝ)*u) = (K : ℝ)*u+u by push_cast; ring, phaseCharacter_add]
    simp only [fejerPhaseSum, sum_range_succ] at ih ⊢
    rw [hphase, add_mul, ih]
    ring

theorem norm_fejerPhaseSum_le (K : ℕ) (u : ℝ) : ‖fejerPhaseSum K u‖ ≤ K := by
  calc
    _ ≤ ∑ j ∈ range K, ‖phaseCharacter ((j : ℝ)*u)‖ := norm_sum_le _ _
    _ = _ := by simp

theorem finiteFejerKernel_le_one (K : ℕ) (u : ℝ) : finiteFejerKernel K u ≤ 1 := by
  by_cases hK : K = 0
  · simp [finiteFejerKernel, hK]
  · have hKr : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
    apply (div_le_one (pow_pos hKr 2)).2
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fejerPhaseSum_le K u) 2

theorem norm_fejerPhaseSum_le_of_far (K : ℕ) (u b : ℝ) (hb : 0 < b)
    (hlo : b ≤ Int.fract u) (hhi : Int.fract u ≤ 1-b) :
    ‖fejerPhaseSum K u‖ ≤ 1/(2*b) := by
  have hf0 : 0 < Int.fract u := hb.trans_le hlo
  have hf1 : Int.fract u < 1 := by linarith
  have hne : 1-phaseCharacter u ≠ 0 := by
    rw [← phaseCharacter_fract u]
    exact one_sub_phaseCharacter_ne_zero _ hf0 hf1
  have he : fejerPhaseSum K u = (1-phaseCharacter ((K : ℝ)*u))*phaseResolvent u := by
    have ht := congrArg (fun z : ℂ => z * (1-phaseCharacter u)⁻¹)
      (fejerPhaseSum_mul_one_sub K u)
    simpa only [mul_assoc, mul_inv_cancel₀ hne, mul_one, phaseResolvent] using ht
  have hr : ‖phaseResolvent u‖ ≤ 1/(4*b) := by
    have ht := norm_phaseResolvent_le b (Int.fract u) hb hlo hhi
    simpa only [phaseResolvent, phaseCharacter_fract] using ht
  have hnum : ‖1-phaseCharacter ((K : ℝ)*u)‖ ≤ 2 := by
    convert norm_sub_le (1 : ℂ) (phaseCharacter ((K : ℝ)*u)) using 1; norm_num
  rw [he, norm_mul]
  calc
    _ ≤ 2*(1/(4*b)) := mul_le_mul hnum hr (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem finiteFejerKernel_le_leakage (K : ℕ) (u b : ℝ) (hK : 0 < K) (hb : 0 < b)
    (hlo : b ≤ Int.fract u) (hhi : Int.fract u ≤ 1-b) :
    finiteFejerKernel K u ≤ fejerLeakage K b := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  calc
    _ ≤ (1/(2*b))^2/(K : ℝ)^2 := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fejerPhaseSum_le_of_far K u b hb hlo hhi) 2)
      (sq_nonneg _)
    _ = _ := by unfold fejerLeakage; field_simp; ring

theorem finiteFejerMinorant_le_indicator (K : ℕ) (c b u : ℝ) (hK : 0 < K) (hb : 0 < b) :
    finiteFejerMinorant K c b u ≤ if inPhaseWindow c b u then 1 else 0 := by
  classical
  have he0 : 0 ≤ fejerLeakage K b := by unfold fejerLeakage; positivity
  by_cases hw : inPhaseWindow c b u
  · simp only [if_pos hw, finiteFejerMinorant]
    linarith [finiteFejerKernel_le_one K (u-c)]
  · simp only [if_neg hw, finiteFejerMinorant]
    have hfar : b ≤ Int.fract (u-c) ∧ Int.fract (u-c) ≤ 1-b := by
      simp only [inPhaseWindow, not_or] at hw
      exact ⟨(lt_of_not_ge hw.1).le, (lt_of_not_ge hw.2).le⟩
    linarith [finiteFejerKernel_le_leakage K (u-c) b hK hb hfar.1 hfar.2]

theorem fejer_constant_coefficient_lower (K : ℕ) (b : ℝ) (hK : 0 < K) (_hb : 0 < b)
    (hwidth : 1 ≤ 2*(K : ℝ)*b^2) :
    1/(2*(K : ℝ)) ≤ 1/(K : ℝ) - fejerLeakage K b := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have he : fejerLeakage K b ≤ 1/(2*(K : ℝ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hwidth (show 0 ≤ 2*(K : ℝ) by positivity)]
  have hid : 1/(K : ℝ) = 1/(2*(K : ℝ)) + 1/(2*(K : ℝ)) := by ring
  linarith

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Finset

open scoped ComplexConjugate

noncomputable section

def weightedPhaseSum {α : Type*} (I : Finset α) (w u : α → ℝ) (k : ℤ) : ℂ :=
  ∑ r ∈ I, (w r : ℂ)*phaseCharacter ((k : ℝ)*u r)

theorem weightedPhaseSum_shift {α : Type*} (I : Finset α) (w u : α → ℝ) (k : ℤ) (c : ℝ) :
    weightedPhaseSum I w (fun r => u r-c) k =
      phaseCharacter (-(k : ℝ)*c)*weightedPhaseSum I w u k := by
  unfold weightedPhaseSum
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  rw [show (k : ℝ)*(u r-c) = -(k : ℝ)*c+(k : ℝ)*u r by ring, phaseCharacter_add]
  ring

theorem norm_weightedPhaseSum_shift {α : Type*} (I : Finset α) (w u : α → ℝ) (k : ℤ) (c : ℝ) :
    ‖weightedPhaseSum I w (fun r => u r-c) k‖ = ‖weightedPhaseSum I w u k‖ := by
  rw [weightedPhaseSum_shift, norm_mul, norm_phaseCharacter, one_mul]

theorem fejerPhaseSum_sq_expand (K : ℕ) (u : ℝ) :
    ((‖fejerPhaseSum K u‖^2 : ℝ) : ℂ) =
      ∑ i ∈ range K, ∑ j ∈ range K, phaseCharacter (((i : ℝ)-(j : ℝ))*u) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [fejerPhaseSum, map_sum]
  rw [sum_mul]
  simp only [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [phaseCharacter_mul_conj]
  congr 1
  ring

theorem weighted_fejerPhaseSum_sq_expand {α : Type*}
    (I : Finset α) (w u : α → ℝ) (K : ℕ) (c : ℝ) :
    ((∑ r ∈ I, w r*‖fejerPhaseSum K (u r-c)‖^2 : ℝ) : ℂ) =
      ∑ i ∈ range K, ∑ j ∈ range K,
        ∑ r ∈ I, (w r : ℂ)*phaseCharacter (((i : ℝ)-(j : ℝ))*(u r-c)) := by
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, fejerPhaseSum_sq_expand, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]

theorem fejer_pair_frequency (K i j : ℕ) (hi : i ∈ range K) (hj : j ∈ range K) (hne : i ≠ j) :
    (i : ℤ)-(j : ℤ) ≠ 0 ∧ |(((i : ℤ)-(j : ℤ) : ℤ) : ℝ)| < (K : ℝ) := by
  refine ⟨?_, ?_⟩
  · intro he
    exact hne (by exact_mod_cast sub_eq_zero.mp he)
  · have hiK : (i : ℝ) < K := by exact_mod_cast mem_range.mp hi
    have hjK : (j : ℝ) < K := by exact_mod_cast mem_range.mp hj
    have hi0 := Nat.cast_nonneg (α := ℝ) i
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    push_cast
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem abs_weighted_finiteFejerKernel_sub_mean_le {α : Type*}
    (I : Finset α) (w u : α → ℝ) (K : ℕ) (c E : ℝ) (hK : 0 < K) (hE : 0 ≤ E)
    (hfreq : ∀ k : ℤ, k ≠ 0 → |(k : ℝ)| < (K : ℝ) → ‖weightedPhaseSum I w u k‖ ≤ E) :
    |(∑ r ∈ I, w r*finiteFejerKernel K (u r-c)) - (∑ r ∈ I, w r)/(K : ℝ)| ≤ E := by
  classical
  let M : ℝ := ∑ r ∈ I, w r
  let Q := fun i j : ℕ => ∑ r ∈ I, (w r : ℂ)*phaseCharacter (((i : ℝ)-(j : ℝ))*(u r-c))
  have hdiag (i : ℕ) : Q i i = (M : ℂ) := by simp [Q, M, phaseCharacter]
  have hdiagSum : (∑ i ∈ range K, ∑ j ∈ range K, if i=j then (M : ℂ) else 0) = (K : ℂ)*M := by
    calc
      _ = ∑ _i ∈ range K, (M : ℂ) := by
        apply sum_congr rfl
        intro i hi
        simp [hi]
      _ = _ := by simp
  have hcenter : (∑ i ∈ range K, ∑ j ∈ range K, Q i j) - (K : ℂ)*M =
      ∑ i ∈ range K, ∑ j ∈ range K, (Q i j - if i=j then (M : ℂ) else 0) := by
    simp only [sum_sub_distrib]
    rw [hdiagSum]
  have hterm (i : ℕ) (hi : i ∈ range K) (j : ℕ) (hj : j ∈ range K) :
      ‖Q i j - if i=j then (M : ℂ) else 0‖ ≤ E := by
    by_cases hij : i=j
    · subst j
      simpa [hdiag] using hE
    · rw [if_neg hij, sub_zero]
      have hk := fejer_pair_frequency K i j hi hj hij
      have ht := (norm_weightedPhaseSum_shift I w u ((i : ℤ)-(j : ℤ)) c).trans_le
        (hfreq _ hk.1 hk.2)
      simpa only [weightedPhaseSum, Int.cast_sub, Int.cast_natCast] using ht
  have hc : ‖(∑ i ∈ range K, ∑ j ∈ range K, Q i j) - (K : ℂ)*M‖ ≤ (K : ℝ)^2*E := by
    rw [hcenter]
    calc
      _ ≤ ∑ i ∈ range K, ∑ j ∈ range K, ‖Q i j - if i=j then (M : ℂ) else 0‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)
      _ ≤ ∑ _i ∈ range K, ∑ _j ∈ range K, E :=
        sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
      _ = _ := by simp; ring
  have hr : |(∑ r ∈ I, w r*‖fejerPhaseSum K (u r-c)‖^2) - (K : ℝ)*M| ≤ (K : ℝ)^2*E := by
    rw [← weighted_fejerPhaseSum_sq_expand I w u K c] at hc
    rw [show (K : ℂ) = ((K : ℝ) : ℂ) by norm_cast] at hc
    simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hc
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hmean : (∑ r ∈ I, w r*finiteFejerKernel K (u r-c)) - M/(K : ℝ) =
      ((∑ r ∈ I, w r*‖fejerPhaseSum K (u r-c)‖^2) - (K : ℝ)*M)/(K : ℝ)^2 := by
    simp only [finiteFejerKernel, ← mul_div_assoc, ← sum_div]
    field_simp
  change |(∑ r ∈ I, w r*finiteFejerKernel K (u r-c)) - M/(K : ℝ)| ≤ E
  rw [hmean, abs_div, abs_of_nonneg (sq_nonneg (K : ℝ))]
  exact (div_le_iff₀ (pow_pos hKr 2)).2 (by simpa only [mul_comm] using hr)

theorem weighted_phaseWindow_mass_lower {α : Type*}
    (I : Finset α) (w u : α → ℝ) (K : ℕ) (c b E : ℝ)
    (hK : 0 < K) (hb : 0 < b) (hE : 0 ≤ E) (hw : ∀ r ∈ I, 0 ≤ w r)
    (hfreq : ∀ k : ℤ, k ≠ 0 → |(k : ℝ)| < (K : ℝ) → ‖weightedPhaseSum I w u k‖ ≤ E) :
    (1/(K : ℝ)-fejerLeakage K b)*(∑ r ∈ I, w r)-E ≤
      ∑ r ∈ I with inPhaseWindow c b (u r), w r := by
  classical
  have he := abs_weighted_finiteFejerKernel_sub_mean_le I w u K c E hK hE hfreq
  have hm : (∑ r ∈ I, w r)/(K : ℝ)-E ≤ ∑ r ∈ I, w r*finiteFejerKernel K (u r-c) := by
    linarith [(abs_le.mp he).1]
  have hsum : (∑ r ∈ I, w r*finiteFejerMinorant K c b (u r)) =
      (∑ r ∈ I, w r*finiteFejerKernel K (u r-c))-fejerLeakage K b*(∑ r ∈ I, w r) := by
    simp only [finiteFejerMinorant, mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  have hcount : (∑ r ∈ I, w r*finiteFejerMinorant K c b (u r)) ≤
      ∑ r ∈ I with inPhaseWindow c b (u r), w r := by
    rw [sum_filter]
    apply sum_le_sum
    intro r hr
    have ht := mul_le_mul_of_nonneg_left
      (finiteFejerMinorant_le_indicator K c b (u r) hK hb) (hw r hr)
    split_ifs at ht ⊢ <;> simpa only [mul_one, mul_zero] using ht
  calc
    _ = (∑ r ∈ I, w r)/(K : ℝ)-E-fejerLeakage K b*(∑ r ∈ I, w r) := by ring
    _ ≤ (∑ r ∈ I, w r*finiteFejerKernel K (u r-c))-fejerLeakage K b*(∑ r ∈ I, w r) :=
      sub_le_sub_right hm _
    _ = _ := hsum.symm
    _ ≤ _ := hcount

theorem weighted_phaseWindow_mass_lower_half {α : Type*}
    (I : Finset α) (w u : α → ℝ) (K : ℕ) (c b E : ℝ)
    (hK : 0 < K) (hb : 0 < b) (hwidth : 1 ≤ 2*(K : ℝ)*b^2)
    (hE : 0 ≤ E) (hw : ∀ r ∈ I, 0 ≤ w r)
    (hfreq : ∀ k : ℤ, k ≠ 0 → |(k : ℝ)| < (K : ℝ) → ‖weightedPhaseSum I w u k‖ ≤ E) :
    (∑ r ∈ I, w r)/(2*(K : ℝ))-E ≤ ∑ r ∈ I with inPhaseWindow c b (u r), w r := by
  have hm : 0 ≤ ∑ r ∈ I, w r := sum_nonneg hw
  calc
    _ = (1/(2*(K : ℝ)))*(∑ r ∈ I, w r)-E := by ring
    _ ≤ (1/(K : ℝ)-fejerLeakage K b)*(∑ r ∈ I, w r)-E :=
      sub_le_sub_right (mul_le_mul_of_nonneg_right (fejer_constant_coefficient_lower K b hK hb hwidth) hm) E
    _ ≤ _ := weighted_phaseWindow_mass_lower I w u K c b E hK hb hE hw hfreq

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Filter Finset

noncomputable section

theorem weightedPhaseSum_reciprocalLog (I : Finset ℕ) (A : ArithmeticFunction ℝ) (t : ℝ) (k : ℤ) :
    weightedPhaseSum I A (fun r => t/Real.log (r : ℝ)) k =
      weightedArithmeticSum I (reciprocalLogWeight ((k : ℝ)*t)) A := by
  simp only [weightedPhaseSum, weightedArithmeticSum, reciprocalLogWeight, mul_div_assoc]

theorem eventually_vonMangoldt_phaseWindow_mass_lower (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t → t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      ∀ Y X : ℕ, P ≤ X → (X : ℝ) ≤ C*P → Y ≤ X →
      ∀ K : ℕ, 0 < K → (K : ℝ) ≤ Real.log (P : ℝ)^6 →
      ∀ c b : ℝ, 0 < b → 1 ≤ 2*(K : ℝ)*b^2 →
      (∑ r ∈ Ioc P Y, ArithmeticFunction.vonMangoldt r)/(2*(K : ℝ)) -
          1000000*C^2*P/Real.log (P : ℝ)^25 ≤
        ∑ r ∈ (Ioc P Y).filter (fun r : ℕ => inPhaseWindow c b (t/Real.log (r : ℝ))),
          ArithmeticFunction.vonMangoldt r := by
  filter_upwards [eventually_vonMangoldt_harmonics_logSaving C hC] with P hp
  intro t htlo hthi Y X hPX hX hYX K hK hKL c b hb hwidth
  have hlog := Real.log_natCast_nonneg P
  apply weighted_phaseWindow_mass_lower_half (Ioc P Y) ArithmeticFunction.vonMangoldt
    (fun r => t/Real.log (r : ℝ)) K c b _ hK hb hwidth (by positivity)
    (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  intro k hk hkK
  rw [weightedPhaseSum_reciprocalLog]
  exact hp t htlo hthi k hk (hkK.le.trans hKL) Y X hPX hX hYX

def trackBFejerOrder (P : ℕ) : ℕ := ⌊Real.log (P : ℝ)^6⌋₊

theorem trackBFejerOrder_bounds (P : ℕ) (hL : 2 ≤ Real.log (P : ℝ)) :
    0 < trackBFejerOrder P ∧ (trackBFejerOrder P : ℝ) ≤ Real.log (P : ℝ)^6 ∧
      Real.log (P : ℝ)^6/2 ≤ (trackBFejerOrder P : ℝ) := by
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 6
  norm_num at hpow
  have hfloor := Nat.lt_floor_add_one (Real.log (P : ℝ)^6)
  have hlo : Real.log (P : ℝ)^6/2 ≤ (trackBFejerOrder P : ℝ) := by
    dsimp [trackBFejerOrder]
    linarith
  refine ⟨?_, Nat.floor_le (by positivity), hlo⟩
  have hK : (0 : ℝ) < trackBFejerOrder P := by linarith
  exact_mod_cast hK

theorem trackBFejerOrder_width (P : ℕ) (hL : 2 ≤ Real.log (P : ℝ)) :
    1 ≤ 2*(trackBFejerOrder P : ℝ)*(1/(2*Real.log (P : ℝ)^2))^2 := by
  have hLp : 0 < Real.log (P : ℝ) := by linarith
  have hK := (trackBFejerOrder_bounds P hL).2.2
  calc
    1 ≤ Real.log (P : ℝ)^2/4 := by apply (le_div_iff₀ (by norm_num)).2; nlinarith
    _ = 2*(Real.log (P : ℝ)^6/2)*(1/(2*Real.log (P : ℝ)^2))^2 := by field_simp; ring
    _ ≤ _ := by gcongr

theorem inPhaseWindow_log_squared_iff (P : ℕ) (u : ℝ) (hL : 2 ≤ Real.log (P : ℝ)) :
    inPhaseWindow (3/(2*Real.log (P : ℝ)^2)) (1/(2*Real.log (P : ℝ)^2)) u ↔
      1/Real.log (P : ℝ)^2 ≤ Int.fract u ∧ Int.fract u ≤ 2/Real.log (P : ℝ)^2 := by
  have hLp : 0 < Real.log (P : ℝ) := by linarith
  have helo : 3/(2*Real.log (P : ℝ)^2)-1/(2*Real.log (P : ℝ)^2) = 1/Real.log (P : ℝ)^2 := by ring
  have hehi : 3/(2*Real.log (P : ℝ)^2)+1/(2*Real.log (P : ℝ)^2) = 2/Real.log (P : ℝ)^2 := by ring
  have hlo : 0 < 3/(2*Real.log (P : ℝ)^2)-1/(2*Real.log (P : ℝ)^2) := by rw [helo]; positivity
  have hhi : 3/(2*Real.log (P : ℝ)^2)+1/(2*Real.log (P : ℝ)^2) < 1 := by
    rw [hehi]
    apply (div_lt_one (by positivity)).2
    nlinarith
  simpa only [helo, hehi] using inPhaseWindow_iff_fract_mem _ _ u (by positivity) hlo hhi

theorem eventually_vonMangoldt_logSquaredWindow_mass_lower (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t → t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      ∀ Y X : ℕ, P ≤ X → (X : ℝ) ≤ C*P → Y ≤ X →
      (∑ r ∈ Ioc P Y, ArithmeticFunction.vonMangoldt r)/(2*Real.log (P : ℝ)^6) -
          1000000*C^2*P/Real.log (P : ℝ)^25 ≤
        ∑ r ∈ (Ioc P Y).filter (fun r : ℕ =>
          1/Real.log (P : ℝ)^2 ≤ Int.fract (t/Real.log (r : ℝ)) ∧
          Int.fract (t/Real.log (r : ℝ)) ≤ 2/Real.log (P : ℝ)^2),
            ArithmeticFunction.vonMangoldt r := by
  have hlog : ∀ᶠ P : ℕ in atTop, 2 ≤ Real.log (P : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_vonMangoldt_phaseWindow_mass_lower C hC, hlog] with P hp hL
  intro t htlo hthi Y X hPX hX hYX
  obtain ⟨hK, hKhi, _⟩ := trackBFejerOrder_bounds P hL
  have hb : 0 < 1/(2*Real.log (P : ℝ)^2) := by positivity
  have ht := hp t htlo hthi Y X hPX hX hYX (trackBFejerOrder P) hK hKhi
    (3/(2*Real.log (P : ℝ)^2)) (1/(2*Real.log (P : ℝ)^2)) hb (trackBFejerOrder_width P hL)
  simp_rw [inPhaseWindow_log_squared_iff P _ hL] at ht
  refine le_trans ?_ ht
  apply sub_le_sub_right
  apply div_le_div_of_nonneg_left (sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    (by positivity) (by gcongr)

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Filter Finset

noncomputable section

def logSquaredGoodSet (P : ℕ) (t : ℝ) : Finset ℕ :=
  (Ioc P (16*P)).filter (fun r : ℕ =>
    1/Real.log (P : ℝ)^2 ≤ Int.fract (t/Real.log (r : ℝ)) ∧
      Int.fract (t/Real.log (r : ℝ)) ≤ 2/Real.log (P : ℝ)^2)

def logSquaredGoodPrimes (P : ℕ) (t : ℝ) : Finset ℕ :=
  (logSquaredGoodSet P t).filter Nat.Prime

theorem sum_prime_vonMangoldt_Ioc_eq_theta_sub (P Q : ℕ) (hPQ : P ≤ Q) :
    (∑ n ∈ (Ioc P Q).filter Nat.Prime, ArithmeticFunction.vonMangoldt n) =
      Chebyshev.theta Q - Chebyshev.theta P := by
  have hd : Disjoint ((Ioc 0 P).filter Nat.Prime) ((Ioc P Q).filter Nat.Prime) :=
    Disjoint.mono (filter_subset _ _) (filter_subset _ _) (Ioc_disjoint_Ioc_of_le le_rfl)
  have hu : (Ioc 0 P).filter Nat.Prime ∪ (Ioc P Q).filter Nat.Prime =
      (Ioc 0 Q).filter Nat.Prime := by
    rw [← filter_union, Ioc_union_Ioc_eq_Ioc (show 0 ≤ P by omega) hPQ]
  have he (R : ℕ) : (∑ n ∈ (Ioc 0 R).filter Nat.Prime, ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ (Ioc 0 R).filter Nat.Prime, Real.log n := by
    apply sum_congr rfl
    intro n hn
    exact ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hn).2
  have hs : (∑ n ∈ (Ioc 0 Q).filter Nat.Prime, ArithmeticFunction.vonMangoldt n) =
      (∑ n ∈ (Ioc 0 P).filter Nat.Prime, ArithmeticFunction.vonMangoldt n) +
        ∑ n ∈ (Ioc P Q).filter Nat.Prime, ArithmeticFunction.vonMangoldt n := by
    rw [← hu, sum_union hd]
  rw [he P, he Q] at hs
  simp only [Chebyshev.theta, Nat.floor_natCast] at hs ⊢
  linarith

theorem sum_vonMangoldt_wide_band_lower (P : ℕ) (h : trackBScaleCondition P) :
    5*(P : ℝ) ≤ ∑ n ∈ Ioc P (16*P), ArithmeticFunction.vonMangoldt n := by
  let L := Real.log (P : ℝ)
  let S := Real.sqrt (P : ℝ)
  have hP16 := trackBScaleCondition_sixteen_le P h
  have hP : 0 < P := by omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hlog16 : Real.log ((16*P+1 : ℕ) : ℝ) ≤ 3*L := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      (trackBEndpoint_log_bounds 16 P (16*P) h (by exact_mod_cast hP16) (by omega) (by norm_num)).2.1
  have hlog16P : Real.log ((16*P : ℕ) : ℝ) ≤ 2*L := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (trackBEndpoint_log_bounds 16 P (16*P) h (by exact_mod_cast hP16) (by omega) (by norm_num)).1
  have hsqrt16 : Real.sqrt ((16*P : ℕ) : ℝ) = 4*S := by
    have hsqrt_four : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = (4 : ℝ)^2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    calc
      _ = Real.sqrt ((16 : ℝ)*(P : ℝ)) := by norm_cast
      _ = Real.sqrt (16 : ℝ)*Real.sqrt (P : ℝ) := Real.sqrt_mul (by norm_num) _
      _ = _ := by rw [hsqrt_four]
  have hlogerr : Real.log ((16*P+1 : ℕ) : ℝ) ≤ (P : ℝ)/4 := by
    have hLP : 16*L ≤ (P : ℝ) := by
      calc
        _ = 16*L^1 := by ring
        _ ≤ 16*L^400 := mul_le_mul_of_nonneg_left
          (show L^1 ≤ L^400 by exact (pow_le_pow_right₀ h.1 (by decide))) (by norm_num)
        _ ≤ _ := h.2
    linarith
  have hsqrt : 4*L ≤ S := by
    calc
      _ = 4*L^1 := by ring
      _ ≤ 4*L^200 := mul_le_mul_of_nonneg_left
        (show L^1 ≤ L^200 by exact pow_le_pow_right₀ h.1 (by decide)) (by norm_num)
      _ ≤ _ := trackBScaleCondition_sqrt_lower P h
  have hsqrterr : 2*Real.sqrt ((16*P : ℕ) : ℝ)*Real.log ((16*P : ℕ) : ℝ) ≤ 4*(P : ℝ) := by
    rw [hsqrt16]
    have hSS := Real.sq_sqrt (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
    have hlog0 : 0 ≤ Real.log ((16*P : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 16*P by omega))
    have hprod := mul_le_mul_of_nonneg_left hlog16P (Real.sqrt_nonneg (P : ℝ))
    have hprod2 := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 4*S by positivity)
    nlinarith
  have htheta16 := Chebyshev.theta_ge (16*P)
  have hthetaP := Chebyshev.theta_le_log4_mul_x (x := (P : ℝ)) hPr.le
  have hprimeBand : 5*(P : ℝ) ≤
      Chebyshev.theta (16*P) - Chebyshev.theta P := by
    rw [Real.log_four_eq] at hthetaP
    have hlog2 := Real.log_two_gt_d9
    have hlog2P := mul_le_mul_of_nonneg_right hlog2.le hPr.le
    have hmain : (19/2 : ℝ)*(P : ℝ) ≤ 14*Real.log 2*(P : ℝ) := by nlinarith
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at htheta16
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hlogerr hsqrterr
    nlinarith
  have hprime : 5*(P : ℝ) ≤
      ∑ n ∈ (Ioc P (16*P)).filter Nat.Prime, ArithmeticFunction.vonMangoldt n := by
    rw [sum_prime_vonMangoldt_Ioc_eq_theta_sub P (16*P) (by omega)]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact hprimeBand
  exact hprime.trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg))

theorem sum_nonprime_vonMangoldt_wide_upper (P : ℕ) (h : trackBScaleCondition P)
    (hL2 : 2 ≤ Real.log (P : ℝ)) :
    (∑ n ∈ (Ioc 0 (16*P)).filter (fun n => ¬n.Prime), ArithmeticFunction.vonMangoldt n) ≤
      (P : ℝ)/(2*Real.log (P : ℝ)^6) := by
  let L := Real.log (P : ℝ)
  let S := Real.sqrt (P : ℝ)
  have hP : 0 < P := by have := trackBScaleCondition_sixteen_le P h; omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hL : 0 < L := by linarith
  have hlog16P : Real.log ((16*P : ℕ) : ℝ) ≤ 2*L := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (trackBEndpoint_log_bounds 16 P (16*P) h
        (by exact_mod_cast trackBScaleCondition_sixteen_le P h) (by omega) (by norm_num)).1
  have hsqrt16 : Real.sqrt ((16*P : ℕ) : ℝ) = 4*S := by
    have hsqrt_four : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = (4 : ℝ)^2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    calc
      _ = Real.sqrt ((16 : ℝ)*(P : ℝ)) := by norm_cast
      _ = Real.sqrt (16 : ℝ)*Real.sqrt (P : ℝ) := Real.sqrt_mul (by norm_num) _
      _ = _ := by rw [hsqrt_four]
  have hL193 : 8 ≤ L^193 := by
    calc
      8 = (2 : ℝ)^3 := by norm_num
      _ ≤ L^3 := pow_le_pow_left₀ (by norm_num) hL2 3
      _ ≤ L^193 := pow_le_pow_right₀ (by linarith) (by decide)
  have hscale : 32*L^7 ≤ S := by
    have ht : 8*L^7 ≤ L^193*L^7 := mul_le_mul_of_nonneg_right hL193 (pow_nonneg hL.le 7)
    calc
      _ = 4*(8*L^7) := by ring
      _ ≤ 4*(L^193*L^7) := mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = 4*L^200 := by ring
      _ ≤ _ := trackBScaleCondition_sqrt_lower P h
  have he := Chebyshev.psi_sub_theta_eq_sum_not_prime ((16*P : ℕ) : ℝ)
  simp only [Nat.floor_natCast] at he
  rw [← he]
  have ht := Chebyshev.psi_sub_theta_le (x := ((16*P : ℕ) : ℝ)) (by exact_mod_cast (show 1 ≤ 16*P by omega))
  rw [hsqrt16] at ht
  refine ht.trans ?_
  have hSS := Real.sq_sqrt (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
  have hlog0 : 0 ≤ Real.log ((16*P : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 16*P by omega))
  apply (le_div_iff₀ (by positivity)).2
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have ha : 16*S*Real.log ((16*P : ℕ) : ℝ)*L^6 ≤ 32*S*L^7 := by
    calc
      _ = (16*S*L^6)*Real.log ((16*P : ℕ) : ℝ) := by ring
      _ ≤ (16*S*L^6)*(2*L) := mul_le_mul_of_nonneg_left hlog16P
        (mul_nonneg (mul_nonneg (by norm_num) hS0) (pow_nonneg hL.le 6))
      _ = _ := by ring
  have hb : 32*S*L^7 ≤ S*S := by
    have hm := mul_le_mul_of_nonneg_left hscale hS0
    nlinarith
  rw [show S*S = (P : ℝ) by nlinarith [hSS]] at hb
  nlinarith

theorem logSquaredGoodSet_sum_split (P : ℕ) (t : ℝ) :
    (∑ n ∈ logSquaredGoodSet P t, ArithmeticFunction.vonMangoldt n) =
      (∑ p ∈ logSquaredGoodPrimes P t, ArithmeticFunction.vonMangoldt p) +
        ∑ n ∈ (logSquaredGoodSet P t).filter (fun n => ¬n.Prime),
          ArithmeticFunction.vonMangoldt n := by
  rw [logSquaredGoodPrimes]
  exact (sum_filter_add_sum_filter_not (logSquaredGoodSet P t) Nat.Prime
    ArithmeticFunction.vonMangoldt).symm

theorem logSquaredGoodSet_nonprime_subset (P : ℕ) (t : ℝ) :
    (logSquaredGoodSet P t).filter (fun n => ¬n.Prime) ⊆
      (Ioc 0 (16*P)).filter (fun n => ¬n.Prime) := by
  intro n hn
  rw [mem_filter] at hn ⊢
  have hband := (mem_filter.mp hn.1).1
  refine ⟨?_, hn.2⟩
  rw [mem_Ioc]
  exact ⟨lt_of_le_of_lt (Nat.zero_le P) (mem_Ioc.mp hband).1,
    (mem_Ioc.mp hband).2⟩

theorem eventually_goodPrime_vonMangoldt_mass_lower :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t →
      t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      (P : ℝ)/Real.log (P : ℝ)^6 ≤
        ∑ p ∈ logSquaredGoodPrimes P t, ArithmeticFunction.vonMangoldt p := by
  have hlog : ∀ᶠ P : ℕ in atTop, 3 ≤ Real.log (P : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 3)
  filter_upwards [eventually_vonMangoldt_logSquaredWindow_mass_lower 16 (by norm_num),
    eventually_trackBScaleCondition, hlog] with P hwindow hscale hL3
  intro t htlo hthi
  let L := Real.log (P : ℝ)
  have hP : 0 < P := by have := trackBScaleCondition_sixteen_le P hscale; omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hL : 0 < L := by dsimp [L]; linarith
  have hwide := sum_vonMangoldt_wide_band_lower P hscale
  have hwindow' :
      (∑ n ∈ Ioc P (16*P), ArithmeticFunction.vonMangoldt n)/(2*L^6) -
          256000000*(P : ℝ)/L^25 ≤
        ∑ n ∈ logSquaredGoodSet P t, ArithmeticFunction.vonMangoldt n := by
    have hw := hwindow t htlo hthi (16*P) (16*P) (by omega) (by norm_num) (by omega)
    have hc : (1000000 : ℝ)*16^2 = 256000000 := by norm_num
    rw [hc] at hw
    simpa only [logSquaredGoodSet, L] using hw
  have hpow19 : (512000000 : ℝ) ≤ L^19 := by
    calc
      _ ≤ (3 : ℝ)^19 := by norm_num
      _ ≤ L^19 := pow_le_pow_left₀ (by norm_num) (by simpa only [L] using hL3) 19
  have hpow : (512000000 : ℝ)*L^6 ≤ L^25 := by
    have hp := mul_le_mul_of_nonneg_right hpow19 (pow_nonneg hL.le 6)
    calc
      _ ≤ L^19*L^6 := hp
      _ = _ := by ring
  have herr : 256000000*(P : ℝ)/L^25 ≤ (P : ℝ)/(2*L^6) := by
    apply (div_le_div_iff₀ (pow_pos hL 25) (mul_pos (by norm_num) (pow_pos hL 6))).2
    calc
      (256000000*(P : ℝ))*(2*L^6) = (P : ℝ)*((512000000 : ℝ)*L^6) := by ring
      _ ≤ (P : ℝ)*L^25 := mul_le_mul_of_nonneg_left hpow hPr.le
  have hmain : 5*(P : ℝ)/(2*L^6) ≤
      (∑ n ∈ Ioc P (16*P), ArithmeticFunction.vonMangoldt n)/(2*L^6) :=
    div_le_div_of_nonneg_right hwide (by positivity)
  have hgood : 2*(P : ℝ)/L^6 ≤
      ∑ n ∈ logSquaredGoodSet P t, ArithmeticFunction.vonMangoldt n := by
    calc
      2*(P : ℝ)/L^6 = 5*(P : ℝ)/(2*L^6) - (P : ℝ)/(2*L^6) := by field_simp; ring
      _ ≤ (∑ n ∈ Ioc P (16*P), ArithmeticFunction.vonMangoldt n)/(2*L^6) -
          256000000*(P : ℝ)/L^25 := sub_le_sub hmain herr
      _ ≤ _ := hwindow'
  have hnonprime :
      (∑ n ∈ (logSquaredGoodSet P t).filter (fun n => ¬n.Prime),
        ArithmeticFunction.vonMangoldt n) ≤ (P : ℝ)/(2*L^6) := by
    exact (sum_le_sum_of_subset_of_nonneg (logSquaredGoodSet_nonprime_subset P t)
      (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)).trans
        (by
          simpa only [L] using
            (sum_nonprime_vonMangoldt_wide_upper P hscale
              (by linarith : 2 ≤ Real.log (P : ℝ))))
  have hsplit := logSquaredGoodSet_sum_split P t
  have hsafe : (P : ℝ)/L^6 ≤ 2*(P : ℝ)/L^6 - (P : ℝ)/(2*L^6) := by
    apply (div_le_iff₀ (pow_pos hL 6)).2
    field_simp
    nlinarith
  calc
    (P : ℝ)/Real.log (P : ℝ)^6 = (P : ℝ)/L^6 := by rfl
    _ ≤ 2*(P : ℝ)/L^6 - (P : ℝ)/(2*L^6) := hsafe
    _ ≤ (∑ n ∈ logSquaredGoodSet P t, ArithmeticFunction.vonMangoldt n) -
        ∑ n ∈ (logSquaredGoodSet P t).filter (fun n => ¬n.Prime),
          ArithmeticFunction.vonMangoldt n := sub_le_sub hgood hnonprime
    _ = ∑ p ∈ logSquaredGoodPrimes P t, ArithmeticFunction.vonMangoldt p := by linarith

theorem goodPrime_vonMangoldt_le_two_log (P : ℕ) (t : ℝ)
    (hscale : trackBScaleCondition P) (p : ℕ) (hp : p ∈ logSquaredGoodPrimes P t) :
    ArithmeticFunction.vonMangoldt p ≤ 2*Real.log (P : ℝ) := by
  have hpfilter := mem_filter.mp hp
  have hpprime : p.Prime := hpfilter.2
  have hpband := (mem_filter.mp hpfilter.1).1
  have hp_le : p ≤ 16*P := (mem_Ioc.mp hpband).2
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hP_pos : (0 : ℝ) < P := by
    exact_mod_cast (show 0 < P by have := trackBScaleCondition_sixteen_le P hscale; omega)
  have hlogmono : Real.log (p : ℝ) ≤ Real.log ((16*P : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (show (p : ℝ) ∈ Set.Ioi 0 by exact hp_pos)
      (show ((16*P : ℕ) : ℝ) ∈ Set.Ioi 0 by
        change (0 : ℝ) < ((16*P : ℕ) : ℝ)
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        positivity)
      (by exact_mod_cast hp_le)
  have hlogendpoint : Real.log ((16*P : ℕ) : ℝ) ≤ 2*Real.log (P : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (trackBEndpoint_log_bounds 16 P (16*P) hscale
        (by exact_mod_cast trackBScaleCondition_sixteen_le P hscale) (by omega) (by norm_num)).1
  rw [ArithmeticFunction.vonMangoldt_apply_prime hpprime]
  exact hlogmono.trans hlogendpoint

theorem eventually_logSquaredGoodPrimes_card_lower :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t →
      t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      (P : ℝ)/(2*Real.log (P : ℝ)^7) ≤ (logSquaredGoodPrimes P t).card := by
  have hlog : ∀ᶠ P : ℕ in atTop, 3 ≤ Real.log (P : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 3)
  filter_upwards [eventually_goodPrime_vonMangoldt_mass_lower,
    eventually_trackBScaleCondition, hlog] with P hmass hscale hL3
  intro t htlo hthi
  let L := Real.log (P : ℝ)
  have hL : 0 < L := by dsimp [L]; linarith
  have hmass' : (P : ℝ)/L^6 ≤
      ∑ p ∈ logSquaredGoodPrimes P t, ArithmeticFunction.vonMangoldt p := by
    simpa only [L] using hmass t htlo hthi
  have hsum : (∑ p ∈ logSquaredGoodPrimes P t, ArithmeticFunction.vonMangoldt p) ≤
      (logSquaredGoodPrimes P t).card*(2*L) := by
    calc
      _ ≤ ∑ _p ∈ logSquaredGoodPrimes P t, 2*L := by
        apply sum_le_sum
        intro p hp
        simpa only [L] using goodPrime_vonMangoldt_le_two_log P t hscale p hp
      _ = _ := by simp [mul_comm]
  have hmassCard : (P : ℝ)/L^6 ≤ (logSquaredGoodPrimes P t).card*(2*L) :=
    hmass'.trans hsum
  have hmul : (P : ℝ) ≤ (logSquaredGoodPrimes P t).card*(2*L)*L^6 :=
    (div_le_iff₀ (pow_pos hL 6)).mp hmassCard
  apply (div_le_iff₀ (mul_pos (by norm_num) (pow_pos hL 7))).2
  calc
    (P : ℝ) ≤ (logSquaredGoodPrimes P t).card*(2*L)*L^6 := hmul
    _ = ((logSquaredGoodPrimes P t).card : ℝ)*(2*L^7) := by ring

theorem exists_logSquaredGoodPrime_family_of_card_le (P N : ℕ) (t : ℝ)
    (hN : N ≤ (logSquaredGoodPrimes P t).card) :
    ∃ S : Finset ℕ, S ⊆ logSquaredGoodPrimes P t ∧ S.card = N ∧
      ∀ p ∈ S, p.Prime ∧ P < p ∧ p ≤ 16*P ∧
        1/Real.log (P : ℝ)^2 ≤ Int.fract (t/Real.log (p : ℝ)) ∧
        Int.fract (t/Real.log (p : ℝ)) ≤ 2/Real.log (P : ℝ)^2 := by
  obtain ⟨S, hsub, hcard⟩ := exists_subset_card_eq hN
  refine ⟨S, hsub, hcard, ?_⟩
  intro p hp
  have hpg := mem_filter.mp (hsub hp)
  have hbase := mem_filter.mp hpg.1
  exact ⟨hpg.2, (mem_Ioc.mp hbase.1).1, (mem_Ioc.mp hbase.1).2,
    hbase.2.1, hbase.2.2⟩

theorem eventually_exists_logSquaredGoodPrime_family :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t →
      t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      ∀ N : ℕ, (N : ℝ) ≤ (P : ℝ)/(2*Real.log (P : ℝ)^7) →
      ∃ S : Finset ℕ, S ⊆ logSquaredGoodPrimes P t ∧ S.card = N ∧
        ∀ p ∈ S, p.Prime ∧ P < p ∧ p ≤ 16*P ∧
          1/Real.log (P : ℝ)^2 ≤ Int.fract (t/Real.log (p : ℝ)) ∧
          Int.fract (t/Real.log (p : ℝ)) ≤ 2/Real.log (P : ℝ)^2 := by
  filter_upwards [eventually_logSquaredGoodPrimes_card_lower] with P hcard
  intro t htlo hthi N hN
  apply exists_logSquaredGoodPrime_family_of_card_le P N t
  exact_mod_cast hN.trans (hcard t htlo hthi)

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Filter Finset

noncomputable section

def phaseExponent (t : ℝ) (p : ℕ) : ℕ :=
  ⌊t/Real.log (p : ℝ)⌋₊

theorem phaseExponent_mul_log (t : ℝ) {p : ℕ} (hp : 1 < p) (ht : 0 ≤ t) :
    (phaseExponent t p : ℝ)*Real.log (p : ℝ) =
      t - Int.fract (t/Real.log (p : ℝ))*Real.log (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  have hu : 0 ≤ t/Real.log (p : ℝ) := div_nonneg ht hlog.le
  have hfloor : (phaseExponent t p : ℝ) =
      ((⌊t/Real.log (p : ℝ)⌋ : ℤ) : ℝ) := by
    exact natCast_floor_eq_intCast_floor hu
  calc
    (phaseExponent t p : ℝ)*Real.log (p : ℝ) =
        ((⌊t/Real.log (p : ℝ)⌋ : ℤ) : ℝ)*Real.log (p : ℝ) := by rw [hfloor]
    _ = (t/Real.log (p : ℝ) - Int.fract (t/Real.log (p : ℝ)))*
          Real.log (p : ℝ) := by
      rw [show ((⌊t/Real.log (p : ℝ)⌋ : ℤ) : ℝ) =
        t/Real.log (p : ℝ) - Int.fract (t/Real.log (p : ℝ)) by
          linarith [Int.floor_add_fract (t/Real.log (p : ℝ))]]
    _ = _ := by rw [sub_mul, div_mul_cancel₀ t hlog.ne']

theorem phaseExponent_power_eq_exp (t : ℝ) {p : ℕ} (hp : 1 < p) (ht : 0 ≤ t) :
    ((p : ℝ)^phaseExponent t p) =
      Real.exp (t - Int.fract (t/Real.log (p : ℝ))*Real.log (p : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  calc
    ((p : ℝ)^phaseExponent t p) =
        Real.exp (Real.log ((p : ℝ)^phaseExponent t p)) :=
      (Real.exp_log (pow_pos hpR _)).symm
    _ = Real.exp ((phaseExponent t p : ℝ)*Real.log (p : ℝ)) := by
      rw [Real.log_pow]
    _ = _ := congrArg Real.exp (phaseExponent_mul_log t hp ht)

theorem goodPrime_phaseExponent_power_bounds (P : ℕ) (t : ℝ)
    (hscale : trackBScaleCondition P) (ht : 0 ≤ t) {p : ℕ}
    (hp : p ∈ logSquaredGoodPrimes P t) :
    Real.exp (t - 4/Real.log (P : ℝ)) ≤ ((p : ℝ)^phaseExponent t p) ∧
      ((p : ℝ)^phaseExponent t p) ≤ Real.exp (t - 1/Real.log (P : ℝ)) := by
  let L := Real.log (P : ℝ)
  have hP : 0 < P := by have := trackBScaleCondition_sixteen_le P hscale; omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hL : 0 < L := by dsimp [L]; exact zero_lt_one.trans_le hscale.1
  have hpfilter := mem_filter.mp hp
  have hpprime : p.Prime := hpfilter.2
  have hpbase := mem_filter.mp hpfilter.1
  have hpband := mem_Ioc.mp hpbase.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpprime.one_lt)
  have hloglower : L ≤ Real.log (p : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
      (show (P : ℝ) ∈ Set.Ioi 0 by exact hPr)
      (show (p : ℝ) ∈ Set.Ioi 0 by exact hpR)
    exact_mod_cast hpband.1.le
  have hlogupper : Real.log (p : ℝ) ≤ 2*L := by
    have hp_le : p ≤ 16*P := hpband.2
    have hmono : Real.log (p : ℝ) ≤ Real.log ((16*P : ℕ) : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (show (p : ℝ) ∈ Set.Ioi 0 by exact hpR)
        (show ((16*P : ℕ) : ℝ) ∈ Set.Ioi 0 by
          change (0 : ℝ) < ((16*P : ℕ) : ℝ)
          exact_mod_cast (show 0 < 16*P by omega))
        (by exact_mod_cast hp_le)
    exact hmono.trans (by
      simpa only [L, Nat.cast_mul, Nat.cast_ofNat] using
        (trackBEndpoint_log_bounds 16 P (16*P) hscale
          (by exact_mod_cast trackBScaleCondition_sixteen_le P hscale)
          (by omega) (by norm_num)).1)
  have hphaseLower : 1/L^2 ≤ Int.fract (t/Real.log (p : ℝ)) := by
    simpa only [L] using hpbase.2.1
  have hphaseUpper : Int.fract (t/Real.log (p : ℝ)) ≤ 2/L^2 := by
    simpa only [L] using hpbase.2.2
  have hproductLower : 1/L ≤
      Int.fract (t/Real.log (p : ℝ))*Real.log (p : ℝ) := by
    calc
      1/L = (1/L^2)*L := by field_simp
      _ ≤ _ := mul_le_mul hphaseLower hloglower hL.le (Int.fract_nonneg _)
  have hproductUpper :
      Int.fract (t/Real.log (p : ℝ))*Real.log (p : ℝ) ≤ 4/L := by
    calc
      _ ≤ (2/L^2)*(2*L) := mul_le_mul hphaseUpper hlogupper hlogp.le (by positivity)
      _ = 4/L := by field_simp; norm_num
  rw [phaseExponent_power_eq_exp t hpprime.one_lt ht]
  constructor
  · apply Real.exp_le_exp.mpr
    linarith
  · apply Real.exp_le_exp.mpr
    linarith

theorem sum_phaseExponent_power_lower {P : ℕ} {t : ℝ} (hscale : trackBScaleCondition P)
    (ht : 0 ≤ t) {S : Finset ℕ} (hS : S ⊆ logSquaredGoodPrimes P t) :
    (S.card : ℝ)*Real.exp (t - 4/Real.log (P : ℝ)) ≤
      ∑ p ∈ S, ((p : ℝ)^phaseExponent t p) := by
  calc
    _ = ∑ _p ∈ S, Real.exp (t - 4/Real.log (P : ℝ)) := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      exact (goodPrime_phaseExponent_power_bounds P t hscale ht (hS hp)).1

end

end Local878.TrackB

end

section

namespace LeanPool.PartialRegularity.Extension

lemma sorted_primes_get_ge (l : List ℕ) (hsort : l.SortedLT) (hge2 : ∀ x ∈ l, 2 ≤ x)
    (i : Fin l.length) : i.val + 2 ≤ l.get i := by
  have hmono : StrictMono l.get := List.SortedLT.strictMono_get hsort
  induction h : i.val generalizing i with
  | zero =>
    simpa only [zero_add] using hge2 (l.get i) (List.get_mem ..)
  | succ n ih =>
    have hn_lt : n < l.length := by have := h ▸ i.isLt; omega
    let j : Fin l.length := ⟨n, hn_lt⟩
    have ih_j : n + 2 ≤ l.get j := ih j rfl
    have hlt : l.get j < l.get i := hmono (by change n < i.val; omega)
    omega

lemma factorial_le_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    (S.card + 1).factorial ≤ ∏ p ∈ S, p := by
  let l := S.sort (· ≤ ·)
  have hl_sorted : l.SortedLT := Finset.sortedLT_sort S
  have hl_length : l.length = S.card := Finset.length_sort (· ≤ ·)
  have hl_prod : l.prod = ∏ p ∈ S, p := by
    rw [← Finset.prod_toList]
    exact (Finset.sort_perm_toList S (· ≤ ·)).prod_eq
  have hl_ge2 : ∀ x ∈ l, 2 ≤ x := fun x hx => (hS x ((Finset.mem_sort _).mp hx)).two_le
  rw [← hl_prod, ← hl_length]
  have hfact : (l.length + 1).factorial = ∏ i ∈ Finset.range l.length, (i + 2) := by
    have h := Finset.prod_range_succ' (fun k => k + 1) l.length
    simpa only [zero_add, mul_one, Finset.prod_range_add_one_eq_factorial] using h
  rw [hfact]
  have hprod_eq : l.prod = ∏ i : Fin l.length, l.get i := by
    simp_all
  rw [hprod_eq]
  calc ∏ i ∈ Finset.range l.length, (i + 2)
      = ∏ i : Fin l.length, (i.val + 2) := (Fin.prod_univ_eq_prod_range _ _).symm
    _ ≤ ∏ i : Fin l.length, l.get i := Finset.prod_le_prod' fun i _ =>
        sorted_primes_get_ge l hl_sorted hl_ge2 i

lemma primeFactors_factorial_le_1 (n : ℕ) (hn : 0 < n) :
    (n.primeFactors.card + 1).factorial ≤ n := by
  calc (n.primeFactors.card + 1).factorial
      ≤ ∏ p ∈ n.primeFactors, p := factorial_le_prod_primes n.primeFactors
          (fun p hp => Nat.prime_of_mem_primeFactors hp)
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

end LeanPool.PartialRegularity.Extension

end

section

open Filter Topology

open scoped Real Topology

namespace Local878

private theorem succ_omega_factorial_le (n : ℕ) (hn : 0 < n) :
    (n.primeFactors.card + 1).factorial ≤ n :=
  LeanPool.PartialRegularity.Extension.primeFactors_factorial_le_1 n hn

private theorem succ_omega_log_sub_le_log (n : ℕ) (hn : 0 < n) :
    let k := n.primeFactors.card + 1
    (k : ℝ) * Real.log k - k ≤ Real.log n := by
  let k := n.primeFactors.card + 1
  have hk : k ≠ 0 := by simp [k]
  have hfac : k.factorial ≤ n := by
    simpa [k] using succ_omega_factorial_le n hn
  have hfacReal : (k.factorial : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfac
  have hlogFac : Real.log (k.factorial : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hfacReal
  have hstirling := Stirling.le_log_factorial_stirling hk
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by simp [k])
  have hlogTwoPi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  dsimp only
  linarith

private noncomputable def factorialBarrier (x : ℝ) : ℝ := x * Real.log x - x

private theorem factorialBarrier_strictMonoOn :
    StrictMonoOn factorialBarrier (Set.Ici 1) := by
  unfold factorialBarrier
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
  · fun_prop
  · intro x hx
    have hx1 : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
    rw [show deriv (fun y : ℝ ↦ y * Real.log y - y) x = Real.log x by
      change deriv ((fun y : ℝ ↦ y * Real.log y) - id) x = Real.log x
      simpa using ((Real.hasDerivAt_mul_log hx0).sub (hasDerivAt_id x)).deriv]
    exact Real.log_pos hx1

private theorem tendsto_factorialBarrier_candidate (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ ↦ factorialBarrier (c * x / Real.log x) / x)
      atTop (𝓝 c) := by
  have hloglog :
      Tendsto (fun x : ℝ ↦ Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).tendsto_div_nhds_zero
  have hconst :
      Tendsto (fun x : ℝ ↦ (Real.log c - 1) / Real.log x) atTop (𝓝 0) :=
    Real.isLittleO_const_log_atTop.tendsto_div_nhds_zero
  have hone : Tendsto (fun _x : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hmain :
      Tendsto
        (fun x : ℝ ↦ c *
          ((Real.log c - 1) / Real.log x + 1 -
            Real.log (Real.log x) / Real.log x)) atTop (𝓝 c) := by
    simpa using (hconst.add hone |>.sub hloglog).const_mul c
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogx0 : Real.log x ≠ 0 := hlogx.ne'
  rw [factorialBarrier, Real.log_div (mul_ne_zero hc.ne' hx0) hlogx0,
    Real.log_mul hc.ne' hx0]
  field_simp
  ring

private theorem eventually_lt_factorialBarrier_candidate (c : ℝ) (hc : 1 < c) :
    ∀ᶠ x : ℝ in atTop, x < factorialBarrier (c * x / Real.log x) := by
  filter_upwards [
    (tendsto_factorialBarrier_candidate c (zero_lt_one.trans hc)).eventually_const_lt hc,
    eventually_gt_atTop (0 : ℝ)] with x hratio hx
  have h := (lt_div_iff₀ hx).mp (by simpa using hratio)
  nlinarith

theorem eventually_max_card_primeFactors_le_log_div_loglog (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (((Finset.range (x + 1)).sup fun n ↦ n.primeFactors.card : ℕ) : ℝ) ≤
        (1 + ε) * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ)) := by
  let c : ℝ := 1 + ε
  have hc : 1 < c := by simp [c, hε]
  have hlogNat :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [
    hlogNat.eventually (eventually_lt_factorialBarrier_candidate c hc),
    hlogNat.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with x hbarrier hlogx hx
  let L : ℝ := Real.log (x : ℝ)
  let A : ℝ := c * L / Real.log L
  have hL : 0 < L := zero_lt_one.trans hlogx
  have hlogL : 0 < Real.log L := Real.log_pos hlogx
  have hApos : 0 < A := div_pos (mul_pos (zero_lt_one.trans hc) hL) hlogL
  have hLA : L < factorialBarrier A := by simpa [L, A] using hbarrier
  have hAone : 1 ≤ A := by
    by_contra hA
    have hAlt : A < 1 := lt_of_not_ge hA
    have hlogA : Real.log A < 0 := Real.log_neg hApos hAlt
    have : factorialBarrier A < 0 := by
      unfold factorialBarrier
      nlinarith
    linarith
  have hrange : (Finset.range (x + 1)).Nonempty := by simp
  obtain ⟨n, hnrange, hsup⟩ :=
    Finset.sup_mem_of_nonempty (f := fun n ↦ n.primeFactors.card) hrange
  rw [show (Finset.range (x + 1)).sup (fun n ↦ n.primeFactors.card) =
      n.primeFactors.card from hsup.symm]
  by_cases hn0 : n = 0
  · simp only [hn0, Nat.primeFactors_zero, Finset.card_empty, Nat.cast_zero]
    simpa [A, L, c] using hApos.le
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hnx : n ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnrange)
  have hlognL : Real.log (n : ℝ) ≤ L := by
    apply Real.log_le_log
    · exact_mod_cast hnpos
    · exact_mod_cast hnx
  let k : ℝ := (n.primeFactors.card + 1 : ℕ)
  have hkone : 1 ≤ k := by simp [k]
  have hkbarrier : factorialBarrier k ≤ L := by
    calc
      factorialBarrier k ≤ Real.log (n : ℝ) := by
        simpa [factorialBarrier, k] using
          succ_omega_log_sub_le_log n hnpos
      _ ≤ L := hlognL
  have hkA : k ≤ A := by
    by_contra hk
    have hAk : A < k := lt_of_not_ge hk
    have := factorialBarrier_strictMonoOn hAone hkone hAk
    linarith
  change (n.primeFactors.card : ℝ) ≤
    (1 + ε) * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ))
  have homega_le_k : (n.primeFactors.card : ℝ) ≤ k := by
    simp [k]
  exact homega_le_k.trans (by simpa [A, L, c] using hkA)

end Local878

end
section

open Classical Filter Asymptotics

open scoped Topology Real

namespace Local878

noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

noncomputable def sourceH (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 x, (f n : ℝ) / (n : ℝ)

noncomputable abbrev H (x : ℕ) : ℝ := sourceH x

noncomputable def omega (n : ℕ) : ℕ := n.primeFactors.card

def IsAdmissible (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 n ∧
    (A : Set ℕ).Pairwise (fun a b ↦ Nat.Coprime a b) ∧
    ∀ a ∈ A, ∀ p, p.Prime → p ∣ a → p ∣ n

noncomputable def F (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).powerset.filter (IsAdmissible n)).sup fun A ↦ ∑ a ∈ A, a

noncomputable def scale (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (Real.log (n : ℝ))

noncomputable def maxUpTo (g : ℕ → ℕ) (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).sup g

noncomputable def maximalOrderScale (x : ℕ) : ℝ :=
  (x : ℝ) * Real.log x / Real.log (Real.log x)

theorem eventually_maximalOrderScale_pos : ∀ᶠ x : ℕ in atTop,
    0 < maximalOrderScale x := by
  have hlog : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun x : ℕ ↦ Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with x hlogx hloglogx hx
  unfold maximalOrderScale
  exact div_pos (mul_pos (by exact_mod_cast hx) hlogx) hloglogx

noncomputable def h (x : ℕ) : ℕ := maxUpTo omega x

noncomputable def m (x : ℕ) : ℕ := maxUpTo f x

theorem f_le_mul_omega (n : ℕ) (hn : n ≠ 0) : f n ≤ n * omega n := by
  unfold f omega
  calc
    ∑ p ∈ n.primeFactors, p ^ Nat.log p n ≤ ∑ _p ∈ n.primeFactors, n := by
      gcongr with p hp
      exact Nat.pow_log_le_self p hn
    _ = n * n.primeFactors.card := by simp [Nat.mul_comm]

theorem maxUpTo_f_le_mul_maxUpTo_omega (x : ℕ) :
    maxUpTo f x ≤ x * maxUpTo omega x := by
  unfold maxUpTo
  apply Finset.sup_le
  intro n hn
  have hnx : n ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  by_cases hn0 : n = 0
  · simp [hn0, f]
  · exact (f_le_mul_omega n hn0).trans
      (Nat.mul_le_mul hnx (Finset.le_sup (f := omega) hn))

theorem eventually_maxUpTo_f_le_one_add_mul_scale (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (maxUpTo f x : ℝ) ≤ (1 + ε) * maximalOrderScale x := by
  filter_upwards [eventually_max_card_primeFactors_le_log_div_loglog ε hε] with x homega
  have hfinite := maxUpTo_f_le_mul_maxUpTo_omega x
  have homega' :
      (maxUpTo omega x : ℝ) ≤
        (1 + ε) * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ)) := by
    change (((Finset.range (x + 1)).sup fun n ↦ n.primeFactors.card : ℕ) : ℝ) ≤
      (1 + ε) * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ))
    exact homega
  calc
    (maxUpTo f x : ℝ) ≤ (x * maxUpTo omega x : ℕ) := by exact_mod_cast hfinite
    _ = (x : ℝ) * (maxUpTo omega x : ℝ) := by norm_cast
    _ ≤ (x : ℝ) *
        ((1 + ε) * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ))) := by
      exact mul_le_mul_of_nonneg_left homega' (by positivity)
    _ = (1 + ε) * maximalOrderScale x := by
      unfold maximalOrderScale
      ring

theorem eventually_maxUpTo_f_ratio_le_one_add (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (maxUpTo f x : ℝ) / maximalOrderScale x ≤ 1 + ε := by
  have hlogNat :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_maxUpTo_f_le_one_add_mul_scale ε hε,
    hlogNat.eventually (eventually_gt_atTop (1 : ℝ))] with x hupper hlogx
  have hx : 1 < (x : ℝ) :=
    (Real.log_pos_iff (by positivity)).mp (zero_lt_one.trans hlogx)
  have hscale : 0 < maximalOrderScale x := by
    unfold maximalOrderScale
    exact div_pos (mul_pos (zero_lt_one.trans hx) (zero_lt_one.trans hlogx))
      (Real.log_pos hlogx)
  exact (div_le_iff₀ hscale).mpr (by simpa [mul_comm] using hupper)

theorem tendsto_maximalOrder_of_eventually_one_sub_le
    (hlower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℕ in atTop,
        1 - ε ≤ (maxUpTo f x : ℝ) / maximalOrderScale x) :
    Tendsto (fun x : ℕ ↦
      (maxUpTo f x : ℝ) / maximalOrderScale x) atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let ε : ℝ := (1 - a) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [hlower ε hε] with x hx
    dsimp [ε] at hx
    linarith
  · intro b hb
    let ε : ℝ := (b - 1) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [eventually_maxUpTo_f_ratio_le_one_add ε hε] with x hx
    dsimp [ε] at hx
    linarith

theorem f_le_maxUpTo {n x : ℕ} (hnx : n ≤ x) : f n ≤ maxUpTo f x := by
  exact Finset.le_sup (f := f) (Finset.mem_range.mpr (Nat.lt_succ_of_le hnx))

theorem sum_primePower_le_maxUpTo_f_of_prime_family
    {n x : ℕ} (hn : n ≠ 0) (hnx : n ≤ x) {S : Finset ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ∣ n) :
    (∑ p ∈ S, p ^ Nat.log p n) ≤ maxUpTo f x := by
  have hsubset : S ⊆ n.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hdvd p hp, hn⟩
  have hsum : (∑ p ∈ S, p ^ Nat.log p n) ≤ f n := by
    unfold f
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by simp)
  exact hsum.trans (f_le_maxUpTo hnx)

noncomputable def primeProduct (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

noncomputable def multipleBelow (X : ℕ) (S : Finset ℕ) : ℕ :=
  primeProduct S * (X / primeProduct S)

theorem primeProduct_pos {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime) :
    0 < primeProduct S := by
  unfold primeProduct
  exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos

theorem primeProduct_le_pow_card {S : Finset ℕ} {P : ℕ}
    (hP : ∀ p ∈ S, p ≤ P) : primeProduct S ≤ P ^ S.card := by
  unfold primeProduct
  exact Finset.prod_le_pow_card S id P hP

theorem multipleBelow_le (X : ℕ) (S : Finset ℕ) : multipleBelow X S ≤ X := by
  unfold multipleBelow
  simpa [Nat.mul_comm] using Nat.div_mul_le_self X (primeProduct S)

theorem multipleBelow_add_primeProduct_gt (X : ℕ) {S : Finset ℕ}
    (hprime : ∀ p ∈ S, p.Prime) :
    X < multipleBelow X S + primeProduct S := by
  have hprodPos : 0 < primeProduct S := primeProduct_pos hprime
  have hmod : X % primeProduct S < primeProduct S := Nat.mod_lt X hprodPos
  have hdecomp := Nat.mod_add_div X (primeProduct S)
  unfold multipleBelow
  omega

theorem sum_primePower_le_maxUpTo_f_of_selected_primes
    {X : ℕ} (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hprod : primeProduct S ≤ X) :
    (∑ p ∈ S, p ^ Nat.log p (multipleBelow X S)) ≤ maxUpTo f X := by
  have hprodPos : 0 < primeProduct S := primeProduct_pos hprime
  have hquotPos : 0 < X / primeProduct S := Nat.div_pos hprod hprodPos
  have hn : multipleBelow X S ≠ 0 := by
    unfold multipleBelow
    exact Nat.mul_ne_zero hprodPos.ne' hquotPos.ne'
  have hdvd : ∀ p ∈ S, p ∣ multipleBelow X S := by
    intro p hp
    exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem id hp) _
  exact sum_primePower_le_maxUpTo_f_of_prime_family hn
    (multipleBelow_le X S) hprime hdvd

def erdos_878.parts.i : Prop :=
    True ↔ ∃ A : Set ℕ, A.HasDensity 1 ∧
      (fun n : A ↦ (f n : ℝ)) =o[atTop] (fun n : A ↦ scale n) ∧
      (fun n : A ↦ scale n) =O[atTop] (fun n : A ↦ (F n : ℝ))

def proof_targets.parts_ii : Prop :=
    Tendsto (fun x : ℕ ↦
      (maxUpTo f x : ℝ) / ((x : ℝ) * Real.log x / Real.log (Real.log x)))
      atTop (𝓝 1)

namespace erdos_878.variants

end erdos_878.variants

namespace erdos_878.variants

end erdos_878.variants

theorem second_question_iff :
    proof_targets.parts_ii ↔
      Tendsto (fun x : ℕ ↦
        (maxUpTo f x : ℝ) / maximalOrderScale x) atTop (𝓝 1) := by
  simp [proof_targets.parts_ii, maximalOrderScale]

end Local878

end

section

namespace Local878.TrackB

open Filter Finset

noncomputable section

theorem goodPrime_family_prime {P : ℕ} {t : ℝ} {S : Finset ℕ}
    (hS : S ⊆ logSquaredGoodPrimes P t) : ∀ p ∈ S, p.Prime := by
  intro p hp
  exact (mem_filter.mp (hS hp)).2

theorem goodPrime_family_product_le {P : ℕ} {t : ℝ} {S : Finset ℕ}
    (hS : S ⊆ logSquaredGoodPrimes P t) :
    Local878.primeProduct S ≤ (16*P)^S.card := by
  apply Local878.primeProduct_le_pow_card
  intro p hp
  exact (mem_Ioc.mp (mem_filter.mp (mem_filter.mp (hS hp)).1).1).2

theorem phaseExponent_le_log_multipleBelow {X P : ℕ} {t : ℝ} {S : Finset ℕ}
    (hscale : trackBScaleCondition P) (ht : 0 ≤ t)
    (hS : S ⊆ logSquaredGoodPrimes P t)
    (hmultiple : Real.exp (t - 1/Real.log (P : ℝ)) ≤
      (Local878.multipleBelow X S : ℝ)) :
    ∀ p ∈ S, phaseExponent t p ≤ Nat.log p (Local878.multipleBelow X S) := by
  intro p hp
  have hprime := goodPrime_family_prime hS p hp
  apply Nat.le_log_of_pow_le hprime.one_lt
  exact_mod_cast (goodPrime_phaseExponent_power_bounds P t hscale ht (hS hp)).2.trans hmultiple

theorem card_mul_exp_le_maxUpTo_f_of_goodPrime_family
    {X P : ℕ} {t : ℝ} {S : Finset ℕ}
    (hscale : trackBScaleCondition P) (ht : 0 ≤ t)
    (hS : S ⊆ logSquaredGoodPrimes P t)
    (hprod : Local878.primeProduct S ≤ X)
    (hmultiple : Real.exp (t - 1/Real.log (P : ℝ)) ≤
      (Local878.multipleBelow X S : ℝ)) :
    (S.card : ℝ)*Real.exp (t - 4/Real.log (P : ℝ)) ≤
      (Local878.maxUpTo Local878.f X : ℝ) := by
  have hprime := goodPrime_family_prime hS
  have hexponents := phaseExponent_le_log_multipleBelow hscale ht hS hmultiple
  have hphase := sum_phaseExponent_power_lower hscale ht hS
  have hsum : (∑ p ∈ S, ((p : ℝ)^phaseExponent t p)) ≤
      ∑ p ∈ S, ((p ^ Nat.log p (Local878.multipleBelow X S) : ℕ) : ℝ) := by
    apply sum_le_sum
    intro p hp
    exact_mod_cast Nat.pow_le_pow_right (hprime p hp).pos (hexponents p hp)
  have hmaxNat := Local878.sum_primePower_le_maxUpTo_f_of_selected_primes S hprime hprod
  have hmax : (∑ p ∈ S,
      ((p ^ Nat.log p (Local878.multipleBelow X S) : ℕ) : ℝ)) ≤
      (Local878.maxUpTo Local878.f X : ℝ) := by
    exact_mod_cast hmaxNat
  exact hphase.trans (hsum.trans hmax)

theorem card_mul_exp_le_maxUpTo_f_of_goodPrime_family_of_additive_budget
    {X P : ℕ} {t : ℝ} {S : Finset ℕ}
    (hscale : trackBScaleCondition P) (ht : 0 ≤ t)
    (hS : S ⊆ logSquaredGoodPrimes P t)
    (hbudget : Real.exp (t - 1/Real.log (P : ℝ)) +
      (((16*P)^S.card : ℕ) : ℝ) ≤ (X : ℝ)) :
    (S.card : ℝ)*Real.exp (t - 4/Real.log (P : ℝ)) ≤
      (Local878.maxUpTo Local878.f X : ℝ) := by
  have hprime := goodPrime_family_prime hS
  have hprodNat := goodPrime_family_product_le hS
  have hprod : Local878.primeProduct S ≤ X := by
    have hpowReal : ((((16*P)^S.card : ℕ) : ℝ)) ≤ (X : ℝ) :=
      hbudget.trans' (le_add_of_nonneg_left (Real.exp_pos _).le)
    exact hprodNat.trans (by exact_mod_cast hpowReal)
  have hgapNat := Local878.multipleBelow_add_primeProduct_gt X hprime
  have hgap : (X : ℝ) < (Local878.multipleBelow X S : ℝ) +
      (Local878.primeProduct S : ℝ) := by exact_mod_cast hgapNat
  have hprodReal : (Local878.primeProduct S : ℝ) ≤
      (((16*P)^S.card : ℕ) : ℝ) := by exact_mod_cast hprodNat
  have hmultiple : Real.exp (t - 1/Real.log (P : ℝ)) ≤
      (Local878.multipleBelow X S : ℝ) := by linarith
  exact card_mul_exp_le_maxUpTo_f_of_goodPrime_family hscale ht hS hprod hmultiple

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Filter Finset

noncomputable section

def endpointConditions (ε : ℝ) (X P N : ℕ) (t : ℝ) : Prop :=
  0 ≤ t ∧
  (P : ℝ)/Real.log (P : ℝ)^130 ≤ t ∧
  t ≤ (P : ℝ)/Real.log (P : ℝ)^126 ∧
  (N : ℝ) ≤ (P : ℝ)/(2*Real.log (P : ℝ)^7) ∧
  Real.exp (t - 1/Real.log (P : ℝ)) + (((16*P)^N : ℕ) : ℝ) ≤ (X : ℝ) ∧
  0 < Local878.maximalOrderScale X ∧
  1-ε ≤ (N : ℝ)*Real.exp (t - 4/Real.log (P : ℝ)) /
    Local878.maximalOrderScale X

theorem eventually_maxUpTo_ratio_ge_one_sub_of_endpointConditions
    (ε : ℝ) (P N : ℕ → ℕ) (t : ℕ → ℝ)
    (hP : Tendsto P atTop atTop)
    (hcond : ∀ᶠ X : ℕ in atTop, endpointConditions ε X (P X) (N X) (t X)) :
    ∀ᶠ X : ℕ in atTop,
      1-ε ≤ (Local878.maxUpTo Local878.f X : ℝ) / Local878.maximalOrderScale X := by
  have hselect := hP.eventually eventually_exists_logSquaredGoodPrime_family
  have hscale := hP.eventually eventually_trackBScaleCondition
  filter_upwards [hselect, hscale, hcond] with X hselectX hscaleX hX
  rcases hX with ⟨ht0, htlo, hthi, hN, hbudget, hscalePos, hnormalized⟩
  obtain ⟨S, hsubset, hcard, _⟩ := hselectX (t X) htlo hthi (N X) hN
  have hbudgetS : Real.exp (t X - 1/Real.log (P X : ℝ)) +
      (((16*(P X))^S.card : ℕ) : ℝ) ≤ (X : ℝ) := by
    simpa only [hcard] using hbudget
  have hpacked := card_mul_exp_le_maxUpTo_f_of_goodPrime_family_of_additive_budget
    hscaleX ht0 hsubset hbudgetS
  have hpacked' : (N X : ℝ)*Real.exp (t X - 4/Real.log (P X : ℝ)) ≤
      (Local878.maxUpTo Local878.f X : ℝ) := by
    simpa only [hcard] using hpacked
  have hquot : (N X : ℝ)*Real.exp (t X - 4/Real.log (P X : ℝ)) /
      Local878.maximalOrderScale X ≤
      (Local878.maxUpTo Local878.f X : ℝ) / Local878.maximalOrderScale X :=
    div_le_div_of_nonneg_right hpacked' hscalePos.le
  exact hnormalized.trans hquot

theorem second_question_of_endpointParameters
    (hparams : ∀ ε : ℝ, 0 < ε →
      ∃ (P N : ℕ → ℕ) (t : ℕ → ℝ),
        Tendsto P atTop atTop ∧
        ∀ᶠ X : ℕ in atTop, endpointConditions ε X (P X) (N X) (t X)) :
    proof_targets.parts_ii := by
  apply Local878.second_question_iff.mpr
  apply Local878.tendsto_maximalOrder_of_eventually_one_sub_le
  intro ε hε
  obtain ⟨P, N, t, hP, hcond⟩ := hparams ε hε
  exact eventually_maxUpTo_ratio_ge_one_sub_of_endpointConditions ε P N t hP hcond

end

end Local878.TrackB

end

section

namespace Local878.TrackB

open Filter

open scoped Topology

noncomputable section

def endpointT (X : ℕ) : ℝ := Real.log (X : ℝ)

def endpointV (X : ℕ) : ℝ := Real.log (endpointT X)

def endpointPrimeReal (X : ℕ) : ℝ := endpointT X * endpointV X ^ 128

def endpointPrimeScale (X : ℕ) : ℕ := Nat.ceil (endpointPrimeReal X)

def endpointLogScale (X : ℕ) : ℝ := Real.log (endpointPrimeScale X : ℝ)

def endpointSelectedCount (δ : ℝ) (X : ℕ) : ℕ :=
  Nat.floor ((1-δ)*endpointT X / Real.log ((16*endpointPrimeScale X : ℕ) : ℝ))

theorem tendsto_endpointT : Tendsto endpointT atTop atTop := by
  change Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_endpointV : Tendsto endpointV atTop atTop := by
  change Tendsto (fun X : ℕ => Real.log (endpointT X)) atTop atTop
  exact Real.tendsto_log_atTop.comp tendsto_endpointT

theorem tendsto_endpointV_div_endpointT :
    Tendsto (fun X : ℕ => endpointV X / endpointT X) atTop (𝓝 0) := by
  simpa only [Function.comp_def, id_eq, endpointV] using
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_endpointT

theorem eventually_endpointPrimeReal_ge_endpointT :
    ∀ᶠ X : ℕ in atTop, endpointT X ≤ endpointPrimeReal X := by
  filter_upwards [tendsto_endpointT.eventually (eventually_ge_atTop (0 : ℝ)),
    tendsto_endpointV.eventually (eventually_ge_atTop (1 : ℝ))] with X hT hV
  rw [endpointPrimeReal]
  exact le_mul_of_one_le_right hT (one_le_pow₀ hV)

theorem tendsto_endpointPrimeReal : Tendsto endpointPrimeReal atTop atTop :=
  Filter.tendsto_atTop_mono' atTop eventually_endpointPrimeReal_ge_endpointT tendsto_endpointT

theorem tendsto_endpointPrimeScale : Tendsto endpointPrimeScale atTop atTop := by
  change Tendsto (fun X : ℕ => Nat.ceil (endpointPrimeReal X)) atTop atTop
  exact tendsto_nat_ceil_atTop.comp tendsto_endpointPrimeReal

theorem endpointPrimeScale_bounds {X : ℕ} (hA : 0 ≤ endpointPrimeReal X) :
    endpointPrimeReal X ≤ (endpointPrimeScale X : ℝ) ∧
      (endpointPrimeScale X : ℝ) < endpointPrimeReal X + 1 := by
  exact ⟨Nat.le_ceil _, by simpa only [endpointPrimeScale] using Nat.ceil_lt_add_one hA⟩

theorem tendsto_endpointLogScale : Tendsto endpointLogScale atTop atTop := by
  change Tendsto (fun X : ℕ => Real.log (endpointPrimeScale X : ℝ)) atTop atTop
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp tendsto_endpointPrimeScale)

theorem tendsto_log_endpointPrimeReal_div_endpointV :
    Tendsto (fun X : ℕ => Real.log (endpointPrimeReal X) / endpointV X)
      atTop (𝓝 1) := by
  have hlogdiv : Tendsto
      (fun X : ℕ => Real.log (endpointV X) / endpointV X) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_endpointV
  have hmain : Tendsto
      (fun X : ℕ => 1 + 128*(Real.log (endpointV X)/endpointV X))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (hlogdiv.const_mul 128))
  apply hmain.congr'
  filter_upwards [tendsto_endpointT.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ))] with X hT hV
  rw [endpointPrimeReal, Real.log_mul hT.ne' (pow_ne_zero 128 hV.ne'), Real.log_pow]
  have hTV : Real.log (endpointT X) = endpointV X := by rfl
  rw [hTV]
  field_simp
  ring

theorem tendsto_endpointLogScale_div_endpointV :
    Tendsto (fun X : ℕ => endpointLogScale X / endpointV X) atTop (𝓝 1) := by
  have hlower := tendsto_log_endpointPrimeReal_div_endpointV
  have hinv : Tendsto (fun X : ℕ => (endpointV X)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_endpointV
  have hconst : Tendsto (fun X : ℕ => Real.log 2 / endpointV X) atTop (𝓝 0) := by
    have hc : Tendsto (fun _X : ℕ => Real.log 2) atTop (𝓝 (Real.log 2)) :=
      tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero] using hc.mul hinv
  have hupper : Tendsto (fun X : ℕ =>
      Real.log (endpointPrimeReal X) / endpointV X + Real.log 2 / endpointV X)
      atTop (𝓝 1) := by
    simpa using hlower.add hconst
  have hbounds : ∀ᶠ X : ℕ in atTop,
      Real.log (endpointPrimeReal X) / endpointV X ≤
        endpointLogScale X / endpointV X ∧
      endpointLogScale X / endpointV X ≤
        Real.log (endpointPrimeReal X) / endpointV X + Real.log 2 / endpointV X := by
    filter_upwards [tendsto_endpointPrimeReal.eventually (eventually_ge_atTop (1 : ℝ)),
      tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ))] with X hA hV
    have hA0 : 0 ≤ endpointPrimeReal X := hA.trans' zero_le_one
    obtain ⟨hceilLo, hceilHi⟩ := endpointPrimeScale_bounds hA0
    have hceilUpper : (endpointPrimeScale X : ℝ) ≤ 2*endpointPrimeReal X := by linarith
    have hPpos : (0 : ℝ) < endpointPrimeScale X :=
      zero_lt_one.trans_le (hA.trans hceilLo)
    have hlogLo : Real.log (endpointPrimeReal X) ≤
        Real.log (endpointPrimeScale X : ℝ) :=
      Real.log_le_log (zero_lt_one.trans_le hA) hceilLo
    have hlogHi : Real.log (endpointPrimeScale X : ℝ) ≤
        Real.log (2*endpointPrimeReal X) := Real.log_le_log hPpos hceilUpper
    have hlogMul : Real.log (2*endpointPrimeReal X) =
        Real.log 2 + Real.log (endpointPrimeReal X) :=
      Real.log_mul (by norm_num) (zero_lt_one.trans_le hA).ne'
    constructor
    · exact div_le_div_of_nonneg_right hlogLo hV.le
    · calc
        endpointLogScale X / endpointV X ≤
            Real.log (2*endpointPrimeReal X) / endpointV X := by
          exact div_le_div_of_nonneg_right (by simpa only [endpointLogScale] using hlogHi) hV.le
        _ = Real.log (endpointPrimeReal X) / endpointV X +
            Real.log 2 / endpointV X := by rw [hlogMul]; ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

theorem tendsto_endpointBandLog_div_endpointV :
    Tendsto (fun X : ℕ =>
      Real.log ((16*endpointPrimeScale X : ℕ) : ℝ) / endpointV X)
      atTop (𝓝 1) := by
  have hinv : Tendsto (fun X : ℕ => (endpointV X)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_endpointV
  have hc : Tendsto (fun X : ℕ => Real.log 16 / endpointV X) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _X : ℕ => Real.log 16) atTop (𝓝 (Real.log 16)) :=
      tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero] using hconst.mul hinv
  have hmain : Tendsto (fun X : ℕ =>
      endpointLogScale X / endpointV X + Real.log 16 / endpointV X)
      atTop (𝓝 1) := by
    simpa using tendsto_endpointLogScale_div_endpointV.add hc
  refine hmain.congr' ?_
  filter_upwards [tendsto_endpointPrimeScale.eventually (eventually_gt_atTop 0)] with X hP
  have hPr : (0 : ℝ) < endpointPrimeScale X := by exact_mod_cast hP
  rw [show (((16*endpointPrimeScale X : ℕ) : ℝ)) =
    (16 : ℝ)*(endpointPrimeScale X : ℝ) by norm_num, Real.log_mul (by norm_num) hPr.ne']
  simp only [endpointLogScale]
  ring

theorem eventually_endpointLogScale_between_half_two :
    ∀ᶠ X : ℕ in atTop,
      endpointV X/2 ≤ endpointLogScale X ∧ endpointLogScale X ≤ 2*endpointV X := by
  have hlo : ∀ᶠ X : ℕ in atTop,
      (1/2 : ℝ) < endpointLogScale X / endpointV X :=
    (tendsto_order.1 tendsto_endpointLogScale_div_endpointV).1 _ (by norm_num)
  have hhi : ∀ᶠ X : ℕ in atTop,
      endpointLogScale X / endpointV X < 2 :=
    (tendsto_order.1 tendsto_endpointLogScale_div_endpointV).2 _ (by norm_num)
  filter_upwards [hlo, hhi,
    tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ))] with X hlo hhi hV
  have hlo' := (lt_div_iff₀ hV).mp hlo
  have hhi' := (div_lt_iff₀ hV).mp hhi
  constructor <;> nlinarith

theorem eventually_endpointT_in_frequencyWindow :
    ∀ᶠ X : ℕ in atTop,
      (endpointPrimeScale X : ℝ)/endpointLogScale X^130 ≤ endpointT X ∧
      endpointT X ≤ (endpointPrimeScale X : ℝ)/endpointLogScale X^126 := by
  filter_upwards [tendsto_endpointT.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_endpointV.eventually (eventually_ge_atTop ((2 : ℝ)^66)),
    eventually_endpointLogScale_between_half_two] with X hT hV hLbounds
  let v := endpointV X
  let L := endpointLogScale X
  have hv0 : 0 < v := by dsimp [v]; positivity
  have hL0 : 0 < L := by dsimp [L]; nlinarith [hLbounds.1]
  have hvv : (2 : ℝ)^132 ≤ v^2 := by
    have hm := mul_le_mul hV hV (by positivity : (0 : ℝ) ≤ (2 : ℝ)^66)
      (by positivity : 0 ≤ endpointV X)
    calc
      (2 : ℝ)^132 = (2 : ℝ)^66*(2 : ℝ)^66 := by ring
      _ ≤ endpointV X*endpointV X := hm
      _ = v^2 := by simp only [v]; ring
  have hA0 : 0 ≤ endpointPrimeReal X := by
    rw [endpointPrimeReal]
    positivity
  obtain ⟨hPlo, hPhi⟩ := endpointPrimeScale_bounds hA0
  have hAone : 1 ≤ endpointPrimeReal X := by
    rw [endpointPrimeReal]
    have hvpow : 1 ≤ endpointV X^128 := one_le_pow₀ (le_trans (by norm_num) hV)
    nlinarith [mul_le_mul hT hvpow (by norm_num : (0 : ℝ) ≤ 1)
      (zero_le_one.trans hT)]
  have hPupper : (endpointPrimeScale X : ℝ) ≤
      2*endpointT X*v^128 := by
    calc
      (endpointPrimeScale X : ℝ) ≤ 2*endpointPrimeReal X := by linarith
      _ = 2*endpointT X*v^128 := by simp only [endpointPrimeReal, v]; ring
  have h2lo : (2 : ℝ)^131 ≤ v^2 :=
    (show (2 : ℝ)^131 ≤ (2 : ℝ)^132 by norm_num).trans hvv
  have hcoefLower : 2*v^128 ≤ (v/2)^130 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos (by norm_num) 130)).2
    calc
      (2*v^128)*2^130 = v^128*(2 : ℝ)^131 := by ring
      _ ≤ v^128*v^2 := mul_le_mul_of_nonneg_left h2lo (pow_nonneg hv0.le 128)
      _ = v^130 := by ring
  have hpowLower : 2*v^128 ≤ L^130 := by
    exact hcoefLower.trans (pow_le_pow_left₀ (by positivity) (by simpa only [v, L] using hLbounds.1) 130)
  have hfrequencyLower : (endpointPrimeScale X : ℝ)/L^130 ≤ endpointT X := by
    apply (div_le_iff₀ (pow_pos hL0 130)).2
    calc
      (endpointPrimeScale X : ℝ) ≤ 2*endpointT X*v^128 := hPupper
      _ = endpointT X*(2*v^128) := by ring
      _ ≤ endpointT X*L^130 := mul_le_mul_of_nonneg_left hpowLower (zero_le_one.trans hT)
  have h2hi : (2 : ℝ)^126 ≤ v^2 :=
    (show (2 : ℝ)^126 ≤ (2 : ℝ)^132 by norm_num).trans hvv
  have hcoefUpper : (2*v)^126 ≤ v^128 := by
    rw [mul_pow]
    calc
      (2 : ℝ)^126*v^126 ≤ v^2*v^126 :=
        mul_le_mul_of_nonneg_right h2hi (pow_nonneg hv0.le 126)
      _ = v^128 := by ring
  have hpowUpper : L^126 ≤ v^128 := by
    exact (pow_le_pow_left₀ hL0.le (by simpa only [v, L] using hLbounds.2) 126).trans
      hcoefUpper
  have hfrequencyUpper : endpointT X ≤ (endpointPrimeScale X : ℝ)/L^126 := by
    apply (le_div_iff₀ (pow_pos hL0 126)).2
    calc
      endpointT X*L^126 ≤ endpointT X*v^128 :=
        mul_le_mul_of_nonneg_left hpowUpper (zero_le_one.trans hT)
      _ = endpointPrimeReal X := by rw [endpointPrimeReal]
      _ ≤ (endpointPrimeScale X : ℝ) := hPlo
  simpa only [L] using And.intro hfrequencyLower hfrequencyUpper

theorem eventually_endpointSelectedCount_le_primeCapacity
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ X : ℕ in atTop,
      (endpointSelectedCount δ X : ℝ) ≤
        (endpointPrimeScale X : ℝ) / (2 * endpointLogScale X ^ 7) := by
  filter_upwards [tendsto_endpointT.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_endpointV.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_endpointLogScale_between_half_two,
    tendsto_endpointPrimeScale.eventually (eventually_gt_atTop 0)] with
      X hT hV hLbounds hPnat
  let v := endpointV X
  let L := endpointLogScale X
  let B := Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)
  have hv0 : 0 < v := by dsimp [v]; linarith
  have hL0 : 0 < L := by dsimp [L]; nlinarith [hLbounds.1]
  have hPr : (0 : ℝ) < endpointPrimeScale X := by exact_mod_cast hPnat
  have hBformula : B = Real.log 16 + L := by
    dsimp only [B, L, endpointLogScale]
    rw [Nat.cast_mul, Nat.cast_ofNat]
    exact Real.log_mul (by norm_num) hPr.ne'
  have hLB : L ≤ B := by
    rw [hBformula]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 16)]
  have hvB : v / 2 ≤ B := hLbounds.1.trans hLB
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity : 0 < v / 2) hvB
  have hnum0 : 0 ≤ (1 - δ) * endpointT X :=
    mul_nonneg (sub_nonneg.mpr hδ1) (zero_le_one.trans hT)
  have hnum_le : (1 - δ) * endpointT X ≤ endpointT X := by
    have := mul_le_mul_of_nonneg_right (by linarith : 1 - δ ≤ 1)
      (zero_le_one.trans hT)
    simpa using this
  have hraw0 : 0 ≤ (1 - δ) * endpointT X / B := div_nonneg hnum0 hB0.le
  have hfloor : (endpointSelectedCount δ X : ℝ) ≤
      (1 - δ) * endpointT X / B := by
    simpa only [endpointSelectedCount, B] using Nat.floor_le hraw0
  have hraw_le : (1 - δ) * endpointT X / B ≤ 2 * endpointT X / v := by
    calc
      (1 - δ) * endpointT X / B ≤ endpointT X / B :=
        div_le_div_of_nonneg_right hnum_le hB0.le
      _ ≤ endpointT X / (v / 2) :=
        div_le_div_of_nonneg_left (zero_le_one.trans hT) (by positivity) hvB
      _ = 2 * endpointT X / v := by field_simp
  have hv122 : (512 : ℝ) ≤ v ^ 122 := by
    calc
      (512 : ℝ) ≤ (2 : ℝ) ^ 122 := by norm_num
      _ ≤ v ^ 122 := pow_le_pow_left₀ (by norm_num) (by simpa only [v] using hV) 122
  have hwideDen0 : 0 < 2 * (2 * v) ^ 7 := by positivity
  have hcompare : 2 * endpointT X / v ≤
      endpointT X * v ^ 128 / (2 * (2 * v) ^ 7) := by
    apply (div_le_div_iff₀ hv0 hwideDen0).2
    have hm := mul_le_mul_of_nonneg_left hv122
      (mul_nonneg (zero_le_one.trans hT) (pow_nonneg hv0.le 7))
    calc
      (2 * endpointT X) * (2 * (2 * v) ^ 7) =
          (endpointT X * v ^ 7) * 512 := by ring
      _ ≤ (endpointT X * v ^ 7) * v ^ 122 := hm
      _ = (endpointT X * v ^ 128) * v := by ring
  have hA0 : 0 ≤ endpointPrimeReal X := by
    rw [endpointPrimeReal]
    positivity
  have hPlo : endpointT X * v ^ 128 ≤ (endpointPrimeScale X : ℝ) := by
    have := (endpointPrimeScale_bounds hA0).1
    simpa only [endpointPrimeReal, v] using this
  have hLpow : L ^ 7 ≤ (2 * v) ^ 7 :=
    pow_le_pow_left₀ hL0.le (by simpa only [L, v] using hLbounds.2) 7
  have hnarrowDen0 : 0 < 2 * L ^ 7 := by positivity
  have hden : 2 * L ^ 7 ≤ 2 * (2 * v) ^ 7 :=
    mul_le_mul_of_nonneg_left hLpow (by norm_num)
  have hcapacityLower : endpointT X * v ^ 128 / (2 * (2 * v) ^ 7) ≤
      (endpointPrimeScale X : ℝ) / (2 * L ^ 7) := by
    apply (div_le_div_iff₀ hwideDen0 hnarrowDen0).2
    calc
      (endpointT X * v ^ 128) * (2 * L ^ 7) ≤
          (endpointPrimeScale X : ℝ) * (2 * L ^ 7) :=
        mul_le_mul_of_nonneg_right hPlo hnarrowDen0.le
      _ ≤ (endpointPrimeScale X : ℝ) * (2 * (2 * v) ^ 7) :=
        mul_le_mul_of_nonneg_left hden hPr.le
  simpa only [L] using hfloor.trans (hraw_le.trans (hcompare.trans hcapacityLower))

theorem eventually_endpoint_additiveBudget
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ X : ℕ in atTop,
      Real.exp (endpointT X - 1 / endpointLogScale X) +
          ((((16 * endpointPrimeScale X) ^ endpointSelectedCount δ X : ℕ) : ℝ)) ≤
        (X : ℝ) := by
  have hsmall : ∀ᶠ X : ℕ in atTop,
      endpointV X / endpointT X < δ / 4 :=
    (tendsto_order.1 tendsto_endpointV_div_endpointT).2 _ (by linarith)
  filter_upwards [hsmall,
    tendsto_endpointT.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_endpointLogScale.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_endpointLogScale_between_half_two,
    tendsto_endpointPrimeScale.eventually (eventually_gt_atTop 0),
    eventually_gt_atTop (0 : ℕ)] with X hsmallX hT hV hLone hLbounds hPnat hXnat
  let T := endpointT X
  let v := endpointV X
  let L := endpointLogScale X
  let B := Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)
  let a := 1 / L
  have hT0 : 0 < T := by simpa only [T] using hT
  have hv0 : 0 < v := by simpa only [v] using hV
  have hL0 : 0 < L := by dsimp [L]; linarith
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (div_le_one hL0).2 hLone
  have hPr : (0 : ℝ) < endpointPrimeScale X := by exact_mod_cast hPnat
  have hQnat : 0 < 16 * endpointPrimeScale X := Nat.mul_pos (by norm_num) hPnat
  have hQr : (0 : ℝ) < ((16 * endpointPrimeScale X : ℕ) : ℝ) := by
    exact_mod_cast hQnat
  have hB0 : 0 < B := by
    dsimp only [B]
    exact Real.log_pos (by exact_mod_cast (show 1 < 16 * endpointPrimeScale X by omega))
  have hfourv : 4 * v ≤ δ * T := by
    have hratio : v / T < δ / 4 := by simpa only [v, T] using hsmallX
    have hmul := (div_lt_iff₀ hT0).mp hratio
    nlinarith
  have htwoL : 2 * L ≤ Real.exp (δ * T) := by
    calc
      2 * L ≤ 4 * v := by
        have := mul_le_mul_of_nonneg_left
          (by simpa only [L, v] using hLbounds.2) (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith
      _ ≤ δ * T := hfourv
      _ ≤ δ * T + 1 := by linarith
      _ ≤ Real.exp (δ * T) := Real.add_one_le_exp _
  have htwoLpos : 0 < 2 * L := by positivity
  have hexpNegDelta : Real.exp (-δ * T) ≤ a / 2 := by
    have hinv := one_div_le_one_div_of_le htwoLpos htwoL
    calc
      Real.exp (-δ * T) = 1 / Real.exp (δ * T) := by
        rw [show -δ * T = -(δ * T) by ring, Real.exp_neg]
        simp only [one_div]
      _ ≤ 1 / (2 * L) := hinv
      _ = a / 2 := by dsimp only [a]; field_simp
  have hexpNegA : Real.exp (-a) ≤ 1 - a / 2 := by
    have hdenExp : 1 + a ≤ Real.exp a := by
      simpa only [add_comm] using Real.add_one_le_exp a
    have hrecip : Real.exp (-a) ≤ 1 / (1 + a) := by
      rw [Real.exp_neg]
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hdenExp
    have hrational : 1 / (1 + a) ≤ 1 - a / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 1 + a)).2
      have hprod : 0 ≤ a * (1 - a) := mul_nonneg ha0.le (sub_nonneg.mpr ha1)
      nlinarith
    exact hrecip.trans hrational
  have hmain : Real.exp (T - a) ≤ Real.exp T * (1 - a / 2) := by
    rw [show T - a = T + (-a) by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_left hexpNegA (Real.exp_pos T).le
  have hraw0 : 0 ≤ (1 - δ) * T / B :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hδ1) hT0.le) hB0.le
  have hfloor : (endpointSelectedCount δ X : ℝ) ≤ (1 - δ) * T / B := by
    simpa only [endpointSelectedCount, T, B] using Nat.floor_le hraw0
  have hexponent : B * (endpointSelectedCount δ X : ℝ) ≤ (1 - δ) * T := by
    have := mul_le_mul_of_nonneg_left hfloor hB0.le
    field_simp at this
    exact this
  have hproduct :
      ((((16 * endpointPrimeScale X) ^ endpointSelectedCount δ X : ℕ) : ℝ)) ≤
        Real.exp ((1 - δ) * T) := by
    calc
      ((((16 * endpointPrimeScale X) ^ endpointSelectedCount δ X : ℕ) : ℝ)) =
          ((16 * endpointPrimeScale X : ℕ) : ℝ) ^ endpointSelectedCount δ X := by
            norm_num
      _ = Real.exp ((endpointSelectedCount δ X : ℝ) * B) := by
        symm
        rw [Real.exp_nat_mul]
        dsimp only [B]
        rw [Real.exp_log hQr]
      _ = Real.exp (B * (endpointSelectedCount δ X : ℝ)) := by
        congr 1
        exact mul_comm _ _
      _ ≤ Real.exp ((1 - δ) * T) := Real.exp_le_exp.mpr hexponent
  have hsecondary : Real.exp ((1 - δ) * T) ≤ Real.exp T * (a / 2) := by
    calc
      Real.exp ((1 - δ) * T) = Real.exp T * Real.exp (-δ * T) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp T * (a / 2) :=
        mul_le_mul_of_nonneg_left hexpNegDelta (Real.exp_pos T).le
  have hsum : Real.exp (T - a) +
      ((((16 * endpointPrimeScale X) ^ endpointSelectedCount δ X : ℕ) : ℝ)) ≤
      Real.exp T := by
    calc
      Real.exp (T - a) +
          ((((16 * endpointPrimeScale X) ^ endpointSelectedCount δ X : ℕ) : ℝ)) ≤
          Real.exp T * (1 - a / 2) + Real.exp ((1 - δ) * T) :=
        add_le_add hmain hproduct
      _ ≤ Real.exp T * (1 - a / 2) + Real.exp T * (a / 2) :=
        add_le_add_right hsecondary _
      _ = Real.exp T := by ring
  have hexpT : Real.exp T = (X : ℝ) := by
    dsimp only [T, endpointT]
    exact Real.exp_log (by exact_mod_cast hXnat)
  simpa only [T, L, a, hexpT] using hsum

theorem tendsto_endpointV_div_endpointBandLog :
    Tendsto (fun X : ℕ => endpointV X /
      Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) atTop (𝓝 1) := by
  have hinv := tendsto_endpointBandLog_div_endpointV.inv₀
    (by norm_num : (1 : ℝ) ≠ 0)
  have hinv' : Tendsto (fun X : ℕ =>
      (Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ) / endpointV X)⁻¹)
      atTop (𝓝 1) := by simpa using hinv
  apply hinv'.congr'
  filter_upwards [tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_endpointPrimeScale.eventually (eventually_gt_atTop 0)] with X hV hP
  have hQ : (0 : ℝ) < ((16 * endpointPrimeScale X : ℕ) : ℝ) := by positivity
  have hlogQ : 0 < Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 16 * endpointPrimeScale X by omega)
  field_simp

theorem tendsto_endpointSelectedCount_normalized
    {δ : ℝ} (hδ1 : δ ≤ 1) :
    Tendsto (fun X : ℕ =>
      (endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X)
      atTop (𝓝 (1 - δ)) := by
  have hupper : Tendsto (fun X : ℕ =>
      (1 - δ) * (endpointV X /
        Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)))
      atTop (𝓝 (1 - δ)) := by
    simpa using tendsto_const_nhds.mul tendsto_endpointV_div_endpointBandLog
  have hlower : Tendsto (fun X : ℕ =>
      (1 - δ) * (endpointV X /
        Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) -
        endpointV X / endpointT X)
      atTop (𝓝 (1 - δ)) := by
    simpa using hupper.sub tendsto_endpointV_div_endpointT
  have hbounds : ∀ᶠ X : ℕ in atTop,
      (1 - δ) * (endpointV X /
          Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) -
          endpointV X / endpointT X ≤
        (endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X ∧
      (endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X ≤
        (1 - δ) * (endpointV X /
          Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) := by
    filter_upwards [tendsto_endpointT.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_endpointPrimeScale.eventually (eventually_gt_atTop 0)] with X hT hV hPnat
    let T := endpointT X
    let v := endpointV X
    let B := Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)
    have hT0 : 0 < T := by simpa only [T] using hT
    have hv0 : 0 < v := by simpa only [v] using hV
    have hB0 : 0 < B := by
      dsimp only [B]
      apply Real.log_pos
      exact_mod_cast (show 1 < 16 * endpointPrimeScale X by omega)
    have hraw0 : 0 ≤ (1 - δ) * T / B :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hδ1) hT0.le) hB0.le
    have hfloorUpper : (endpointSelectedCount δ X : ℝ) ≤ (1 - δ) * T / B := by
      simpa only [endpointSelectedCount, T, B] using Nat.floor_le hraw0
    have hfloorLower : (1 - δ) * T / B - 1 ≤
        (endpointSelectedCount δ X : ℝ) := by
      have hlt := Nat.lt_floor_add_one ((1 - δ) * T / B)
      have hlt' : (1 - δ) * T / B <
          (endpointSelectedCount δ X : ℝ) + 1 := by
        simpa only [endpointSelectedCount, T, B] using hlt
      linarith
    have hfactor0 : 0 ≤ v / T := div_nonneg hv0.le hT0.le
    have hlo := mul_le_mul_of_nonneg_right hfloorLower hfactor0
    have hhi := mul_le_mul_of_nonneg_right hfloorUpper hfactor0
    constructor
    · calc
        (1 - δ) * (endpointV X /
            Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) -
            endpointV X / endpointT X =
            ((1 - δ) * T / B - 1) * (v / T) := by
              simp only [T, v, B]
              field_simp
        _ ≤ (endpointSelectedCount δ X : ℝ) * (v / T) := hlo
        _ = (endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X := by
          simp only [T, v]
          ring
    · calc
        (endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X =
            (endpointSelectedCount δ X : ℝ) * (v / T) := by
          simp only [T, v]
          ring
        _ ≤ ((1 - δ) * T / B) * (v / T) := hhi
        _ = (1 - δ) * (endpointV X /
            Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) := by
          simp only [T, v, B]
          field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

theorem tendsto_endpointExpShift :
    Tendsto (fun X : ℕ => Real.exp (-4 / endpointLogScale X))
      atTop (𝓝 1) := by
  have hinv : Tendsto (fun X : ℕ => (endpointLogScale X)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_endpointLogScale
  have harg : Tendsto (fun X : ℕ => -4 / endpointLogScale X) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (-4)
  simpa only [Function.comp_def, Real.exp_zero] using
    Real.continuous_exp.continuousAt.tendsto.comp harg

theorem tendsto_endpointNormalizedWeight
    {δ : ℝ} (hδ1 : δ ≤ 1) :
    Tendsto (fun X : ℕ =>
      (endpointSelectedCount δ X : ℝ) *
          Real.exp (endpointT X - 4 / endpointLogScale X) /
        Local878.maximalOrderScale X)
      atTop (𝓝 (1 - δ)) := by
  have hprod := (tendsto_endpointSelectedCount_normalized hδ1).mul
    tendsto_endpointExpShift
  have hprod' : Tendsto (fun X : ℕ =>
      ((endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X) *
        Real.exp (-4 / endpointLogScale X)) atTop (𝓝 (1 - δ)) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    tendsto_endpointT.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ))] with X hX hT hV
  let T := endpointT X
  let v := endpointV X
  let L := endpointLogScale X
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hT0 : 0 < T := by simpa only [T] using hT
  have hv0 : 0 < v := by simpa only [v] using hV
  have hexpT : Real.exp T = (X : ℝ) := by
    dsimp only [T, endpointT]
    exact Real.exp_log hXr
  have hshift : Real.exp (T - 4 / L) =
      (X : ℝ) * Real.exp (-4 / L) := by
    rw [show T - 4 / L = T + (-4 / L) by ring, Real.exp_add, hexpT]
  have hscale : Local878.maximalOrderScale X = (X : ℝ) * T / v := by
    rfl
  rw [hshift, hscale]
  field_simp
  ring

theorem eventually_endpointNormalizedWeight_ge_one_sub
    {δ ε : ℝ} (hδ1 : δ ≤ 1) (hδε : δ < ε) :
    ∀ᶠ X : ℕ in atTop,
      1 - ε ≤
        (endpointSelectedCount δ X : ℝ) *
            Real.exp (endpointT X - 4 / endpointLogScale X) /
          Local878.maximalOrderScale X := by
  have hstrict : 1 - ε < 1 - δ := by linarith
  exact ((tendsto_order.1 (tendsto_endpointNormalizedWeight hδ1)).1 _ hstrict).mono
    (fun _ h => h.le)

theorem eventually_endpointConditions_concrete
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδε : δ < ε) :
    ∀ᶠ X : ℕ in atTop,
      endpointConditions ε X (endpointPrimeScale X)
        (endpointSelectedCount δ X) (endpointT X) := by
  filter_upwards [tendsto_endpointT.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_endpointT_in_frequencyWindow,
    eventually_endpointSelectedCount_le_primeCapacity hδ0.le hδ1,
    eventually_endpoint_additiveBudget hδ0 hδ1,
    Local878.eventually_maximalOrderScale_pos,
    eventually_endpointNormalizedWeight_ge_one_sub hδ1 hδε] with
      X hT hfrequency hcapacity hbudget hscale hnormalized
  exact ⟨hT, hfrequency.1, hfrequency.2, hcapacity, hbudget, hscale, hnormalized⟩

theorem second_question_of_concreteEndpoints : proof_targets.parts_ii := by
  apply second_question_of_endpointParameters
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ0 : 0 < δ := by
    dsimp only [δ]
    exact lt_min (half_pos hε) (by norm_num)
  have hδ1 : δ ≤ 1 := by
    exact (min_le_right (ε / 2) (1 / 2)).trans (by norm_num)
  have hδε : δ < ε := by
    exact (min_le_left (ε / 2) (1 / 2)).trans_lt (half_lt_self hε)
  exact ⟨endpointPrimeScale, endpointSelectedCount δ, endpointT,
    tendsto_endpointPrimeScale,
    eventually_endpointConditions_concrete hδ0 hδ1 hδε⟩

theorem erdos_878_parts_ii_proved : proof_targets.parts_ii := by
  exact second_question_of_concreteEndpoints

end

end Local878.TrackB

end

open Filter in
theorem OMA.solution : type_of% @Erdos878.erdos_878.variants.second_question_subsequence := by
  exact ⟨id, tendsto_id, Local878.TrackB.erdos_878_parts_ii_proved⟩
