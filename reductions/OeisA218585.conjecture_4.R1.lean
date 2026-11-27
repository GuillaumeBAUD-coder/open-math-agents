import FormalConjectures.OEIS.«218585»
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Second moments of Eisenstein prime coordinates

Recover the Cartesian projections from the norm and angle of a split prime.
Their sector averages give normalized second moments of 2/3 and 2/3 − √3/π.
-/

namespace OMA.R_OeisA218585_conjecture_4_R1

open OeisA218585 Real Filter MeasureTheory
open scoped BigOperators Topology

/-- The two searches in the upstream definitions recover the coordinates of
the same Eisenstein integer of norm p. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 3 = 1 → xp p ^ 2 + xp p * yp p + yp p ^ 2 = p

/-- The norm-weighted angular form of Hecke equidistribution for split primes,
in the fundamental sector from zero to π/6. -/
def H2 : Prop :=
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  let primes (N : ℕ) := (Finset.range N).filter fun p => p.Prime ∧ p % 3 = 1
  ∀ f : ℝ → ℝ, Continuous f →
    Tendsto (fun N => (∑ p ∈ primes N, (p : ℝ) * f (z p).arg) / ∑ p ∈ primes N, (p : ℝ))
      atTop (𝓝 ((6 / π) * ∫ t in 0..π / 6, f t))

lemma projection_integral (a b : ℝ) :
    (∫ t in 0..π / 6, (a * cos t + b * sin t) ^ 2) =
      a ^ 2 * (√3 / 4 + π / 6) / 2 + (2 * a * b) / 8 +
      b ^ 2 * (π / 6 - √3 / 4) / 2 := by
  have split (t : ℝ) : (a * cos t + b * sin t) ^ 2 =
      (a ^ 2 * cos t ^ 2 + (2 * a * b) * (sin t * cos t)) + b ^ 2 * sin t ^ 2 := by ring
  simp_rw [split]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const_mul, integral_cos_sq, integral_sin_sq,
      integral_sin_mul_cos₁, sin_zero, cos_zero, sin_pi_div_six, cos_pi_div_six]
    ring
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

lemma coordinate_moments (x y p : ℝ) (hp : x ^ 2 + x * y + y ^ 2 = p) :
    let z : ℂ := ⟨x + y / 2, √3 * y / 2⟩
    p * (1 * cos z.arg + (-(√3) / 3) * sin z.arg) ^ 2 = x ^ 2 ∧
    p * (0 * cos z.arg + (2 * √3 / 3) * sin z.arg) ^ 2 = y ^ 2 := by
  let z : ℂ := ⟨x + y / 2, √3 * y / 2⟩
  have hs : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : ‖z‖ ^ 2 = p := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [z]
    linear_combination hp + (y ^ 2 / 4) * hs
  have hc : ‖z‖ * cos z.arg = x + y / 2 := Complex.norm_mul_cos_arg z
  have hi : ‖z‖ * sin z.arg = √3 * y / 2 := Complex.norm_mul_sin_arg z
  have proj (a b : ℝ) : p * (a * cos z.arg + b * sin z.arg) ^ 2 =
      (a * (x + y / 2) + b * (√3 * y / 2)) ^ 2 := by
    rw [← hn, ← mul_pow, ← hc, ← hi]
    ring
  constructor
  · rw [show _ = _ from proj 1 (-(√3) / 3)]
    congr 1
    linear_combination -(y / 6) * hs
  · rw [show _ = _ from proj 0 (2 * √3 / 3)]
    congr 1
    linear_combination (y / 3) * hs

theorem main : H1 → H2 → type_of% @OeisA218585.conjecture_4 := by
  intro hnorm hequid hclaimed
  let primes (N : ℕ) := (Finset.range N).filter fun p => p.Prime ∧ p % 3 = 1
  let mass (N : ℕ) := ∑ p ∈ primes N, (p : ℝ)
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  let X (N : ℕ) := ∑ p ∈ primes N, (xp p : ℝ) ^ 2
  let Y (N : ℕ) := ∑ p ∈ primes N, (yp p : ℝ) ^ 2
  let moment (a b : ℝ) (t : ℝ) := (a * cos t + b * sin t) ^ 2
  have moments (p : ℕ) (hp : p.Prime ∧ p % 3 = 1) :
      (p : ℝ) * moment 1 (-(√3) / 3) (z p).arg = (xp p : ℝ) ^ 2 ∧
      (p : ℝ) * moment 0 (2 * √3 / 3) (z p).arg = (yp p : ℝ) ^ 2 := by
    apply coordinate_moments
    exact_mod_cast hnorm p hp.1 hp.2
  have limits (a b : ℝ) :
      Tendsto (fun N => (∑ p ∈ primes N, (p : ℝ) * moment a b (z p).arg) / mass N)
        atTop (𝓝 ((6 / π) * (a ^ 2 * (√3 / 4 + π / 6) / 2 + (2 * a * b) / 8 +
                              b ^ 2 * (π / 6 - √3 / 4) / 2))) := by
    rw [← projection_integral]
    exact hequid (moment a b) (by dsimp [moment]; fun_prop)
  have hs : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hx := limits 1 (-(√3) / 3)
  have hy := limits 0 (2 * √3 / 3)
  have sx (N : ℕ) : (∑ p ∈ primes N, (p : ℝ) * moment 1 (-(√3) / 3) (z p).arg) = X N :=
    Finset.sum_congr rfl fun p hp => (moments p (Finset.mem_filter.mp hp).2).1
  have sy (N : ℕ) : (∑ p ∈ primes N, (p : ℝ) * moment 0 (2 * √3 / 3) (z p).arg) = Y N :=
    Finset.sum_congr rfl fun p hp => (moments p (Finset.mem_filter.mp hp).2).2
  simp_rw [sx] at hx
  simp_rw [sy] at hy
  have pi0 := Real.pi_ne_zero
  have vx : (6 / π) * (1 ^ 2 * (√3 / 4 + π / 6) / 2 + (2 * 1 * (-(√3) / 3)) / 8 +
      (-(√3) / 3) ^ 2 * (π / 6 - √3 / 4) / 2) = 2 / 3 := by
    rw [div_pow, neg_sq, hs]
    field_simp
    ring
  have vy : (6 / π) * (0 ^ 2 * (√3 / 4 + π / 6) / 2 + (2 * 0 * (2 * √3 / 3)) / 8 +
      (2 * √3 / 3) ^ 2 * (π / 6 - √3 / 4) / 2) = 2 / 3 - √3 / π := by
    rw [div_pow, mul_pow, hs]
    field_simp
    ring
  rw [vx] at hx
  rw [vy] at hy
  have sqrt_upper : √(3 : ℝ) < 2 := by nlinarith
  have denom_pos : 0 < 2 / 3 - √3 / π := by
    rw [sub_pos, div_lt_iff₀ Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hm : ∀ᶠ N in atTop, mass N ≠ 0 := by
    filter_upwards [eventually_ge_atTop 8] with N hN
    have h7 : 7 ∈ primes N := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by decide⟩
    have hle := Finset.single_le_sum (f := fun p : ℕ => (p : ℝ))
      (fun p _ => Nat.cast_nonneg p) h7
    change (∑ p ∈ primes N, (p : ℝ)) ≠ 0
    norm_num at hle
    linarith
  have actual : Tendsto (fun N => X N / Y N) atTop (𝓝 ((2 / 3) / (2 / 3 - √3 / π))) := by
    apply (hx.div hy denom_pos.ne').congr'
    filter_upwards [hm] with N hN
    exact div_div_div_cancel_right₀ hN _ _
  have heq := tendsto_nhds_unique actual hclaimed
  have impossible := (div_eq_iff denom_pos.ne').mp heq
  have sqrt_lower : (1.732 : ℝ) < √3 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  field_simp at impossible
  linarith [Real.pi_lt_d4]

end OMA.R_OeisA218585_conjecture_4_R1
