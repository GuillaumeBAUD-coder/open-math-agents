import OMAStatements.S_oeis_a211163

/-!
# Alcover’s logarithmic moment conjecture (OEIS A211163)

Source: https://oeis.org/A211163
Credit: @bmendonca3

The beta integral evaluates the generating function, dominated convergence identifies
its Taylor coefficients, and the von Staudt–Clausen theorem determines the denominator.
-/

namespace OMA.A211163Steps

open OMA.S_oeis_a211163

/-- The principal logarithm has a constant imaginary part along the integration interval. -/
theorem branch_identity {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Complex.log (1 - 1 / (x : ℂ)) =
      (Real.log ((1 - x) / x) : ℂ) + Real.pi * Complex.I := by
  have hr : 0 < (1 - x) / x := div_pos (sub_pos.mpr hx.2) hx.1
  have h : 1 - 1 / (x : ℂ) = (((1 - x) / x : ℝ) : ℂ) * (-1) := by
    push_cast
    field_simp [show (x : ℂ) ≠ 0 by exact_mod_cast hx.1.ne']
    ring
  rw [h, Complex.log_ofReal_mul hr (by norm_num), Complex.log_neg_one]

/-- This rewrite applies to every moment, including those where the endpoints are singular. -/
theorem integral_branch (n : ℕ) :
    (∫ x in (0 : ℝ)..1, Complex.log (1 - 1 / (x : ℂ)) ^ n) =
      ∫ x in (0 : ℝ)..1, ((Real.log ((1 - x) / x) : ℂ) + Real.pi * Complex.I) ^ n := by
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  exact congrArg (· ^ n) (branch_identity hx)

/-- No odd prime minus one can divide an odd exponent. -/
theorem denominator_odd {n : ℕ} (hn : Odd n) : A141459 n = 1 := by
  unfold A141459
  have h : (Finset.range (n + 2)).filter (fun p => Nat.Prime p ∧ Odd p ∧ (p - 1) ∣ n) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨_, _, ⟨k, hk⟩, hd⟩ := Finset.mem_filter.mp hp
    have he : 2 ∣ p - 1 := ⟨k, by omega⟩
    have hd' := he.trans hd
    obtain ⟨j, hj⟩ := hn
    omega
  simp [h]

/-- For odd exponents greater than one, the predicted Bernoulli expression has the required denominator. -/
theorem odd_bernoulli_denominator {n : ℕ} (hn : Odd n) (h : 1 < n) :
    ((2 : ℚ) ^ n * |bernoulli n|).den = A141459 n := by
  simp [bernoulli_eq_zero_of_odd hn h, denominator_odd hn]


private theorem den_add_coprime (a b : ℚ) (h : a.den.Coprime b.den) :
    (a+b).den = a.den * b.den := by
  apply Nat.dvd_antisymm (Rat.add_den_dvd _ _)
  apply h.mul_dvd_of_dvd_of_dvd
  · exact h.dvd_of_dvd_mul_right (by simpa using Rat.add_den_dvd (a+b) (-b))
  · exact h.symm.dvd_of_dvd_mul_right (by simpa [add_comm a b] using Rat.add_den_dvd (b+a) (-a))

private theorem reciprocal_prime_sum_den (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    (∑ p ∈ s, (1:ℚ) / p).den = ∏ p ∈ s, p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hprime := hs p (Finset.mem_insert_self _ _)
    have hs' : ∀ q ∈ s, Nat.Prime q := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hden : ((1:ℚ) / p).den = p := by simp [one_div, hprime.ne_zero]
    rw [Finset.sum_insert hp, Finset.prod_insert hp, den_add_coprime, hden, ih hs']
    rw [hden, ih hs']
    apply Nat.Coprime.prod_right
    intro q hq
    exact (Nat.coprime_primes hprime (hs' q hq)).mpr (fun he => hp (he ▸ hq))

/-- Exact reduced denominator of the even Bernoulli number before normalization by 2^n. -/
theorem even_bernoulli_denominator (k : ℕ) :
    (bernoulli (2*k)).den =
      ∏ p ∈ (Finset.range (2*k+2)).filter (fun p => Nat.Prime p ∧ (p-1) ∣ 2*k), p := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  let s := (Finset.range (2*k+2)).filter (fun p => Nat.Prime p ∧ (p-1) ∣ 2*k)
  have he : bernoulli (2*k) = (z : ℚ) - ∑ p ∈ s, (1:ℚ) / p := by
    apply eq_sub_iff_add_eq.mpr
    exact hz.symm
  rw [he, Rat.intCast_sub_den]
  exact reciprocal_prime_sum_den s (fun p hp => (Finset.mem_filter.mp hp).2.1)

private theorem cancel_two_pow (q : ℚ) (D m : ℕ) (hd : q.den = 2 * D)
    (ho : Odd D) : ((2 : ℚ) ^ (m+1) * q).den = D := by
  have hn : q.num.natAbs.Coprime D := q.reduced.of_dvd_right (hd ▸ Nat.dvd_mul_left D 2)
  have hc := (ho.coprime_two_left.pow_left m).mul_left hn
  have hcast : (2 : ℚ)^(m+1) = ((2^(m+1) : ℕ) : ℚ) := by norm_cast
  rw [hcast, Rat.mul_den, Int.natAbs_mul]
  have num_nat (x : ℕ) : (x : ℚ).num.natAbs = x := by simp
  have den_nat (x : ℕ) : (x : ℚ).den = 1 := by simp
  rw [num_nat, den_nat, one_mul, hd, pow_succ']
  rw [mul_assoc, Nat.gcd_mul_left, hc.gcd_eq_one, mul_one]
  exact Nat.mul_div_cancel_left D (by decide)


private theorem bernoulli_den_twice (k : ℕ) (hk : 0 < k) :
    (bernoulli (2*k)).den = 2 * A141459 (2*k) := by
  classical
  let s := (Finset.range (2*k+2)).filter (fun p => Nat.Prime p ∧ Odd p ∧ (p-1) ∣ 2*k)
  have hn : 2 ∉ s := by simp [s]
  have he : (Finset.range (2*k+2)).filter (fun p => Nat.Prime p ∧ (p-1) ∣ 2*k) =
      insert 2 s := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, s]
    constructor
    · rintro ⟨h1,h2,h3⟩
      by_cases hh : p = 2
      · exact Or.inl hh
      · exact Or.inr ⟨h1,h2,h2.odd_iff.mpr (by have := h2.two_le; omega),h3⟩
    · rintro (rfl | ⟨h1,h2,_,h3⟩)
      · exact ⟨by omega, Nat.prime_two, by simp⟩
      · exact ⟨h1,h2,h3⟩
  rw [even_bernoulli_denominator, he, Finset.prod_insert hn]
  rfl

/-- The rational proposed by the moment calculation has exactly the OEIS denominator. -/
theorem bernoulli_denominator {n : ℕ} (hn : 2 ≤ n) :
    ((2 : ℚ)^n * |bernoulli n|).den = A141459 n := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k,hk⟩ := he
    have he' : n = 2*k := by omega
    have hb : (bernoulli n).den = 2 * A141459 n := he' ▸ bernoulli_den_twice k (by omega)
    have hd : (|bernoulli n|).den = (bernoulli n).den := by rcases le_total 0 (bernoulli n) with h|h <;> simp [abs_of_nonneg, abs_of_nonpos, h]
    have hodd : Odd (A141459 n) := by
      apply Nat.coprime_two_left.mp
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Finset.mem_filter.mp hp).2.2.1.coprime_two_left
    obtain ⟨m,hm⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
    simpa only [← hm] using cancel_two_pow |bernoulli n| (A141459 n) m (hd.trans hb) hodd
  · exact odd_bernoulli_denominator ho hn

/-- The bilateral Laplace transform of the principal logarithm on the unit interval. -/
theorem laplace_moment {z : ℂ} (hlo : -1 < z.re) (hhi : z.re < 1) (hz : z ≠ 0) :
    (∫ x in (0 : ℝ)..1, Complex.exp (z * Complex.log (1 - 1 / (x : ℂ)))) =
      Complex.exp (z * (Real.pi * Complex.I)) *
        (z * (Real.pi / Complex.sin (Real.pi * z))) := by
  let c := Complex.exp (z * (Real.pi * Complex.I))
  have hbeta : (∫ x in (0 : ℝ)..1, Complex.exp (z * Complex.log (1 - 1 / (x : ℂ)))) =
      c * Complex.betaIntegral (1-z) (1+z) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    have hpos : 0 < 1-x := sub_pos.mpr hx.2
    have hne : (1 - (x : ℂ)) ≠ 0 := by exact_mod_cast hpos.ne'
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
    change Complex.exp _ = c * ((x : ℂ) ^ ((1-z)-1) * (1-(x : ℂ)) ^ ((1+z)-1))
    rw [branch_identity hx, Real.log_div hpos.ne' hx.1.ne', Complex.ofReal_sub,
      Complex.cpow_def_of_ne_zero hxne, Complex.cpow_def_of_ne_zero hne]
    have hlog : Complex.log (1 - (x : ℂ)) = (Real.log (1-x) : ℂ) := by
      simpa using (Complex.ofReal_log hpos.le).symm
    rw [hlog, ← Complex.ofReal_log hx.1.le]
    dsimp [c]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [hbeta, Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simp; linarith) (by simp; linarith)]
  congr 1
  rw [show (1-z)+(1+z) = 1+1 by ring, Complex.Gamma_add_one 1 one_ne_zero,
    Complex.Gamma_one, one_mul, div_one, add_comm 1 z, Complex.Gamma_add_one z hz,
    ← Complex.Gamma_mul_Gamma_one_sub]
  ring

/-- The transform in the form used by the Bernoulli exponential generating function. -/
theorem laplace_bernoulli_form {z : ℂ} (hlo : -1 < z.re) (hhi : z.re < 1) (hz : z ≠ 0) :
    (∫ x in (0 : ℝ)..1, Complex.exp (z * Complex.log (1 - 1 / (x : ℂ)))) =
      (2 * Real.pi * Complex.I * z) * Complex.exp (2 * Real.pi * Complex.I * z) /
        (Complex.exp (2 * Real.pi * Complex.I * z) - 1) := by
  rw [laplace_moment hlo hhi hz]
  let t : ℂ := Real.pi * z * Complex.I
  have h1 : 2 * Real.pi * Complex.I * z = t+t := by dsimp [t]; ring
  have h2 : z * (Real.pi * Complex.I) = t := by dsimp [t]; ring
  have h3 : -(Real.pi * z) * Complex.I = -t := by dsimp [t]; ring
  rw [h1, h2, Complex.exp_add, Complex.sin, h3, Complex.exp_neg]
  change Complex.exp t * (z * (Real.pi / (((Complex.exp t)⁻¹ - Complex.exp t) * Complex.I / 2))) =
    (t+t) * (Complex.exp t * Complex.exp t) / (Complex.exp t * Complex.exp t - 1)
  let e := Complex.exp t
  have he : e ≠ 0 := Complex.exp_ne_zero t
  by_cases h : e*e = 1
  · have hh : e⁻¹ = e := (mul_eq_one_iff_inv_eq₀ he).mp h
    change e * (z * (Real.pi / ((e⁻¹-e) * Complex.I / 2))) = (t+t)*(e*e)/(e*e-1)
    simp [hh,h]
  · have hne : e*e-1 ≠ 0 := sub_ne_zero.mpr h
    have hd : e⁻¹-e ≠ 0 := sub_ne_zero.mpr (fun eq => h ((mul_eq_one_iff_inv_eq₀ he).mpr eq))
    change e * (z * (Real.pi / ((e⁻¹-e) * Complex.I / 2))) = (t+t)*(e*e)/(e*e-1)
    dsimp only [t]
    field_simp [he,hd,hne,Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq]
    rw [show (1-e^2) = -(-1+e^2) by ring, inv_neg]
    ring

open MeasureTheory in
theorem log_aemeasurable :
    AEStronglyMeasurable (fun x : ℝ => Complex.log (1-1/(x:ℂ)))
      (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have h : Measurable (fun x : ℝ => (Real.log ((1-x)/x) : ℂ) + Real.pi * Complex.I) := by fun_prop
  apply h.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioo (a:=(0:ℝ)) (b:=1))] with x hx
  exact (branch_identity hx).symm

open MeasureTheory in
theorem log_exp_majorant {z : ℂ} (hz : ‖z‖ < 1) :
    IntervalIntegrable (fun x : ℝ => Real.exp ‖z * Complex.log (1-1/(x:ℂ))‖) volume 0 1 := by
  let u : ℂ := 1 - (‖z‖:ℂ)
  have hu : 0 < u.re := by simpa [u] using sub_pos.mpr hz
  have hb := (Complex.betaIntegral_convergent (u:=u) (v:=u) hu hu).norm.const_mul
    (Real.exp (‖z‖ * Real.pi))
  have hm := log_aemeasurable
  apply hb.mono_fun' (Real.continuous_exp.comp_aestronglyMeasurable (hm.const_mul z).norm)
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioo (a:=(0:ℝ)) (b:=1))] with x hx
  have hy : 0 < 1-x := sub_pos.mpr hx.2
  change ‖Real.exp _‖ ≤ Real.exp _ * ‖(x:ℂ)^(u-1) * (1-(x:ℂ))^(u-1)‖
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_mul, branch_identity hx,
    Real.log_div hy.ne' hx.1.ne', norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  rw [Real.rpow_def_of_pos hx.1, Real.rpow_def_of_pos hy, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hxlog : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2.le
  have hylog : Real.log (1-x) ≤ 0 := Real.log_nonpos hy.le (by linarith [hx.1])
  have hn := norm_add_le ((Real.log (1-x)-Real.log x : ℝ):ℂ) ((Real.pi:ℂ)*Complex.I)
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one] at hn
  have ha : |Real.log (1-x)-Real.log x| ≤ -Real.log x - Real.log (1-x) := by
    rw [abs_le]; constructor <;> linarith
  have he : (u-1).re = - ‖z‖ := by simp [u]
  simp only [Complex.ofReal_one,he]
  calc
    _ ≤ ‖z‖ * (-Real.log x - Real.log (1-x) + Real.pi) :=
      mul_le_mul_of_nonneg_left (le_trans hn (by linarith)) (norm_nonneg _)
    _ = _ := by ring
open MeasureTheory in
/-- An integrable exponential majorant justifies integrating the Taylor series term by term. -/
theorem hasSum_moments_of_majorant (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict (Set.uIoc (0:ℝ) 1))) (z : ℂ)
    (hdom : IntervalIntegrable (fun x => Real.exp ‖z * f x‖) volume 0 1) :
    HasSum (fun n => (z ^ n / n.factorial) * ∫ x in (0:ℝ)..1, (f x)^n)
      (∫ x in (0:ℝ)..1, Complex.exp (z * f x)) := by
  let bound := fun (n : ℕ) (x : ℝ) => ‖z * f x‖ ^ n / n.factorial
  have hsum (x : ℝ) : HasSum (fun n => bound n x) (Real.exp ‖z * f x‖) := by
    simpa [bound, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp ‖z * f x‖
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a:= (0:ℝ)) (b:=1) (μ:=volume) (F := fun n x => (z * f x)^n / (n.factorial : ℂ))
    (f := fun x => Complex.exp (z * f x)) bound
    (fun n => by simpa only [Pi.pow_apply, div_eq_mul_inv] using ((hf.const_mul z).pow n).mul_const ((n.factorial : ℂ)⁻¹))
    (fun n => Filter.Eventually.of_forall fun x _ => by simp [bound, norm_pow])
    (Filter.Eventually.of_forall fun x _ => (hsum x).summable)
    (by simpa only [(hsum _).tsum_eq] using hdom)
    (Filter.Eventually.of_forall fun x _ => by
      simpa [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (z*f x))
  apply h.congr_fun
  intro n
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp
  ring

open Filter PowerSeries
open scoped Topology


/-- A convergent scalar power series considered in a neighborhood of zero. -/
private def Represents (P : PowerSeries ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ᶠ z in 𝓝 0, HasSum (fun n => z^n * coeff n P) (f z)

private theorem represents_unique {P Q : PowerSeries ℂ} {f g : ℂ → ℂ}
    (hP : Represents P f) (hQ : Represents Q g) (he : f =ᶠ[𝓝 0] g) : P = Q := by
  have aux {A : PowerSeries ℂ} {v : ℂ → ℂ} (h : Represents A v) :
      HasFPowerSeriesAt v (.ofScalars ℂ (fun n => coeff n A)) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    simpa only [zero_add, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul] using (show ∀ᶠ z in 𝓝 0, HasSum (fun n => z^n * coeff n A) (v z) from h)
  have e := (aux hP).eq_formalMultilinearSeries_of_eventually (aux hQ) he
  ext n
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) e

private theorem represents_mul {P Q : PowerSeries ℂ} {f g : ℂ → ℂ}
    (hP : Represents P f) (hQ : Represents Q g) :
    Represents (P*Q) (fun z => f z * g z) := by
  filter_upwards [hP,hQ] with z hz hw
  let a := fun n => z^n * coeff n P
  let b := fun n => z^n * coeff n Q
  have ha : Summable (fun n => ‖a n‖) := hz.summable.norm
  have hb : Summable (fun n => ‖b n‖) := hw.summable.norm
  have he : f z * g z = ∑' (n : ℕ), ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a ij.1 * b ij.2 := by
    rw [← hz.tsum_eq, ← hw.tsum_eq]
    exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hb
  rw [he]
  apply (summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb).of_norm.hasSum.congr_fun
  intro n
  rw [coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  dsimp [a,b]
  rw [← h, pow_add]
  ring

private theorem represents_exp : Represents (exp ℂ) Complex.exp := by
  apply Eventually.of_forall
  intro z
  simpa [coeff_exp, Complex.exp_eq_exp_ℂ,div_eq_mul_inv] using NormedSpace.expSeries_div_hasSum_exp z

private theorem represents_one : Represents 1 (fun _ => 1) := by
  apply Eventually.of_forall
  intro z
  apply (hasSum_ite_eq (0:ℕ) (1:ℂ)).congr_fun
  intro n
  by_cases hn : n=0 <;> simp [coeff_one,hn]

private theorem represents_X : Represents X id := by
  apply Eventually.of_forall
  intro z
  apply (hasSum_ite_eq (1:ℕ) z).congr_fun
  intro n
  by_cases hn : n=1 <;> simp [coeff_X,hn]

private theorem represents_exp_sub_one : Represents (exp ℂ-1) (fun z => Complex.exp z-1) := by
  filter_upwards [represents_exp, represents_one] with z hz hw
  simpa only [map_sub,mul_sub] using hz.sub hw

theorem bernoulli_coefficients {P : PowerSeries ℂ} {f : ℂ → ℂ} (hp : Represents P f)
    (hfe : (fun z => f z * (Complex.exp z-1)) =ᶠ[𝓝 0] (fun z => z * Complex.exp z)) :
    P = bernoulli'PowerSeries ℂ := by
  have he := represents_unique (represents_mul hp represents_exp_sub_one)
    (represents_mul represents_X represents_exp) hfe
  apply mul_right_cancel₀ (b:=exp ℂ - 1) _ (he.trans (bernoulli'PowerSeries_mul_exp_sub_one ℂ).symm)
  intro h
  have := congrArg (coeff (R:=ℂ) 1) h
  norm_num [coeff_exp] at this


open MeasureTheory in
theorem logarithmic_moment {n : ℕ} (hn : 2 ≤ n) :
    (∫ x in (0:ℝ)..1, Complex.log (1 - 1 / (x:ℂ)) ^ n) =
      (2 * (Real.pi:ℂ) * Complex.I)^n * (bernoulli n : ℂ) := by
  classical
  let L : ℝ → ℂ := fun x => Complex.log (1-1/(x:ℂ))
  let c : ℂ := 2 * Real.pi * Complex.I
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hcn : 1 < ‖c‖ := by
    dsimp [c]; rw [norm_mul,norm_mul,Complex.norm_I,Complex.norm_real]
    norm_num [abs_of_pos Real.pi_pos, Real.norm_eq_abs]; linarith [Real.pi_gt_three]
  let P : PowerSeries ℂ := PowerSeries.mk (fun j =>
    (∫ x in (0:ℝ)..1, L x ^ j) / (j.factorial * c ^ j))
  let M := fun w : ℂ => ∫ x in (0:ℝ)..1, Complex.exp ((w/c) * L x)
  have small {w : ℂ} (hw : ‖w‖ < 1) : ‖w/c‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hc)]
    exact hw.trans hcn
  have hp : Represents P M := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (show (0:ℝ)<1 by norm_num)] with w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    have h := hasSum_moments_of_majorant L log_aemeasurable (w/c) (log_exp_majorant (small hw'))
    apply h.congr_fun
    intro j
    simp only [P, PowerSeries.coeff_mk, div_pow]
    ring
  have hfe : (fun w => M w * (Complex.exp w-1)) =ᶠ[𝓝 0] (fun w => w * Complex.exp w) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (show (0:ℝ)<1 by norm_num)] with w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    by_cases hw0 : w = 0
    · simp [hw0]
    have hab := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt (small hw'))
    have h := laplace_bernoulli_form hab.1 hab.2 (div_ne_zero hw0 hc)
    have hcw : 2 * (Real.pi:ℂ) * Complex.I * (w/c) = w := by change c * (w/c) = w; field_simp
    rw [hcw] at h
    change (∫ x in (0:ℝ)..1, Complex.exp (w/c * Complex.log (1-1/(x:ℂ)))) * _ = _
    rw [h, div_mul_cancel₀]
    intro he
    have hwe := sub_eq_zero.mp he
    apply hw0
    have him := abs_lt.mp ((Complex.abs_im_le_norm w).trans_lt hw')
    have hwlog := Complex.log_exp (x:=w) (by linarith [him.1,Real.pi_gt_three]) (by linarith [him.2,Real.pi_gt_three])
    simpa [hwe] using hwlog.symm
  have he := congrArg (PowerSeries.coeff (R:=ℂ) n) (bernoulli_coefficients hp hfe)
  simp only [P, PowerSeries.coeff_mk, bernoulli'PowerSeries] at he
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by omega : n≠1)] at he
  push_cast at he
  change (∫ x in (0:ℝ)..1, L x ^ n) = c^n * (bernoulli n:ℂ)
  field_simp [hc, Nat.factorial_ne_zero] at he
  exact he

end OMA.A211163Steps
namespace OMA.A211163Steps

/-- The moment identity implies both rationality and the exact reduced denominator.
For even indices the power of i is a sign. Odd Bernoulli numbers vanish here. -/
theorem finish_of_moments
    (hm : ∀ n : ℕ, 2 ≤ n →
      (∫ x in (0 : ℝ)..1, Complex.log (1 - 1 / (x : ℂ)) ^ n) =
        (2 * (Real.pi : ℂ) * Complex.I) ^ n * (bernoulli n : ℂ)) :
    type_of% @OMA.S_oeis_a211163.main := by
  intro n hn
  rw [hm n hn]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcancel : (-1 / (Real.pi : ℂ)^n) *
      ((2 * (Real.pi : ℂ) * Complex.I)^n * (bernoulli n : ℂ)) =
      -((2 : ℂ)^n * Complex.I^n * (bernoulli n : ℂ)) := by
    simp only [mul_pow]
    field_simp
  have hd := bernoulli_denominator hn
  rw [hcancel]
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ho
  · have he : n = 2*k := by omega
    have hi : Complex.I^n = (-1:ℂ)^k := by rw [he, pow_mul, Complex.I_sq]
    rw [hi]
    refine ⟨-((2:ℚ)^n * (-1:ℚ)^k * bernoulli n), by push_cast; ring, ?_⟩
    rw [← Rat.den_abs_eq_den]
    simpa [abs_mul, abs_pow] using hd
  · have hb := bernoulli_eq_zero_of_odd ho (by omega : 1 < n)
    refine ⟨0, by simp [hb], ?_⟩
    simpa [hb] using hd

end OMA.A211163Steps

theorem OMA.solution : type_of% @OMA.S_oeis_a211163.main := OMA.A211163Steps.finish_of_moments (fun _ hn => OMA.A211163Steps.logarithmic_moment hn)
