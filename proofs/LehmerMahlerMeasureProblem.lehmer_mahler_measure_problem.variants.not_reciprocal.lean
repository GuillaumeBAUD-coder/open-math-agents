import FormalConjectures.Wikipedia.LehmerMahlerMeasureProblem

/-
Ported from an existing public Lean proof; the mathematics and the Lean proof are the original author's.
Original: https://github.com/stalex444/smyth-mahler-bound-rho/blob/41bc4f35be759b02602e2884bf70307d95b9e1c3/Smyth/Main.lean  (theorem SmythEntry.nonreciprocal_mahler_bound, via Smyth.nonreciprocal_mahler_bound)
  with Smyth/Contractions.lean, Factorization.lean, Compression.lean, CoefficientBound.lean, Quotient.lean from
  the same commit, and, for the value M(X^3 - X - 1) = rho, declarations from its dependency
  https://github.com/stalex444/arithmetic-of-time-slowest-clock/blob/49eafbab4af8899b2a66469697bf74683a88ce87/
  (PdtPisotBoundary.lean: PDT.cubic_conj_norm_lt_one; Irreducibility.lean: Time.cubicQ_irreducible;
  Settling.lean: Time.one_lt_root; SlowestClock.lean: Time.Clock.rho_bounds, cubic_root_unique,
  mahler_eq_of_pisot) and the private lemma plastic_mem of Smyth/Siegel.lean.
  Formalises C. J. Smyth, Bull. London Math. Soc. 3 (1971), 169-175.
Original author: Stephanie Alexander (stalex444)   Licence: MIT (LICENSE in both repositories)
Submitted to lefttosolve.com by @senamakel; ported to Lean v4.33.1 / formal-conjectures 9097e2f.
Changes: inlined the needed declarations into one file under namespace OMAPort_Smyth, dropped the module
  system headers and unused declarations, stated the real root rho of x^3 = x + 1 via the intermediate value
  theorem, and added the glue that derives Smyth's hypotheses (nonzero constant term, f.reverse /= -f) from
  irreducibility and M(f) > 1, and the bridge from mahlerMeasureZ to Mathlib's Polynomial.mahlerMeasure.

Both original repositories carry this licence:

MIT License

Copyright (c) 2026 Stephanie Alexander

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the Software), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED AS IS, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
(Double quotes around Software and AS IS removed to satisfy the site lint.)
-/

namespace OMAPort_Smyth

/- ===== from Smyth/Contractions.lean ===== -/

/- Finite coefficient energy for the two linear factors in Smyth's argument.
The telescoping identity constructs the Schur factors without an infinite-series
boundary convergence argument. -/


namespace Smyth
open PowerSeries
open scoped ComplexConjugate

noncomputable section

def energy (n : ℕ) (p : PowerSeries ℂ) : ℝ :=
  ∑ i ∈ Finset.range n, Complex.normSq (coeff i p)

def Contractive (f : PowerSeries ℂ) : Prop :=
  ∀ (n : ℕ) (p : PowerSeries ℂ), energy n (f * p) ≤ energy n p

theorem contractive_one : Contractive 1 := by
  intro n p
  simp

theorem Contractive.mul {f g : PowerSeries ℂ} (hf : Contractive f) (hg : Contractive g) :
    Contractive (f * g) := by
  intro n p
  rw [mul_assoc]
  exact (hf n (g * p)).trans (hg n p)

theorem contractive_C {z : ℂ} (hz : Complex.normSq z ≤ 1) : Contractive (C z) := by
  intro n p
  apply Finset.sum_le_sum
  intro i _
  rw [coeff_C_mul, Complex.normSq_mul]
  exact mul_le_of_le_one_left (Complex.normSq_nonneg _) hz

/-- The numerator and conjugate-reversed denominator of a single disc factor. -/
def lin (r : ℂ) : PowerSeries ℂ := X - C r
def revLin (r : ℂ) : PowerSeries ℂ := 1 - C (conj r) * X

private theorem local_energy (r a b : ℂ) :
    Complex.normSq (a - conj r * b) - Complex.normSq (b - r * a) =
      (1 - Complex.normSq r) * (Complex.normSq a - Complex.normSq b) := by
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring

/-- All interior coefficient terms cancel. Only the last coefficient remains. -/
theorem linear_energy (r : ℂ) (p : PowerSeries ℂ) (n : ℕ) :
    energy (n+1) (revLin r * p) - energy (n+1) (lin r * p) =
      (1 - Complex.normSq r) * Complex.normSq (coeff n p) := by
  have eqn (i : ℕ) :
      coeff (i+1) (revLin r * p) = coeff (i+1) p - conj r * coeff i p := by
    simp [revLin, sub_mul, mul_assoc, coeff_C_mul, coeff_succ_X_mul]
  have eqd (i : ℕ) : coeff (i+1) (lin r * p) = coeff i p - r * coeff (i+1) p := by
    simp [lin, sub_mul, coeff_C_mul, coeff_succ_X_mul]
  induction n with
  | zero =>
    simp [energy, revLin, lin, sub_mul, mul_assoc, Complex.normSq_mul]
  | succ n ih =>
    unfold energy at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i => Complex.normSq (coeff i (lin r * p)))]
    rw [eqn, eqd]
    linarith [local_energy r (coeff (n+1) p) (coeff n p)]

/-- Division by a factor with nonzero constant term yields an actual
contractive formal power series, with the defining identity retained. -/
private theorem quotient_contractive (a d : PowerSeries ℂ) (hd : IsUnit d)
    (h : ∀ n p, energy n (a * p) ≤ energy n (d * p)) :
    ∃ f, Contractive f ∧ d * f = a := by
  obtain ⟨u, rfl⟩ := hd
  refine ⟨a * ↑u⁻¹, ?_, by simp [mul_left_comm]⟩
  intro n p
  simpa [mul_assoc] using h n ((↑u⁻¹ : PowerSeries ℂ) * p)

theorem factor_pair (r : ℂ) :
    ∃ d f g : PowerSeries ℂ, Contractive f ∧ Contractive g ∧
      d * f = lin r ∧ d * g = revLin r ∧ ‖constantCoeff d‖ = max 1 ‖r‖ := by
  by_cases hr : ‖r‖ ≤ 1
  · have h : Complex.normSq r ≤ 1 := by nlinarith [Complex.sq_norm r, norm_nonneg r]
    have hd : IsUnit (revLin r) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp [revLin]
    obtain ⟨f, hf, hf'⟩ := quotient_contractive (lin r) (revLin r) hd (fun n p => by
      cases n with
      | zero => simp [energy]
      | succ n =>
        have H := linear_energy r p n
        linarith [mul_nonneg (sub_nonneg.mpr h) (Complex.normSq_nonneg (coeff n p))])
    exact ⟨revLin r, f, 1, hf, contractive_one, hf', mul_one _, by simp [revLin, max_eq_left hr]⟩
  · have hr' : 1 ≤ ‖r‖ := (lt_of_not_ge hr).le
    have h : 1 ≤ Complex.normSq r := by nlinarith [Complex.sq_norm r]
    have hn : r ≠ 0 := by intro e; simp [e] at hr
    have hd : IsUnit (lin r) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simpa [lin] using hn
    obtain ⟨g, hg, hg'⟩ := quotient_contractive (revLin r) (lin r) hd (fun n p => by
      cases n with
      | zero => simp [energy]
      | succ n =>
        have H := linear_energy r p n
        linarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (Complex.normSq_nonneg (coeff n p))])
    exact ⟨lin r, 1, g, contractive_one, hg, mul_one _, hg', by simp [lin, max_eq_right hr']⟩

end
end Smyth

/- ===== from Smyth/Factorization.lean ===== -/

/- A monic polynomial and its conjugate reciprocal have contractive series
representatives with a common denominator. Its constant coefficient has
modulus equal to the Mahler measure. -/

namespace Smyth
open Polynomial
open scoped ComplexConjugate

noncomputable section

private theorem reverse_linear (z : ℂ) :
    (X - C z).reverse = 1 - C z * X := by
  simp [Polynomial.reverse, reflect_sub, reflect_C]

private theorem pair_prod (s : Multiset ℂ) :
    let p : ℂ[X] := (s.map (fun z => X - C z)).prod
    ∃ d f g : PowerSeries ℂ, Contractive f ∧ Contractive g ∧
      d * f = ↑p ∧ d * g = ↑((p.map (starRingEnd ℂ)).reverse) ∧
      ‖PowerSeries.constantCoeff d‖ = p.mahlerMeasure := by
  dsimp only
  induction s using Multiset.induction_on with
  | empty =>
    have hr : (1 : ℂ[X]).reverse = 1 := by
      change reflect (1 : ℂ[X]).natDegree 1 = 1
      rw [natDegree_one, ← C_1, reflect_C]
      simp
    exact ⟨1,1,1,contractive_one,contractive_one,by simp,by simp [hr],by simp⟩
  | cons z s ih =>
    let p : ℂ[X] := (s.map (fun r => X - C r)).prod
    obtain ⟨d,f,g,hf,hg,he,he',hn⟩ := ih
    obtain ⟨t,a,b,ha,hb,hta,htb,ht⟩ := factor_pair z
    have hm : p.Monic := monic_multisetProd_X_sub_C _
    have hc : ((X - C (conj z)) * p.map (starRingEnd ℂ)).reverse =
        (1 - C (conj z) * X) * (p.map (starRingEnd ℂ)).reverse := by
      rw [reverse_mul, reverse_linear]
      simp [(hm.map _).leadingCoeff]
    simp only [Multiset.map_cons, Multiset.prod_cons]
    refine ⟨t*d, a*f, b*g, ha.mul hf, hb.mul hg, ?_, ?_, ?_⟩
    · rw [mul_mul_mul_comm, hta, he]
      simp [lin]
    · rw [mul_mul_mul_comm, htb, he']
      simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
      change _ = (((X - C (conj z)) * p.map (starRingEnd ℂ)).reverse : PowerSeries ℂ)
      rw [hc]
      simp [revLin, p]
    · rw [map_mul, norm_mul, ht, hn, mahlerMeasure_mul, mahlerMeasure_X_sub_C]

theorem polynomial_pair (p : ℤ[X]) (hm : p.Monic) :
    let q := p.map (Int.castRingHom ℂ)
    ∃ d f g : PowerSeries ℂ, Contractive f ∧ Contractive g ∧
      d*f = ↑q ∧ d*g = ↑(p.reverse.map (Int.castRingHom ℂ)) ∧
      ‖PowerSeries.constantCoeff d‖ = q.mahlerMeasure := by
  let q := p.map (Int.castRingHom ℂ)
  have fac := (IsAlgClosed.splits q).eq_prod_roots_of_monic (hm.map _)
  have realq : q.map (starRingEnd ℂ) = q := by ext; simp [q]
  have rev : q.reverse = p.reverse.map (Int.castRingHom ℂ) := by
    simp [q, Polynomial.reverse, reflect_map, hm.natDegree_map]
  have H := pair_prod q.roots
  dsimp only at H
  rwa [← fac, realq, rev] at H

end
end Smyth

/- ===== from Smyth/Compression.lean ===== -/

/- Real parts of a complex contractive formal series satisfy every finite
real coefficient inequality used in Smyth's proof. -/

namespace Smyth
open PowerSeries
noncomputable section

def realPart (f : PowerSeries ℂ) : PowerSeries ℝ := mk fun i => (coeff i f).re

@[simp] theorem coeff_realPart (f : PowerSeries ℂ) (i : ℕ) :
    coeff i (realPart f) = (coeff i f).re := coeff_mk _ _

theorem realPart_int_mul (f : PowerSeries ℂ) (a : PowerSeries ℤ) :
    realPart (f * map (Int.castRingHom ℂ) a) =
      realPart f * map (Int.castRingHom ℝ) a := by
  ext n
  simp [coeff_mul, Complex.re_sum, Complex.mul_re]

theorem finite_compression {f : PowerSeries ℂ} (hf : Contractive f)
    (I J : Finset ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ J, (∑ j ∈ I, if j ≤ i then u j * coeff (i-j) (realPart f) else 0)^2)
      ≤ ∑ j ∈ I, (u j)^2 := by
  classical
  let p : PowerSeries ℂ := ∑ j ∈ I, C (u j : ℂ) * X^j
  let n := (I ∪ J).sup id + 1
  have hsub : I ∪ J ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have inp (i : ℕ) : coeff i p = if i ∈ I then (u i : ℂ) else 0 := by
    by_cases h : i ∈ I <;> simp [p, coeff_C_mul, coeff_X_pow, apply_ite, h]
  have out (i : ℕ) : (coeff i (f*p)).re =
      ∑ j ∈ I, if j ≤ i then u j * coeff (i-j) (realPart f) else 0 := by
    simp only [p, Finset.mul_sum, map_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc, mul_comm f, mul_assoc, coeff_C_mul, coeff_mul_X_pow']
    by_cases h : j ≤ i <;> simp [h]
  calc
    _ = ∑ i ∈ J, (coeff i (f*p)).re^2 := by simp_rw [out]
    _ ≤ ∑ i ∈ J, Complex.normSq (coeff i (f*p)) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [Complex.normSq_apply]; nlinarith [sq_nonneg (coeff i (f*p)).im]
    _ ≤ energy n (f*p) := Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => hsub (Finset.mem_union_right I hi)) (fun _ _ _ => Complex.normSq_nonneg _)
    _ ≤ energy n p := hf _ _
    _ = ∑ i ∈ I, (u i)^2 := by
      unfold energy
      rw [← Finset.sum_subset (s₁ := I) (s₂ := Finset.range n)
        (fun i hi => hsub (Finset.mem_union_left J hi)) (fun i _ hi => by simp [inp, hi])]
      apply Finset.sum_congr rfl
      intro i hi; simp [inp, hi, Complex.normSq_apply, pow_two]
end
end Smyth

/- ===== from Smyth/CoefficientBound.lean ===== -/


/-
# Smyth's coefficient estimate

The finite compression of a contractive Toeplitz matrix suffices for the
coefficient argument of Smyth (1971), as given in Schinzel (1973), pp. 389–391.
-/

namespace Smyth

/-- Every finite restriction of multiplication by the power series with coefficients
`f` has operator norm at most one on real square-summable sequences. -/
def CoefficientContraction (f : ℕ → ℝ) : Prop :=
  ∀ (I J : Finset ℕ) (u : ℕ → ℝ),
    (∑ i ∈ J, (∑ j ∈ I, if j ≤ i then u j * f (i-j) else 0)^2) ≤
      ∑ j ∈ I, (u j)^2

/-- This rational separates the smaller positive zero of the quartic in the
early-coefficient case from the reciprocal of the plastic number. -/
private theorem above_cut {c : ℝ} (hc : 0 ≤ c) (h : 1 < c^2 + c^3) :
    (75485 / 100000 : ℝ) < c := by
  by_contra! h'
  have h₂ := pow_le_pow_left₀ hc h' 2
  have h₃ := pow_le_pow_left₀ hc h' 3
  norm_num at h₂ h₃
  linarith

/-- The branch where another nonzero coefficient occurs strictly before index `2k`.
Here `v` is the common coefficient of the two power series at index `l-k`. -/
theorem bound_of_early_coefficient {c v : ℝ} {a : ℤ}
    (hc : 0 ≤ c) (hfirst : c ≤ 2 * (1-c^2)) (ha : a ≠ 0)
    (htest : ∀ b g : ℝ, 5*c^2/4 + (v+g*c)^2 +
      ((a:ℝ)*c/2-v/2+g*c/2+b*c)^2 ≤ 2+g^2+b^2) :
    c^2 + c^3 ≤ 1 := by
  by_contra! h
  have hcut := above_cut hc h
  have hu : c < 79/100 := by
    by_contra! hn
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 79/100) hn 2
    nlinarith
  have hsq := pow_le_pow_left₀ hc hu.le 2
  have hd : 0 < 5-8*c^2 := by nlinarith
  -- At b = g = s the test expression is a convex quadratic in v.
  -- Its exact minimum is m, attained at t. This avoids diagonalizing a matrix.
  let d := 5-8*c^2
  let s := 2*(a:ℝ)*c^2/d
  let t := (a:ℝ)*c*(1-2*c^2)/d
  let m := (4*(a:ℝ)^2*c^2+25*c^2-40*c^4)/(4*d)
  have hsplit :
      5*c^2/4 + (v+s*c)^2 + ((a:ℝ)*c/2-v/2+s*c/2+s*c)^2 - 2*s^2 =
        m + 5/4*(v-t)^2 := by
    dsimp only [s,t,m]
    field_simp [show d ≠ 0 from ne_of_gt hd]
    dsimp only [d]
    ring
  have hm : m ≤ 2 := by nlinarith [htest s s, sq_nonneg (v-t)]
  have hm' := (div_le_iff₀ (show 0 < 4*d by dsimp [d]; positivity)).mp hm
  have hA : (1:ℤ) ≤ a^2 := by
    have hpos : 0 < a^2 := sq_pos_of_ne_zero ha
    omega
  have hAr : (1:ℝ) ≤ (a:ℝ)^2 := by exact_mod_cast hA
  dsimp [d] at hm'
  have hp : 0 ≤ 40*c^4-93*c^2+40 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hAr) (sq_nonneg c)]
  let q : ℝ := 75485/100000
  have hq : q^2 < c^2 := by
    exact pow_lt_pow_left₀ hcut (by norm_num [q]) (by decide)
  have hh : (c^2-q^2)*(93-40*(c^2+q^2)) ≥ 0 := by
    apply mul_nonneg (sub_nonneg.mpr hq.le)
    dsimp [q]
    nlinarith
  dsimp [q] at hh
  nlinarith

/-- On the interval allowed by the first coefficient estimate, the extreme value
in Schinzel (18) is reached at `x = 1-c²`. All divisions are cleared. -/
private theorem endpoint_bound {c x : ℝ}
    (hc : 3/4 ≤ c) (hx : x ≤ 1-c^2)
    (h : (c-(1-c^2))*(1-c^2) + (1-c)*x^2 + (1+c)*(c-x)^2 ≤ 2*(1-c^2)^2) :
    c^2+c^3 ≤ 1 := by
  have hc2 : (3/4:ℝ)^2 ≤ c^2 := pow_le_pow_left₀ (by norm_num) hc 2
  have hprod : 0 ≤ ((1-c^2)-x)*(2*c^2+c-1-x) := by
    apply mul_nonneg (by linarith) (by nlinarith)
  have hb : (1+c)*(1-c^2-c^3) ≥ 0 := by nlinarith
  by_contra! hn
  exact (not_lt_of_ge hb) (mul_neg_of_pos_of_neg (by linarith) (by linarith))

/-- The branch where all quotient coefficients strictly between `k` and `2k` vanish.
The integral coefficient `a` at `2k` can itself vanish. The inequalities on the
second coefficients are stated with positive denominators cleared. -/
theorem bound_of_late_coefficient {c u v z w : ℝ} {a : ℤ}
    (hc : 0 ≤ c) (hc1 : c < 1) (hu : u ≤ 1-c^2) (hv : -v ≤ 1-c^2)
    (hfirst : u = c+v) (hnext : z-w = (a:ℝ)*c + v)
    (uz : (1-c)*z ≤ (1-c)*(1-c^2)-u^2)
    (lz : -(1+c)*(1-c^2)+u^2 ≤ (1+c)*z)
    (uw : (1-c)*w ≤ (1-c)*(1-c^2)-v^2)
    (lw : -(1+c)*(1-c^2)+v^2 ≤ (1+c)*w) :
    c^2 + c^3 ≤ 1 := by
  by_contra! hn
  have hcut := above_cut hc hn
  have hc' : 3/4 ≤ c := by linarith
  have hm : 0 ≤ 1-c := by linarith
  have hp : 0 ≤ 1+c := by linarith
  have hh : 0 ≤ 1-c^2 := by nlinarith [mul_nonneg hm hp]
  rcases le_or_gt a 0 with ha | ha
  · have har : (a:ℝ) ≤ 0 := by exact_mod_cast ha
    have hx : c-(1-c^2) ≤ w-z := by nlinarith [mul_nonpos_of_nonpos_of_nonneg har hc]
    apply not_le_of_gt hn (endpoint_bound (x:=u) hc' hu ?_)
    rw [show c-u = -v by linarith]
    nlinarith only [mul_le_mul_of_nonneg_right hx hh, mul_le_mul_of_nonneg_right uw hp,
      mul_le_mul_of_nonneg_right lz hm]
  · have ha' : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ a by omega)
    have hx : c-(1-c^2) ≤ z-w := by nlinarith [mul_le_mul_of_nonneg_right ha' hc]
    apply not_le_of_gt hn (endpoint_bound (x:=-v) hc' hv ?_)
    rw [hfirst] at uz
    nlinarith [mul_le_mul_of_nonneg_right hx hh, mul_le_mul_of_nonneg_right uz hp,
      mul_le_mul_of_nonneg_right lw hm]


private theorem compression₂ {f : ℕ → ℝ} (hf : CoefficientContraction f)
    {k : ℕ} (hk : 0 < k) (x y : ℝ) :
    (x*f 0)^2 + (x*f k+y*f 0)^2 ≤ x^2+y^2 := by
  classical
  have h := hf {0,k} {0,k} (fun j => if j = 0 then x else y)
  simpa [Finset.sum_insert, hk.ne', hk.ne, show ¬k ≤ 0 by omega] using h

private theorem compression₃ {f : ℕ → ℝ} (hf : CoefficientContraction f)
    {k : ℕ} (hk : 0 < k) (x y z : ℝ) :
    (x*f 0)^2 + (x*f k+y*f 0)^2 + (x*f (2*k)+y*f k+z*f 0)^2 ≤
      x^2+y^2+z^2 := by
  classical
  have h := hf {0,k,2*k} {0,k,2*k} (fun j => if j=0 then x else if j=k then y else z)
  have h2 : 0 < 2*k := by omega
  have h3 : k < 2*k := by omega
  simpa [Finset.sum_insert, hk.ne', hk.ne, h2.ne', h2.ne, h3.ne', h3.ne, h3.le,
    show ¬k ≤ 0 by omega, show ¬2*k ≤ 0 by omega, show ¬2*k ≤ k by omega,
    show 2*k-k = k by omega, add_assoc] using h

theorem schur_first {f : ℕ → ℝ} (hf : CoefficientContraction f)
    {k : ℕ} (hk : 0 < k) : |f k| ≤ 1-(f 0)^2 := by
  have hplus := compression₂ hf hk 1 (f 0)
  have hminus := compression₂ hf hk 1 (- f 0)
  rw [abs_le]
  constructor
  · by_contra! h
    nlinarith [sq_nonneg (f k-(f 0)^2+1)]
  · by_contra! h
    nlinarith [sq_nonneg (f k+(f 0)^2-1)]

/-- Apply the three-index compression to a vector and pair the output with
its reversed input. The positive and negative quadratic-form bounds, tested
on the two displayed vectors, give the sharp second-coefficient inequalities. -/
theorem schur_second {f : ℕ → ℝ} (hf : CoefficientContraction f) {k : ℕ}
    (hk : 0 < k) (hc : 0 ≤ f 0) (hc1 : f 0 < 1) :
    (1-f 0)*f (2*k) ≤ (1-f 0)*(1-(f 0)^2)-(f k)^2 ∧
    -(1+f 0)*(1-(f 0)^2)+(f k)^2 ≤ (1+f 0)*f (2*k) := by
  let c := f 0
  let u := f k
  let v := f (2*k)
  have hp (x y z : ℝ) :
      x*(x*v+y*u+z*c) + y*(x*u+y*c) + z*(x*c) ≤ x^2+y^2+z^2 := by
    have h := compression₃ hf hk x y z
    change (x*c)^2+(x*u+y*c)^2+(x*v+y*u+z*c)^2 ≤ _ at h
    nlinarith only [h, sq_nonneg (z-x*c), sq_nonneg (y-(x*u+y*c)),
      sq_nonneg (x-(x*v+y*u+z*c))]
  have hm (x y z : ℝ) :
      -(x^2+y^2+z^2) ≤ x*(x*v+y*u+z*c) + y*(x*u+y*c) + z*(x*c) := by
    have h := compression₃ hf hk x y z
    change (x*c)^2+(x*u+y*c)^2+(x*v+y*u+z*c)^2 ≤ _ at h
    nlinarith only [h, sq_nonneg (z+x*c), sq_nonneg (y+(x*u+y*c)),
      sq_nonneg (x+(x*v+y*u+z*c))]
  change (1-c)*v ≤ (1-c)*(1-c^2)-u^2 ∧ -(1+c)*(1-c^2)+u^2 ≤ (1+c)*v
  constructor
  · apply le_of_mul_le_mul_left (a := 1-c) _ (by dsimp [c]; linarith)
    nlinarith only [hp (1-c) u (c*(1-c))]
  · apply le_of_mul_le_mul_left (a := 1+c) _ (by dsimp [c]; linarith)
    nlinarith only [hm (1+c) (-u) (-c*(1+c))]

private theorem compression₄ {f : ℕ → ℝ} (hf : CoefficientContraction f)
    {i k : ℕ} (hi : 0 < i) (hik : i < k) (g s b : ℝ) :
    (f 0)^2 + (f i+g*f 0)^2 + (f k+g*f (k-i)+s*f 0)^2 +
      (f (k+i)+g*f k+s*f i+b*f 0)^2 ≤ 1+g^2+s^2+b^2 := by
  classical
  let I : Finset ℕ := {0,i,k,k+i}
  have h := hf I I (fun j => if j=0 then 1 else if j=i then g else if j=k then s else b)
  have h₁ : 0 < k := by omega
  have h₂ : k < k+i := by omega
  have h₃ : i < k+i := by omega
  have h₄ : 0 < k+i := by omega
  simpa [I, Finset.sum_insert, hi.ne, hi.ne', h₁.ne, h₁.ne', h₂.ne, h₂.ne', h₃.ne,
    h₃.ne', h₄.ne, h₄.ne', hik.ne, hik.ne', hi.le, h₁.le, h₂.le, h₃.le, h₄.le,
    hik.le, not_le.mpr hi, not_le.mpr h₁, not_le.mpr h₂, not_le.mpr h₃,
    not_le.mpr h₄, not_le.mpr hik, add_assoc] using h

private theorem early_test {f g : ℕ → ℝ} (hf : CoefficientContraction f)
    (hg : CoefficientContraction g) {i k : ℕ} (hi : 0 < i) (hik : i < k)
    {c a : ℝ} (hf0 : f 0=c) (hg0 : g 0=c)
    (hsmall : ∀ j < k, f j = g j)
    (hfirst : f k = c + g k) (hsecond : f (k+i) = a*c + g i + g (k+i))
    (b t : ℝ) :
    5*c^2/4 + (g i+t*c)^2 + (a*c/2-g i/2+t*c/2+b*c)^2 ≤ 2+t^2+b^2 := by
  -- Use the two test inputs 1 + t X^i ∓ X^k ± b X^(k+i).
  have h₁ := compression₄ hf hi hik t (-1) b
  have h₂ := compression₄ hg hi hik t 1 (-b)
  have hki : k-i < k := by omega
  rw [hf0, hfirst, hsecond, hsmall i hik, hsmall (k-i) hki] at h₁
  rw [hg0] at h₂
  -- At indices k and k+i project onto the difference of the two outputs.
  have hs (x y : ℝ) : 2*((x-y)/2)^2 ≤ x^2+y^2 := by nlinarith [sq_nonneg (x+y)]
  have hkproj := hs (c+g k+t*g (k-i)+(-1)*c) (g k+t*g (k-i)+1*c)
  have hlproj := hs (a*c+g i+g (k+i)+t*(c+g k)+(-1)*g i+b*c)
    (g (k+i)+t*g k+1*g i+-b*c)
  nlinarith only [h₁,h₂,hkproj,hlproj]

open PowerSeries

private theorem coeff_sparse {f g : PowerSeries ℝ} {a : PowerSeries ℤ}
    (hfg : g * PowerSeries.map (Int.castRingHom ℝ) a = f) (n : ℕ) (S : Finset ℕ)
    (hs : S ⊆ Finset.range (n+1))
    (hzero : ∀ j ≤ n, j ∉ S → coeff j a = 0) :
    coeff n f = ∑ j ∈ S, ((coeff j a : ℤ) : ℝ) * coeff (n-j) g := by
  rw [← hfg, mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_map, Int.coe_castRingHom]
  symm
  apply Finset.sum_subset hs
  intro j hj hnot
  simp [hzero j (by simpa [Nat.lt_succ_iff] using hj) hnot]

private theorem coeff_before {f g : PowerSeries ℝ} {a : PowerSeries ℤ}
    (hfg : g * PowerSeries.map (Int.castRingHom ℝ) a = f) (h0 : coeff 0 a = 1)
    {k : ℕ} (hzero : ∀ j, 0 < j → j < k → coeff j a = 0) {n : ℕ} (hn : n < k) :
    coeff n f = coeff n g := by
  have e := coeff_sparse hfg n {0} (by simp)
    (fun j hj hnot => hzero j (by simp at hnot; omega)
      (by omega))
  simpa [h0] using e

private theorem coeff_at_first {f g : PowerSeries ℝ} {a : PowerSeries ℤ}
    (hfg : g * PowerSeries.map (Int.castRingHom ℝ) a = f) (h0 : coeff 0 a = 1)
    {k : ℕ} (hk : 0 < k) (hzero : ∀ j, 0 < j → j < k → coeff j a = 0) :
    coeff k f = ((coeff k a : ℤ) : ℝ)*coeff 0 g + coeff k g := by
  have e := coeff_sparse hfg k {0,k} (by intro j hj; simp at hj; rcases hj with rfl | rfl <;> simp)
    (fun j hj hnot => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      exact hzero j (by omega) (by omega))
  simpa [h0,hk.ne,hk.ne',add_comm] using e

private theorem coeff_at_second {f g : PowerSeries ℝ} {a : PowerSeries ℤ}
    (hfg : g * PowerSeries.map (Int.castRingHom ℝ) a = f) (h0 : coeff 0 a = 1)
    {k n : ℕ} (hk : 0 < k) (hkn : k < n)
    (hzero : ∀ j, 0 < j → j < n → j ≠ k → coeff j a = 0) :
    coeff n f = ((coeff n a : ℤ) : ℝ)*coeff 0 g + ((coeff k a : ℤ) : ℝ)*coeff (n-k) g + coeff n g := by
  have hn : 0 < n := by omega
  have e := coeff_sparse hfg n {0,k,n} (by intro j hj; simp at hj; rcases hj with rfl | rfl | rfl <;> simp [hkn.le])
    (fun j hj hnot => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      exact hzero j (by omega) (by omega) (by tauto))
  simpa [h0,hk.ne,hk.ne',hn.ne,hn.ne',hkn.ne,hkn.ne',add_comm,add_assoc,add_left_comm] using e

private theorem late_test {f g : ℕ → ℝ} (hf : CoefficientContraction f)
    (hg : CoefficientContraction g) {k : ℕ} (hk : 0 < k)
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) (hf0 : f 0=c) (hg0 : g 0=c)
    (hfirst : f k = c + g k) {a : ℤ} (hsecond : f (2*k) - g (2*k) = (a:ℝ)*c + g k) :
    c^2+c^3 ≤ 1 := by
  obtain ⟨uz,lz⟩ := schur_second hf hk (hf0 ▸ hc) (hf0 ▸ hc1)
  obtain ⟨uw,lw⟩ := schur_second hg hk (hg0 ▸ hc) (hg0 ▸ hc1)
  have hu := schur_first hf hk
  have hv := schur_first hg hk
  rw [hf0, abs_le] at hu
  rw [hg0, abs_le] at hv
  rw [hf0] at uz lz
  rw [hg0] at uw lw
  exact bound_of_late_coefficient hc hc1 hu.2 (by linarith [hv.1]) hfirst hsecond uz lz uw lw

/-- **Smyth's sharp coefficient bound.** The integral quotient has constant term
one and at least one further nonzero coefficient. Both real Taylor series must
act contractively on finite vectors and have equal positive constant terms. -/
theorem sharp_coefficient_bound {f g : PowerSeries ℝ} {a : PowerSeries ℤ}
    (hf : CoefficientContraction (fun n => coeff n f))
    (hg : CoefficientContraction (fun n => coeff n g))
    (hfg : g * PowerSeries.map (Int.castRingHom ℝ) a = f)
    (ha0 : constantCoeff a = 1) (ha : a ≠ 1)
    (hc : 0 < coeff 0 f) (h0 : coeff 0 g = coeff 0 f) :
    (coeff 0 f)^2 + (coeff 0 f)^3 ≤ 1 := by
  classical
  let c := coeff 0 f
  change c^2+c^3 ≤ 1
  change 0 < c at hc
  change coeff 0 g = c at h0
  have ha0' : coeff 0 a = 1 := by simpa only [coeff_zero_eq_constantCoeff_apply] using ha0
  have hex : ∃ n, 0 < n ∧ coeff n a ≠ 0 := by
    by_contra! hn
    apply ha
    ext n
    rcases n with _ | n
    · simpa using ha0
    · simp [hn _ (Nat.succ_pos n)]
  let k := Nat.find hex
  have hk : 0 < k := (Nat.find_spec hex).1
  have hak : coeff k a ≠ 0 := (Nat.find_spec hex).2
  have hbelow (j : ℕ) (hj : 0 < j) (hjk : j < k) : coeff j a = 0 := by
    by_contra h
    have := Nat.find_min' hex (show 0 < j ∧ coeff j a ≠ 0 from ⟨hj,h⟩)
    omega
  have hsmall (j : ℕ) (hj : j < k) : coeff j f = coeff j g := coeff_before hfg ha0' hbelow hj
  have hu := (abs_le.mp (schur_first hf hk))
  have hv := (abs_le.mp (schur_first hg hk))
  change -(1-c^2) ≤ coeff k f ∧ coeff k f ≤ 1-c^2 at hu
  change -(1-(coeff 0 g)^2) ≤ coeff k g ∧ coeff k g ≤ 1-(coeff 0 g)^2 at hv
  rw [h0] at hv
  have eqk := coeff_at_first hfg ha0' hk hbelow
  rw [h0] at eqk
  by_contra! hn
  have hcut := above_cut hc.le hn
  have hbig : 1-c^2 < c := by nlinarith [sq_nonneg (c-3/4)]
  have hc1 : c < 1 := by
    by_contra! hh
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hh 2
    have he : (coeff k a : ℤ) = 0 := by
      have hh' : (((coeff k a : ℤ) : ℝ))*c = 0 := by linarith [hu.1,hu.2,hv.1,hv.2]
      exact_mod_cast (mul_eq_zero.mp hh').resolve_right hc.ne'
    exact hak he
  have hak' : coeff k a = 1 ∨ coeff k a = -1 := by
    by_contra! he
    have hcases : coeff k a ≤ -2 ∨ 2 ≤ coeff k a := by omega
    rcases hcases with h | h
    · have hr : ((coeff k a : ℤ) : ℝ) ≤ -2 := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_right hr hc.le, hu.1, hv.2]
    · have hr : (2:ℝ) ≤ ((coeff k a : ℤ) : ℝ) := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_right hr hc.le, hu.2, hv.1]
  have hfirst : c ≤ 2*(1-c^2) := by
    rcases hak' with h | h <;> rw [h] at eqk <;> norm_num at eqk <;>
      linarith [hu.1,hu.2,hv.1,hv.2]
  -- The first integral coefficient is ±1. For the negative sign exchange
  -- the two series. At index 2k the exchanged coefficient is 1-a₂ₖ.
  by_cases hearly : ∃ l : ℕ, k < l ∧ l < 2*k ∧ coeff l a ≠ 0
  · let l := Nat.find hearly
    obtain ⟨hkl,hl2,hal⟩ := Nat.find_spec hearly
    change k < l at hkl
    change l < 2*k at hl2
    change coeff l a ≠ 0 at hal
    have hb (j : ℕ) (hj : 0 < j) (hjl : j < l) (hjk : j ≠ k) : coeff j a = 0 := by
      rcases lt_or_gt_of_ne hjk with h | h
      · exact hbelow j hj h
      · by_contra hne
        have := Nat.find_min' hearly (show k < j ∧ j < 2*k ∧ coeff j a ≠ 0 from ⟨h,by omega,hne⟩)
        omega
    have eql := coeff_at_second hfg ha0' hk hkl hb
    rw [h0] at eql
    let i := l-k
    have hi : 0 < i := by dsimp [i]; omega
    have hik : i < k := by dsimp [i]; omega
    have hidx : k+i=l := by dsimp [i]; omega
    change coeff l f = ((coeff l a : ℤ):ℝ)*c + ((coeff k a : ℤ):ℝ)*coeff i g + coeff l g at eql
    rcases hak' with h | h
    · rw [h] at eqk eql
      norm_num at eqk eql
      refine not_le_of_gt hn (bound_of_early_coefficient (v:=coeff i g) hc.le hfirst hal ?_)
      refine early_test hf hg hi hik rfl h0 hsmall eqk ?_
      simpa only [hidx] using eql
    · rw [h] at eqk eql
      norm_num at eqk eql
      refine not_le_of_gt hn (bound_of_early_coefficient (v:=coeff i f) hc.le hfirst (neg_ne_zero.mpr hal) ?_)
      refine early_test hg hf hi hik h0 rfl (fun j h => (hsmall j h).symm) (by linarith) ?_
      rw [hidx,hsmall i hik,Int.cast_neg]
      linarith
  · have hb (j : ℕ) (hj : 0 < j) (hj2 : j < 2*k) (hjk : j ≠ k) : coeff j a = 0 := by
      rcases lt_or_gt_of_ne hjk with h | h
      · exact hbelow j hj h
      · by_contra hne
        exact hearly ⟨j,h,hj2,hne⟩
    have eql := coeff_at_second hfg ha0' hk (show k < 2*k by omega) hb
    rw [show 2*k-k = k by omega, h0] at eql
    rcases hak' with h | h
    · rw [h] at eqk eql
      norm_num at eqk eql
      apply not_le_of_gt hn (late_test hf hg hk hc.le hc1 rfl h0 eqk (a:=coeff (2*k) a) ?_)
      linarith
    · rw [h] at eqk eql
      norm_num at eqk eql
      apply not_le_of_gt hn (late_test hg hf hk hc.le hc1 h0 rfl (by linarith)
        (a:=1-coeff (2*k) a) ?_)
      push_cast
      linarith

end Smyth

/- ===== from Smyth/Quotient.lean ===== -/

/- The sign-normalized reciprocal quotient has integer coefficients. The
normalized numerator and denominator have the same positive constant term. -/

namespace Smyth
open PowerSeries
open scoped Polynomial

noncomputable section

private theorem integer_quotient (p : Polynomial ℤ) (hp : p.Monic)
    (hε : p.coeff 0 = 1 ∨ p.coeff 0 = -1) (hpos : p.reverse ≠ p) (hneg : p.reverse ≠ -p) :
    ∃ a : PowerSeries ℤ, constantCoeff a = 1 ∧ a ≠ 1 ∧
      (p.reverse : PowerSeries ℤ) * a = C (p.coeff 0) * (p : PowerSeries ℤ) := by
  have h0 : constantCoeff (p.reverse : PowerSeries ℤ) = 1 := by
    simp [Polynomial.coeff_zero_reverse, hp.leadingCoeff]
  have hu : IsUnit (p.reverse : PowerSeries ℤ) := isUnit_iff_constantCoeff.mpr (h0 ▸ isUnit_one)
  obtain ⟨u, hu⟩ := hu
  let a : PowerSeries ℤ := ↑u⁻¹ * (C (p.coeff 0) * ↑p)
  have ha : (p.reverse : PowerSeries ℤ) * a = C (p.coeff 0) * ↑p := by
    rw [← hu]; simp [a]
  refine ⟨a, ?_, ?_, ha⟩
  · have he := congrArg (constantCoeff (R := ℤ)) ha
    rcases hε with h|h <;> simpa [h0, h] using he
  · intro h
    rw [h, mul_one] at ha
    rcases hε with e|e
    · apply hpos; apply Polynomial.coe_injective ℤ
      simpa [e] using ha
    · apply hneg; apply Polynomial.coe_injective ℤ
      simpa [e] using ha

theorem normalized_pair (p : Polynomial ℤ) (hp : p.Monic)
    (hε : p.coeff 0 = 1 ∨ p.coeff 0 = -1) (hpos : p.reverse ≠ p) (hneg : p.reverse ≠ -p) :
    let M := (p.map (Int.castRingHom ℂ)).mahlerMeasure
    ∃ (f g : PowerSeries ℂ) (a : PowerSeries ℤ),
      Contractive f ∧ Contractive g ∧ constantCoeff f = (M⁻¹ : ℝ) ∧
      constantCoeff g = (M⁻¹ : ℝ) ∧ constantCoeff a = 1 ∧ a ≠ 1 ∧
      g * map (Int.castRingHom ℂ) a = f := by
  let M := (p.map (Int.castRingHom ℂ)).mahlerMeasure
  let ε : ℂ := (p.coeff 0 : ℤ)
  have e_cases : ε = 1 ∨ ε = -1 := by rcases hε with e|e <;> simp [ε, e]
  have e2 : ε * ε = 1 := by rcases e_cases with e|e <;> simp [e]
  have eSchur : Contractive (C ε) := contractive_C (by rcases e_cases with e|e <;> simp [e])
  obtain ⟨a, ha₀, hane, ha⟩ := integer_quotient p hp hε hpos hneg
  obtain ⟨d, f, g, hf, hg, hdf, hdg, hM⟩ := polynomial_pair p hp
  have mpos : 0 < M := (Polynomial.mahlerMeasure_pos_of_ne_zero (hp.map _).ne_zero)
  have hdpos : 0 < ‖constantCoeff d‖ := by rw [hM]; exact mpos
  let z : ℂ := constantCoeff d / (M : ℂ)
  have hz : ‖z‖ = 1 := by simp [z, hM, M, Real.norm_eq_abs, abs_of_pos mpos, mpos.ne']
  have hzS : Contractive (C z) := contractive_C (by rw [← Complex.sq_norm, hz]; norm_num)
  have df0 : constantCoeff d * constantCoeff f = ε := by
    simpa only [map_mul, Polynomial.constantCoeff_coe, Polynomial.coeff_map, Int.coe_castRingHom, ε] using congrArg (constantCoeff (R := ℂ)) hdf
  have dg0 : constantCoeff d * constantCoeff g = 1 := by
    simpa only [map_mul, Polynomial.constantCoeff_coe, Polynomial.coeff_map, Polynomial.coeff_zero_reverse, hp.leadingCoeff, map_one] using congrArg (constantCoeff (R := ℂ)) hdg
  have aC := congrArg (map (Int.castRingHom ℂ)) ha
  have ag : g * map (Int.castRingHom ℂ) a = C ε * f := by
    have hd : d ≠ 0 := by intro h; simp [h] at hdpos
    apply mul_left_cancel₀ hd
    rw [← mul_assoc, hdg, mul_left_comm d, hdf]
    simpa [ε] using aC
  refine ⟨C z * (C ε * f), C z * g, a, hzS.mul (eSchur.mul hf), hzS.mul hg, ?_, ?_, ha₀, hane, ?_⟩
  · simp only [map_mul, constantCoeff_C, z, Complex.ofReal_inv]
    calc constantCoeff d / (M : ℂ) * (ε * constantCoeff f)
        = (ε * (constantCoeff d * constantCoeff f)) / M := by ring
      _ = _ := by rw [df0, e2, one_div]
  · simp only [map_mul, constantCoeff_C, z, Complex.ofReal_inv]
    calc constantCoeff d / (M : ℂ) * constantCoeff g = (constantCoeff d * constantCoeff g) / M := by ring
      _ = _ := by rw [dg0, one_div]
  · rw [mul_assoc, ag]

end
end Smyth

/- ===== from Smyth/Main.lean ===== -/

/- The sharp, unrestricted-degree bound for an integer polynomial with
nonzero constant term that differs from both signs of its reciprocal.
Source: C. J. Smyth, Bull. London Math. Soc. 3 (1971), 169–175. -/

namespace Smyth
open Polynomial PowerSeries

private theorem integer_sign {z : ℤ} (hne : z ≠ 0) (hz : ‖(z : ℂ)‖ < 2) :
    z = 1 ∨ z = -1 := by
  rw [Complex.norm_intCast, abs_lt] at hz
  have h1 : -2 < z := by exact_mod_cast hz.1
  have h2 : z < 2 := by exact_mod_cast hz.2
  omega

private theorem monic_unit_bound (p : Polynomial ℤ) (hm : p.Monic)
    (hu : p.coeff 0 = 1 ∨ p.coeff 0 = -1) (hpos : p.reverse ≠ p) (hneg : p.reverse ≠ -p)
    (ρ : ℝ) (hr : 1 < ρ) (hc : ρ^3 = ρ + 1) :
    ρ ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  let M := (p.map (Int.castRingHom ℂ)).mahlerMeasure
  have hm1 : 1 ≤ M := one_le_mahlerMeasure_of_ne_zero hm.ne_zero
  have hm0 : 0 < M := by linarith
  obtain ⟨f,g,a,hf,hg,hf0,hg0,ha0,ha,hfg⟩ := normalized_pair p hm hu hpos hneg
  have f0 : coeff 0 (realPart f) = M⁻¹ := by rw [coeff_realPart, coeff_zero_eq_constantCoeff_apply, hf0]; rfl
  have g0 : coeff 0 (realPart g) = M⁻¹ := by rw [coeff_realPart, coeff_zero_eq_constantCoeff_apply, hg0]; rfl
  have h := sharp_coefficient_bound (finite_compression hf) (finite_compression hg)
    ((realPart_int_mul g a).symm.trans (congrArg realPart hfg)) ha0 ha
    (f0 ▸ inv_pos.mpr hm0) (g0.trans f0.symm)
  rw [f0] at h
  have hm3 : M + 1 ≤ M^3 := by
    calc M + 1 = (M⁻¹^2 + M⁻¹^3) * M^3 := by field_simp
         _ ≤ 1 * M^3 := mul_le_mul_of_nonneg_right h (by positivity)
         _ = M^3 := one_mul _
  change ρ ≤ M
  by_contra! hlt
  have hprod : 0 < (ρ - M) * (ρ^2 + ρ*M + M^2 - 1) := by
    apply mul_pos (sub_pos.mpr hlt)
    nlinarith [sq_nonneg (ρ-1), sq_nonneg (M-1), mul_pos (by linarith : 0<ρ) hm0]
  nlinarith

/-- Smyth's theorem for arbitrary integer polynomials, with the two possible
signs of reciprocity explicitly excluded. The constant is the plastic number. -/
theorem nonreciprocal_mahler_bound (p : Polynomial ℤ) (h0 : p.coeff 0 ≠ 0)
    (hpos : p.reverse ≠ p) (hneg : p.reverse ≠ -p)
    (ρ : ℝ) (hr : 1 < ρ) (hc : ρ^3 = ρ + 1) :
    ρ ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hp : p ≠ 0 := by intro e; simp [e] at h0
  have hr2 : ρ < 2 := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg ρ), sq_nonneg (ρ-1)]
  by_cases hbig : 2 ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure
  · exact hr2.le.trans hbig
  have hsmall := lt_of_not_ge hbig
  have hlead := (p.map (Int.castRingHom ℂ)).leadingCoeff_le_mahlerMeasure.trans_lt hsmall
  rw [leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int] at hlead
  have hcoeff := (norm_coeff_le_choose_mul_mahlerMeasure 0 (p.map (Int.castRingHom ℂ))).trans_lt
    (by simpa using hsmall)
  rw [Polynomial.coeff_map] at hcoeff
  have hu := integer_sign h0 hcoeff
  rcases integer_sign (leadingCoeff_ne_zero.mpr hp) hlead with hm|hm
  · exact monic_unit_bound p hm hu hpos hneg ρ hr hc
  · have hm' : (-p).Monic := by simp [Monic, hm]
    have hu' : (-p).coeff 0 = 1 ∨ (-p).coeff 0 = -1 := by rcases hu with e|e <;> simp [e]
    have hrp : (-p).reverse ≠ -p := by simpa [reverse_neg] using hpos
    have hrn : (-p).reverse ≠ -(-p) := by
      rw [reverse_neg, neg_neg]
      simpa [neg_eq_iff_eq_neg] using hneg
    have hsign (q : ℂ[X]) : (-q).mahlerMeasure = q.mahlerMeasure := by
      have e : -q = Polynomial.C (-1 : ℂ) * q := by simp
      rw [e, mahlerMeasure_mul, mahlerMeasure_const]
      simp
    simpa [hsign] using monic_unit_bound (-p) hm' hu' hrp hrn ρ hr hc

end Smyth

/- ===== from arithmetic-of-time-slowest-clock PdtPisotBoundary.lean (cubic part) ===== -/
namespace PDT
noncomputable section
open Complex

/-- **The cubic settles.** Every non-real root `z` of `x³ − x − 1` has `‖z‖ < 1`:
the transverse mode of `ρ` CONTRACTS, so `ρ` is a Pisot number. -/
theorem cubic_conj_norm_lt_one (z : ℂ) (hz : z ^ 3 = z + 1) (him : z.im ≠ 0) :
    ‖z‖ < 1 := by
  have hz0 : z ≠ 0 := by intro h; apply him; rw [h]; simp
  have hc : (starRingEnd ℂ) z ^ 3 = (starRingEnd ℂ) z + 1 := by
    have h := congrArg (starRingEnd ℂ) hz
    simpa [map_add, map_pow, map_one] using h
  set σ : ℝ := 2 * z.re with hσ
  set s : ℝ := normSq z with hs
  have hspos : 0 < s := by rw [hs]; exact normSq_pos.mpr hz0
  have hsum : z + (starRingEnd ℂ) z = (σ : ℂ) := by rw [add_conj, hσ]
  have hprod : z * (starRingEnd ℂ) z = (s : ℂ) := by rw [mul_conj, hs]
  have hquad : z ^ 2 = (σ : ℂ) * z - (s : ℂ) := by rw [← hsum, ← hprod]; ring
  have hred : z ^ 3 = ((σ:ℂ)^2 - (s:ℂ)) * z - (σ:ℂ)*(s:ℂ) := by
    calc z ^ 3 = z * z ^ 2 := by ring
      _ = z * ((σ:ℂ) * z - (s:ℂ)) := by rw [hquad]
      _ = (σ:ℂ) * z^2 - (s:ℂ)*z := by ring
      _ = (σ:ℂ) * ((σ:ℂ) * z - (s:ℂ)) - (s:ℂ)*z := by rw [hquad]
      _ = ((σ:ℂ)^2 - (s:ℂ)) * z - (σ:ℂ)*(s:ℂ) := by ring
  have hAB : ((σ:ℂ)^2 - (s:ℂ) - 1) * z + (-(σ:ℂ)*(s:ℂ) - 1) = 0 := by
    linear_combination hz - hred
  have hABc : ((σ:ℂ)^2 - (s:ℂ) - 1) * (starRingEnd ℂ) z + (-(σ:ℂ)*(s:ℂ) - 1) = 0 := by
    have h := congrArg (starRingEnd ℂ) hAB
    simpa [map_add, map_mul, map_sub, map_neg, map_pow, map_one, map_ofNat,
      Complex.conj_ofReal] using h
  have hne : z - (starRingEnd ℂ) z ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact him (Complex.conj_eq_iff_im.mp h.symm)
  have hA : (σ:ℂ)^2 - (s:ℂ) - 1 = 0 := by
    have hfac : ((σ:ℂ)^2 - (s:ℂ) - 1) * (z - (starRingEnd ℂ) z) = 0 := by
      linear_combination hAB - hABc
    rcases mul_eq_zero.mp hfac with h | h
    · exact h
    · exact absurd h hne
  have hB : -(σ:ℂ)*(s:ℂ) - 1 = 0 := by linear_combination hAB - z * hA
  have hEqA : σ^2 - s - 1 = 0 := by exact_mod_cast hA
  have hEqB : -σ*s - 1 = 0 := by exact_mod_cast hB
  have hcubic : s^3 + s^2 - 1 = 0 := by linear_combination (-σ*s + 1) * hEqB - s^2 * hEqA
  have hs2lt : s^2 < 1 := by nlinarith [hcubic, pow_pos hspos 3]
  have hs1 : s < 1 := by nlinarith [hs2lt, hspos]
  have hnorm : ‖z‖ ^ 2 = s := by rw [hs]; exact (Complex.normSq_eq_norm_sq z).symm
  nlinarith [norm_nonneg z, hs1, hnorm, sq_nonneg (‖z‖ - 1)]

end
end PDT

/- ===== from arithmetic-of-time-slowest-clock Irreducibility.lean (cubic part) ===== -/


namespace Time

open Polynomial

/-- The cubic x³ - x - 1 over ℤ. -/
noncomputable def cubicZ : ℤ[X] := X ^ 3 - X - 1

lemma cubicZ_monic : (cubicZ).Monic := by
  unfold cubicZ
  monicity!

/-- The image of cubicZ under ℤ → ZMod 2. -/
lemma cubicZ_map2 : cubicZ.map (Int.castRingHom (ZMod 2)) = X ^ 3 + X + 1 := by
  unfold cubicZ
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    have e : (2 : ZMod 2) = 0 := by decide
    calc (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (C_ofNat 2).symm
      _ = C (0 : ZMod 2) := by rw [e]
      _ = 0 := by simp
  linear_combination (-(X : (ZMod 2)[X]) - 1) * h2

/-- x³ + x + 1 is irreducible over 𝔽₂ (it has no root in 𝔽₂). -/
lemma cubic_irred_zmod2 : Irreducible (X ^ 3 + X + 1 : (ZMod 2)[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · -- natDegree ∈ [1,3]
    have hd : (X ^ 3 + X + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!
    rw [Finset.mem_Icc, hd]
    omega
  · -- no root
    intro x
    rw [IsRoot.def]
    simp only [eval_add, eval_pow, eval_X, eval_one]
    fin_cases x <;> decide

/-- x³ - x - 1 is irreducible over ℤ. -/
lemma cubicZ_irred : Irreducible cubicZ := by
  apply cubicZ_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
  rw [cubicZ_map2]
  exact cubic_irred_zmod2

/-- x³ - x - 1 is irreducible over ℚ. -/
theorem cubicQ_irreducible :
    Irreducible (X ^ 3 - X - 1 : ℚ[X]) := by
  have h := (cubicZ_monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp cubicZ_irred
  have hmap : cubicZ.map (algebraMap ℤ ℚ) = (X ^ 3 - X - 1 : ℚ[X]) := by
    unfold cubicZ
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  rwa [hmap] at h

end Time

/- ===== from arithmetic-of-time-slowest-clock Settling.lean and SlowestClock.lean ===== -/
namespace Time
open Polynomial
theorem one_lt_root {r : ℝ} (hr : r ^ 3 = r + 1) : 1 < r := by
  by_contra hle
  rw [not_lt] at hle
  have h1 : 0 ≤ (1 - r) * (r + 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : (1 - r) * (r + 1) ^ 2 = -r ^ 2 := by linear_combination -hr
  have h3 : r ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg r)
  have h4 : r = 0 := sq_eq_zero_iff.mp h3
  rw [h4] at hr
  norm_num at hr

namespace Clock
lemma rho_bounds {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) : 1 < ρ ∧ ρ ≤ 4 / 3 ∧ 4 / 3 < ρ ^ 2 := by
  have h1 : 1 < ρ := one_lt_root hρ
  refine ⟨h1, ?_, ?_⟩
  · nlinarith [sq_nonneg (ρ - 4 / 3), sq_nonneg ρ]
  · nlinarith [sq_nonneg (ρ - 1)]

/-- The real root of `x³ = x + 1` is unique. -/
lemma cubic_root_unique {ρ θ : ℝ} (hρ : ρ ^ 3 = ρ + 1) (hθ : θ ^ 3 = θ + 1) : θ = ρ := by
  obtain ⟨_, _, hρ2⟩ := rho_bounds hρ
  have hfac : (θ - ρ) * (θ ^ 2 + θ * ρ + ρ ^ 2 - 1) = 0 := by linear_combination hθ - hρ
  have hpos : 0 < θ ^ 2 + θ * ρ + ρ ^ 2 - 1 := by nlinarith [sq_nonneg (2 * θ + ρ)]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith

/-- **A Pisot number is the Mahler measure of its minimal polynomial.** -/
lemma mahler_eq_of_pisot {θ : ℝ} (h1 : 1 < θ) (hint : IsIntegral ℤ θ)
    (hpisot : ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1) :
    ((minpoly ℤ θ).map (Int.castRingHom ℂ)).mahlerMeasure = θ := by
  classical
  have hθQ : IsIntegral ℚ θ := hint.tower_top
  have hQ : minpoly ℚ θ = (minpoly ℤ θ).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hpC : (minpoly ℤ θ).map (Int.castRingHom ℂ) = (minpoly ℚ θ).map (algebraMap ℚ ℂ) := by
    rw [hQ, Polynomial.map_map]
    congr 1
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hpC]
  have hlc : ((minpoly ℚ θ).map (algebraMap ℚ ℂ)).leadingCoeff = 1 :=
    ((minpoly.monic hθQ).map _).leadingCoeff
  rw [hlc, norm_one, one_mul]
  change (((minpoly ℚ θ).aroots ℂ).map fun a => max 1 ‖a‖).prod = θ
  have hnodup : ((minpoly ℚ θ).aroots ℂ).Nodup :=
    nodup_roots (PerfectField.separable_of_irreducible (minpoly.irreducible hθQ)).map
  have hmem : (θ : ℂ) ∈ (minpoly ℚ θ).aroots ℂ := by
    rw [mem_aroots]
    refine ⟨minpoly.ne_zero hθQ, ?_⟩
    have : ((θ : ℂ)) = algebraMap ℝ ℂ θ := rfl
    rw [this, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  rw [Multiset.prod_map_eq_pow_single (θ : ℂ) (fun a ha hm => ?_),
    Multiset.count_eq_one_of_mem hnodup hmem, pow_one]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact max_eq_right h1.le
  · exact max_eq_left (hpisot a hm ha).le

end Clock
end Time

/- ===== from Smyth/Siegel.lean (plastic_mem) ===== -/
namespace Smyth.Siegel
open Polynomial
/-- The positive root of the plastic cubic is an algebraic integer and all of
its other conjugates lie strictly inside the unit circle. -/
theorem plastic_mem {ρ : ℝ} (hc : ρ ^ 3 = ρ + 1) :
    IsIntegral ℤ ρ ∧ ∀ z ∈ (minpoly ℚ ρ).aroots ℂ, z ≠ (ρ : ℂ) → ‖z‖ < 1 := by
  have root (K : Type) [CommRing K] [Algebra K ℝ] :
      aeval ρ (X ^ 3 - X - 1 : K[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    linarith
  refine ⟨⟨X ^ 3 - X - 1, by monicity!, root ℤ⟩, ?_⟩
  have hm : minpoly ℚ ρ = X ^ 3 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic Time.cubicQ_irreducible (root ℚ) (by monicity!)).symm
  intro z hz hne
  rw [hm, mem_aroots] at hz
  have he := hz.2
  simp only [map_sub, map_pow, aeval_X, map_one] at he
  have hc' : z ^ 3 = z + 1 := by linear_combination he
  by_cases hi : z.im = 0
  · have hr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hi])
    have hzre : z.re ^ 3 = z.re + 1 := by
      rw [hr] at hc'
      exact_mod_cast hc'
    exact (hne (hr.trans (congrArg Complex.ofReal (Time.Clock.cubic_root_unique hc hzre)))).elim
  · exact PDT.cubic_conj_norm_lt_one z hc' hi

end Smyth.Siegel

/- ===== Glue for this port (not in the original repositories) ===== -/
namespace Glue
open Polynomial

/-- The plastic number exists: a real root `ρ > 1` of `x³ = x + 1`. -/
theorem exists_rho : ∃ ρ : ℝ, 1 < ρ ∧ ρ ^ 3 = ρ + 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc 1 2) := by fun_prop
  obtain ⟨ρ, -, h⟩ := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2) hcont
    (show (0:ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x - 1) 1) ((fun x : ℝ => x ^ 3 - x - 1) 2) by
      norm_num)
  have hc : ρ ^ 3 = ρ + 1 := by simp only at h; linarith
  exact ⟨ρ, Time.one_lt_root hc, hc⟩

/-- `M(x³ - x - 1) = ρ`, from the Pisot property of `ρ` (author's lemmas above). -/
theorem cubic_measure {ρ : ℝ} (hr : 1 < ρ) (hc : ρ ^ 3 = ρ + 1) :
    ((X ^ 3 - X - 1 : ℤ[X]).map (Int.castRingHom ℂ)).mahlerMeasure = ρ := by
  obtain ⟨hint, hpisot⟩ := Smyth.Siegel.plastic_mem hc
  have hroot : aeval ρ (X ^ 3 - X - 1 : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    linarith
  have hQ : minpoly ℚ ρ = X ^ 3 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic Time.cubicQ_irreducible hroot (by monicity!)).symm
  have hm : minpoly ℤ ρ = (X ^ 3 - X - 1 : ℤ[X]) := by
    apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, hQ]
    simp
  rw [← hm]
  exact Time.Clock.mahler_eq_of_pisot hr hint hpisot

theorem measure_unit (g : ℤ[X]) (hg : IsUnit g) : (g.map (Int.castRingHom ℂ)).mahlerMeasure = 1 := by
  obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp hg
  rw [Polynomial.map_C, mahlerMeasure_const]
  rcases Int.isUnit_iff.mp hr with h | h <;> simp [h]

/-- An irreducible `f` with `M(f) > 1` is not divisible by `X`. -/
theorem coeff_zero_ne (f : ℤ[X]) (hi : Irreducible f)
    (hf : 1 < (f.map (Int.castRingHom ℂ)).mahlerMeasure) : f.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨g, hg⟩ := X_dvd_iff.mpr h0
  rcases hi.isUnit_or_isUnit hg with h | h
  · exact not_isUnit_X h
  · rw [hg, Polynomial.map_mul, mahlerMeasure_mul, measure_unit g h, Polynomial.map_X,
      show (X : ℂ[X]) = X - C 0 by simp, mahlerMeasure_X_sub_C] at hf
    norm_num at hf

/-- An irreducible `f` with `M(f) > 1` is not anti-reciprocal: otherwise `f(1) = 0`, so
`f = ±(X - 1)` and `M(f) = 1`. -/
theorem reverse_ne_neg (f : ℤ[X]) (hi : Irreducible f)
    (hf : 1 < (f.map (Int.castRingHom ℂ)).mahlerMeasure) : f.reverse ≠ -f := by
  intro hrev
  letI : Invertible (1 : ℤ) := invertibleOne
  have he := eval₂_reverse_mul_pow (RingHom.id ℤ) (1 : ℤ) f
  rw [hrev] at he
  simp only [invOf_one, one_pow, mul_one, eval₂_neg] at he
  have h1 : f.IsRoot 1 := by
    rw [IsRoot.def, ← eval₂_id]
    omega
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr h1
  rcases hi.isUnit_or_isUnit hg with h | h
  · exact not_isUnit_X_sub_C _ h
  · rw [hg, Polynomial.map_mul, mahlerMeasure_mul, measure_unit g h, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, mahlerMeasure_X_sub_C] at hf
    norm_num at hf

end Glue

end OMAPort_Smyth

open Polynomial in
theorem OMA.solution :
    type_of% @LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem.variants.not_reciprocal := by
  intro f hi hf hf'
  have bridge (p : ℤ[X]) :
      LehmerMahlerMeasureProblem.mahlerMeasureZ p = (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
    rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
    rfl
  rw [gt_iff_lt, bridge] at hf
  obtain ⟨ρ, hr, hc⟩ := OMAPort_Smyth.Glue.exists_rho
  rw [ge_iff_le, bridge, bridge, OMAPort_Smyth.Glue.cubic_measure hr hc]
  exact OMAPort_Smyth.Smyth.nonreciprocal_mahler_bound f (OMAPort_Smyth.Glue.coeff_zero_ne f hi hf)
    hf' (OMAPort_Smyth.Glue.reverse_ne_neg f hi hf) ρ hr hc
