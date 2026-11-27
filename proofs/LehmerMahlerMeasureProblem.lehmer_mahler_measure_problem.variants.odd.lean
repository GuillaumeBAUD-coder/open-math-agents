import FormalConjectures.Wikipedia.LehmerMahlerMeasureProblem

/-
Ported from an existing public Lean proof; the mathematics and the Lean proof are the original author's.
Original: https://github.com/stalex444/golden-mahler-bound-odd/blob/a433fcc7d66394587f5d66347178dbe172a1e787/GoldenMahler/Bound.lean  (theorem GoldenMahlerEntry.odd_mahler_bound, via GoldenMahler.odd_mahler_bound)
  with GoldenMahler/Attainment.lean (GoldenMahler.quadratic_measure) from the same commit, and its dependency
  https://github.com/stalex444/smyth-mahler-bound-rho/blob/41bc4f35be759b02602e2884bf70307d95b9e1c3/Smyth/
  (Contractions.lean, Factorization.lean, Compression.lean, CoefficientBound.lean: only the declarations used here).
  Formalises Borwein, Hare and Mossinghoff, Bull. London Math. Soc. 36 (2004), Corollary 1.2.
Original author: Stephanie Alexander (stalex444)   Licence: MIT (LICENSE in both repositories)
Submitted to lefttosolve.com by @senamakel; ported to Lean v4.33.1 / formal-conjectures 9097e2f.
Changes: inlined the two repositories into one file under namespace OMAPort_Golden, dropped the module
  system headers and unused declarations, and added the bridge from mahlerMeasureZ to Mathlib's
  Polynomial.mahlerMeasure given in the golden-mahler-bound-odd README.

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

namespace OMAPort_Golden


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

/- From Smyth/CoefficientBound.lean (only the first-coefficient estimate). -/
namespace Smyth

/-- Every finite restriction of multiplication by the power series with coefficients
`f` has operator norm at most one on real square-summable sequences. -/
def CoefficientContraction (f : ℕ → ℝ) : Prop :=
  ∀ (I J : Finset ℕ) (u : ℕ → ℝ),
    (∑ i ∈ J, (∑ j ∈ I, if j ≤ i then u j * f (i-j) else 0)^2) ≤
      ∑ j ∈ I, (u j)^2

private theorem compression₂ {f : ℕ → ℝ} (hf : CoefficientContraction f)
    {k : ℕ} (hk : 0 < k) (x y : ℝ) :
    (x*f 0)^2 + (x*f k+y*f 0)^2 ≤ x^2+y^2 := by
  classical
  have h := hf {0,k} {0,k} (fun j => if j = 0 then x else y)
  simpa [Finset.sum_insert, hk.ne', hk.ne, show ¬k ≤ 0 by omega] using h

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

end Smyth


namespace GoldenMahler
open Polynomial
open scoped goldenRatio

/-- The two conjugate roots contribute φ and 1, respectively, to the measure. -/
theorem quadratic_measure :
    (((X^2-X-1 : ℤ[X]).map (Int.castRingHom ℂ))).mahlerMeasure = φ := by
  have hsum : (φ : ℂ) + (ψ : ℂ) = 1 := by exact_mod_cast Real.goldenRatio_add_goldenConj
  have hprod : (φ : ℂ) * (ψ : ℂ) = -1 := by exact_mod_cast Real.goldenRatio_mul_goldenConj
  have hfac : ((X^2-X-1 : ℤ[X]).map (Int.castRingHom ℂ)) =
      (X-C (φ : ℂ))*(X-C (ψ : ℂ)) := by
    simp only [Polynomial.map_sub,Polynomial.map_pow,map_X,Polynomial.map_one]
    have hsum' := congrArg (Polynomial.C : ℂ → ℂ[X]) hsum
    have hprod' := congrArg (Polynomial.C : ℂ → ℂ[X]) hprod
    simp only [map_add,map_mul,map_one,map_neg] at hsum' hprod'
    linear_combination X * hsum' - hprod'
  rw [hfac,mahlerMeasure_mul,mahlerMeasure_X_sub_C,mahlerMeasure_X_sub_C]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.goldenRatio_pos,
    abs_of_neg Real.goldenConj_neg]
  rw [max_eq_right Real.one_lt_goldenRatio.le,
    max_eq_left (by linarith [Real.neg_one_lt_goldenConj] : -ψ ≤ 1), mul_one]

end GoldenMahler



/- The odd-coefficient corollary of Borwein, Hare and Mossinghoff (2004).
We apply the first-coefficient estimate to the first mismatch between the
signed polynomial and its reverse. Its nonzero even size gives the factor 2. -/

namespace GoldenMahler
open Polynomial PowerSeries Smyth
open scoped goldenRatio

/-- At the first nonzero coefficient of a series, multiplication by a second
series uses only the constant term of the second series. -/
private theorem first_product (d s : PowerSeries ℂ) (k : ℕ)
    (h : ∀ i < k, coeff i s = 0) :
    coeff k (d*s) = PowerSeries.constantCoeff d * coeff k s := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single_of_mem (0,k) (by simp)]
  · simp
  · rintro ⟨i,j⟩ hij hne
    have hij' : i+j = k := by simpa using hij
    have hj : j < k := by
      by_contra! hle
      obtain rfl : i = 0 := by omega
      obtain rfl : j = k := by omega
      exact hne rfl
    simp [h j hj]

/-- Rotate a contractive series so its constant term is real. The shared
denominator has constant coefficient D of modulus M and D * f(0) = 1. -/
private theorem rotated_bound {f : PowerSeries ℂ} (hf : Contractive f)
    {D : ℂ} {M : ℝ} (hM : 0 < M) (hD : ‖D‖ = M)
    (h0 : D * PowerSeries.constantCoeff f = 1) {k : ℕ} (hk : 0 < k) :
    |((D / (M : ℂ)) * coeff k f).re| ≤ 1 - M⁻¹ ^ 2 := by
  let z := D / (M : ℂ)
  have hz : ‖z‖ = 1 := by simp [z, hD, Real.norm_eq_abs, abs_of_pos hM, hM.ne']
  have hC : Contractive (PowerSeries.C z) :=
    contractive_C (by rw [← Complex.sq_norm, hz]; norm_num)
  have hzero : z * PowerSeries.constantCoeff f = ((M⁻¹ : ℝ) : ℂ) := by
    dsimp [z]
    rw [div_mul_eq_mul_div, h0, one_div, Complex.ofReal_inv]
  let t := PowerSeries.C z * f
  have H := schur_first (f := fun i => PowerSeries.coeff i (realPart t))
    (finite_compression (f := t) (hC.mul hf)) hk
  have ht0 : coeff 0 (realPart t) = M⁻¹ := by
    rw [coeff_realPart, PowerSeries.coeff_C_mul, coeff_zero_eq_constantCoeff_apply, hzero]
    rfl
  rw [ht0] at H
  simpa only [t, coeff_realPart, PowerSeries.coeff_C_mul] using H

private theorem monic_odd_bound (p : ℤ[X]) (hm : p.Monic)
    (hu : p.coeff 0 = 1 ∨ p.coeff 0 = -1)
    (hpos : p.reverse ≠ p) (hneg : p.reverse ≠ -p)
    (hodd : ∀ i ≤ p.natDegree, Odd (p.coeff i)) :
    Real.goldenRatio ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  classical
  let M := (p.map (Int.castRingHom ℂ)).mahlerMeasure
  have hM : 0 < M := mahlerMeasure_pos_of_ne_zero (hm.map _).ne_zero
  let ε : ℂ := (p.coeff 0 : ℤ)
  have e_cases : ε = 1 ∨ ε = -1 := by rcases hu with e|e <;> simp [ε,e]
  obtain ⟨d,f,g,hf,hg,hdp,hdr,hD⟩ := polynomial_pair p hm
  let u := PowerSeries.C ε * f
  let D := PowerSeries.constantCoeff d
  have hD' : D ≠ 0 := by
    have h : 0 < ‖D‖ := hD.symm ▸ hM
    exact norm_pos_iff.mp h
  have hcu : Contractive u :=
    (contractive_C (by rcases e_cases with e|e <;> simp [e])).mul hf
  have df0 : D * PowerSeries.constantCoeff f = ε := by
    simpa only [D,ε,map_mul,Polynomial.constantCoeff_coe,Polynomial.coeff_map,Int.coe_castRingHom] using congrArg (PowerSeries.constantCoeff (R := ℂ)) hdp
  have du0 : D * PowerSeries.constantCoeff u = 1 := by
    simp only [u,map_mul,PowerSeries.constantCoeff_C]
    rw [mul_left_comm,df0]
    rcases e_cases with e|e <;> simp [e]
  have dg0 : D * PowerSeries.constantCoeff g = 1 := by
    simpa only [D,map_mul,Polynomial.constantCoeff_coe,Polynomial.coeff_map,Polynomial.coeff_zero_reverse,hm.leadingCoeff,map_one] using
      congrArg (PowerSeries.constantCoeff (R := ℂ)) hdr
  let δ (i : ℕ) := p.coeff 0 * p.coeff i - p.reverse.coeff i
  have identity (i : ℕ) : coeff i (d * (u-g)) = (δ i : ℤ) := by
    rw [mul_sub, show d*u = PowerSeries.C ε * (d*f) by dsimp [u]; ring, hdp, hdr]
    simp only [δ, ε, map_sub, PowerSeries.coeff_C_mul, Polynomial.coeff_coe, Polynomial.coeff_map,
      Int.coe_castRingHom]
    push_cast
    ring
  have exists_diff : ∃ k, coeff k (u-g) ≠ 0 := by
    by_contra! he
    have heq : u - g = 0 := by ext i; simpa using he i
    have hδ (i : ℕ) : δ i = 0 := by
      have he' := identity i
      rw [heq, mul_zero, map_zero] at he'
      exact_mod_cast he'.symm
    rcases hu with e|e
    · apply hpos
      ext i
      have h := hδ i
      simp only [δ,e,one_mul,sub_eq_zero] at h
      simpa using h.symm
    · apply hneg
      ext i
      have h := hδ i
      simp only [δ,e,neg_one_mul,sub_eq_zero] at h
      simpa using h.symm
  let k := Nat.find exists_diff
  have hk' : coeff k (u-g) ≠ 0 := Nat.find_spec exists_diff
  have hfirst := first_product d (u-g) k (fun i hi => by
    by_contra H
    exact (Nat.not_lt_of_ge (Nat.find_min' exists_diff H)) hi)
  have hδk : D * coeff k (u-g) = (δ k : ℤ) := hfirst.symm.trans (identity k)
  have hδne : δ k ≠ 0 := by
    intro h
    rw [h,Int.cast_zero] at hδk
    exact hk' ((mul_eq_zero.mp hδk).resolve_left hD')
  have hk : 0 < k := by
    by_contra! hn
    have hk0 : k = 0 := by omega
    apply hδne
    rcases hu with e|e <;> simp [δ,hk0,e,Polynomial.coeff_zero_reverse,hm.leadingCoeff]
  have hdeg : k ≤ p.natDegree := by
    by_contra! hn
    apply hδne
    simp [δ,coeff_eq_zero_of_natDegree_lt hn,
      coeff_eq_zero_of_natDegree_lt (p.reverse_natDegree_le.trans_lt hn)]
  have hrevOdd : Odd (p.reverse.coeff k) := by
    rw [Polynomial.coeff_reverse,revAt_le hdeg]
    exact hodd _ (Nat.sub_le _ _)
  have heven : Even (δ k) :=
    ((hodd 0 (Nat.zero_le _)).mul (hodd k hdeg)).sub_odd hrevOdd
  obtain ⟨b,hb⟩ := heven
  have hsize : 2 ≤ |δ k| := by
    rcases le_or_gt 0 (δ k) with hs|hs
    · rw [abs_of_nonneg hs]; omega
    · rw [abs_of_neg hs]; omega
  have huB := rotated_bound hcu hM hD du0 hk
  have hgB := rotated_bound hg hM hD dg0 hk
  have cdiff : D / (M : ℂ) * coeff k u - D / M * coeff k g = (δ k : ℤ) / (M : ℂ) := by
    rw [← mul_sub, ← map_sub, div_mul_eq_mul_div, hδk]
  have diff := congrArg Complex.re cdiff
  simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.intCast_re] at diff
  have gap : |(δ k : ℝ) / M| ≤ 2 * (1 - M⁻¹ ^ 2) := by
    rw [← diff]
    exact (abs_sub _ _).trans (by linarith)
  have hsize' : (2 : ℝ) ≤ |(δ k : ℝ)| := by exact_mod_cast hsize
  rw [abs_div,abs_of_pos hM] at gap
  have hscalar : 2 / M ≤ 2 * (1 - M⁻¹ ^ 2) :=
    (div_le_div_of_nonneg_right hsize' hM.le).trans gap
  have hquad : M + 1 ≤ M^2 := by
    field_simp [hM.ne'] at hscalar
    nlinarith
  change Real.goldenRatio ≤ M
  by_contra! hlt
  have hprod := mul_pos (sub_pos.mpr hlt)
    (show 0 < Real.goldenRatio + M - 1 by linarith [Real.one_lt_goldenRatio])
  nlinarith [Real.goldenRatio_sq]

/-- Every nonreciprocal integer polynomial with odd coefficients has
multiplicative Mahler measure at least the golden ratio, in every degree. -/
theorem odd_mahler_bound (p : ℤ[X]) (hpos : p.reverse ≠ p) (hneg : p.reverse ≠ -p)
    (hodd : ∀ i ≤ p.natDegree, Odd (p.coeff i)) :
    Real.goldenRatio ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨b,hb⟩ := hodd 0 (Nat.zero_le _)
  have hp0 : p.coeff 0 ≠ 0 := by omega
  have hp : p ≠ 0 := by intro e; simp [e] at hp0
  by_cases hbig : 2 ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure
  · exact Real.goldenRatio_lt_two.le.trans hbig
  have hsmall := lt_of_not_ge hbig
  have sign (z : ℤ) (hz : z ≠ 0) (h : ‖(z : ℂ)‖ < 2) : z = 1 ∨ z = -1 := by
    rw [Complex.norm_intCast,abs_lt] at h
    obtain ⟨h1,h2⟩ := h
    have h1' : -2 < z := by exact_mod_cast h1
    have h2' : z < 2 := by exact_mod_cast h2
    omega
  have hl := (p.map (Int.castRingHom ℂ)).leadingCoeff_le_mahlerMeasure.trans_lt hsmall
  rw [leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int] at hl
  have hc := (norm_coeff_le_choose_mul_mahlerMeasure 0 (p.map (Int.castRingHom ℂ))).trans_lt
    (by simpa using hsmall)
  rw [Polynomial.coeff_map] at hc
  have hu := sign _ hp0 hc
  rcases sign _ (leadingCoeff_ne_zero.mpr hp) hl with h|h
  · exact monic_odd_bound p h hu hpos hneg hodd
  · have hm : (-p).Monic := by simp [Monic,h]
    have hu' : (-p).coeff 0 = 1 ∨ (-p).coeff 0 = -1 := by rcases hu with e|e <;> simp [e]
    have hpos' : (-p).reverse ≠ -p := by simpa [reverse_neg] using hpos
    have hneg' : (-p).reverse ≠ -(-p) := by simpa [reverse_neg,neg_eq_iff_eq_neg] using hneg
    have H := monic_odd_bound (-p) hm hu' hpos' hneg' (fun i hi => by
      simpa using (hodd i (by simpa using hi)).neg)
    have hsign (q : ℂ[X]) : (-q).mahlerMeasure = q.mahlerMeasure := by
      rw [show -q = Polynomial.C (-1 : ℂ) * q by simp,mahlerMeasure_mul,mahlerMeasure_const]
      simp
    simpa [hsign] using H
end GoldenMahler

end OMAPort_Golden

open Polynomial in
theorem OMA.solution : type_of% @LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem.variants.odd := by
  intro f hf hf' hf'' hodd
  have bridge (p : ℤ[X]) :
      LehmerMahlerMeasureProblem.mahlerMeasureZ p = (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
    rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
    rfl
  rw [ge_iff_le, bridge, bridge, OMAPort_Golden.GoldenMahler.quadratic_measure]
  exact OMAPort_Golden.GoldenMahler.odd_mahler_bound f hf' hf'' hodd
