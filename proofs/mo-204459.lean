import OMAStatements.S_mo_204459
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Set.Card
import Mathlib.Topology.Order.Rolle
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Convex.Topology
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Nonvanishing of the oscillatory integral in MathOverflow 204459

Source: https://mathoverflow.net/questions/204459 (Iosif Pinelis).
Credit: @rahul-mahadik.

This proves the complete approved target: every n >= 1, every real a, and
pLow(n,a) < p < n, with an actual nonzero ordinary improper limit.
The proof uses minimal oscillation and vanishing moments of finite differences
of truncated powers, a Cauchy transform, and actual Mellin/logarithmic formulas.
The classical polynomial/Hilbert commutation ingredient is also discussed in
Chen, Huang, Riemenschneider and Xu, Advances in Computational Mathematics 24
(2006), Theorem 5.2. Integer exponents are handled by logarithmic formulas.
-/

open Filter MeasureTheory Polynomial Asymptotics Set Complex ComplexConjugate
open scoped Topology BigOperators

namespace IntegralOrthogonalCauchy

theorem polynomial_moments_of_monomial_moments
    {μ : Measure ℝ} {f : ℝ → ℝ} {d : ℕ}
    (hmom : ∀ k < d, Integrable (fun t => f t * t ^ k) μ ∧
      (∫ t, f t * t ^ k ∂μ) = 0)
    (q : ℝ[X]) (hq : q.degree < (d : WithBot ℕ)) :
    Integrable (fun t => f t * q.eval t) μ ∧
      (∫ t, f t * q.eval t ∂μ) = 0 := by
  classical
  have hk (k : ℕ) (h : k ∈ q.support) : k < d := by
    exact WithBot.coe_lt_coe.mp (lt_of_le_of_lt (q.le_degree_of_mem_supp k h) hq)
  have hi (k : ℕ) (h : k ∈ q.support) :
      Integrable (fun t => q.coeff k * (f t * t ^ k)) μ :=
    ((hmom k (hk k h)).1).const_mul _
  have he (t : ℝ) : f t * q.eval t =
      ∑ k ∈ q.support, q.coeff k * (f t * t ^ k) := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  constructor
  · simp_rw [he]
    exact integrable_finsetSum _ hi
  · simp_rw [he]
    rw [integral_finsetSum _ hi]
    apply Finset.sum_eq_zero
    intro k h
    rw [integral_const_mul, (hmom k (hk k h)).2, mul_zero]

theorem polynomial_weighted_quotient_integral
    {μ : Measure ℝ} [NullSingletonClass μ]
    {f : ℝ → ℝ} (x : ℝ) (q : ℝ[X])
    (hg : Integrable (fun t => f t / (t - x)) μ)
    (hr : Integrable (fun t => f t * (q /ₘ (X - C x)).eval t) μ) :
    (∫ t, f t / (t - x) * q.eval t ∂μ) =
      q.eval x * (∫ t, f t / (t - x) ∂μ) +
        ∫ t, f t * (q /ₘ (X - C x)).eval t ∂μ := by
  have hpoly (t : ℝ) : q.eval t = q.eval x +
      (t - x) * (q /ₘ (X - C x)).eval t := by
    have h := congrArg (fun r : ℝ[X] => r.eval t)
      (Polynomial.modByMonic_add_div q (X - C x))
    simpa using h.symm
  have he : (fun t => f t / (t - x) * q.eval t) =ᵐ[μ]
      (fun t => q.eval x * (f t / (t - x)) +
        f t * (q /ₘ (X - C x)).eval t) := by
    filter_upwards [μ.ae_ne x] with t ht
    rw [hpoly]
    field_simp [sub_ne_zero.mpr ht]
  rw [integral_congr_ae he, integral_add (hg.const_mul _) hr, integral_const_mul]

theorem cauchy_ne_zero_of_polynomial_sign_witness
    {μ : Measure ℝ} [NullSingletonClass μ]
    {f : ℝ → ℝ} (x : ℝ) (q : ℝ[X]) (hq : q ≠ 0)
    (hg : Integrable (fun t => f t / (t - x)) μ)
    (hmom : ∀ r : ℝ[X], r.degree < q.degree →
      Integrable (fun t => f t * r.eval t) μ ∧
        (∫ t, f t * r.eval t ∂μ) = 0)
    (hw : Integrable (fun t => f t / (t - x) * q.eval t) μ)
    (hnonneg : ∀ᵐ t ∂μ, 0 ≤ f t / (t - x) * q.eval t)
    (hpos : 0 < μ (Function.support (fun t => f t / (t - x) * q.eval t))) :
    (∫ t, f t / (t - x) ∂μ) ≠ 0 := by
  have hdeg : (q /ₘ (X - C x)).degree < q.degree :=
    Polynomial.degree_divByMonic_lt _ _ hq (by simp)
  obtain ⟨hr, hz⟩ := hmom _ hdeg
  have hpositive : 0 < ∫ t, f t / (t - x) * q.eval t ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg hw).mpr hpos
  intro hzero
  rw [polynomial_weighted_quotient_integral x q hg hr, hz, hzero,
    mul_zero, zero_add] at hpositive
  exact (lt_irrefl 0) hpositive

theorem cauchy_ne_zero_of_moments_and_sign_witness
    {μ : Measure ℝ} [NullSingletonClass μ]
    {f : ℝ → ℝ} {d : ℕ} (x : ℝ) (q : ℝ[X]) (hq : q ≠ 0)
    (hqdeg : q.degree ≤ (d : WithBot ℕ))
    (hg : Integrable (fun t => f t / (t - x)) μ)
    (hmom : ∀ k < d, Integrable (fun t => f t * t ^ k) μ ∧
      (∫ t, f t * t ^ k ∂μ) = 0)
    (hw : Integrable (fun t => f t / (t - x) * q.eval t) μ)
    (hnonneg : ∀ᵐ t ∂μ, 0 ≤ f t / (t - x) * q.eval t)
    (hpos : 0 < μ (Function.support (fun t => f t / (t - x) * q.eval t))) :
    (∫ t, f t / (t - x) ∂μ) ≠ 0 := by
  apply cauchy_ne_zero_of_polynomial_sign_witness x q hq hg _ hw hnonneg hpos
  intro r hr
  exact polynomial_moments_of_monomial_moments hmom r (hr.trans_le hqdeg)

end IntegralOrthogonalCauchy


namespace IntegralOrthogonalCauchy

theorem integrable_polynomial_weighted_quotient
    {μ : Measure ℝ} [NullSingletonClass μ]
    {f : ℝ → ℝ} (x : ℝ) (q : ℝ[X])
    (hg : Integrable (fun t => f t / (t - x)) μ)
    (hr : Integrable (fun t => f t * (q /ₘ (X - C x)).eval t) μ) :
    Integrable (fun t => f t / (t - x) * q.eval t) μ := by
  have hpoly (t : ℝ) : q.eval t = q.eval x +
      (t - x) * (q /ₘ (X - C x)).eval t := by
    have h := congrArg (fun r : ℝ[X] => r.eval t)
      (Polynomial.modByMonic_add_div q (X - C x))
    simpa using h.symm
  have he : (fun t => f t / (t - x) * q.eval t) =ᵐ[μ]
      (fun t => q.eval x * (f t / (t - x)) +
        f t * (q /ₘ (X - C x)).eval t) := by
    filter_upwards [μ.ae_ne x] with t ht
    rw [hpoly]
    field_simp [sub_ne_zero.mpr ht]
  exact ((hg.const_mul _).add hr).congr he.symm

end IntegralOrthogonalCauchy


namespace IntegralPolynomialSignWitness

lemma zero_free_constant_sign {s : Set ℝ} {f : ℝ → ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hne : ∀ x ∈ s, f x ≠ 0) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ x ∈ s, 0 < ε * f x := by
  by_cases hp : ∃ x ∈ s, 0 < f x
  · obtain ⟨x, hx, hpx⟩ := hp
    refine ⟨1, Or.inl rfl, ?_⟩
    intro y hy
    have hpy : 0 < f y := by
      by_contra h
      have hny : f y < 0 := lt_of_le_of_ne (le_of_not_gt h) (hne y hy)
      obtain ⟨z, hz, hzero⟩ :=
        hs.isPreconnected.intermediate_value hy hx hf ⟨hny.le, hpx.le⟩
      exact hne z hz hzero
    simpa using hpy
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro x hx
    have hn : f x < 0 := lt_of_le_of_ne (le_of_not_gt (fun h => hp ⟨x, hx, h⟩))
      (hne x hx)
    simpa using neg_pos.mpr hn

/-- Select only the roots at which the sign changes. The construction is by
largest-root induction and works for every continuous function, including
multiple or nondifferentiable roots. -/
theorem exists_selected_root_product (Z : Finset ℝ) :
    ∀ (s : Set ℝ) (f : ℝ → ℝ), Convex ℝ s → ContinuousOn f s →
      (∀ x ∈ s, f x = 0 ↔ x ∈ Z) →
      ∃ S : Finset ℝ, S ⊆ Z ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        ∀ x ∈ s, x ∉ Z → 0 < ε * f x * ∏ r ∈ S, (x - r) := by
  classical
  induction Z using Finset.induction_on_max with
  | empty =>
      intro s f hs hf hZ
      obtain ⟨ε, hε, hsign⟩ := zero_free_constant_sign hs hf (by
        intro x hx hz
        simpa using (hZ x hx).mp hz)
      refine ⟨∅, Finset.Subset.refl _, ε, hε, ?_⟩
      intro x hx _
      simpa using hsign x hx
  | insert r Z hmax ih =>
      intro s f hs hf hZ
      have hrZ : r ∉ Z := by
        intro hr
        exact (lt_irrefl r) (hmax r hr)
      obtain ⟨S, hSZ, ε₁, hε₁, hleft⟩ :=
        ih (s ∩ Iio r) f (hs.inter (convex_Iio r))
          (hf.mono inter_subset_left) (by
            intro x hx
            rw [hZ x hx.1]
            simp only [Finset.mem_insert]
            exact or_iff_right (ne_of_lt hx.2))
      have hmaxS (a : ℝ) (ha : a ∈ S) : a < r := hmax a (hSZ ha)
      have hrS : r ∉ S := fun h => hrZ (hSZ h)
      obtain ⟨ε₂, hε₂, hright⟩ :=
        zero_free_constant_sign (hs.inter (convex_Ioi r))
          (hf.mono inter_subset_left) (by
            intro x hx hz
            rcases Finset.mem_insert.mp ((hZ x hx.1).mp hz) with h | h
            · exact (ne_of_gt hx.2) h
            · exact (lt_irrefl x) ((hmax x h).trans hx.2))
      have heps : ε₂ = ε₁ ∨ ε₂ = -ε₁ := by
        rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> norm_num
      rcases heps with heq | heq
      · refine ⟨S, hSZ.trans (Finset.subset_insert _ _), ε₁, hε₁, ?_⟩
        intro x hx hxZ
        have hxr : x ≠ r := by
          intro h
          exact hxZ (h ▸ Finset.mem_insert_self _ _)
        rcases lt_or_gt_of_ne hxr with hlt | hgt
        · exact hleft x ⟨hx, hlt⟩ (fun h => hxZ (Finset.mem_insert_of_mem h))
        · have hp : 0 < ∏ a ∈ S, (x - a) :=
            Finset.prod_pos (fun a ha => sub_pos.mpr ((hmaxS a ha).trans hgt))
          rw [← heq]
          exact mul_pos (hright x ⟨hx, hgt⟩) hp
      · refine ⟨insert r S, Finset.insert_subset_insert r hSZ, ε₂, hε₂, ?_⟩
        intro x hx hxZ
        have hxr : x ≠ r := by
          intro h
          exact hxZ (h ▸ Finset.mem_insert_self _ _)
        rcases lt_or_gt_of_ne hxr with hlt | hgt
        · have h := mul_pos
            (hleft x ⟨hx, hlt⟩ (fun h => hxZ (Finset.mem_insert_of_mem h)))
            (sub_pos.mpr hlt)
          have he : ε₂ * f x * (∏ a ∈ insert r S, (x - a)) =
              (ε₁ * f x * ∏ a ∈ S, (x - a)) * (r - x) := by
            rw [Finset.prod_insert hrS, heq]
            ring
          rwa [he]
        · have hp : 0 < ∏ a ∈ insert r S, (x - a) := by
            apply Finset.prod_pos
            intro a ha
            rcases Finset.mem_insert.mp ha with rfl | ha
            · exact sub_pos.mpr hgt
            · exact sub_pos.mpr ((hmaxS a ha).trans hgt)
          exact mul_pos (hright x ⟨hx, hgt⟩) hp

theorem exists_polynomial_sign_witness {s : Set ℝ} {f : ℝ → ℝ}
    (Z : Finset ℝ) (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hZ : ∀ x ∈ s, f x = 0 ↔ x ∈ Z) :
    ∃ q : ℝ[X], q ≠ 0 ∧ q.natDegree ≤ Z.card ∧
      (∀ x ∈ s, 0 ≤ f x * q.eval x) ∧
      (∀ x ∈ s, x ∉ Z → 0 < f x * q.eval x) := by
  classical
  obtain ⟨S, hSZ, ε, hε, hsign⟩ := exists_selected_root_product Z s f hs hf hZ
  let q : ℝ[X] := C ε * ∏ r ∈ S, (X - C r)
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hq : q ≠ 0 := by
    dsimp only [q]
    exact mul_ne_zero (C_ne_zero.mpr hεne)
      (Finset.prod_ne_zero_iff.mpr (fun r _ => X_sub_C_ne_zero r))
  have he (x : ℝ) : f x * q.eval x = ε * f x * ∏ r ∈ S, (x - r) := by
    simp only [q, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    ring
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · calc
      q.natDegree ≤ (∏ r ∈ S, (X - C r : ℝ[X])).natDegree := natDegree_C_mul_le _ _
      _ ≤ ∑ r ∈ S, (X - C r : ℝ[X]).natDegree := Polynomial.natDegree_prod_le S _
      _ = S.card := by simp
      _ ≤ Z.card := Finset.card_le_card hSZ
  · intro x hx
    by_cases h : x ∈ Z
    · rw [(hZ x hx).mpr h, zero_mul]
    · exact (he x ▸ hsign x hx h).le
  · intro x hx h
    rw [he]
    exact hsign x hx h

end IntegralPolynomialSignWitness


namespace IntegralPolynomialSignMoments

open MeasureTheory Set Polynomial

/-- A nonzero continuous real function with d vanishing moments has at least d
roots, whenever its zero set on an open convex domain is finite. No simplicity
or assumed sign-pattern hypothesis is used. -/
theorem card_zeros_ge_of_vanishing_moments
    {μ : Measure ℝ} [μ.IsOpenPosMeasure]
    {s : Set ℝ} {f : ℝ → ℝ} {d : ℕ}
    (Z : Finset ℝ) (hs : Convex ℝ s) (hopen : IsOpen s)
    (hf : ContinuousOn f s)
    (hZ : ∀ x ∈ s, f x = 0 ↔ x ∈ Z)
    (hne : ∃ x ∈ s, f x ≠ 0)
    (hmom : ∀ k < d, Integrable (fun t => f t * t ^ k) (μ.restrict s) ∧
      (∫ t, f t * t ^ k ∂μ.restrict s) = 0) :
    d ≤ Z.card := by
  classical
  by_contra h
  have hcard : Z.card < d := Nat.lt_of_not_ge h
  obtain ⟨q, hq, hdeg, hnonneg, hpos⟩ :=
    IntegralPolynomialSignWitness.exists_polynomial_sign_witness Z hs hf hZ
  have hqdeg : q.degree < (d : WithBot ℕ) := by
    rw [degree_eq_natDegree hq]
    exact WithBot.coe_lt_coe.mpr (hdeg.trans_lt hcard)
  obtain ⟨hint, hz⟩ :=
    IntegralOrthogonalCauchy.polynomial_moments_of_monomial_moments hmom q hqdeg
  have hnn : 0 ≤ᵐ[μ.restrict s] (fun t => f t * q.eval t) := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with t ht
    exact hnonneg t ht
  have heq : (fun t => f t * q.eval t) =ᵐ[μ.restrict s] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hz
  have hall := Measure.eqOn_open_of_ae_eq heq hopen
    (hf.mul q.continuous.continuousOn) continuousOn_const
  obtain ⟨x, hx, hfx⟩ := hne
  have hxZ : x ∉ Z := fun h => hfx ((hZ x hx).mpr h)
  have hp := hpos x hx hxZ
  have he := hall hx
  exact (ne_of_gt hp) he

/-- Half-line form used by the truncated-power moment argument. -/
theorem card_positive_zeros_ge_of_vanishing_moments
    {μ : Measure ℝ} [μ.IsOpenPosMeasure]
    {f : ℝ → ℝ} {d : ℕ}
    (Z : Finset ℝ) (hf : ContinuousOn f (Ioi 0))
    (hZ : ∀ x, 0 < x → (f x = 0 ↔ x ∈ Z))
    (hne : ∃ x, 0 < x ∧ f x ≠ 0)
    (hmom : ∀ k < d, Integrable (fun t => f t * t ^ k) (μ.restrict (Ioi 0)) ∧
      (∫ t, f t * t ^ k ∂μ.restrict (Ioi 0)) = 0) :
    d ≤ Z.card :=
  card_zeros_ge_of_vanishing_moments Z (convex_Ioi 0) isOpen_Ioi hf hZ hne hmom

end IntegralPolynomialSignMoments


namespace IntegralPolynomialSignMoments

open MeasureTheory Set Polynomial

/-- When the number of roots is the minimal number forced by the moments,
every root occurs in the polynomial sign witness. No derivative simplicity
hypothesis is needed for this conclusion. -/
theorem full_root_product_sign_of_minimal_zeros
    {μ : Measure ℝ} [μ.IsOpenPosMeasure]
    {s : Set ℝ} {f : ℝ → ℝ}
    (Z : Finset ℝ) (hs : Convex ℝ s) (hopen : IsOpen s)
    (hf : ContinuousOn f s)
    (hZ : ∀ x ∈ s, f x = 0 ↔ x ∈ Z)
    (hne : ∃ x ∈ s, f x ≠ 0)
    (hmom : ∀ k < Z.card,
      Integrable (fun t => f t * t ^ k) (μ.restrict s) ∧
        (∫ t, f t * t ^ k ∂μ.restrict s) = 0) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ x ∈ s, x ∉ Z → 0 < ε * f x * ∏ r ∈ Z, (x - r) := by
  classical
  obtain ⟨S, hSZ, ε, hε, hsign⟩ :=
    IntegralPolynomialSignWitness.exists_selected_root_product Z s f hs hf hZ
  have hcard : Z.card ≤ S.card := by
    by_contra hn
    have hlt : S.card < Z.card := Nat.lt_of_not_ge hn
    let q : ℝ[X] := C ε * ∏ r ∈ S, (X - C r)
    have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    have hq : q ≠ 0 := by
      exact mul_ne_zero (C_ne_zero.mpr hεne)
        (Finset.prod_ne_zero_iff.mpr (fun r _ => X_sub_C_ne_zero r))
    have hqdeg : q.natDegree ≤ S.card := by
      calc
        q.natDegree ≤ (∏ r ∈ S, (X - C r : ℝ[X])).natDegree := natDegree_C_mul_le _ _
        _ ≤ ∑ r ∈ S, (X - C r : ℝ[X]).natDegree := Polynomial.natDegree_prod_le S _
        _ = S.card := by simp
    have he (x : ℝ) : f x * q.eval x = ε * f x * ∏ r ∈ S, (x - r) := by
      simp only [q, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
      ring
    have hqdegree : q.degree < (Z.card : WithBot ℕ) := by
      rw [degree_eq_natDegree hq]
      exact WithBot.coe_lt_coe.mpr (hqdeg.trans_lt hlt)
    obtain ⟨hint, hz⟩ :=
      IntegralOrthogonalCauchy.polynomial_moments_of_monomial_moments hmom q hqdegree
    have hnn : 0 ≤ᵐ[μ.restrict s] (fun t => f t * q.eval t) := by
      filter_upwards [ae_restrict_mem hopen.measurableSet] with t ht
      change (0 : ℝ) ≤ f t * q.eval t
      by_cases hz : t ∈ Z
      · simp only [(hZ t ht).mpr hz, zero_mul, le_refl]
      · rw [he]
        exact (hsign t ht hz).le
    have heq : (fun t => f t * q.eval t) =ᵐ[μ.restrict s] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hz
    have hall := Measure.eqOn_open_of_ae_eq heq hopen
      (hf.mul q.continuous.continuousOn) continuousOn_const
    obtain ⟨x, hx, hfx⟩ := hne
    have hxZ : x ∉ Z := fun h => hfx ((hZ x hx).mpr h)
    have hp := hsign x hx hxZ
    have hxzero : f x * q.eval x = 0 := hall hx
    rw [he] at hxzero
    exact (ne_of_gt hp) hxzero
  have hSZeq : S = Z := Finset.eq_of_subset_of_card_le hSZ hcard
  subst S
  exact ⟨ε, hε, hsign⟩

end IntegralPolynomialSignMoments


namespace IntegralMinimalCauchy

open MeasureTheory Set Polynomial

/-- Minimal oscillation plus genuine vanishing moments forces a nonzero
ordinary Cauchy quotient at any root where that quotient is integrable. -/
theorem cauchy_ne_zero_at_minimal_root
    {μ : Measure ℝ} [μ.IsOpenPosMeasure] [NullSingletonClass μ]
    {s : Set ℝ} {f : ℝ → ℝ}
    (Z : Finset ℝ) (hs : Convex ℝ s) (hopen : IsOpen s)
    (hf : ContinuousOn f s)
    (hZ : ∀ t ∈ s, f t = 0 ↔ t ∈ Z)
    (hne : ∃ t ∈ s, f t ≠ 0)
    (hmom : ∀ k < Z.card,
      Integrable (fun t => f t * t ^ k) (μ.restrict s) ∧
        (∫ t, f t * t ^ k ∂μ.restrict s) = 0)
    (x : ℝ) (hxZ : x ∈ Z)
    (hg : Integrable (fun t => f t / (t - x)) (μ.restrict s)) :
    (∫ t, f t / (t - x) ∂μ.restrict s) ≠ 0 := by
  classical
  obtain ⟨ε, hε, hsign⟩ :=
    IntegralPolynomialSignMoments.full_root_product_sign_of_minimal_zeros
      Z hs hopen hf hZ hne hmom
  let P : ℝ[X] := C ε * ∏ r ∈ Z, (X - C r)
  let q : ℝ[X] := C ε * ∏ r ∈ Z.erase x, (X - C r)
  let w : ℝ → ℝ := fun t => f t / (t - x) * q.eval t
  let v : ℝ → ℝ := fun t => f t * P.eval t
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hq : q ≠ 0 := by
    exact mul_ne_zero (C_ne_zero.mpr hεne)
      (Finset.prod_ne_zero_iff.mpr (fun r _ => X_sub_C_ne_zero r))
  have hqdeg : q.degree ≤ (Z.card : WithBot ℕ) := by
    rw [degree_eq_natDegree hq]
    apply WithBot.coe_le_coe.mpr
    calc
      q.natDegree ≤ (∏ r ∈ Z.erase x, (X - C r : ℝ[X])).natDegree := natDegree_C_mul_le _ _
      _ ≤ ∑ r ∈ Z.erase x, (X - C r : ℝ[X]).natDegree := Polynomial.natDegree_prod_le _ _
      _ = (Z.erase x).card := by simp
      _ ≤ Z.card := Finset.card_le_card (Finset.erase_subset _ _)
  have hPeval (t : ℝ) : P.eval t = (t - x) * q.eval t := by
    simp only [P, q, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    rw [← Finset.mul_prod_erase Z (fun r => t - r) hxZ]
    ring
  have hv (t : ℝ) : v t = ε * f t * ∏ r ∈ Z, (t - r) := by
    dsimp only [v]
    simp only [P, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    ring
  have hfactor (t : ℝ) : v t = (t - x) ^ 2 * w t := by
    dsimp only [v, w]
    rw [hPeval]
    by_cases ht : t = x
    · simp [ht]
    · field_simp [sub_ne_zero.mpr ht]
  have hvnonneg (t : ℝ) (ht : t ∈ s) : 0 ≤ v t := by
    by_cases htZ : t ∈ Z
    · dsimp only [v]
      rw [(hZ t ht).mpr htZ, zero_mul]
    · rw [hv]
      exact (hsign t ht htZ).le
  have hwnonneg : ∀ᵐ t ∂μ.restrict s, 0 ≤ w t := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with t ht
    by_cases htx : t = x
    · simp [w, htx]
    · by_contra hn
      have hm : (t - x) ^ 2 * w t < 0 :=
        mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (sub_ne_zero.mpr htx)) (lt_of_not_ge hn)
      rw [← hfactor] at hm
      exact (not_lt_of_ge (hvnonneg t ht)) hm
  have hwpos : 0 < (μ.restrict s) (Function.support w) := by
    by_contra hn
    have hmzero : (μ.restrict s) (Function.support w) = 0 :=
      le_antisymm (le_of_not_gt hn) bot_le
    have hwzero : w =ᵐ[μ.restrict s] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      simpa only [Function.support, Pi.zero_apply] using hmzero
    have hvzero : v =ᵐ[μ.restrict s] 0 := by
      filter_upwards [hwzero] with t ht
      change v t = 0
      change w t = 0 at ht
      rw [hfactor, ht, mul_zero]
    have hall := Measure.eqOn_open_of_ae_eq hvzero hopen
      (hf.mul P.continuous.continuousOn) continuousOn_const
    obtain ⟨t, ht, hft⟩ := hne
    have htZ : t ∉ Z := fun h => hft ((hZ t ht).mpr h)
    have hp : 0 < v t := by rw [hv]; exact hsign t ht htZ
    exact (ne_of_gt hp) (hall ht)
  have hdeg : (q /ₘ (X - C x)).degree < q.degree :=
    Polynomial.degree_divByMonic_lt _ _ hq (by simp)
  have hr := (IntegralOrthogonalCauchy.polynomial_moments_of_monomial_moments
    hmom (q /ₘ (X - C x)) (hdeg.trans_le hqdeg)).1
  have hw := IntegralOrthogonalCauchy.integrable_polynomial_weighted_quotient x q hg hr
  apply IntegralOrthogonalCauchy.cauchy_ne_zero_of_moments_and_sign_witness
    x q hq hqdeg hg hmom hw hwnonneg hwpos

end IntegralMinimalCauchy


namespace IntegralMinimalCauchy

open MeasureTheory Set Polynomial

/-- Outside either end of the support, the full root polynomial is a strict
sign witness. Endpoints are included whenever the quotient is integrable. -/
theorem cauchy_ne_zero_outside_minimal_roots
    {μ : Measure ℝ} [μ.IsOpenPosMeasure] [NullSingletonClass μ]
    {s : Set ℝ} {f : ℝ → ℝ}
    (Z : Finset ℝ) (hs : Convex ℝ s) (hopen : IsOpen s)
    (hf : ContinuousOn f s)
    (hZ : ∀ t ∈ s, f t = 0 ↔ t ∈ Z)
    (hne : ∃ t ∈ s, f t ≠ 0)
    (hmom : ∀ k < Z.card,
      Integrable (fun t => f t * t ^ k) (μ.restrict s) ∧
        (∫ t, f t * t ^ k ∂μ.restrict s) = 0)
    (x : ℝ) (hside : (∀ t ∈ s, x < t) ∨ (∀ t ∈ s, t < x))
    (hg : Integrable (fun t => f t / (t - x)) (μ.restrict s)) :
    (∫ t, f t / (t - x) ∂μ.restrict s) ≠ 0 := by
  classical
  obtain ⟨ε, hε, hsign⟩ :=
    IntegralPolynomialSignMoments.full_root_product_sign_of_minimal_zeros
      Z hs hopen hf hZ hne hmom
  obtain ⟨σ, hσ, hside'⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ t ∈ s, 0 < σ * (t - x) := by
    rcases hside with hl | hr
    · exact ⟨1, Or.inl rfl, fun t ht => by simpa using sub_pos.mpr (hl t ht)⟩
    · exact ⟨-1, Or.inr rfl, fun t ht => by have h := hr t ht; linarith⟩
  let P : ℝ[X] := C ε * ∏ r ∈ Z, (X - C r)
  let q : ℝ[X] := C σ * P
  let w : ℝ → ℝ := fun t => f t / (t - x) * q.eval t
  let v : ℝ → ℝ := fun t => f t * P.eval t
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hP : P ≠ 0 := by
    exact mul_ne_zero (C_ne_zero.mpr hεne)
      (Finset.prod_ne_zero_iff.mpr (fun r _ => X_sub_C_ne_zero r))
  have hq : q ≠ 0 := mul_ne_zero (C_ne_zero.mpr hσne) hP
  have hqdeg : q.degree ≤ (Z.card : WithBot ℕ) := by
    rw [degree_eq_natDegree hq]
    apply WithBot.coe_le_coe.mpr
    calc
      q.natDegree ≤ P.natDegree := natDegree_C_mul_le _ _
      _ ≤ (∏ r ∈ Z, (X - C r : ℝ[X])).natDegree := natDegree_C_mul_le _ _
      _ ≤ ∑ r ∈ Z, (X - C r : ℝ[X]).natDegree := Polynomial.natDegree_prod_le _ _
      _ = Z.card := by simp
  have hv (t : ℝ) : v t = ε * f t * ∏ r ∈ Z, (t - r) := by
    dsimp only [v]
    simp only [P, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    ring
  have hfactor (t : ℝ) (ht : t ∈ s) : v t = (σ * (t - x)) * w t := by
    have htx : t - x ≠ 0 := by
      intro hz
      have hp := hside' t ht
      simp [hz] at hp
    dsimp only [v, w, q]
    simp only [eval_mul, eval_C]
    rcases hσ with rfl | rfl <;> field_simp [htx]
  have hvnonneg (t : ℝ) (ht : t ∈ s) : 0 ≤ v t := by
    by_cases htZ : t ∈ Z
    · dsimp only [v]
      rw [(hZ t ht).mpr htZ, zero_mul]
    · rw [hv]
      exact (hsign t ht htZ).le
  have hwnonneg : ∀ᵐ t ∂μ.restrict s, 0 ≤ w t := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with t ht
    by_contra hn
    have hm : (σ * (t - x)) * w t < 0 :=
      mul_neg_of_pos_of_neg (hside' t ht) (lt_of_not_ge hn)
    rw [← hfactor t ht] at hm
    exact (not_lt_of_ge (hvnonneg t ht)) hm
  have hwpos : 0 < (μ.restrict s) (Function.support w) := by
    by_contra hn
    have hmzero : (μ.restrict s) (Function.support w) = 0 :=
      le_antisymm (le_of_not_gt hn) bot_le
    have hwzero : w =ᵐ[μ.restrict s] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      simpa only [Function.support, Pi.zero_apply] using hmzero
    have hvzero : v =ᵐ[μ.restrict s] 0 := by
      filter_upwards [hwzero, ae_restrict_mem hopen.measurableSet] with t ht hts
      change v t = 0
      change w t = 0 at ht
      rw [hfactor t hts, ht, mul_zero]
    have hall := Measure.eqOn_open_of_ae_eq hvzero hopen
      (hf.mul P.continuous.continuousOn) continuousOn_const
    obtain ⟨t, ht, hft⟩ := hne
    have htZ : t ∉ Z := fun h => hft ((hZ t ht).mpr h)
    have hp : 0 < v t := by rw [hv]; exact hsign t ht htZ
    exact (ne_of_gt hp) (hall ht)
  have hdeg : (q /ₘ (X - C x)).degree < q.degree :=
    Polynomial.degree_divByMonic_lt _ _ hq (by simp)
  have hr := (IntegralOrthogonalCauchy.polynomial_moments_of_monomial_moments
    hmom (q /ₘ (X - C x)) (hdeg.trans_le hqdeg)).1
  have hw := IntegralOrthogonalCauchy.integrable_polynomial_weighted_quotient x q hg hr
  apply IntegralOrthogonalCauchy.cauchy_ne_zero_of_moments_and_sign_witness
    x q hq hqdeg hg hmom hw hwnonneg hwpos

end IntegralMinimalCauchy


namespace IntegralBinomialPrefix

open Finset

noncomputable def prefixSum (n j : ℕ) (z : ℝ) : ℝ :=
  ∑ l ∈ range (j + 1), (-1 : ℝ)^l * (n.choose l : ℝ) * z^l

theorem prefix_zero (n : ℕ) (z : ℝ) : prefixSum n 0 z = 1 := by
  simp [prefixSum]

theorem prefix_succ_succ (n j : ℕ) (z : ℝ) :
    prefixSum (n+1) (j+1) z = prefixSum n (j+1) z - z * prefixSum n j z := by
  have ht (l : ℕ) :
      (-1 : ℝ)^(l+1) * ((n+1).choose (l+1) : ℝ) * z^(l+1) =
        (-1 : ℝ)^(l+1) * (n.choose (l+1) : ℝ) * z^(l+1) -
          z * ((-1 : ℝ)^l * (n.choose l : ℝ) * z^l) := by
    rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ, pow_succ]
    ring
  have hs (m : ℕ) : prefixSum m (j+1) z =
      (∑ l ∈ range (j+1), (-1 : ℝ)^(l+1) * (m.choose (l+1) : ℝ) * z^(l+1)) + 1 := by
    unfold prefixSum
    rw [sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [hs (n+1), hs n]
  rw [sum_congr rfl (fun l _ => ht l), sum_sub_distrib, ← mul_sum]
  unfold prefixSum
  ring

theorem prefix_full (n : ℕ) (z : ℝ) : prefixSum n n z = (1-z)^n := by
  have h := add_pow (-z) (1 : ℝ) n
  have he : -z + (1 : ℝ) = 1-z := by ring
  rw [he] at h
  rw [prefixSum, h]
  apply sum_congr rfl
  intro l hl
  simp only [one_pow, mul_one]
  rw [neg_pow z l]
  ring

theorem signed_full_nonneg (n : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    0 ≤ (-1 : ℝ)^n * prefixSum n n z := by
  rw [prefix_full, ← mul_pow]
  have he : (-1 : ℝ) * (1-z) = z-1 := by ring
  rw [he]
  exact pow_nonneg (sub_nonneg.mpr hz) n

theorem signed_full_pos (n : ℕ) (z : ℝ) (hz : 1 < z) :
    0 < (-1 : ℝ)^n * prefixSum n n z := by
  rw [prefix_full, ← mul_pow]
  have he : (-1 : ℝ) * (1-z) = z-1 := by ring
  rw [he]
  exact pow_pos (sub_pos.mpr hz) n

theorem signed_prefix_pos (n j : ℕ) (hj : j < n) (z : ℝ) (hz : 1 ≤ z) :
    0 < (-1 : ℝ)^j * prefixSum n j z := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [prefix_zero]
    | succ j =>
      have hjn : j < n := by omega
      have hsmall := ih j hjn
      have hfirst : 0 ≤ (-1 : ℝ)^(j+1) * prefixSum n (j+1) z := by
        by_cases hlt : j+1 < n
        · exact (ih (j+1) hlt).le
        · have he : j+1 = n := by omega
          simpa only [he] using signed_full_nonneg n z hz
      have hsecond : 0 < z * ((-1 : ℝ)^j * prefixSum n j z) :=
        mul_pos (lt_of_lt_of_le zero_lt_one hz) hsmall
      rw [prefix_succ_succ]
      have he : (-1 : ℝ)^(j+1) *
          (prefixSum n (j+1) z - z * prefixSum n j z) =
          (-1 : ℝ)^(j+1) * prefixSum n (j+1) z +
            z * ((-1 : ℝ)^j * prefixSum n j z) := by
        rw [pow_succ]
        ring
      rw [he]
      exact add_pos_of_nonneg_of_pos hfirst hsecond

theorem signed_prefix_pos_of_one_lt (n j : ℕ) (hj : j ≤ n)
    (z : ℝ) (hz : 1 < z) :
    0 < (-1 : ℝ)^j * prefixSum n j z := by
  obtain hlt | he := hj.lt_or_eq
  · exact signed_prefix_pos n j hlt z hz.le
  · subst j
    exact signed_full_pos n z hz

theorem prefix_ne_zero (n j : ℕ) (hj : j ≤ n) (z : ℝ) (hz : 1 < z) :
    prefixSum n j z ≠ 0 := by
  have h := signed_prefix_pos_of_one_lt n j hj z hz
  intro he
  simp only [he, mul_zero, lt_self_iff_false] at h

end IntegralBinomialPrefix


namespace IntegralNegativePowerPrefix

open MeasureTheory Set Finset
open IntegralBinomialPrefix

lemma negative_power_kernel_integrable (q y : ℝ) (hq : q < 0) (hy : 0 < y) :
    IntegrableOn (fun u : ℝ => u^(-q-1) * Real.exp (-(y*u))) (Set.Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -q-1)
      (b := y) (by linarith) zero_lt_one hy)

lemma negative_power_kernel_integral (q y : ℝ) (hq : q < 0) (hy : 0 < y) :
    (∫ u : ℝ in Set.Ioi 0, u^(-q-1) * Real.exp (-(y*u))) = y^q * Real.Gamma (-q) := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < -q) hy]
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow, neg_neg]

/-- A negative-power prefix has a strict sign, for every negative exponent.
This is the analytic sign base for the truncated-power zero count. -/
theorem signed_negative_power_prefix_pos (n j : ℕ) (hj : j ≤ n)
    (q t : ℝ) (hq : q < 0) (ht : (j : ℝ) < t) :
    0 < (-1 : ℝ)^j *
      (∑ l ∈ range (j+1), (-1 : ℝ)^l * (n.choose l : ℝ) * (t-l)^q) := by
  let K (u : ℝ) : ℝ := ∑ l ∈ range (j+1),
    (-1 : ℝ)^l * (n.choose l : ℝ) *
      (u^(-q-1) * Real.exp (-((t-l)*u)))
  have htl (l : ℕ) (hl : l ∈ range (j+1)) : 0 < t-(l : ℝ) := by
    have hlj : l ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
    have hcast : (l : ℝ) ≤ j := by exact_mod_cast hlj
    linarith
  have hInt (l : ℕ) (hl : l ∈ range (j+1)) :
      IntegrableOn (fun u : ℝ => (-1 : ℝ)^l * (n.choose l : ℝ) *
        (u^(-q-1) * Real.exp (-((t-l)*u)))) (Set.Ioi 0) :=
    (negative_power_kernel_integrable q (t-l) hq (htl l hl)).const_mul _
  have hKI : IntegrableOn K (Set.Ioi 0) := integrable_finsetSum _ hInt
  have hKIntegral : (∫ u : ℝ in Set.Ioi 0, K u) =
      (∑ l ∈ range (j+1), (-1 : ℝ)^l * (n.choose l : ℝ) * (t-l)^q) *
        Real.Gamma (-q) := by
    unfold K
    rw [integral_finsetSum _ hInt]
    rw [sum_mul]
    apply sum_congr rfl
    intro l hl
    rw [integral_const_mul, negative_power_kernel_integral q (t-l) hq (htl l hl)]
    ring
  have hK (u : ℝ) : K u = u^(-q-1) * Real.exp (-t*u) * prefixSum n j (Real.exp u) := by
    unfold K prefixSum
    rw [mul_sum]
    apply sum_congr rfl
    intro l hl
    have he : Real.exp (-((t-(l : ℝ))*u)) = Real.exp (-t*u) * (Real.exp u)^l := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  let H (u : ℝ) := (-1 : ℝ)^j * K u
  have hHI : IntegrableOn H (Set.Ioi 0) := hKI.const_mul _
  have hpos (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) : 0 < H u := by
    have hu' : 0 < u := hu
    have hpoly := signed_prefix_pos_of_one_lt n j hj (Real.exp u)
      (Real.one_lt_exp_iff.mpr hu')
    have he : H u = (u^(-q-1) * Real.exp (-t*u)) *
        ((-1 : ℝ)^j * prefixSum n j (Real.exp u)) := by
      dsimp only [H]
      rw [hK]
      ring
    rw [he]
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos hu' _) (Real.exp_pos _)) hpoly
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] H := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hpos u hu).le
  have hsupp : Function.support H ∩ Ioi (0 : ℝ) = Set.Ioi 0 := by
    ext u
    constructor
    · exact And.right
    · intro hu
      exact ⟨(hpos u hu).ne', hu⟩
  have hIntegralPos : 0 < ∫ u : ℝ in Set.Ioi 0, H u := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hHI).mpr
    rw [hsupp]
    simp
  dsimp only [H] at hIntegralPos
  rw [integral_const_mul, hKIntegral] at hIntegralPos
  have he : (-1 : ℝ)^j *
      ((∑ l ∈ range (j+1), (-1 : ℝ)^l * (n.choose l : ℝ) * (t-l)^q) *
        Real.Gamma (-q)) =
      ((-1 : ℝ)^j * (∑ l ∈ range (j+1), (-1 : ℝ)^l * (n.choose l : ℝ) * (t-l)^q)) *
        Real.Gamma (-q) := by ring
  rw [he] at hIntegralPos
  exact pos_of_mul_pos_left hIntegralPos (Real.Gamma_pos_of_pos (neg_pos.mpr hq)).le

end IntegralNegativePowerPrefix


namespace IntegralTruncatedPower

noncomputable def truncatedPower (p x : ℝ) : ℝ :=
  if 0 < p then (max x 0) ^ p else if 0 < x then x ^ p else 0

noncomputable def T (n : ℕ) (p t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ j * (n.choose j : ℝ) * truncatedPower p (t - (j : ℝ))

lemma truncatedPower_eq_active (p x : ℝ) :
    truncatedPower p x = if 0 < x then x ^ p else 0 := by
  by_cases hp : 0 < p
  · by_cases hx : 0 < x
    · simp [truncatedPower, hp, hx, max_eq_left hx.le]
    · simp [truncatedPower, hp, hx, max_eq_right (le_of_not_gt hx),
        Real.zero_rpow (ne_of_gt hp)]
  · simp [truncatedPower, hp]

lemma truncatedPower_of_pos (p : ℝ) {x : ℝ} (hx : 0 < x) :
    truncatedPower p x = x ^ p := by
  simp [truncatedPower_eq_active, hx]

lemma truncatedPower_of_nonpos (p : ℝ) {x : ℝ} (hx : x ≤ 0) :
    truncatedPower p x = 0 := by
  simp [truncatedPower_eq_active, not_lt.mpr hx]

lemma truncatedPower_eq_max_rpow {p : ℝ} (hp : 0 < p) (x : ℝ) :
    truncatedPower p x = (max x 0) ^ p := by
  simp [truncatedPower, hp]

lemma truncatedPower_nonneg (p x : ℝ) : 0 ≤ truncatedPower p x := by
  rw [truncatedPower_eq_active]
  split_ifs with hx
  · exact Real.rpow_nonneg hx.le _
  · exact le_rfl

lemma truncatedPower_pos (p : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < truncatedPower p x := by
  rw [truncatedPower_of_pos p hx]
  exact Real.rpow_pos_of_pos hx _

lemma T_eq_zero_of_nonpos (n : ℕ) (p : ℝ) {t : ℝ} (ht : t ≤ 0) :
    T n p t = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [truncatedPower_of_nonpos p (by linarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j] : t - (j : ℝ) ≤ 0)]
  simp

lemma continuous_truncatedPower {p : ℝ} (hp : 0 < p) :
    Continuous (truncatedPower p) := by
  change Continuous (fun x => if 0 < p then (max x 0) ^ p else
    if 0 < x then x ^ p else 0)
  simp only [if_pos hp]
  exact (continuous_id.max continuous_const).rpow_const fun _ => Or.inr hp.le

lemma continuous_T (n : ℕ) {p : ℝ} (hp : 0 < p) : Continuous (T n p) := by
  unfold T
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul ((continuous_truncatedPower hp).comp
    (continuous_id.sub continuous_const))

lemma hasDerivAt_truncatedPower_of_pos (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (truncatedPower p) (p * truncatedPower (p - 1) x) x := by
  rw [truncatedPower_of_pos (p - 1) hx]
  apply (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact truncatedPower_of_pos p hy

lemma hasDerivAt_truncatedPower_of_neg (p : ℝ) {x : ℝ} (hx : x < 0) :
    HasDerivAt (truncatedPower p) (p * truncatedPower (p - 1) x) x := by
  rw [truncatedPower_of_nonpos (p - 1) hx.le, mul_zero]
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
  exact truncatedPower_of_nonpos p hy.le

lemma hasDerivAt_truncatedPower_of_ne (p : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (truncatedPower p) (p * truncatedPower (p - 1) x) x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · exact hasDerivAt_truncatedPower_of_neg p hneg
  · exact hasDerivAt_truncatedPower_of_pos p hpos

lemma hasDerivAt_truncatedPower {p : ℝ} (hp : 1 < p) (x : ℝ) :
    HasDerivAt (truncatedPower p) (p * truncatedPower (p - 1) x) x := by
  by_cases hx : x = 0
  · subst x
    exact hasDerivAt_of_hasDerivAt_of_ne
      (fun y hy => hasDerivAt_truncatedPower_of_ne p hy)
      (continuous_truncatedPower (by linarith : 0 < p)).continuousAt
      (continuous_const.mul (continuous_truncatedPower (by linarith : 0 < p - 1))).continuousAt
  · exact hasDerivAt_truncatedPower_of_ne p hx

lemma hasDerivAt_T_of_no_knot (n : ℕ) (p t : ℝ)
    (ht : ∀ j ∈ Finset.range (n + 1), t ≠ (j : ℝ)) :
    HasDerivAt (T n p) (p * T n (p - 1) t) t := by
  have hsum : HasDerivAt (T n p)
      (∑ j ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ j * (n.choose j : ℝ)) *
          (p * truncatedPower (p - 1) (t - (j : ℝ)))) t := by
    apply HasDerivAt.fun_sum
    intro j hj
    simpa only [Function.comp_apply, id_eq, mul_one] using
      (((hasDerivAt_truncatedPower_of_ne p (sub_ne_zero.mpr (ht j hj))).comp t
        ((hasDerivAt_id t).sub_const (j : ℝ))).const_mul
          ((-1 : ℝ) ^ j * (n.choose j : ℝ)))
  convert hsum using 1
  rw [T, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma hasDerivAt_T (n : ℕ) {p : ℝ} (hp : 1 < p) (t : ℝ) :
    HasDerivAt (T n p) (p * T n (p - 1) t) t := by
  have hsum : HasDerivAt (T n p)
      (∑ j ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ j * (n.choose j : ℝ)) *
          (p * truncatedPower (p - 1) (t - (j : ℝ)))) t := by
    apply HasDerivAt.fun_sum
    intro j hj
    simpa only [Function.comp_apply, id_eq, mul_one] using
      (((hasDerivAt_truncatedPower hp (t - (j : ℝ))).comp t
        ((hasDerivAt_id t).sub_const (j : ℝ))).const_mul
          ((-1 : ℝ) ^ j * (n.choose j : ℝ)))
  convert hsum using 1
  rw [T, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma intervalIntegral_T (n : ℕ) {p : ℝ} (hp : 0 < p) (a b : ℝ) :
    (∫ t in a..b, T n p t) =
      (T n (p + 1) b - T n (p + 1) a) / (p + 1) := by
  have hd : ∀ t, HasDerivAt (T n (p + 1)) ((p + 1) * T n p t) t := by
    intro t
    simpa only [add_sub_cancel_right] using hasDerivAt_T n (by linarith : 1 < p + 1) t
  have hi : IntervalIntegrable (fun t => (p + 1) * T n p t) volume a b :=
    (continuous_const.mul (continuous_T n hp)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at h
  apply (eq_div_iff (by linarith : p + 1 ≠ 0)).mpr
  linarith

end IntegralTruncatedPower


namespace IntegralTruncatedPowerTail

open IntegralTruncatedPower Asymptotics

lemma T_succ (n : ℕ) (p t : ℝ) :
    T (n + 1) p t = T n p t - T n p (t - 1) := by
  have h := Finset.sum_choose_succ_mul
    (fun (j : ℕ) (_ : ℕ) => (-1 : ℝ) ^ j * truncatedPower p (t - (j : ℝ))) n
  have hleft : T (n + 1) p t =
      ∑ j ∈ Finset.range (n + 2), ((n + 1).choose j : ℝ) *
        ((-1 : ℝ) ^ j * truncatedPower p (t - (j : ℝ))) := by
    unfold T
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hleft, h]
  have hfirst : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
      ((-1 : ℝ) ^ j * truncatedPower p (t - (j : ℝ)))) = T n p t := by
    unfold T
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfirst]
  have hsecond : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
      ((-1 : ℝ) ^ (j + 1) * truncatedPower p (t - ((j + 1 : ℕ) : ℝ)))) =
      - T n p (t - 1) := by
    rw [T, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    have he : t - ((j + 1 : ℕ) : ℝ) = t - 1 - (j : ℝ) := by push_cast; ring
    rw [he]
    ring
  rw [hsecond]
  ring

lemma rpow_le_scaled_of_half_le (q : ℝ) {t x : ℝ}
    (ht : 0 < t) (hlo : t / 2 ≤ x) (hhi : x ≤ t) :
    x ^ q ≤ (1 + (2 : ℝ) ^ (-q)) * t ^ q := by
  have hx : 0 < x := lt_of_lt_of_le (by linarith : 0 < t / 2) hlo
  have hp : 0 < t ^ q := Real.rpow_pos_of_pos ht _
  have hk : 0 < (2 : ℝ) ^ (-q) := Real.rpow_pos_of_pos (by norm_num) _
  by_cases hq : 0 ≤ q
  · have h := Real.rpow_le_rpow hx.le hhi hq
    nlinarith
  · have h := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < t / 2) hlo
      (le_of_not_ge hq)
    rw [Real.div_rpow ht.le (by norm_num), div_eq_mul_inv,
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) q] at h
    nlinarith

lemma tail_bound (n : ℕ) (p : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ R : ℝ, ∀ t : ℝ, R ≤ t →
      |T n p t| ≤ C * t ^ (p - (n : ℝ)) := by
  induction n generalizing p with
  | zero =>
      refine ⟨1, by norm_num, 1, ?_⟩
      intro t ht
      have ht0 : 0 < t := by linarith
      simp [T, truncatedPower_of_pos p ht0, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  | succ n ih =>
      obtain ⟨C, hC, R, hR⟩ := ih (p - 1)
      let q : ℝ := p - 1 - (n : ℝ)
      let K : ℝ := 1 + (2 : ℝ) ^ (-q)
      have hK : 0 ≤ K := by dsimp [K]; positivity
      refine ⟨|p| * C * K, mul_nonneg (mul_nonneg (abs_nonneg _) hC) hK,
        max (R + 1) (max ((n : ℝ) + 2) 2), ?_⟩
      intro t ht
      have hRt : R + 1 ≤ t := (le_max_left _ _).trans ht
      have hnt : (n : ℝ) + 2 ≤ t :=
        (le_max_left _ _).trans ((le_max_right _ _).trans ht)
      have ht2 : 2 ≤ t :=
        (le_max_right _ _).trans ((le_max_right _ _).trans ht)
      have hderiv : ∀ x ∈ Set.Icc (t - 1) t,
          HasDerivAt (T n p) (p * T n (p - 1) x) x := by
        intro x hx
        apply hasDerivAt_T_of_no_knot
        intro j hj
        have hjn : (j : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        linarith [hx.1]
      obtain ⟨x, hx, hEq⟩ := exists_hasDerivAt_eq_slope (T n p)
        (fun x => p * T n (p - 1) x) (by linarith : t - 1 < t)
        (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
        (fun x hx => hderiv x ⟨hx.1.le, hx.2.le⟩)
      have he : t - (t - 1) = 1 := by ring
      rw [he, div_one] at hEq
      have hxr : R ≤ x := by linarith [hx.1]
      have hxp : |T n (p - 1) x| ≤ C * x ^ q := hR x hxr
      have hxpow := rpow_le_scaled_of_half_le q (by linarith : 0 < t)
        (by linarith [hx.1] : t / 2 ≤ x) hx.2.le
      have hq : q = p - ((n + 1 : ℕ) : ℝ) := by dsimp [q]; push_cast; ring
      calc
        |T (n + 1) p t| = |p| * |T n (p - 1) x| := by
          rw [T_succ, ← hEq, abs_mul]
        _ ≤ |p| * (C * x ^ q) := mul_le_mul_of_nonneg_left hxp (abs_nonneg _)
        _ ≤ |p| * (C * (K * t ^ q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxpow hC) (abs_nonneg _)
        _ = |p| * C * K * t ^ (p - ((n + 1 : ℕ) : ℝ)) := by rw [hq]; ring

lemma tail_isBigO (n : ℕ) (p : ℝ) :
    (fun t => T n p t) =O[atTop] (fun t => t ^ (p - (n : ℝ))) := by
  obtain ⟨C, hC, R, hR⟩ := tail_bound n p
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (max R 1)] with t ht
  have ht0 : 0 ≤ t := le_trans (by positivity : (0 : ℝ) ≤ 1)
    ((le_max_right _ _).trans ht)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0 _)] using
    hR t ((le_max_left _ _).trans ht)

end IntegralTruncatedPowerTail


namespace IntegralTruncatedPowerMoments

open IntegralTruncatedPower Asymptotics

lemma intervalIntegral_moment_succ (n k : ℕ) {p : ℝ} (hp : 0 < p) (b : ℝ) :
    (p + 1) * (∫ t in (0 : ℝ)..b, t ^ (k + 1) * T n p t) =
      b ^ (k + 1) * T n (p + 1) b -
        (k + 1 : ℝ) * (∫ t in (0 : ℝ)..b, t ^ k * T n (p + 1) t) := by
  have hu : Continuous (fun t : ℝ => t ^ (k + 1)) := continuous_id.pow _
  have hv : Continuous (T n (p + 1)) := continuous_T n (by linarith)
  have hdu : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ (k + 1))
      ((k + 1 : ℝ) * t ^ k) t := by
    intro t
    simpa only [Pi.pow_apply, id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one] using
      hasDerivAt_pow (k + 1) t
  have hdv : ∀ t : ℝ, HasDerivAt (T n (p + 1)) ((p + 1) * T n p t) t := by
    intro t
    simpa only [add_sub_cancel_right] using
      hasDerivAt_T n (by linarith : 1 < p + 1) t
  have hiu : IntervalIntegrable (fun t : ℝ => (k + 1 : ℝ) * t ^ k) volume 0 b :=
    (continuous_const.mul (continuous_id.pow _)).intervalIntegrable 0 b
  have hiv : IntervalIntegrable (fun t : ℝ => (p + 1) * T n p t) volume 0 b :=
    (continuous_const.mul (continuous_T n hp)).intervalIntegrable 0 b
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu.continuousOn hv.continuousOn (fun t _ => hdu t) (fun t _ => hdv t) hiu hiv
  have heq₁ : (fun t : ℝ => t ^ (k + 1) * ((p + 1) * T n p t)) =
      (fun t : ℝ => (p + 1) * (t ^ (k + 1) * T n p t)) := by
    funext t
    ring
  have heq₂ : (fun t : ℝ => ((k + 1 : ℝ) * t ^ k) * T n (p + 1) t) =
      (fun t : ℝ => (k + 1 : ℝ) * (t ^ k * T n (p + 1) t)) := by
    funext t
    ring
  rw [heq₁, heq₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  simpa only [T_eq_zero_of_nonpos n (p + 1) (le_refl 0), mul_zero, sub_zero] using h

lemma moment_isBigO_of_tail (n k : ℕ) (p : ℝ)
    (htail : (fun t => T n p t) =O[atTop] (fun t : ℝ => t ^ (p - (n : ℝ)))) :
    (fun t : ℝ => t ^ k * T n p t) =O[atTop]
      (fun t : ℝ => t ^ (p + (k : ℝ) - (n : ℝ))) := by
  refine ((isBigO_refl (fun t : ℝ => t ^ k) atTop).mul htail).congr'
    Filter.EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [← Real.rpow_natCast, ← Real.rpow_add ht]
  congr 1
  ring

lemma integrableOn_moment_of_tail (n k : ℕ) {p : ℝ} (hp : 0 < p)
    (hkn : p + (k : ℝ) + 1 < (n : ℝ))
    (htail : (fun t => T n p t) =O[atTop] (fun t : ℝ => t ^ (p - (n : ℝ)))) :
    IntegrableOn (fun t : ℝ => t ^ k * T n p t) (Set.Ioi 0) := by
  have hc : Continuous (fun t : ℝ => t ^ k * T n p t) :=
    (continuous_id.pow _).mul (continuous_T n hp)
  have hi : LocallyIntegrableOn (fun t : ℝ => t ^ k * T n p t)
      (Set.Ici 0) volume := hc.continuousOn.locallyIntegrableOn measurableSet_Ici
  have hg : IntegrableAtFilter (fun t : ℝ => t ^ (p + (k : ℝ) - (n : ℝ))) atTop :=
    integrableAtFilter_rpow_atTop_iff.mpr (by linarith)
  exact (hi.integrableOn_of_isBigO_atTop (moment_isBigO_of_tail n k p htail) hg).mono_set
    Set.Ioi_subset_Ici_self

lemma tendsto_weighted_T_zero_of_tail (n k : ℕ) (p : ℝ)
    (hkn : p + (k : ℝ) < (n : ℝ))
    (htail : (fun t => T n p t) =O[atTop] (fun t : ℝ => t ^ (p - (n : ℝ)))) :
    Tendsto (fun t : ℝ => t ^ k * T n p t) atTop (𝓝 0) := by
  apply (moment_isBigO_of_tail n k p htail).trans_tendsto
  have heq : (fun t : ℝ => t ^ (p + (k : ℝ) - (n : ℝ))) =
      (fun t : ℝ => t ^ (-((n : ℝ) - p - (k : ℝ)))) := by
    funext t
    congr 1
    ring
  rw [heq]
  exact tendsto_rpow_neg_atTop (by linarith)

lemma integral_moment_zero_of_tail (n k : ℕ) {p : ℝ} (hp : 0 < p)
    (hkn : p + (k : ℝ) + 1 < (n : ℝ))
    (htail : ∀ s : ℝ, (fun t => T n s t) =O[atTop]
      (fun t : ℝ => t ^ (s - (n : ℝ)))) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ k * T n p t) = 0 := by
  induction k generalizing p with
  | zero =>
      have hi := integrableOn_moment_of_tail n 0 hp hkn (htail p)
      have hlim := tendsto_weighted_T_zero_of_tail n 0 (p + 1)
        (by simpa only [Nat.cast_zero, add_zero] using hkn) (htail (p + 1))
      have hlim' : Tendsto (fun t : ℝ => T n (p + 1) t) atTop (𝓝 0) := by
        simpa only [pow_zero, one_mul] using hlim
      have heq : (fun b : ℝ => ∫ t in (0 : ℝ)..b, T n p t) =
          (fun b : ℝ => T n (p + 1) b / (p + 1)) := by
        funext b
        rw [intervalIntegral_T n hp, T_eq_zero_of_nonpos n (p + 1) (le_refl 0), sub_zero]
      have hz : Tendsto (fun b : ℝ => ∫ t in (0 : ℝ)..b, t ^ 0 * T n p t)
          atTop (𝓝 0) := by
        simp only [pow_zero, one_mul]
        rw [heq]
        simpa only [zero_div] using hlim'.div_const (p + 1)
      exact tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id) hz
  | succ k ih =>
      simp only [Nat.cast_add, Nat.cast_one] at hkn
      have hk' : p + 1 + (k : ℝ) + 1 < (n : ℝ) := by linarith
      have hprev := ih (p := p + 1) (by linarith) hk'
      have hiprev := integrableOn_moment_of_tail n k (by linarith : 0 < p + 1)
        hk' (htail (p + 1))
      have hlimprev : Tendsto (fun b : ℝ =>
          ∫ t in (0 : ℝ)..b, t ^ k * T n (p + 1) t) atTop (𝓝 0) := by
        simpa only [hprev, id_eq] using
          intervalIntegral_tendsto_integral_Ioi 0 hiprev tendsto_id
      have hlimbound := tendsto_weighted_T_zero_of_tail n (k + 1) (p + 1)
        (by simpa only [Nat.cast_add, Nat.cast_one] using (show p + 1 + ((k : ℝ) + 1) < (n : ℝ) by linarith)) (htail (p + 1))
      have hlimrhs := hlimbound.sub (hlimprev.const_mul (k + 1 : ℝ))
      have heq : (fun b : ℝ => (p + 1) *
          (∫ t in (0 : ℝ)..b, t ^ (k + 1) * T n p t)) =
          (fun b : ℝ => b ^ (k + 1) * T n (p + 1) b -
            (k + 1 : ℝ) * (∫ t in (0 : ℝ)..b, t ^ k * T n (p + 1) t)) := by
        funext b
        exact intervalIntegral_moment_succ n k hp b
      have hz : Tendsto (fun b : ℝ => (p + 1) *
          (∫ t in (0 : ℝ)..b, t ^ (k + 1) * T n p t)) atTop (𝓝 0) := by
        rw [heq]
        simpa only [mul_zero, sub_zero] using hlimrhs
      have hi := integrableOn_moment_of_tail n (k + 1) hp
        (by simpa only [Nat.cast_add, Nat.cast_one] using hkn) (htail p)
      have hl := (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id).const_mul (p + 1)
      have he : (p + 1) * (∫ t in Set.Ioi (0 : ℝ), t ^ (k + 1) * T n p t) = 0 :=
        tendsto_nhds_unique hl hz
      exact (mul_eq_zero.mp he).resolve_left (by linarith)

lemma integrableOn_moment (n k : ℕ) {p : ℝ} (hp : 0 < p)
    (hkn : p + (k : ℝ) + 1 < (n : ℝ)) :
    IntegrableOn (fun t : ℝ => t ^ k * T n p t) (Set.Ioi 0) :=
  integrableOn_moment_of_tail n k hp hkn (IntegralTruncatedPowerTail.tail_isBigO n p)

lemma tendsto_weighted_T_zero (n k : ℕ) (p : ℝ)
    (hkn : p + (k : ℝ) < (n : ℝ)) :
    Tendsto (fun t : ℝ => t ^ k * T n p t) atTop (𝓝 0) :=
  tendsto_weighted_T_zero_of_tail n k p hkn (IntegralTruncatedPowerTail.tail_isBigO n p)

lemma T_tendsto_zero (n : ℕ) (p : ℝ) (hpn : p < (n : ℝ)) :
    Tendsto (T n p) atTop (𝓝 0) := by
  simpa only [pow_zero, one_mul] using
    tendsto_weighted_T_zero n 0 p (by simpa only [Nat.cast_zero, add_zero] using hpn)

lemma integral_moment_zero (n k : ℕ) {p : ℝ} (hp : 0 < p)
    (hkn : p + (k : ℝ) + 1 < (n : ℝ)) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ k * T n p t) = 0 :=
  integral_moment_zero_of_tail n k hp hkn (IntegralTruncatedPowerTail.tail_isBigO n)

lemma monomial_moments (n d : ℕ) {p : ℝ} (hp : 0 < p)
    (hpn : p + (d : ℝ) < (n : ℝ)) :
    ∀ k < d, Integrable (fun t : ℝ => T n p t * t ^ k)
      (volume.restrict (Set.Ioi (0 : ℝ))) ∧
        (∫ t in Set.Ioi (0 : ℝ), T n p t * t ^ k) = 0 := by
  intro k hkd
  have hkd' : (k : ℝ) + 1 ≤ (d : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hkd
  have hkn : p + (k : ℝ) + 1 < (n : ℝ) := by linarith
  constructor
  · simpa only [IntegrableOn, mul_comm] using integrableOn_moment n k hp hkn
  · simpa only [mul_comm] using integral_moment_zero n k hp hkn

end IntegralTruncatedPowerMoments


namespace IntegralTruncatedPowerSign

open Set Finset
open IntegralTruncatedPower IntegralNegativePowerPrefix IntegralBinomialPrefix

lemma T_eq_prefix_on_cell (n j : ℕ) (hj : j ≤ n) (p t : ℝ)
    (ht : (j : ℝ) < t) (ht' : t < (j : ℝ)+1) :
    T n p t = ∑ l ∈ Finset.range (j+1),
      (-1 : ℝ)^l * (n.choose l : ℝ) * (t-l)^p := by
  have hsub : Finset.range (j+1) ⊆ Finset.range (n+1) := Finset.range_mono (by omega)
  have hsum : (∑ l ∈ Finset.range (j+1), (-1 : ℝ)^l * (n.choose l : ℝ) *
      truncatedPower p (t-l)) = T n p t := by
    unfold T
    apply Finset.sum_subset hsub
    intro l hl hlj
    have hlarge : j+1 ≤ l := by simpa only [Finset.mem_range, not_lt] using hlj
    have hc : (j : ℝ)+1 ≤ l := by exact_mod_cast hlarge
    rw [truncatedPower_of_nonpos p (by linarith : t-(l : ℝ) ≤ 0)]
    simp
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro l hl
  have hsmall : l ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
  have hc : (l : ℝ) ≤ j := by exact_mod_cast hsmall
  rw [truncatedPower_of_pos p (by linarith : 0 < t-(l : ℝ))]

lemma T_eq_full_prefix_above (n : ℕ) (p t : ℝ) (ht : (n : ℝ) < t) :
    T n p t = ∑ l ∈ Finset.range (n+1),
      (-1 : ℝ)^l * (n.choose l : ℝ) * (t-l)^p := by
  unfold T
  apply Finset.sum_congr rfl
  intro l hl
  have hsmall : l ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
  have hc : (l : ℝ) ≤ n := by exact_mod_cast hsmall
  rw [truncatedPower_of_pos p (by linarith : 0 < t-(l : ℝ))]

/-- The strict alternating sign of every nonpositive-power cell. -/
theorem signed_T_nonpos_cell_pos (n j : ℕ) (hj : j < n) (q t : ℝ)
    (hq : q ≤ 0) (ht : (j : ℝ) < t) (ht' : t < (j : ℝ)+1) :
    0 < (-1 : ℝ)^j * T n q t := by
  rw [T_eq_prefix_on_cell n j hj.le q t ht ht']
  obtain hneg | rfl := hq.lt_or_eq
  · exact signed_negative_power_prefix_pos n j hj.le q t hneg ht
  · have he : (∑ l ∈ Finset.range (j+1),
        (-1 : ℝ)^l * (n.choose l : ℝ) * (t-l)^(0 : ℝ)) = prefixSum n j 1 := by
      simp [prefixSum]
    rw [he]
    exact signed_prefix_pos n j hj 1 le_rfl

theorem signed_T_neg_above_pos (n : ℕ) (q t : ℝ) (hq : q < 0) (ht : (n : ℝ) < t) :
    0 < (-1 : ℝ)^n * T n q t := by
  rw [T_eq_full_prefix_above n q t ht]
  exact signed_negative_power_prefix_pos n n le_rfl q t hq ht

lemma no_knot_in_cell (n j : ℕ) (t : ℝ) (ht : (j : ℝ) < t)
    (ht' : t < (j : ℝ)+1) :
    ∀ l ∈ Finset.range (n+1), t ≠ (l : ℝ) := by
  intro l hl
  by_cases hlj : l ≤ j
  · have hc : (l : ℝ) ≤ j := by exact_mod_cast hlj
    linarith
  · have hlarge : j+1 ≤ l := by omega
    have hc : (j : ℝ)+1 ≤ l := by exact_mod_cast hlarge
    linarith

/-- All base exponents 0<p≤1 give strict alternating monotonicity, including
both endpoints of each unit cell. -/
theorem strictMonoOn_signed_T_cell (n j : ℕ) (hj : j < n) (p : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1) :
    StrictMonoOn (fun t : ℝ => (-1 : ℝ)^j * T n p t)
      (Set.Icc (j : ℝ) ((j : ℝ)+1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuous_const.mul (continuous_T n hp)).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hd := (hasDerivAt_T_of_no_knot n p t (no_knot_in_cell n j t ht.1 ht.2)).const_mul
    ((-1 : ℝ)^j)
  change 0 < deriv (fun y : ℝ => (-1 : ℝ)^j * T n p y) t
  rw [hd.deriv]
  have hsign := signed_T_nonpos_cell_pos n j hj (p-1) t (by linarith) ht.1 ht.2
  have hprod := mul_pos hp hsign
  simpa only [mul_assoc, mul_left_comm p] using hprod

/-- The final cell is also strictly monotone after its alternating sign change. -/
theorem strictMonoOn_signed_T_above (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    StrictMonoOn (fun t : ℝ => (-1 : ℝ)^n * T n p t) (Set.Ici (n : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
    (continuous_const.mul (continuous_T n hp)).continuousOn
  intro t ht
  rw [interior_Ici] at ht
  have htpos : (n : ℝ) < t := ht
  have hnot : ∀ l ∈ Finset.range (n+1), t ≠ (l : ℝ) := by
    intro l hl
    have hsmall : l ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
    have hc : (l : ℝ) ≤ n := by exact_mod_cast hsmall
    linarith
  have hd := (hasDerivAt_T_of_no_knot n p t hnot).const_mul ((-1 : ℝ)^n)
  change 0 < deriv (fun y : ℝ => (-1 : ℝ)^n * T n p y) t
  rw [hd.deriv]
  have hsign := signed_T_neg_above_pos n (p-1) t (by linarith) ht
  have hprod := mul_pos hp hsign
  simpa only [mul_assoc, mul_left_comm p] using hprod

/-- Decay at infinity and final-cell monotonicity give a strict endpoint sign. -/
theorem signed_T_neg_of_tendsto_zero (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hlim : Filter.Tendsto (T n p) Filter.atTop (nhds 0))
    (t : ℝ) (ht : (n : ℝ) ≤ t) :
    (-1 : ℝ)^n * T n p t < 0 := by
  let g (u : ℝ) : ℝ := (-1 : ℝ)^n * T n p u
  have hg : StrictMonoOn g (Set.Ici (n : ℝ)) := strictMonoOn_signed_T_above n p hp hp'
  have hglim : Filter.Tendsto g Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul ((-1 : ℝ)^n) hlim
  have hle (u : ℝ) (hu : (n : ℝ) ≤ u) : g u ≤ 0 := by
    apply ge_of_tendsto hglim
    filter_upwards [Filter.eventually_ge_atTop u] with v hv
    exact hg.monotoneOn hu (hu.trans hv) hv
  have ht1 : (n : ℝ) ≤ t+1 := by linarith
  have hstrict := hg ht ht1 (lt_add_one t)
  exact hstrict.trans_le (hle (t+1) (by linarith))

end IntegralTruncatedPowerSign


namespace IntegralTruncatedPowerCritical

open IntegralTruncatedPower IntegralTruncatedPowerSign
open Set

/-- Within the support, each base-exponent local extremum is an integer knot. -/
theorem localExtr_base_inside_is_knot (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p ≤ 1)
    (t : ℝ) (ht : 0 < t) (htn : t < n) (hext : IsLocalExtr (T n p) t) :
    ∃ j : ℕ, 0 < j ∧ j < n ∧ t = (j : ℝ) := by
  let j : ℕ := Nat.floor t
  have hjn : j < n := (Nat.floor_lt ht.le).mpr htn
  have hjle : (j : ℝ) ≤ t := Nat.floor_le ht.le
  have hjup : t < (j : ℝ)+1 := Nat.lt_floor_add_one t
  by_cases he : t = (j : ℝ)
  · refine ⟨j, ?_, hjn, he⟩
    have hjpos : (0 : ℝ) < j := by simpa only [he] using ht
    exact_mod_cast hjpos
  · have hjlt : (j : ℝ) < t := lt_of_le_of_ne hjle (Ne.symm he)
    have hsign := signed_T_nonpos_cell_pos n j hjn (p-1) t (by linarith) hjlt hjup
    have hprev : T n (p-1) t ≠ 0 := by
      intro hz
      simp only [hz, mul_zero, lt_self_iff_false] at hsign
    have hd := hasDerivAt_T_of_no_knot n p t (no_knot_in_cell n j t hjlt hjup)
    exact False.elim ((mul_ne_zero hp.ne' hprev) (hext.hasDerivAt_eq_zero hd))

/-- For 0<p<1, there are no positive extrema except the n integer knots. -/
theorem localExtr_base_positive_is_knot (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (t : ℝ) (ht : 0 < t) (hext : IsLocalExtr (T n p) t) :
    ∃ j : ℕ, 0 < j ∧ j ≤ n ∧ t = (j : ℝ) := by
  rcases lt_trichotomy t (n : ℝ) with hlt | he | hgt
  · obtain ⟨j, hjpos, hjn, hjt⟩ := localExtr_base_inside_is_knot n p hp hp'.le t ht hlt hext
    exact ⟨j, hjpos, hjn.le, hjt⟩
  · refine ⟨n, ?_, le_rfl, he⟩
    have hnpos : (0 : ℝ) < n := by simpa only [he] using ht
    exact_mod_cast hnpos
  · have hnot : ∀ l ∈ Finset.range (n+1), t ≠ (l : ℝ) := by
      intro l hl
      have hsmall : l ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
      have hc : (l : ℝ) ≤ n := by exact_mod_cast hsmall
      linarith
    have hsign := signed_T_neg_above_pos n (p-1) t (by linarith) hgt
    have hprev : T n (p-1) t ≠ 0 := by
      intro hz
      simp only [hz, mul_zero, lt_self_iff_false] at hsign
    have hd := hasDerivAt_T_of_no_knot n p t hnot
    exact False.elim ((mul_ne_zero hp.ne' hprev) (hext.hasDerivAt_eq_zero hd))

theorem localExtr_base_mem_knots (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (t : ℝ) (ht : 0 < t) (hext : IsLocalExtr (T n p) t) :
    t ∈ (Finset.Icc 1 n).image (fun j : ℕ => (j : ℝ)) := by
  obtain ⟨j, hjpos, hjn, hjt⟩ := localExtr_base_positive_is_knot n p hp hp' t ht hext
  apply Finset.mem_image.mpr
  refine ⟨j, Finset.mem_Icc.mpr ⟨by omega, hjn⟩, hjt.symm⟩

theorem card_base_knots_le (n : ℕ) :
    ((Finset.Icc 1 n).image (fun j : ℕ => (j : ℝ))).card ≤ n := by
  calc
    _ ≤ (Finset.Icc 1 n).card := Finset.card_image_le
    _ = n := by simp [Nat.card_Icc]

end IntegralTruncatedPowerCritical


namespace IntegralTruncatedPowerOne

open IntegralTruncatedPower IntegralTruncatedPowerTail

lemma truncatedPower_one_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    truncatedPower 1 x = x := by
  rw [truncatedPower_eq_max_rpow zero_lt_one, max_eq_left hx, Real.rpow_one]

lemma T_two_one_eq_zero {t : ℝ} (ht : 2 ≤ t) : T 2 1 t = 0 := by
  have h0 : truncatedPower 1 t = t := truncatedPower_one_of_nonneg (by linarith)
  have h1 : truncatedPower 1 (t-1) = t-1 := truncatedPower_one_of_nonneg (by linarith)
  have h2 : truncatedPower 1 (t-2) = t-2 := truncatedPower_one_of_nonneg (by linarith)
  norm_num [T, Finset.sum_range_succ, h0, h1, h2]
  ring

/-- Integer exponent1 is already compactly supported as soon as n≥2. -/
theorem T_one_eq_zero_above (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : (n : ℝ) ≤ t) :
    T n 1 t = 0 := by
  induction n, hn using Nat.le_induction generalizing t with
  | base => exact T_two_one_eq_zero ht
  | succ n hn ih =>
    have ht' : (n : ℝ)+1 ≤ t := by simpa only [Nat.cast_add, Nat.cast_one] using ht
    rw [T_succ, ih t (by linarith), ih (t-1) (by linarith)]
    ring

theorem T_one_at_n_eq_zero (n : ℕ) (hn : 2 ≤ n) : T n 1 n = 0 :=
  T_one_eq_zero_above n hn n le_rfl

end IntegralTruncatedPowerOne


namespace IntegralRolleZeroCount

open Filter Set Topology

/-- A positive value to the right of a zero forces an interior local maximum
when the function tends back to zero. -/
theorem exists_localMax_after_zero_of_pos (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Ici a)) (hfa : f a = 0)
    (hlim : Tendsto f atTop (𝓝 0)) (hab : a < b) (hfb : 0 < f b) :
    ∃ c : ℝ, a < c ∧ IsLocalMax f c := by
  have hevent : ∀ᶠ x in atTop, f x < f b := (tendsto_order.1 hlim).2 (f b) hfb
  obtain ⟨R, hR⟩ := eventually_atTop.1 hevent
  let B : ℝ := max R b + 1
  have hbB : b < B := by dsimp [B]; linarith [le_max_right R b]
  have hRB : R ≤ B := by dsimp [B]; linarith [le_max_left R b]
  have hbound : f B < f b := hR B hRB
  have hboundary : ∀ z ∈ Icc a B \ Ioo a B, f z < f b := by
    rintro z ⟨hz, hnot⟩
    have hz' : z = a ∨ z = B := by
      have hn : ¬ a < z ∨ ¬ z < B := not_and_or.mp hnot
      rcases hn with hn | hn
      · left; exact le_antisymm (le_of_not_gt hn) hz.1
      · right; exact le_antisymm hz.2 (le_of_not_gt hn)
    rcases hz' with rfl | rfl
    · simpa only [hfa] using hfb
    · exact hbound
  obtain ⟨c, hc, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc a B)).exists_isLocalMax_mem_open
      Ioo_subset_Icc_self (hf.mono (fun _ hx => hx.1))
      (show b ∈ Icc a B from ⟨hab.le, hbB.le⟩) hboundary isOpen_Ioo
  exact ⟨c, hc.1, hmax⟩

/-- A zero followed by a zero limit has a later local extremum. A flat tail
also satisfies this conclusion, so no non-flatness assumption is needed. -/
theorem exists_localExtr_after_zero (f : ℝ → ℝ) (a : ℝ)
    (hf : ContinuousOn f (Ici a)) (hfa : f a = 0)
    (hlim : Tendsto f atTop (𝓝 0)) :
    ∃ c : ℝ, a < c ∧ IsLocalExtr f c := by
  classical
  by_cases hnonzero : ∃ b : ℝ, a < b ∧ f b ≠ 0
  · obtain ⟨b, hab, hfb⟩ := hnonzero
    rcases lt_or_gt_of_ne hfb with hneg | hpos
    · obtain ⟨c, hac, hmax⟩ := exists_localMax_after_zero_of_pos
        (fun x => -f x) a b hf.neg (by simp [hfa]) (by simpa using hlim.neg)
        hab (neg_pos.mpr hneg)
      have hmin : IsLocalMin (fun x : ℝ => - - f x) c := hmax.neg
      have heq : (fun x : ℝ => - - f x) = f := by
        funext x
        exact neg_neg (f x)
      rw [heq] at hmin
      exact ⟨c, hac, Or.inl hmin⟩
    · obtain ⟨c, hac, hmax⟩ := exists_localMax_after_zero_of_pos f a b hf hfa hlim hab hpos
      exact ⟨c, hac, Or.inr hmax⟩
  · have hzero : ∀ x : ℝ, a < x → f x = 0 := by
      intro x hx
      by_contra hne
      exact hnonzero ⟨x, hx, hne⟩
    let c : ℝ := a + 1
    have hac : a < c := by dsimp [c]; linarith
    refine ⟨c, hac, Or.inr ?_⟩
    change ∀ᶠ x in 𝓝 c, f x ≤ f c
    filter_upwards [Ioi_mem_nhds hac] with x hx
    rw [hzero x hx, hzero c hac]

/-- The topological Rolle lemma specialized to two zero endpoints. -/
theorem exists_localExtr_between_zeros (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : ContinuousOn f (Icc a b)) (hfa : f a = 0) (hfb : f b = 0) :
    ∃ c ∈ Ioo a b, IsLocalExtr f c :=
  exists_isLocalExtr_Ioo hab hf (hfa.trans hfb.symm)

/-- A derivative version of the extremum beyond a zero. -/
theorem exists_deriv_zero_after_zero (f : ℝ → ℝ) (a : ℝ)
    (hf : ContinuousOn f (Ici a)) (hfa : f a = 0)
    (hlim : Tendsto f atTop (𝓝 0)) :
    ∃ c : ℝ, a < c ∧ deriv f c = 0 := by
  obtain ⟨c, hac, hc⟩ := exists_localExtr_after_zero f a hf hfa hlim
  exact ⟨c, hac, hc.deriv_eq_zero⟩

/-- There is one more positive extremum than any finite collection of positive
zeros, with every chosen extremum outside the zero collection. -/
theorem card_zeros_succ_le_card_extrema_sdiff (f : ℝ → ℝ) (Z S : Finset ℝ)
    (hf : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0)
    (hlim : Tendsto f atTop (𝓝 0))
    (hZ : ∀ x ∈ Z, 0 < x ∧ f x = 0)
    (hS : ∀ x : ℝ, 0 < x → IsLocalExtr f x → x ∈ S) :
    Z.card + 1 ≤ (S \ Z).card := by
  classical
  let A : Finset ℝ := insert 0 Z
  have hAne : A.Nonempty := Finset.insert_nonempty 0 Z
  have hAnonneg : ∀ x ∈ A, 0 ≤ x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact (hZ x hx).1.le
  have hAzero : ∀ x ∈ A, f x = 0 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hf0
    · exact (hZ x hx).2
  let b : ℝ := A.max' hAne
  have hbA : b ∈ A := Finset.max'_mem A hAne
  have hb0 : 0 ≤ b := hAnonneg b hbA
  obtain ⟨c, hbc, hcext⟩ := exists_localExtr_after_zero f b
    (hf.mono (fun _ hx => hb0.trans hx)) (hAzero b hbA) hlim
  have hcS : c ∈ S := hS c (hb0.trans_lt hbc) hcext
  have hcnot : c ∉ Z := by
    intro hcZ
    have hcb : c ≤ b := Finset.le_max' A c (Finset.mem_insert_of_mem hcZ)
    exact (not_le_of_gt hbc) hcb
  have hcT : c ∈ S \ Z := Finset.mem_sdiff.mpr ⟨hcS, hcnot⟩
  have hcard : A.card ≤ ((S \ Z).erase c).card + 1 := by
    apply Finset.card_le_of_interleaved
    intro x hx y hy hxy hbetween
    have hx0 := hAnonneg x hx
    obtain ⟨z, hz, hzext⟩ := exists_localExtr_between_zeros f x y hxy
      (hf.mono (fun _ ht => hx0.trans ht.1)) (hAzero x hx) (hAzero y hy)
    have hzS : z ∈ S := hS z (hx0.trans_lt hz.1) hzext
    have hznot : z ∉ Z := by
      intro hzZ
      exact hbetween z (Finset.mem_insert_of_mem hzZ) hz
    have hyb : y ≤ b := Finset.le_max' A y hy
    have hzc : z ≠ c := by linarith [hz.2]
    exact ⟨z, Finset.mem_erase.mpr ⟨hzc, Finset.mem_sdiff.mpr ⟨hzS, hznot⟩⟩,
      hz.1, hz.2⟩
  have h0not : (0 : ℝ) ∉ Z := by
    intro h0
    exact (lt_irrefl 0) (hZ 0 h0).1
  have hAcard : A.card = Z.card + 1 := Finset.card_insert_of_notMem h0not
  have herase : ((S \ Z).erase c).card + 1 = (S \ Z).card :=
    Finset.card_erase_add_one hcT
  omega

/-- A weaker count without removing any roots from the extremum set. -/
theorem card_zeros_succ_le_card_extrema (f : ℝ → ℝ) (Z S : Finset ℝ)
    (hf : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0)
    (hlim : Tendsto f atTop (𝓝 0))
    (hZ : ∀ x ∈ Z, 0 < x ∧ f x = 0)
    (hS : ∀ x : ℝ, 0 < x → IsLocalExtr f x → x ∈ S) :
    Z.card + 1 ≤ S.card :=
  (card_zeros_succ_le_card_extrema_sdiff f Z S hf hf0 hlim hZ hS).trans
    (Finset.card_le_card Finset.sdiff_subset)

/-- The same count when a finite set contains every positive derivative zero. -/
theorem card_zeros_succ_le_card_derivative_zeros (f : ℝ → ℝ) (Z S : Finset ℝ)
    (hf : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0)
    (hlim : Tendsto f atTop (𝓝 0))
    (hZ : ∀ x ∈ Z, 0 < x ∧ f x = 0)
    (hS : ∀ x : ℝ, 0 < x → deriv f x = 0 → x ∈ S) :
    Z.card + 1 ≤ (S \ Z).card :=
  card_zeros_succ_le_card_extrema_sdiff f Z S hf hf0 hlim hZ
    (fun x hx hext => hS x hx hext.deriv_eq_zero)

end IntegralRolleZeroCount


namespace IntegralRolleZeroCount

open Filter Set Topology

/-- Finitely many positive extrema force finitely many positive roots. -/
theorem finite_positive_zero_set (f : ℝ → ℝ) (S : Finset ℝ)
    (hf : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0)
    (hlim : Tendsto f atTop (𝓝 0))
    (hS : ∀ x : ℝ, 0 < x → IsLocalExtr f x → x ∈ S) :
    {x : ℝ | 0 < x ∧ f x = 0}.Finite := by
  classical
  by_contra hnot
  obtain ⟨Z, hsub, hcard⟩ :=
    Set.Infinite.exists_subset_card_eq hnot S.card
  have hZ : ∀ x ∈ Z, 0 < x ∧ f x = 0 := fun _ hx => hsub hx
  have hbound := card_zeros_succ_le_card_extrema f Z S hf hf0 hlim hZ hS
  omega

/-- A finite exact root list and the stronger count excluding those roots from
the extremum set, without assuming any root is simple. -/
theorem exists_finset_positive_zero_set (f : ℝ → ℝ) (S : Finset ℝ)
    (hf : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0)
    (hlim : Tendsto f atTop (𝓝 0))
    (hS : ∀ x : ℝ, 0 < x → IsLocalExtr f x → x ∈ S) :
    ∃ Z : Finset ℝ, (∀ x : ℝ, x ∈ Z ↔ 0 < x ∧ f x = 0) ∧
      Z.card + 1 ≤ (S \ Z).card := by
  classical
  have hfinite := finite_positive_zero_set f S hf hf0 hlim hS
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro x
    exact hfinite.mem_toFinset
  · exact card_zeros_succ_le_card_extrema_sdiff f hfinite.toFinset S hf hf0 hlim
      (fun _ hx => hfinite.mem_toFinset.mp hx) hS

/-- The positive root set has strictly smaller cardinality than a finite set
containing every positive local extremum. -/
theorem ncard_positive_zero_set_succ_le_card_extrema (f : ℝ → ℝ) (S : Finset ℝ)
    (hf : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0)
    (hlim : Tendsto f atTop (𝓝 0))
    (hS : ∀ x : ℝ, 0 < x → IsLocalExtr f x → x ∈ S) :
    {x : ℝ | 0 < x ∧ f x = 0}.ncard + 1 ≤ S.card := by
  classical
  have hfinite := finite_positive_zero_set f S hf hf0 hlim hS
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact card_zeros_succ_le_card_extrema f hfinite.toFinset S hf hf0 hlim
    (fun _ hx => hfinite.mem_toFinset.mp hx) hS

/-- A finite positive derivative-zero set forces a finite positive root set. -/
theorem finite_positive_zero_set_of_derivative (f : ℝ → ℝ) (S : Finset ℝ)
    (hf : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0)
    (hlim : Tendsto f atTop (𝓝 0))
    (hS : ∀ x : ℝ, 0 < x → deriv f x = 0 → x ∈ S) :
    {x : ℝ | 0 < x ∧ f x = 0}.Finite :=
  finite_positive_zero_set f S hf hf0 hlim
    (fun x hx hext => hS x hx hext.deriv_eq_zero)

/-- Cardinality form of the derivative-zero-set criterion. -/
theorem ncard_positive_zero_set_succ_le_card_derivative_zeros (f : ℝ → ℝ) (S : Finset ℝ)
    (hf : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0)
    (hlim : Tendsto f atTop (𝓝 0))
    (hS : ∀ x : ℝ, 0 < x → deriv f x = 0 → x ∈ S) :
    {x : ℝ | 0 < x ∧ f x = 0}.ncard + 1 ≤ S.card :=
  ncard_positive_zero_set_succ_le_card_extrema f S hf hf0 hlim
    (fun x hx hext => hS x hx hext.deriv_eq_zero)

end IntegralRolleZeroCount


namespace IntegralBoundedRolle

open Set

theorem card_zeros_succ_le_card_extrema_sdiff
    (f : ℝ → ℝ) (a b : ℝ) (Z S : Finset ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hfa : f a = 0) (hfb : f b = 0)
    (hZ : ∀ x ∈ Z, a < x ∧ x < b ∧ f x = 0)
    (hS : ∀ x : ℝ, a < x → x < b → IsLocalExtr f x → x ∈ S) :
    Z.card + 1 ≤ (S \ Z).card := by
  classical
  let A : Finset ℝ := insert a (insert b Z)
  have hAbounds (x : ℝ) (hx : x ∈ A) : a ≤ x ∧ x ≤ b := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨le_rfl, hab.le⟩
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hab.le, le_rfl⟩
      · exact ⟨(hZ x hx).1.le, (hZ x hx).2.1.le⟩
  have hAzero (x : ℝ) (hx : x ∈ A) : f x = 0 := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hfa
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hfb
      · exact (hZ x hx).2.2
  have hcard : A.card ≤ (S \ Z).card + 1 := by
    apply Finset.card_le_of_interleaved
    intro x hx y hy hxy hbetween
    have hxbound := hAbounds x hx
    have hybound := hAbounds y hy
    obtain ⟨z, hz, hext⟩ := exists_isLocalExtr_Ioo hxy
      (hf.mono (fun _ ht => ⟨hxbound.1.trans ht.1, ht.2.trans hybound.2⟩))
      ((hAzero x hx).trans (hAzero y hy).symm)
    have hzS : z ∈ S := hS z (hxbound.1.trans_lt hz.1) (hz.2.trans_le hybound.2) hext
    have hznot : z ∉ Z := by
      intro hzZ
      exact hbetween z (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hzZ)) hz
    exact ⟨z, Finset.mem_sdiff.mpr ⟨hzS, hznot⟩, hz.1, hz.2⟩
  have hanot : a ∉ Z := by
    intro ha
    exact (lt_irrefl a) (hZ a ha).1
  have hbnot : b ∉ Z := by
    intro hb
    exact (lt_irrefl b) (hZ b hb).2.1
  have habnot : a ∉ insert b Z := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hab.ne, hanot⟩
  have hAcard : A.card = Z.card + 2 := by
    dsimp only [A]
    rw [Finset.card_insert_of_notMem habnot, Finset.card_insert_of_notMem hbnot]
  omega

theorem finite_zero_set (f : ℝ → ℝ) (a b : ℝ) (S : Finset ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hfa : f a = 0) (hfb : f b = 0)
    (hS : ∀ x : ℝ, a < x → x < b → IsLocalExtr f x → x ∈ S) :
    {x : ℝ | a < x ∧ x < b ∧ f x = 0}.Finite := by
  classical
  by_contra hnot
  obtain ⟨Z, hsub, hcard⟩ := Set.Infinite.exists_subset_card_eq hnot S.card
  have hZ : ∀ x ∈ Z, a < x ∧ x < b ∧ f x = 0 := fun _ hx => hsub hx
  have hbound := card_zeros_succ_le_card_extrema_sdiff f a b Z S hab hf hfa hfb hZ hS
  have hle : (S \ Z).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
  omega

theorem exists_finset_zero_set (f : ℝ → ℝ) (a b : ℝ) (S : Finset ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hfa : f a = 0) (hfb : f b = 0)
    (hS : ∀ x : ℝ, a < x → x < b → IsLocalExtr f x → x ∈ S) :
    ∃ Z : Finset ℝ, (∀ x : ℝ, x ∈ Z ↔ a < x ∧ x < b ∧ f x = 0) ∧
      Z.card + 1 ≤ (S \ Z).card := by
  classical
  have hfinite := finite_zero_set f a b S hab hf hfa hfb hS
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro x
    exact hfinite.mem_toFinset
  · exact card_zeros_succ_le_card_extrema_sdiff f a b hfinite.toFinset S hab hf hfa hfb
      (fun _ hx => hfinite.mem_toFinset.mp hx) hS

end IntegralBoundedRolle


namespace IntegralTruncatedPowerZeroBase

open IntegralTruncatedPower IntegralTruncatedPowerSign IntegralTruncatedPowerCritical
open IntegralTruncatedPowerMoments IntegralTruncatedPowerOne

lemma T_half_pos (n : ℕ) (p : ℝ) : 0 < T n p (1/2) := by
  have he : T n p (1/2) = (1/2 : ℝ)^p := by
    rw [T_eq_prefix_on_cell n 0 (Nat.zero_le n) p (1/2) (by norm_num) (by norm_num)]
    simp
  rw [he]
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- The actual noninteger base has precisely n−1 positive roots.
The strong count also records that none can consume a critical knot. -/
theorem exists_positive_zero_finset_base (n : ℕ) (hn : 1 ≤ n) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1) :
    ∃ Z : Finset ℝ, (∀ x : ℝ, x ∈ Z ↔ 0 < x ∧ T n p x = 0) ∧
      Z.card = n-1 ∧
      Z.card + 1 ≤ (((Finset.Icc 1 n).image (fun j : ℕ => (j : ℝ))) \ Z).card := by
  classical
  let S : Finset ℝ := (Finset.Icc 1 n).image (fun j : ℕ => (j : ℝ))
  have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpn : p < (n : ℝ) := hp'.trans_le hncast
  obtain ⟨Z, hZ, hbound⟩ := IntegralRolleZeroCount.exists_finset_positive_zero_set
    (T n p) S (continuous_T n hp).continuousOn
    (T_eq_zero_of_nonpos n p le_rfl) (T_tendsto_zero n p hpn)
    (fun x hx hext => localExtr_base_mem_knots n p hp hp' x hx hext)
  have hlower : n-1 ≤ Z.card := by
    apply IntegralPolynomialSignMoments.card_positive_zeros_ge_of_vanishing_moments
      (μ := volume) Z (continuous_T n hp).continuousOn
    · intro x hx
      exact ⟨fun hz => (hZ x).mpr ⟨hx, hz⟩, fun hz => ((hZ x).mp hz).2⟩
    · exact ⟨1/2, by norm_num, (T_half_pos n p).ne'⟩
    · apply monomial_moments n (n-1) hp
      rw [Nat.cast_sub hn, Nat.cast_one]
      linarith
  have hcardS : S.card ≤ n := card_base_knots_le n
  have hsub : (S \ Z).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
  have hcardZ : Z.card = n-1 := by omega
  exact ⟨Z, hZ, hcardZ, hbound⟩

/-- The integer exponent1 base has exactly n−2 roots in its open support. -/
theorem exists_zero_finset_one (n : ℕ) (hn : 2 ≤ n) :
    ∃ Z : Finset ℝ, (∀ x : ℝ, x ∈ Z ↔ 0 < x ∧ x < n ∧ T n 1 x = 0) ∧
      Z.card = n-2 ∧
      Z.card + 1 ≤ (((Finset.Icc 1 (n-1)).image (fun j : ℕ => (j : ℝ))) \ Z).card := by
  classical
  let S : Finset ℝ := (Finset.Icc 1 (n-1)).image (fun j : ℕ => (j : ℝ))
  have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨Z, hZ, hbound⟩ := IntegralBoundedRolle.exists_finset_zero_set
    (T n 1) 0 n S (by linarith) (continuous_T n zero_lt_one).continuousOn
    (T_eq_zero_of_nonpos n 1 le_rfl) (T_one_at_n_eq_zero n hn) (by
      intro x hx hxn hext
      obtain ⟨j, hjpos, hjn, hjx⟩ := localExtr_base_inside_is_knot n 1 zero_lt_one le_rfl x hx hxn hext
      refine Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hjx.symm⟩)
  have hlower : n-2 ≤ Z.card := by
    apply IntegralPolynomialSignMoments.card_zeros_ge_of_vanishing_moments
      (μ := volume) Z (convex_Ioo (0 : ℝ) (n : ℝ)) isOpen_Ioo (continuous_T n zero_lt_one).continuousOn
    · intro x hx
      exact ⟨fun hz => (hZ x).mpr ⟨hx.1, hx.2, hz⟩, fun hz => ((hZ x).mp hz).2.2⟩
    · refine ⟨1/2, ⟨by norm_num, by linarith⟩, (T_half_pos n 1).ne'⟩
    · intro k hk
      have hm := monomial_moments n (n-2) (p := 1) zero_lt_one (by
        rw [Nat.cast_sub hn, Nat.cast_two]
        linarith) k hk
      constructor
      · exact IntegrableOn.mono_set hm.1 Set.Ioo_subset_Ioi_self
      · have heq : (∫ x in Set.Ioi (0 : ℝ), T n 1 x * x^k) =
            ∫ x in Set.Ioo (0 : ℝ) n, T n 1 x * x^k := by
          apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioo_subset_Ioi_self
          intro x hx
          have hxge : (n : ℝ) ≤ x := by
            by_contra hnot
            exact hx.2 ⟨hx.1, lt_of_not_ge hnot⟩
          rw [T_one_eq_zero_above n hn x hxge, zero_mul]
        rw [← heq]
        exact hm.2
  have hcardS : S.card ≤ n-1 := by
    calc
      _ ≤ (Finset.Icc 1 (n-1)).card := Finset.card_image_le
      _ = n-1 := by simp [Nat.card_Icc]
  have hsub : (S \ Z).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
  have hcardZ : Z.card = n-2 := by omega
  exact ⟨Z, hZ, hcardZ, hbound⟩

/-- Every base root avoids all integer knots; this is forced by the sharp count. -/
theorem base_root_not_knot (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (x : ℝ) (hx : 0 < x) (hzero : T n p x = 0) :
    ∀ j ∈ Finset.range (n+1), x ≠ (j : ℝ) := by
  classical
  obtain ⟨Z, hZ, hcard, hbound⟩ := exists_positive_zero_finset_base n hn p hp hp'
  let S : Finset ℝ := (Finset.Icc 1 n).image (fun j : ℕ => (j : ℝ))
  have hxZ : x ∈ Z := (hZ x).mpr ⟨hx, hzero⟩
  have hcardS : S.card ≤ n := card_base_knots_le n
  change Z.card + 1 ≤ (S \ Z).card at hbound
  have heq : S \ Z = S := Finset.eq_of_subset_of_card_le Finset.sdiff_subset (by omega)
  intro j hj he
  have hjpos : 0 < j := by
    have hc : (0 : ℝ) < j := by simpa only [he] using hx
    exact_mod_cast hc
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have hxS : x ∈ S := Finset.mem_image.mpr
    ⟨j, Finset.mem_Icc.mpr ⟨by omega, hjn⟩, he.symm⟩
  have hxD : x ∈ S \ Z := by rw [heq]; exact hxS
  exact (Finset.mem_sdiff.mp hxD).2 hxZ

theorem hasDerivAt_T_base_root (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (x : ℝ) (hx : 0 < x) (hzero : T n p x = 0) :
    HasDerivAt (T n p) (p * T n (p-1) x) x :=
  hasDerivAt_T_of_no_knot n p x (base_root_not_knot n hn p hp hp' x hx hzero)

end IntegralTruncatedPowerZeroBase


namespace IntegralTruncatedPowerNonintegerZeros

open IntegralTruncatedPower IntegralTruncatedPowerMoments IntegralTruncatedPowerZeroBase

/-- Every positive noninteger exponent below n has the minimal number of roots. -/
theorem exists_positive_zero_finset_fractional (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1)
    (r : ℕ) (hr : r < n) :
    ∃ Z : Finset ℝ,
      (∀ x : ℝ, x ∈ Z ↔ 0 < x ∧ T n (δ+(r : ℝ)) x = 0) ∧
        Z.card = n-r-1 := by
  have hall : ∀ r : ℕ, r < n →
      ∃ Z : Finset ℝ,
        (∀ x : ℝ, x ∈ Z ↔ 0 < x ∧ T n (δ+(r : ℝ)) x = 0) ∧
          Z.card = n-r-1 := by
    intro r
    induction r with
    | zero =>
      intro hr
      obtain ⟨Z, hZ, hcard, _⟩ := exists_positive_zero_finset_base n (by omega) δ hδ hδ'
      refine ⟨Z, ?_, ?_⟩
      · simpa only [Nat.cast_zero, add_zero] using hZ
      · simpa only [Nat.sub_zero] using hcard
    | succ r ih =>
      intro hr
      obtain ⟨S, hS, hcardS⟩ := ih (by omega)
      let p : ℝ := δ + ((r+1 : ℕ) : ℝ)
      have hp : 1 < p := by dsimp only [p]; push_cast; linarith [show (0 : ℝ) ≤ (r : ℝ) from Nat.cast_nonneg r]
      have hpn : p < (n : ℝ) := by
        have hnat : r+2 ≤ n := by omega
        have hreal : ((r+2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnat
        dsimp only [p]
        push_cast at *
        linarith
      have hp_prev : p-1 = δ+(r : ℝ) := by dsimp only [p]; push_cast; ring
      have hcrit : ∀ x : ℝ, 0 < x → IsLocalExtr (T n p) x → x ∈ S := by
        intro x hx hext
        have hd : HasDerivAt (T n p) (p * T n (δ+(r : ℝ)) x) x := by
          simpa only [hp_prev] using hasDerivAt_T n hp x
        have hz : p * T n (δ+(r : ℝ)) x = 0 := hext.hasDerivAt_eq_zero hd
        have hprevzero : T n (δ+(r : ℝ)) x = 0 :=
          (mul_eq_zero.mp hz).resolve_left (by linarith : p ≠ 0)
        exact (hS x).mpr ⟨hx, hprevzero⟩
      obtain ⟨Z, hZ, hbound⟩ := IntegralRolleZeroCount.exists_finset_positive_zero_set
        (T n p) S (continuous_T n (by linarith : 0 < p)).continuousOn
        (T_eq_zero_of_nonpos n p le_rfl) (T_tendsto_zero n p hpn) hcrit
      have hlower : n-(r+1)-1 ≤ Z.card := by
        apply IntegralPolynomialSignMoments.card_positive_zeros_ge_of_vanishing_moments
          (μ := volume) Z (continuous_T n (by linarith : 0 < p)).continuousOn
        · intro x hx
          exact ⟨fun hz => (hZ x).mpr ⟨hx, hz⟩, fun hz => ((hZ x).mp hz).2⟩
        · exact ⟨1/2, by norm_num, (T_half_pos n p).ne'⟩
        · apply monomial_moments n (n-(r+1)-1) (by linarith : 0 < p)
          have hnat : r+2 ≤ n := by omega
          have hsub : n-(r+1)-1 = n-(r+2) := by omega
          rw [hsub, Nat.cast_sub hnat]
          dsimp only [p]
          push_cast
          linarith
      have hsub : (S \ Z).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
      have hcardZ : Z.card = n-(r+1)-1 := by omega
      exact ⟨Z, hZ, hcardZ⟩
  exact hall r hr

/-- Floor-index version, requiring only that p is not its integer floor. -/
theorem exists_positive_zero_finset (n : ℕ) (p : ℝ) (hp : 0 < p) (hpn : p < (n : ℝ))
    (hnot : p ≠ (Nat.floor p : ℝ)) :
    ∃ Z : Finset ℝ, (∀ x : ℝ, x ∈ Z ↔ 0 < x ∧ T n p x = 0) ∧
      Z.card = n-Nat.floor p-1 := by
  let r : ℕ := Nat.floor p
  have hrle : (r : ℝ) ≤ p := Nat.floor_le hp.le
  have hδ : 0 < p-(r : ℝ) := sub_pos.mpr (lt_of_le_of_ne hrle (Ne.symm hnot))
  have hδ' : p-(r : ℝ) < 1 := by linarith [Nat.lt_floor_add_one p]
  have hr : r < n := (Nat.floor_lt hp.le).mpr hpn
  obtain ⟨Z, hZ, hcard⟩ := exists_positive_zero_finset_fractional n (p-(r : ℝ)) hδ hδ' r hr
  refine ⟨Z, ?_, hcard⟩
  intro x
  simpa only [sub_add_cancel] using hZ x

end IntegralTruncatedPowerNonintegerZeros


namespace IntegralTruncatedPowerIntegerZeros

open IntegralTruncatedPower IntegralTruncatedPowerMoments IntegralTruncatedPowerOne
open IntegralTruncatedPowerZeroBase

/-- Every positive integer exponent below n has support contained in [0,n]. -/
theorem T_nat_eq_zero_above (n r : ℕ) (hr : 1 ≤ r) (hrn : r < n)
    (t : ℝ) (ht : (n : ℝ) ≤ t) : T n (r : ℝ) t = 0 := by
  have hall : ∀ r : ℕ, 1 ≤ r → r < n →
      ∀ t : ℝ, (n : ℝ) ≤ t → T n (r : ℝ) t = 0 := by
    intro r
    induction r with
    | zero => intro hr; omega
    | succ r ih =>
      intro hr hrn t ht
      by_cases hrzero : r = 0
      · subst r
        simpa only [Nat.zero_add, Nat.cast_one] using T_one_eq_zero_above n (by omega) t ht
      · have hrpos : 1 ≤ r := by omega
        have hprev := ih hrpos (by omega)
        let p : ℝ := ((r+1 : ℕ) : ℝ)
        have hp : 1 < p := by dsimp only [p]; exact_mod_cast (show 1 < r+1 by omega)
        have hpn : p < (n : ℝ) := by dsimp only [p]; exact_mod_cast hrn
        have hp_prev : p-1 = (r : ℝ) := by dsimp only [p]; push_cast; ring
        have hd (x : ℝ) (hx : (n : ℝ) ≤ x) : HasDerivAt (T n p) 0 x := by
          have hd' := hasDerivAt_T n hp x
          rw [hp_prev, hprev x hx, mul_zero] at hd'
          exact hd'
        have hconst (u : ℝ) (hu : (n : ℝ) ≤ u) : T n p u = T n p n := by
          have hi : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (n : ℝ) u :=
            intervalIntegrable_const
          have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun x hx => hd x (by rw [Set.uIcc_of_le hu] at hx; exact hx.1)) hi
          have hz : T n p u - T n p n = 0 := by simpa only [intervalIntegral.integral_zero] using hFTC.symm
          exact sub_eq_zero.mp hz
        have hevent : T n p =ᶠ[atTop] (fun _ => T n p n) := by
          filter_upwards [eventually_ge_atTop (n : ℝ)] with u hu
          exact hconst u hu
        have hlimc : Tendsto (fun _ : ℝ => T n p n) atTop (𝓝 0) :=
          (T_tendsto_zero n p hpn).congr' hevent
        have hnzero : T n p n = 0 := tendsto_nhds_unique tendsto_const_nhds hlimc
        exact (hconst t ht).trans hnzero
  exact hall r hr hrn t ht

/-- All positive integer exponents have the sharp interior root count. -/
theorem exists_zero_finset (n r : ℕ) (hr : 1 ≤ r) (hrn : r < n) :
    ∃ Z : Finset ℝ,
      (∀ x : ℝ, x ∈ Z ↔ 0 < x ∧ x < n ∧ T n (r : ℝ) x = 0) ∧
        Z.card = n-r-1 := by
  have hall : ∀ r : ℕ, 1 ≤ r → r < n →
      ∃ Z : Finset ℝ,
        (∀ x : ℝ, x ∈ Z ↔ 0 < x ∧ x < n ∧ T n (r : ℝ) x = 0) ∧
          Z.card = n-r-1 := by
    intro r
    induction r with
    | zero => intro hr; omega
    | succ r ih =>
      intro hr hrn
      by_cases hrzero : r = 0
      · subst r
        obtain ⟨Z, hZ, hcard, _⟩ := exists_zero_finset_one n (by omega)
        refine ⟨Z, ?_, ?_⟩
        · simpa only [Nat.zero_add, Nat.cast_one] using hZ
        · simpa only [Nat.sub_sub] using hcard
      · have hrpos : 1 ≤ r := by omega
        obtain ⟨S, hS, hcardS⟩ := ih hrpos (by omega)
        let p : ℝ := ((r+1 : ℕ) : ℝ)
        have hp : 1 < p := by dsimp only [p]; exact_mod_cast (show 1 < r+1 by omega)
        have hp0 : 0 < p := by linarith
        have hpn : p < (n : ℝ) := by dsimp only [p]; exact_mod_cast hrn
        have hnpos : (0 : ℝ) < n := hp0.trans hpn
        have hp_prev : p-1 = (r : ℝ) := by dsimp only [p]; push_cast; ring
        have hcrit : ∀ x : ℝ, 0 < x → x < n → IsLocalExtr (T n p) x → x ∈ S := by
          intro x hx hxn hext
          have hd : HasDerivAt (T n p) (p * T n (r : ℝ) x) x := by
            simpa only [hp_prev] using hasDerivAt_T n hp x
          have hz : p * T n (r : ℝ) x = 0 := hext.hasDerivAt_eq_zero hd
          have hprevzero : T n (r : ℝ) x = 0 := (mul_eq_zero.mp hz).resolve_left hp0.ne'
          exact (hS x).mpr ⟨hx, hxn, hprevzero⟩
        obtain ⟨Z, hZ, hbound⟩ := IntegralBoundedRolle.exists_finset_zero_set
          (T n p) 0 n S hnpos (continuous_T n hp0).continuousOn
          (T_eq_zero_of_nonpos n p le_rfl)
          (T_nat_eq_zero_above n (r+1) (by omega) hrn n le_rfl) hcrit
        have hlower : n-(r+1)-1 ≤ Z.card := by
          apply IntegralPolynomialSignMoments.card_zeros_ge_of_vanishing_moments
            (μ := volume) Z (convex_Ioo (0 : ℝ) (n : ℝ)) isOpen_Ioo (continuous_T n hp0).continuousOn
          · intro x hx
            exact ⟨fun hz => (hZ x).mpr ⟨hx.1, hx.2, hz⟩, fun hz => ((hZ x).mp hz).2.2⟩
          · have hncast : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
            exact ⟨1/2, ⟨by norm_num, by linarith⟩, (T_half_pos n p).ne'⟩
          · intro k hk
            have hmoment : p + ((n-(r+1)-1 : ℕ) : ℝ) < (n : ℝ) := by
              have hnat : r+2 ≤ n := by omega
              have hsub : n-(r+1)-1 = n-(r+2) := by omega
              rw [hsub, Nat.cast_sub hnat]
              dsimp only [p]
              push_cast
              linarith
            have hm := monomial_moments n (n-(r+1)-1) hp0 hmoment k hk
            constructor
            · exact IntegrableOn.mono_set hm.1 Set.Ioo_subset_Ioi_self
            · have heq : (∫ x in Set.Ioi (0 : ℝ), T n p x * x^k) =
                  ∫ x in Set.Ioo (0 : ℝ) n, T n p x * x^k := by
                apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioo_subset_Ioi_self
                intro x hx
                have hxge : (n : ℝ) ≤ x := by
                  by_contra hnot
                  exact hx.2 ⟨hx.1, lt_of_not_ge hnot⟩
                rw [T_nat_eq_zero_above n (r+1) (by omega) hrn x hxge, zero_mul]
              rw [← heq]
              exact hm.2
        have hsub : (S \ Z).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
        have hcardZ : Z.card = n-(r+1)-1 := by omega
        exact ⟨Z, hZ, hcardZ⟩
  exact hall r hr hrn

end IntegralTruncatedPowerIntegerZeros


namespace IntegralTruncatedPowerQuotient

open IntegralTruncatedPower Asymptotics

lemma locallyIntegrable_truncatedPower {q : ℝ} (hq : -1 < q) :
    LocallyIntegrable (truncatedPower q) volume := by
  have hr : LocallyIntegrable (fun t : ℝ => t ^ q) volume := by
    intro x
    refine ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    exact (intervalIntegral.intervalIntegrable_rpow' hq).1.mono_set Set.Ioo_subset_Ioc_self
  have heq : truncatedPower q = (Set.Ioi (0 : ℝ)).indicator (fun t => t ^ q) := by
    funext t
    simp only [truncatedPower_eq_active, Set.indicator_apply, Set.mem_Ioi]
  rw [heq]
  exact hr.indicator measurableSet_Ioi

lemma locallyIntegrable_truncatedPower_sub {q : ℝ} (hq : -1 < q) (a : ℝ) :
    LocallyIntegrable (fun t : ℝ => truncatedPower q (t - a)) volume := by
  have hmap : Measure.map (Homeomorph.subRight a) volume = volume := by
    change Measure.map (fun t : ℝ => t - a) volume = volume
    simpa only [sub_eq_add_neg] using map_add_right_eq_self volume (-a)
  have hi : LocallyIntegrable (truncatedPower q)
      (Measure.map (Homeomorph.subRight a) volume) := by
    rw [hmap]
    exact locallyIntegrable_truncatedPower hq
  simpa only [Function.comp_def, Homeomorph.coe_subRight] using!
    (locallyIntegrable_map_homeomorph (Homeomorph.subRight a)).mp hi

lemma locallyIntegrable_difference_quotient {f : ℝ → ℝ} (hf : Continuous f)
    (x : ℝ) (hd : DifferentiableAt ℝ f x) :
    LocallyIntegrable (fun t : ℝ => (f t - f x) / (t - x)) volume := by
  have hc : Continuous (dslope f x) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases ht : t = x
    · subst t
      exact continuousAt_dslope_same.mpr hd
    · exact (continuousAt_dslope_of_ne ht).mpr hf.continuousAt
  apply hc.locallyIntegrable.congr
  filter_upwards [volume.ae_ne x] with t ht
  rw [dslope_of_ne f ht, slope_def_field]

lemma locallyIntegrable_power_difference_quotient {p : ℝ} (hp : 0 < p) (a x : ℝ) :
    LocallyIntegrable (fun t : ℝ =>
      (truncatedPower p (t - a) - truncatedPower p (x - a)) / (t - x)) volume := by
  by_cases hax : x = a
  · subst x
    have heq : (fun t : ℝ =>
        (truncatedPower p (t - a) - truncatedPower p (a - a)) / (t - a)) =
        (fun t : ℝ => truncatedPower (p - 1) (t - a)) := by
      funext t
      rw [sub_self, truncatedPower_of_nonpos p (le_refl 0), sub_zero]
      by_cases ht : 0 < t - a
      · rw [truncatedPower_of_pos p ht, truncatedPower_of_pos (p - 1) ht,
          Real.rpow_sub ht, Real.rpow_one]
      · rw [truncatedPower_of_nonpos p (le_of_not_gt ht),
          truncatedPower_of_nonpos (p - 1) (le_of_not_gt ht), zero_div]
    rw [heq]
    exact locallyIntegrable_truncatedPower_sub (by linarith : -1 < p - 1) a
  · apply locallyIntegrable_difference_quotient
      ((continuous_truncatedPower hp).comp (continuous_id.sub continuous_const)) x
    exact (((hasDerivAt_truncatedPower_of_ne p (sub_ne_zero.mpr hax)).comp x
      ((hasDerivAt_id x).sub_const a))).differentiableAt

lemma locallyIntegrable_T_quotient (n : ℕ) {p : ℝ} (hp : 0 < p) (x : ℝ)
    (hx : T n p x = 0) :
    LocallyIntegrable (fun t : ℝ => T n p t / (t - x)) volume := by
  have hli : ∀ j ∈ Finset.range (n + 1), LocallyIntegrable (fun t : ℝ =>
      ((-1 : ℝ) ^ j * (n.choose j : ℝ)) *
        ((truncatedPower p (t - (j : ℝ)) - truncatedPower p (x - (j : ℝ))) /
          (t - x))) volume := by
    intro j hj
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      (locallyIntegrable_power_difference_quotient hp (j : ℝ) x).smul
        ((-1 : ℝ) ^ j * (n.choose j : ℝ))
  have heq : (fun t : ℝ => T n p t / (t - x)) = (fun t : ℝ =>
      ∑ j ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ j * (n.choose j : ℝ)) *
          ((truncatedPower p (t - (j : ℝ)) - truncatedPower p (x - (j : ℝ))) /
            (t - x))) := by
    funext t
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    congr 1
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    change T n p t = T n p t - T n p x
    rw [hx, sub_zero]
  rw [heq]
  exact locallyIntegrable_finsetSum (Finset.range (n + 1)) hli

lemma inverse_sub_isBigO (x : ℝ) :
    (fun t : ℝ => (t - x)⁻¹) =O[atTop] (fun t : ℝ => t ^ (-1 : ℝ)) := by
  apply IsBigO.of_bound (2 : ℝ)
  filter_upwards [eventually_ge_atTop (max 1 (2 * |x|))] with t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htx : 2 * |x| ≤ t := (le_max_right _ _).trans ht
  have htpos : 0 < t := by linarith
  have hxpos : 0 < t - x := by linarith [le_abs_self x]
  have hhalf : t / 2 ≤ t - x := by linarith [le_abs_self x]
  simp only [Real.norm_eq_abs, abs_inv, Real.rpow_neg_one,
    abs_of_pos htpos, abs_of_pos hxpos]
  calc
    (t - x)⁻¹ = 1 / (t - x) := (one_div _).symm
    _ ≤ 1 / (t / 2) := one_div_le_one_div_of_le (by linarith) hhalf
    _ = 2 * t⁻¹ := by field_simp

lemma quotient_isBigO (n : ℕ) (p x : ℝ) :
    (fun t : ℝ => T n p t / (t - x)) =O[atTop]
      (fun t : ℝ => t ^ (p - (n : ℝ) - 1)) := by
  refine ((IntegralTruncatedPowerTail.tail_isBigO n p).mul (inverse_sub_isBigO x)).congr'
    (Filter.Eventually.of_forall (fun t => (div_eq_mul_inv _ _).symm)) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [← Real.rpow_add ht]
  congr 1

lemma integrableOn_T_quotient (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hpn : p < (n : ℝ)) (x : ℝ) (hx : T n p x = 0) :
    IntegrableOn (fun t : ℝ => T n p t / (t - x)) (Set.Ioi 0) := by
  have hl := (locallyIntegrable_T_quotient n hp x hx).locallyIntegrableOn (Set.Ici (0 : ℝ))
  have hg : IntegrableAtFilter (fun t : ℝ => t ^ (p - (n : ℝ) - 1)) atTop :=
    integrableAtFilter_rpow_atTop_iff.mpr (by linarith)
  exact (hl.integrableOn_of_isBigO_atTop (quotient_isBigO n p x) hg).mono_set
    Set.Ioi_subset_Ici_self

end IntegralTruncatedPowerQuotient


namespace IntegralTruncatedPowerCauchyNonzero

open IntegralTruncatedPower IntegralTruncatedPowerMoments IntegralTruncatedPowerZeroBase
open IntegralTruncatedPowerQuotient

/-- The actual Cauchy quotient cannot vanish at a root for noninteger p. -/
theorem cauchy_nonzero_noninteger (n : ℕ) (p : ℝ) (hp : 0 < p) (hpn : p < (n : ℝ))
    (hnot : p ≠ (Nat.floor p : ℝ)) (x : ℝ) (hx : T n p x = 0) :
    (∫ t in Set.Ioi (0 : ℝ), T n p t / (t-x)) ≠ 0 := by
  obtain ⟨Z, hZ, hcard⟩ := IntegralTruncatedPowerNonintegerZeros.exists_positive_zero_finset
    n p hp hpn hnot
  have hZs : ∀ t ∈ Set.Ioi (0 : ℝ), T n p t = 0 ↔ t ∈ Z := by
    intro t ht
    exact ⟨fun hz => (hZ t).mpr ⟨ht, hz⟩, fun hz => ((hZ t).mp hz).2⟩
  have hne : ∃ t ∈ Set.Ioi (0 : ℝ), T n p t ≠ 0 :=
    ⟨1/2, by norm_num, (T_half_pos n p).ne'⟩
  have hmoment : p + (Z.card : ℝ) < (n : ℝ) := by
    have hrn : Nat.floor p < n := (Nat.floor_lt hp.le).mpr hpn
    have hnat : Nat.floor p+1 ≤ n := by omega
    have hsub : n-Nat.floor p-1 = n-(Nat.floor p+1) := by omega
    rw [hcard, hsub, Nat.cast_sub hnat]
    push_cast
    linarith [Nat.lt_floor_add_one p]
  have hmom := monomial_moments n Z.card hp hmoment
  have hg := integrableOn_T_quotient n hp hpn x hx
  by_cases hxpos : 0 < x
  · exact IntegralMinimalCauchy.cauchy_ne_zero_at_minimal_root
      (μ := volume) Z (convex_Ioi (0 : ℝ)) isOpen_Ioi (continuous_T n hp).continuousOn
      hZs hne hmom x ((hZ x).mpr ⟨hxpos, hx⟩) hg
  · exact IntegralMinimalCauchy.cauchy_ne_zero_outside_minimal_roots
      (μ := volume) Z (convex_Ioi (0 : ℝ)) isOpen_Ioi (continuous_T n hp).continuousOn
      hZs hne hmom x (Or.inl (fun t ht => lt_of_le_of_lt (le_of_not_gt hxpos) ht)) hg

/-- The integer branch uses the actual compact support and its sharp root count. -/
theorem cauchy_nonzero_integer (n r : ℕ) (hr : 1 ≤ r) (hrn : r < n)
    (x : ℝ) (hx : T n (r : ℝ) x = 0) :
    (∫ t in Set.Ioi (0 : ℝ), T n (r : ℝ) t / (t-x)) ≠ 0 := by
  have hp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hpn : (r : ℝ) < n := by exact_mod_cast hrn
  have hncast : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  obtain ⟨Z, hZ, hcard⟩ := IntegralTruncatedPowerIntegerZeros.exists_zero_finset n r hr hrn
  have hZs : ∀ t ∈ Set.Ioo (0 : ℝ) n, T n (r : ℝ) t = 0 ↔ t ∈ Z := by
    intro t ht
    exact ⟨fun hz => (hZ t).mpr ⟨ht.1, ht.2, hz⟩, fun hz => ((hZ t).mp hz).2.2⟩
  have hne : ∃ t ∈ Set.Ioo (0 : ℝ) n, T n (r : ℝ) t ≠ 0 :=
    ⟨1/2, ⟨by norm_num, by linarith⟩, (T_half_pos n r).ne'⟩
  have hmoment : (r : ℝ) + (Z.card : ℝ) < (n : ℝ) := by
    have hnat : r+1 ≤ n := by omega
    have hsub : n-r-1 = n-(r+1) := by omega
    rw [hcard, hsub, Nat.cast_sub hnat]
    push_cast
    linarith
  have hmom : ∀ k < Z.card,
      Integrable (fun t : ℝ => T n (r : ℝ) t * t^k) (volume.restrict (Set.Ioo 0 n)) ∧
        (∫ t in Set.Ioo (0 : ℝ) n, T n (r : ℝ) t * t^k) = 0 := by
    intro k hk
    have hm := monomial_moments n Z.card hp hmoment k hk
    constructor
    · exact IntegrableOn.mono_set hm.1 Set.Ioo_subset_Ioi_self
    · have heq : (∫ t in Set.Ioi (0 : ℝ), T n (r : ℝ) t * t^k) =
          ∫ t in Set.Ioo (0 : ℝ) n, T n (r : ℝ) t * t^k := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioo_subset_Ioi_self
        intro t ht
        have htge : (n : ℝ) ≤ t := by
          by_contra hnot
          exact ht.2 ⟨ht.1, lt_of_not_ge hnot⟩
        rw [IntegralTruncatedPowerIntegerZeros.T_nat_eq_zero_above n r hr hrn t htge, zero_mul]
      rw [← heq]
      exact hm.2
  have hg := IntegrableOn.mono_set (integrableOn_T_quotient n hp hpn x hx)
    (Set.Ioo_subset_Ioi_self : Set.Ioo (0 : ℝ) n ⊆ Set.Ioi 0)
  have heq : (∫ t in Set.Ioi (0 : ℝ), T n (r : ℝ) t / (t-x)) =
      ∫ t in Set.Ioo (0 : ℝ) n, T n (r : ℝ) t / (t-x) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioo_subset_Ioi_self
    intro t ht
    have htge : (n : ℝ) ≤ t := by
      by_contra hnot
      exact ht.2 ⟨ht.1, lt_of_not_ge hnot⟩
    rw [IntegralTruncatedPowerIntegerZeros.T_nat_eq_zero_above n r hr hrn t htge, zero_div]
  rw [heq]
  by_cases hxin : x ∈ Set.Ioo (0 : ℝ) n
  · exact IntegralMinimalCauchy.cauchy_ne_zero_at_minimal_root
      (μ := volume) Z (convex_Ioo (0 : ℝ) (n : ℝ)) isOpen_Ioo
      (continuous_T n hp).continuousOn hZs hne hmom x ((hZ x).mpr ⟨hxin.1, hxin.2, hx⟩) hg
  · have hside : (∀ t ∈ Set.Ioo (0 : ℝ) n, x < t) ∨
        (∀ t ∈ Set.Ioo (0 : ℝ) n, t < x) := by
      by_cases hxle : x ≤ 0
      · exact Or.inl (fun t ht => lt_of_le_of_lt hxle ht.1)
      · have hxge : (n : ℝ) ≤ x := by
          by_contra hnot
          exact hxin ⟨lt_of_not_ge hxle, lt_of_not_ge hnot⟩
        exact Or.inr (fun t ht => lt_of_lt_of_le ht.2 hxge)
    exact IntegralMinimalCauchy.cauchy_ne_zero_outside_minimal_roots
      (μ := volume) Z (convex_Ioo (0 : ℝ) (n : ℝ)) isOpen_Ioo
      (continuous_T n hp).continuousOn hZs hne hmom x hside hg

/-- Full positive-exponent real Cauchy nonvanishing for the actual finite difference. -/
theorem cauchy_nonzero (n : ℕ) (p : ℝ) (hp : 0 < p) (hpn : p < (n : ℝ))
    (x : ℝ) (hx : T n p x = 0) :
    (∫ t in Set.Ioi (0 : ℝ), T n p t / (t-x)) ≠ 0 := by
  by_cases hint : p = (Nat.floor p : ℝ)
  · let r : ℕ := Nat.floor p
    have he : p = (r : ℝ) := hint
    have hrreal : (0 : ℝ) < r := by rw [← he]; exact hp
    have hr : 1 ≤ r := by exact_mod_cast hrreal
    have hrn : r < n := (Nat.floor_lt hp.le).mpr hpn
    have hx' : T n (r : ℝ) x = 0 := by rw [← he]; exact hx
    have h := cauchy_nonzero_integer n r hr hrn x hx'
    simpa only [← he] using h
  · exact cauchy_nonzero_noninteger n p hp hpn hint x hx

end IntegralTruncatedPowerCauchyNonzero


namespace IntegralCauchyBoundary

lemma norm_cauchy_kernel_le_real_quotient (f t x ε : ℝ) (ht : t ≠ x) :
    ‖(f : ℂ) / (((t - x : ℝ) : ℂ) - Complex.I * (ε : ℂ))‖ ≤
      ‖f / (t - x)‖ := by
  have hden : ‖t - x‖ ≤ ‖((t - x : ℝ) : ℂ) - Complex.I * (ε : ℂ)‖ := by
    simpa [Real.norm_eq_abs] using
      Complex.abs_re_le_norm (((t - x : ℝ) : ℂ) - Complex.I * (ε : ℂ))
  rw [norm_div, norm_div, Complex.norm_real]
  exact div_le_div_of_nonneg_left (norm_nonneg f)
    (norm_pos_iff.mpr (sub_ne_zero.mpr ht)) hden

theorem tendsto_cauchy_boundary_of_integrable_quotient
    {μ : Measure ℝ} [NullSingletonClass μ]
    {f : ℝ → ℝ} (x : ℝ)
    (hf : AEStronglyMeasurable (fun t => (f t : ℂ)) μ)
    (hg : Integrable (fun t => f t / (t - x)) μ) :
    Tendsto
      (fun ε : ℝ => ∫ t, (f t : ℂ) /
        (((t - x : ℝ) : ℂ) - Complex.I * (ε : ℂ)) ∂μ)
      (𝓝 0) (𝓝 ((∫ t, f t / (t - x) ∂μ : ℝ) : ℂ)) := by
  have hmeas (ε : ℝ) : AEStronglyMeasurable
      (fun t => (f t : ℂ) / (((t - x : ℝ) : ℂ) - Complex.I * (ε : ℂ))) μ := by
    apply hf.div₀
    exact (((Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).sub
      continuous_const).aestronglyMeasurable)
  have hlim : ∀ᵐ t ∂μ, Tendsto
      (fun ε : ℝ => (f t : ℂ) /
        (((t - x : ℝ) : ℂ) - Complex.I * (ε : ℂ)))
      (𝓝 0) (𝓝 ((f t / (t - x) : ℝ) : ℂ)) := by
    filter_upwards [μ.ae_ne x] with t ht
    have hd : Tendsto
        (fun ε : ℝ => ((t - x : ℝ) : ℂ) - Complex.I * (ε : ℂ))
        (𝓝 0) (𝓝 ((t - x : ℝ) : ℂ)) := by
      have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).ofReal
      have hterm : Tendsto (fun ε : ℝ => Complex.I * (ε : ℂ)) (𝓝 0) (𝓝 0) := by
        simpa using hε.const_mul Complex.I
      simpa only [sub_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => ((t - x : ℝ) : ℂ))
          (𝓝 0) (𝓝 ((t - x : ℝ) : ℂ))).sub hterm
    have hh : Tendsto
        (fun ε : ℝ => (f t : ℂ) /
          (((t - x : ℝ) : ℂ) - Complex.I * (ε : ℂ)))
        (𝓝 0) (𝓝 ((f t : ℂ) / ((t - x : ℝ) : ℂ))) :=
      tendsto_const_nhds.div hd (by exact_mod_cast sub_ne_zero.mpr ht)
    simpa only [Complex.ofReal_div] using hh
  have hb : ∀ᶠ ε : ℝ in 𝓝 0, ∀ᵐ t ∂μ,
      ‖(f t : ℂ) / (((t - x : ℝ) : ℂ) - Complex.I * (ε : ℂ))‖ ≤
        ‖f t / (t - x)‖ := by
    apply Eventually.of_forall
    intro ε
    filter_upwards [μ.ae_ne x] with t ht
    exact norm_cauchy_kernel_le_real_quotient (f t) t x ε ht
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖f t / (t - x)‖) (Eventually.of_forall hmeas) hb hg.norm hlim
  simpa only [integral_complex_ofReal] using h

end IntegralCauchyBoundary


namespace IntegralStieltjesPositive

lemma stieltjes_neg_I_im (q u : ℝ) :
    (((u ^ q : ℝ) : ℂ) / ((u : ℂ) - Complex.I)).im =
      u ^ q / (u ^ 2 + 1) := by
  simp [Complex.div_im, Complex.normSq_apply, pow_two, neg_div]

theorem integral_stieltjes_neg_I_im_pos (q : ℝ)
    (hi : IntegrableOn (fun u : ℝ => ((u ^ q : ℝ) : ℂ) /
      ((u : ℂ) - Complex.I)) (Ioi 0)) :
    0 < (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) /
      ((u : ℂ) - Complex.I)).im := by
  have hp (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
      0 < (((u ^ q : ℝ) : ℂ) / ((u : ℂ) - Complex.I)).im := by
    rw [stieltjes_neg_I_im]
    exact div_pos (Real.rpow_pos_of_pos hu _) (by positivity)
  have hnonneg : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ (((u ^ q : ℝ) : ℂ) / ((u : ℂ) - Complex.I)).im := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hp u hu).le
  have hs : Function.support (fun u : ℝ =>
      (((u ^ q : ℝ) : ℂ) / ((u : ℂ) - Complex.I)).im) ∩ Ioi 0 = Ioi 0 := by
    apply inter_eq_right.mpr
    intro u hu
    exact (hp u hu).ne'
  have him := integral_im hi
  change (∫ u : ℝ in Ioi 0, (((u ^ q : ℝ) : ℂ) /
    ((u : ℂ) - Complex.I)).im) =
      (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) /
        ((u : ℂ) - Complex.I)).im at him
  rw [← him]
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hi.im).mpr
  change 0 < volume (Function.support (fun u : ℝ =>
    (((u ^ q : ℝ) : ℂ) / ((u : ℂ) - Complex.I)).im) ∩ Ioi 0)
  rw [hs]
  simp

theorem integral_stieltjes_neg_I_ne_zero (q : ℝ)
    (hi : IntegrableOn (fun u : ℝ => ((u ^ q : ℝ) : ℂ) /
      ((u : ℂ) - Complex.I)) (Ioi 0)) :
    (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) /
      ((u : ℂ) - Complex.I)) ≠ 0 := by
  intro hz
  have hp := integral_stieltjes_neg_I_im_pos q hi
  simp [hz] at hp

lemma continuousOn_real_stieltjes_one (q : ℝ) :
    ContinuousOn (fun u : ℝ => u ^ q / (u + 1)) (Ioi 0) := by
  apply ContinuousOn.div
  · exact continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt hu))
  · fun_prop
  · intro u hu
    exact (add_pos hu zero_lt_one).ne'

theorem integrableOn_real_stieltjes_one (q : ℝ) (hq : -1 < q) (hq' : q < 0) :
    IntegrableOn (fun u : ℝ => u ^ q / (u + 1)) (Ioi 0) := by
  have hnear : IntegrableOn (fun u : ℝ => u ^ q / (u + 1)) (Ioo 0 1) := by
    apply ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr hq).mono'
      ((continuousOn_real_stieltjes_one q).mono Ioo_subset_Ioi_self
        |>.aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hr : 0 ≤ u ^ q := Real.rpow_nonneg hu.1.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr (by linarith [hu.1]))]
    exact div_le_self hr (by linarith [hu.1])
  have htail : IntegrableOn (fun u : ℝ => u ^ q / (u + 1)) (Ioi 1) := by
    apply (integrableOn_Ioi_rpow_of_lt (by linarith : q - 1 < -1) zero_lt_one).mono'
      ((continuousOn_real_stieltjes_one q).mono (Ioi_subset_Ioi zero_le_one)
        |>.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    have hr : 0 ≤ u ^ q := Real.rpow_nonneg hu0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr (by linarith))]
    calc
      u ^ q / (u + 1) ≤ u ^ q / u :=
        div_le_div_of_nonneg_left hr hu0 (by linarith)
      _ = u ^ (q - 1) := by rw [Real.rpow_sub hu0, Real.rpow_one]
  have htail' : IntegrableOn (fun u : ℝ => u ^ q / (u + 1)) (Ici 1) := by
    rwa [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa only [Ioo_union_Ici_eq_Ioi zero_lt_one] using hnear.union htail'

theorem integral_real_stieltjes_one_pos (q : ℝ) (hq : -1 < q) (hq' : q < 0) :
    0 < ∫ u : ℝ in Ioi 0, u ^ q / (u + 1) := by
  have hp (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) : 0 < u ^ q / (u + 1) :=
    div_pos (Real.rpow_pos_of_pos hu _) (add_pos hu zero_lt_one)
  have hn : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ u ^ q / (u + 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hp u hu).le
  have hs : Function.support (fun u : ℝ => u ^ q / (u + 1)) ∩ Ioi 0 = Ioi 0 := by
    apply inter_eq_right.mpr
    intro u hu
    exact (hp u hu).ne'
  apply (setIntegral_pos_iff_support_of_nonneg_ae hn
    (integrableOn_real_stieltjes_one q hq hq')).mpr
  rw [hs]
  simp

end IntegralStieltjesPositive


namespace IntegralStieltjesPositive

/-- Identify an initially unknown complex Stieltjes scalar by an exterior
boundary limit, without evaluating a beta or Gamma integral. -/
theorem stieltjes_scalar_eq_real_integral
    (q : ℝ) (hq : -1 < q) (hq' : q < 0) (K : ℂ)
    (hK : ∀ a : ℂ, a.im < 0 →
      (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a)) =
        K * a ^ (q : ℂ)) :
    K = ((∫ u : ℝ in Ioi 0, u ^ q / (u + 1) : ℝ) : ℂ) := by
  have hf : AEStronglyMeasurable (fun u : ℝ => ((u ^ q : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt hu)))
      |>.aestronglyMeasurable measurableSet_Ioi)
  have hg : Integrable (fun u : ℝ => u ^ q / (u - (-1)))
      (volume.restrict (Ioi 0)) := by
    simpa only [sub_neg_eq_add, IntegrableOn] using integrableOn_real_stieltjes_one q hq hq'
  have hb := IntegralCauchyBoundary.tendsto_cauchy_boundary_of_integrable_quotient
    (-1) hf hg
  have heq (ε : ℝ) :
      (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) /
        ((u : ℂ) + (1 - Complex.I * (ε : ℂ)))) =
      (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) /
        (((u - (-1) : ℝ) : ℂ) - Complex.I * (ε : ℂ))) := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro u
    push_cast
    ring
  have hb' : Tendsto
      (fun ε : ℝ => ∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) /
        ((u : ℂ) + (1 - Complex.I * (ε : ℂ))))
      (𝓝[>] 0) (𝓝 ((∫ u : ℝ in Ioi 0, u ^ q / (u + 1) : ℝ) : ℂ)) := by
    simpa only [heq, sub_neg_eq_add] using hb.mono_left nhdsWithin_le_nhds
  have ha : Tendsto (fun ε : ℝ => (1 : ℂ) - Complex.I * (ε : ℂ))
      (𝓝 0) (𝓝 1) := by
    have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).ofReal
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ))
      (𝓝 0) (𝓝 1)).sub (hε.const_mul Complex.I)
  have hpow : Tendsto
      (fun ε : ℝ => ((1 : ℂ) - Complex.I * (ε : ℂ)) ^ (q : ℂ))
      (𝓝[>] 0) (𝓝 1) := by
    have hc :=
      ((continuousAt_cpow_const (b := (q : ℂ))
        (by simp [Complex.mem_slitPlane_iff] : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp
        ha).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    convert hc using 1 <;> first | rfl | simp only [Complex.one_cpow]
  have hrel :
      (fun ε : ℝ => ∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) /
        ((u : ℂ) + (1 - Complex.I * (ε : ℂ)))) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => K * ((1 : ℂ) - Complex.I * (ε : ℂ)) ^ (q : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply hK
    change 0 < ε at hε
    simpa using neg_lt_zero.mpr hε
  have hk : Tendsto
      (fun ε : ℝ => ∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) /
        ((u : ℂ) + (1 - Complex.I * (ε : ℂ))))
      (𝓝[>] 0) (𝓝 K) := by
    have hmul : Tendsto
        (fun ε : ℝ => K * ((1 : ℂ) - Complex.I * (ε : ℂ)) ^ (q : ℂ))
        (𝓝[>] 0) (𝓝 K) := by
      simpa using hpow.const_mul K
    exact hmul.congr' hrel.symm
  exact (tendsto_nhds_unique hb' hk).symm

theorem stieltjes_scalar_is_positive_real
    (q : ℝ) (hq : -1 < q) (hq' : q < 0) (K : ℂ)
    (hK : ∀ a : ℂ, a.im < 0 →
      (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a)) =
        K * a ^ (q : ℂ)) :
    ∃ k : ℝ, 0 < k ∧ K = (k : ℂ) := by
  exact ⟨_, integral_real_stieltjes_one_pos q hq hq',
    stieltjes_scalar_eq_real_integral q hq hq' K hK⟩

end IntegralStieltjesPositive


namespace IntegralStieltjesODE

lemma hasDerivAt_ratio_cpow {S : ℂ → ℂ} {q a : ℂ}
    (ha : a ∈ Complex.slitPlane)
    (hS : HasDerivAt S (q * S a / a) a) :
    HasDerivAt (fun z => S z / z ^ q) 0 a := by
  have hane : a ≠ 0 := Complex.slitPlane_ne_zero ha
  have hpow : HasDerivAt (fun z : ℂ => z ^ q) (q * a ^ q / a) a := by
    simpa only [id_eq, mul_one, Complex.cpow_sub q 1 hane, Complex.cpow_one,
      mul_div_assoc] using (hasDerivAt_id a).cpow_const (c := q) ha
  have hpne : a ^ q ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hane)
  have hnum : (q * S a / a) * a ^ q - S a * (q * a ^ q / a) = 0 := by ring
  convert hS.div hpow hpne using 1
  · rfl
  · rfl
  · rfl
  · rw [hnum, zero_div]

theorem exists_nonzero_cpow_scalar_of_lower_half_plane_ode
    (S : ℂ → ℂ) (q : ℂ)
    (hS : ∀ a : ℂ, a.im < 0 → HasDerivAt S (q * S a / a) a)
    (hne : S (-Complex.I) ≠ 0) :
    ∃ K : ℂ, K ≠ 0 ∧ ∀ a : ℂ, a.im < 0 → S a = K * a ^ q := by
  have hratio (a : ℂ) (ha : a.im < 0) :
      HasDerivAt (fun z => S z / z ^ q) 0 a :=
    hasDerivAt_ratio_cpow (Or.inr (ne_of_lt ha)) (hS a ha)
  have hopen : IsOpen {a : ℂ | a.im < 0} :=
    isOpen_lt Complex.continuous_im continuous_const
  have hbase : (-Complex.I).im < 0 := by simp
  have hpow : (-Complex.I) ^ q ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (neg_ne_zero.mpr Complex.I_ne_zero))
  refine ⟨S (-Complex.I) / (-Complex.I) ^ q, div_ne_zero hne hpow, ?_⟩
  intro a ha
  have heq : S a / a ^ q = S (-Complex.I) / (-Complex.I) ^ q :=
    hopen.is_const_of_deriv_eq_zero (convex_halfSpace_im_lt 0).isPreconnected
      (fun z hz => (hratio z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hratio z hz).deriv) ha hbase
  have hane : a ≠ 0 := fun h => by simp [h] at ha
  exact (div_eq_iff (Complex.cpow_ne_zero_iff.mpr (Or.inl hane))).mp heq

end IntegralStieltjesODE


namespace IntegralStieltjesIBP

lemma add_ofReal_ne_zero (a : ℂ) (ha : a.im < 0) (u : ℝ) :
    (u : ℂ) + a ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] at hi
  exact (ne_of_lt ha) hi

lemma parameter_ne_zero (a : ℂ) (ha : a.im < 0) : a ≠ 0 := by
  simpa using add_ofReal_ne_zero a ha 0

lemma primitive_continuousAt_zero (q : ℝ) (a : ℂ)
    (hq : -1 < q) (ha : a ≠ 0) :
    ContinuousAt (fun u : ℝ => ((u ^ (q + 1) : ℝ) : ℂ) / ((u : ℂ) + a)) 0 := by
  have hn := (Complex.continuous_ofReal.comp
    (Real.continuous_rpow_const (by linarith : 0 ≤ q + 1))).continuousAt (x := 0)
  have hd : ContinuousAt (fun u : ℝ => (u : ℂ) + a) 0 :=
    Complex.continuous_ofReal.continuousAt.add_const a
  exact hn.div hd (by simpa using ha)

lemma primitive_tendsto_atTop_zero (q : ℝ) (a : ℂ) (hq : q < 0)
    (ha : a.im < 0) :
    Tendsto (fun u : ℝ => ((u ^ (q + 1) : ℝ) : ℂ) / ((u : ℂ) + a))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℝ => ((u ^ q : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [neg_neg, Complex.ofReal_zero] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hq)).ofReal
  have hi : Tendsto (fun u : ℝ => ((u : ℂ))⁻¹) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0)).ofReal
  have hd : Tendsto (fun u : ℝ => 1 + a / (u : ℂ)) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hi)
  have ht := hp.div hd (one_ne_zero : (1 : ℂ) ≠ 0)
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
  have hden := add_ofReal_ne_zero a ha u
  change ((u ^ q : ℝ) : ℂ) / (1 + a / (u : ℂ)) =
    ((u ^ (q + 1) : ℝ) : ℂ) / ((u : ℂ) + a)
  rw [Real.rpow_add hu, Real.rpow_one, Complex.ofReal_mul]
  field_simp

lemma hasDerivAt_primitive (q : ℝ) (a : ℂ) (ha : a.im < 0)
    (u : ℝ) (hu : 0 < u) :
    HasDerivAt
      (fun v : ℝ => ((v ^ (q + 1) : ℝ) : ℂ) / ((v : ℂ) + a))
      ((q : ℂ) * (((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a)) +
        a * (((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a) ^ 2)) u := by
  have hn : HasDerivAt (fun v : ℝ => ((v ^ (q + 1) : ℝ) : ℂ))
      (((q + 1 : ℝ) : ℂ) * ((u ^ q : ℝ) : ℂ)) u := by
    simpa only [add_sub_cancel_right, Complex.ofReal_mul] using
      (Real.hasDerivAt_rpow_const (x := u) (p := q + 1)
        (Or.inl (ne_of_gt hu))).ofReal_comp
  have hd : HasDerivAt (fun v : ℝ => (v : ℂ) + a) 1 u := by
    simpa only [Complex.ofReal_one, id_eq] using! (hasDerivAt_id u).ofReal_comp.add_const a
  convert! hn.div hd (add_ofReal_ne_zero a ha u) using 1
  rw [Real.rpow_add hu, Real.rpow_one, Complex.ofReal_mul]
  push_cast
  field_simp
  ring

/-- The actual raw-integral identity; no endpoint limit is assumed. -/
theorem integral_kernel_sq_eq (q : ℝ) (a : ℂ)
    (hq : -1 < q) (hq' : q < 0) (ha : a.im < 0)
    (hK : IntegrableOn (fun u : ℝ => ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a)) (Ioi 0))
    (hK2 : IntegrableOn (fun u : ℝ => ((u ^ q : ℝ) : ℂ) /
      ((u : ℂ) + a) ^ 2) (Ioi 0)) :
    (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a) ^ 2) =
      -((q : ℂ) / a) *
        (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a)) := by
  have hane := parameter_ne_zero a ha
  have hdi : IntegrableOn
      (fun u : ℝ => (q : ℂ) * (((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a)) +
        a * (((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a) ^ 2)) (Ioi 0) :=
    (hK.const_mul (q : ℂ)).add (hK2.const_mul a)
  have hzero := integral_Ioi_of_hasDerivAt_of_tendsto
    (primitive_continuousAt_zero q a hq hane).continuousWithinAt
    (fun u hu => hasDerivAt_primitive q a ha u hu) hdi
    (primitive_tendsto_atTop_zero q a hq' ha)
  simp only [Real.zero_rpow (by linarith : q + 1 ≠ 0), Complex.ofReal_zero,
    zero_div, sub_zero] at hzero
  rw [integral_add (hK.const_mul _) (hK2.const_mul _),
    integral_const_mul, integral_const_mul] at hzero
  apply (mul_left_cancel₀ hane)
  calc
    a * (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a) ^ 2) =
        ((q : ℂ) * (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a)) +
          a * (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a) ^ 2)) -
        (q : ℂ) * (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a)) := by ring
    _ = - (q : ℂ) *
        (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a)) := by rw [hzero]; ring
    _ = a * (-((q : ℂ) / a) *
        (∫ u : ℝ in Ioi 0, ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a))) := by
      field_simp

end IntegralStieltjesIBP


namespace IntegralStieltjesTransform

noncomputable def kernel (q : ℝ) (a : ℂ) (u : ℝ) : ℂ :=
  ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a)

noncomputable def kernelSq (q : ℝ) (a : ℂ) (u : ℝ) : ℂ :=
  ((u ^ q : ℝ) : ℂ) / ((u : ℂ) + a) ^ 2

noncomputable def S (q : ℝ) (a : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi 0, kernel q a u

lemma measurable_kernel (q : ℝ) (a : ℂ) : Measurable (kernel q a) := by
  unfold kernel
  fun_prop

lemma measurable_kernelSq (q : ℝ) (a : ℂ) : Measurable (kernelSq q a) := by
  unfold kernelSq
  fun_prop

lemma imag_bound (a : ℂ) (u : ℝ) : -a.im ≤ ‖(u : ℂ) + a‖ := by
  have h := Complex.abs_im_le_norm ((u : ℂ) + a)
  simp only [Complex.add_im, Complex.ofReal_im, zero_add] at h
  exact (neg_le_abs a.im).trans h

lemma norm_kernel (q : ℝ) (a : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖kernel q a u‖ = u ^ q / ‖(u : ℂ) + a‖ := by
  simp [kernel, Complex.norm_real, abs_of_nonneg (Real.rpow_nonneg hu _)]

lemma norm_kernelSq (q : ℝ) (a : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖kernelSq q a u‖ = u ^ q / ‖(u : ℂ) + a‖ ^ 2 := by
  simp [kernelSq, norm_pow, Complex.norm_real,
    abs_of_nonneg (Real.rpow_nonneg hu _)]

lemma norm_kernel_le_real_one (q : ℝ) {a : ℂ} (ha : a.im < 0)
    {u : ℝ} (hu : 0 < u) :
    ‖kernel q a u‖ ≤ (1 + (‖a‖ + 1) / (-a.im)) * (u ^ q / (u + 1)) := by
  have hc : 0 < -a.im := by linarith
  have hd : 0 < ‖(u : ℂ) + a‖ := hc.trans_le (imag_bound a u)
  have htri := norm_sub_le ((u : ℂ) + a) a
  simp only [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu] at htri
  have hmul : ‖a‖ + 1 ≤ ((‖a‖ + 1) / (-a.im)) * ‖(u : ℂ) + a‖ := by
    calc
      ‖a‖ + 1 = ((‖a‖ + 1) / (-a.im)) * (-a.im) := by field_simp [ne_of_lt ha]
      _ ≤ _ := mul_le_mul_of_nonneg_left (imag_bound a u) (by positivity)
  have hratio : (u + 1) / ‖(u : ℂ) + a‖ ≤ 1 + (‖a‖ + 1) / (-a.im) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  rw [norm_kernel q a hu.le]
  calc
    u ^ q / ‖(u : ℂ) + a‖ =
        (u ^ q / (u + 1)) * ((u + 1) / ‖(u : ℂ) + a‖) := by
      field_simp
    _ ≤ (u ^ q / (u + 1)) * (1 + (‖a‖ + 1) / (-a.im)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

lemma integrable_kernel (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (a : ℂ) (ha : a.im < 0) : IntegrableOn (kernel q a) (Ioi 0) := by
  apply ((IntegralStieltjesPositive.integrableOn_real_stieltjes_one q hq hq0).const_mul
    (1 + (‖a‖ + 1) / (-a.im))).mono' (measurable_kernel q a).aestronglyMeasurable
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => norm_kernel_le_real_one q ha hu

lemma kernelSq_eq_div (q : ℝ) (a : ℂ) (u : ℝ) :
    kernelSq q a u = kernel q a u / ((u : ℂ) + a) := by
  simp only [kernelSq, kernel, div_div, pow_two]

lemma norm_kernelSq_le (q : ℝ) {a : ℂ} (ha : a.im < 0) (u : ℝ) :
    ‖kernelSq q a u‖ ≤ (1 / (-a.im)) * ‖kernel q a u‖ := by
  rw [kernelSq_eq_div, norm_div]
  calc
    ‖kernel q a u‖ / ‖(u : ℂ) + a‖ ≤ ‖kernel q a u‖ / (-a.im) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) (imag_bound a u)
    _ = (1 / (-a.im)) * ‖kernel q a u‖ := by ring

lemma integrable_kernelSq (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (a : ℂ) (ha : a.im < 0) : IntegrableOn (kernelSq q a) (Ioi 0) := by
  apply ((integrable_kernel q hq hq0 a ha).norm.const_mul (1 / (-a.im))).mono'
    (measurable_kernelSq q a).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_kernelSq_le q ha)


lemma denominator_lower_near {a z : ℂ} (_ha : a.im < 0)
    (hz : ‖z - a‖ < (-a.im) / 2) (u : ℝ) :
    ‖(u : ℂ) + a‖ / 2 ≤ ‖(u : ℂ) + z‖ := by
  have htri := norm_add_le ((u : ℂ) + z) (a - z)
  have he : ((u : ℂ) + z) + (a - z) = (u : ℂ) + a := by ring
  rw [he, norm_sub_rev a z] at htri
  have hi := imag_bound a u
  linarith

lemma norm_kernelSq_le_four {a z : ℂ} (q : ℝ) (ha : a.im < 0)
    (hz : ‖z - a‖ < (-a.im) / 2) (u : ℝ) :
    ‖kernelSq q z u‖ ≤ 4 * ‖kernelSq q a u‖ := by
  have hB : 0 < ‖(u : ℂ) + a‖ := lt_of_lt_of_le (by linarith) (imag_bound a u)
  have hN : ‖(u : ℂ) + a‖ / 2 ≤ ‖(u : ℂ) + z‖ := denominator_lower_near ha hz u
  have hBhalf : 0 < ‖(u : ℂ) + a‖ / 2 := by linarith
  have hsq : (‖(u : ℂ) + a‖ / 2) ^ 2 ≤ ‖(u : ℂ) + z‖ ^ 2 :=
    pow_le_pow_left₀ hBhalf.le hN 2
  simp only [kernelSq, norm_div, norm_pow]
  calc
    ‖((u ^ q : ℝ) : ℂ)‖ / ‖(u : ℂ) + z‖ ^ 2 ≤
        ‖((u ^ q : ℝ) : ℂ)‖ / (‖(u : ℂ) + a‖ / 2) ^ 2 :=
      div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hBhalf) hsq
    _ = 4 * (‖((u ^ q : ℝ) : ℂ)‖ / ‖(u : ℂ) + a‖ ^ 2) := by ring

lemma hasDerivAt_kernel (q : ℝ) (a : ℂ) (u : ℝ)
    (h : (u : ℂ) + a ≠ 0) :
    HasDerivAt (fun z : ℂ => kernel q z u) (-kernelSq q a u) a := by
  simpa only [kernel, kernelSq, zero_add, zero_mul, mul_one, zero_sub, neg_div] using!
    (hasDerivAt_const a ((u ^ q : ℝ) : ℂ)).div
      ((hasDerivAt_const a (u : ℂ)).add (hasDerivAt_id a)) h

lemma hasDerivAt_S_raw (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (a : ℂ) (ha : a.im < 0) :
    HasDerivAt (S q) (-(∫ u : ℝ in Ioi 0, kernelSq q a u)) a := by
  let radius : ℝ := (-a.im) / 2
  have hr : 0 < radius := by dsimp [radius]; linarith
  have hnear : Metric.ball a radius ∈ 𝓝 a := Metric.ball_mem_nhds a hr
  have hbound : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      ∀ z ∈ Metric.ball a radius, ‖-kernelSq q z u‖ ≤ 4 * ‖kernelSq q a u‖ := by
    apply Filter.Eventually.of_forall
    intro u z hz
    rw [norm_neg]
    exact norm_kernelSq_le_four q ha (by simpa only [Metric.mem_ball, dist_eq_norm] using hz) u
  have hdiff : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      ∀ z ∈ Metric.ball a radius,
        HasDerivAt (fun w : ℂ => kernel q w u) (-kernelSq q z u) z := by
    apply Filter.Eventually.of_forall
    intro u z hz
    apply hasDerivAt_kernel
    apply norm_pos_iff.mp
    have hB : 0 < ‖(u : ℂ) + a‖ := lt_of_lt_of_le (by linarith) (imag_bound a u)
    have hN := denominator_lower_near ha
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hz) u
    linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le hnear
    (Filter.Eventually.of_forall (fun z : ℂ => (measurable_kernel q z).aestronglyMeasurable))
    (integrable_kernel q hq hq0 a ha)
    ((measurable_kernelSq q a).neg.aestronglyMeasurable)
    hbound ((integrable_kernelSq q hq hq0 a ha).norm.const_mul 4) hdiff
  simpa only [S, integral_neg] using! h.2


/-- The actual complex Stieltjes transform differential equation. -/
theorem hasDerivAt_S (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (a : ℂ) (ha : a.im < 0) :
    HasDerivAt (S q) ((q : ℂ) * S q a / a) a := by
  have hid : (∫ u : ℝ in Ioi 0, kernelSq q a u) = -((q : ℂ) / a) * S q a := by
    exact IntegralStieltjesIBP.integral_kernel_sq_eq q a hq hq0 ha
      (integrable_kernel q hq hq0 a ha) (integrable_kernelSq q hq hq0 a ha)
  have he : -(∫ u : ℝ in Ioi 0, kernelSq q a u) = (q : ℂ) * S q a / a := by
    rw [hid]
    ring
  rw [← he]
  exact hasDerivAt_S_raw q hq hq0 a ha

end IntegralStieltjesTransform


namespace IntegralStieltjesTransform

/-- The actual transform is a positive real multiple of the principal complex power. -/
theorem exists_positive_cpow_scalar (q : ℝ) (hq : -1 < q) (hq0 : q < 0) :
    ∃ k : ℝ, 0 < k ∧ ∀ a : ℂ, a.im < 0 → S q a = (k : ℂ) * a ^ (q : ℂ) := by
  have hne : S q (-Complex.I) ≠ 0 := by
    apply IntegralStieltjesPositive.integral_stieltjes_neg_I_ne_zero q
    simpa only [kernel, sub_eq_add_neg] using!
      integrable_kernel q hq hq0 (-Complex.I) (by simp)
  obtain ⟨K, _hKne, hK⟩ :=
    IntegralStieltjesODE.exists_nonzero_cpow_scalar_of_lower_half_plane_ode
      (S q) (q : ℂ) (fun a ha => hasDerivAt_S q hq hq0 a ha) hne
  obtain ⟨k, hk, hKk⟩ := IntegralStieltjesPositive.stieltjes_scalar_is_positive_real
    q hq hq0 K hK
  refine ⟨k, hk, ?_⟩
  intro a ha
  simpa only [hKk] using hK a ha

/-- A nonzero denominator in the slit plane makes the actual transform nonzero. -/
theorem S_ne_zero (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (a : ℂ) (ha : a.im < 0) : S q a ≠ 0 := by
  obtain ⟨k, hk, hform⟩ := exists_positive_cpow_scalar q hq hq0
  rw [hform a ha]
  apply mul_ne_zero (Complex.ofReal_ne_zero.mpr hk.ne')
  apply Complex.cpow_ne_zero_iff.mpr
  left
  exact IntegralStieltjesIBP.parameter_ne_zero a ha

end IntegralStieltjesTransform


namespace IntegralTruncatedPowerCauchy

open MeasureTheory Set
open scoped BigOperators

noncomputable def C (n : ℕ) (p : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (IntegralTruncatedPower.T n p t : ℂ) / ((t : ℂ) - z)

noncomputable def F (n : ℕ) (p : ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) * ((j : ℂ) - z) ^ (p : ℂ)

lemma shifted_kernel_eq_indicator (q : ℝ) (j : ℕ) (z : ℂ) (t : ℝ) :
    ((IntegralTruncatedPower.truncatedPower q (t - (j : ℝ)) : ℝ) : ℂ) /
      ((t : ℂ) - z) =
    (Ioi (0 : ℝ)).indicator (IntegralStieltjesTransform.kernel q ((j : ℂ) - z))
      (t - (j : ℝ)) := by
  by_cases ht : 0 < t - (j : ℝ)
  · rw [IntegralTruncatedPower.truncatedPower_of_pos q ht,
      indicator_of_mem (show t - (j : ℝ) ∈ Ioi 0 from ht)]
    unfold IntegralStieltjesTransform.kernel
    congr 1
    push_cast
    ring
  · rw [IntegralTruncatedPower.truncatedPower_of_nonpos q (le_of_not_gt ht),
      indicator_of_notMem (show t - (j : ℝ) ∉ Ioi 0 from ht)]
    simp

lemma integrable_shifted_kernel (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (j : ℕ) (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun t : ℝ =>
      ((IntegralTruncatedPower.truncatedPower q (t - (j : ℝ)) : ℝ) : ℂ) /
        ((t : ℂ) - z)) := by
  have ha : ((j : ℂ) - z).im < 0 := by simpa using neg_lt_zero.mpr hz
  have hk := IntegralStieltjesTransform.integrable_kernel q hq hq0 _ ha
  have hi := hk.integrable_indicator measurableSet_Ioi
  have ht := hi.comp_add_right (-(j : ℝ))
  have he : (fun t : ℝ =>
      ((IntegralTruncatedPower.truncatedPower q (t - (j : ℝ)) : ℝ) : ℂ) /
        ((t : ℂ) - z)) =
      (fun t : ℝ => (Ioi (0 : ℝ)).indicator
        (IntegralStieltjesTransform.kernel q ((j : ℂ) - z)) (t + -(j : ℝ))) := by
    funext t
    rw [shifted_kernel_eq_indicator]
    simp only [sub_eq_add_neg]
  rw [he]
  exact ht

lemma integral_shifted_kernel_eq_S (q : ℝ) (j : ℕ) (z : ℂ) :
    (∫ t : ℝ in Ioi 0,
      ((IntegralTruncatedPower.truncatedPower q (t - (j : ℝ)) : ℝ) : ℂ) /
        ((t : ℂ) - z)) = IntegralStieltjesTransform.S q ((j : ℂ) - z) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
    have hnonpos : t - (j : ℝ) ≤ 0 := by
      have ht0 : t ≤ 0 := le_of_not_gt ht
      have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    rw [IntegralTruncatedPower.truncatedPower_of_nonpos q hnonpos]
    simp)]
  simp_rw [shifted_kernel_eq_indicator]
  have he := integral_add_right_eq_self
    ((Ioi (0 : ℝ)).indicator (IntegralStieltjesTransform.kernel q ((j : ℂ) - z)))
    (-(j : ℝ)) (μ := volume)
  have he' :
      (∫ t : ℝ, (Ioi (0 : ℝ)).indicator
        (IntegralStieltjesTransform.kernel q ((j : ℂ) - z)) (t - (j : ℝ))) =
      ∫ u : ℝ, (Ioi (0 : ℝ)).indicator
        (IntegralStieltjesTransform.kernel q ((j : ℂ) - z)) u := by
    simpa only [sub_eq_add_neg] using he
  rw [he', integral_indicator measurableSet_Ioi]
  rfl

lemma cauchy_integrand_eq_sum (n : ℕ) (p : ℝ) (z : ℂ) (t : ℝ) :
    (IntegralTruncatedPower.T n p t : ℂ) / ((t : ℂ) - z) =
    ∑ j ∈ Finset.range (n + 1),
      (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        (((IntegralTruncatedPower.truncatedPower p (t - (j : ℝ)) : ℝ) : ℂ) /
          ((t : ℂ) - z)) := by
  simp only [IntegralTruncatedPower.T, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_div, mul_div_assoc, Complex.ofReal_pow]

lemma integrable_C_negative (n : ℕ) (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (z : ℂ) (hz : 0 < z.im) :
    IntegrableOn (fun t : ℝ => (IntegralTruncatedPower.T n q t : ℂ) /
      ((t : ℂ) - z)) (Ioi 0) := by
  simp_rw [cauchy_integrand_eq_sum]
  apply integrable_finsetSum
  intro j hj
  exact ((integrable_shifted_kernel q hq hq0 j z hz).integrableOn).const_mul _

/-- The finite-sum interchange and each term's translation are actual identities. -/
theorem C_negative_eq_sum_S (n : ℕ) (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (z : ℂ) (hz : 0 < z.im) :
    C n q z = ∑ j ∈ Finset.range (n + 1),
      (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        IntegralStieltjesTransform.S q ((j : ℂ) - z) := by
  unfold C
  simp_rw [cauchy_integrand_eq_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul, integral_shifted_kernel_eq_S]
  · intro j hj
    exact ((integrable_shifted_kernel q hq hq0 j z hz).integrableOn).const_mul _

/-- The genuine negative-exponent Cauchy base with a positive real scalar,
uniformly in the finite-difference order and the upper-half-plane parameter. -/
theorem exists_positive_scalar_negative (q : ℝ) (hq : -1 < q) (hq0 : q < 0) :
    ∃ k : ℝ, 0 < k ∧ ∀ (n : ℕ) (z : ℂ), 0 < z.im →
      C n q z = (k : ℂ) * F n q z := by
  obtain ⟨k, hk, hS⟩ :=
    IntegralStieltjesTransform.exists_positive_cpow_scalar q hq hq0
  refine ⟨k, hk, ?_⟩
  intro n z hz
  rw [C_negative_eq_sum_S n q hq hq0 z hz]
  unfold F
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hS ((j : ℂ) - z) (by simpa using neg_lt_zero.mpr hz)]
  ring

theorem C_negative_eq_zero_iff (n : ℕ) (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (z : ℂ) (hz : 0 < z.im) : C n q z = 0 ↔ F n q z = 0 := by
  obtain ⟨k, hk, heq⟩ := exists_positive_scalar_negative q hq hq0
  rw [heq n z hz]
  exact mul_eq_zero_iff_left (Complex.ofReal_ne_zero.mpr (ne_of_gt hk))

end IntegralTruncatedPowerCauchy


namespace IntegralCauchyParametric

open Filter MeasureTheory Metric
open scoped Topology

lemma im_le_norm_real_sub (t : ℝ) (w : ℂ) (hw : 0<w.im) :
    w.im ≤ ‖(t:ℂ)-w‖ := by
  simpa only [Complex.sub_im,Complex.ofReal_im,zero_sub,abs_neg,abs_of_pos hw] using
    Complex.abs_im_le_norm ((t:ℂ)-w)

lemma real_sub_ne_zero (t : ℝ) (w : ℂ) (hw : 0<w.im) : (t:ℂ)-w ≠ 0 :=
  norm_pos_iff.mp (hw.trans_le (im_le_norm_real_sub t w hw))

lemma aestronglyMeasurable_kernel {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (w : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => f t/((t:ℂ)-w)) μ := by
  exact (hf.aestronglyMeasurable.aemeasurable.div
    (Complex.measurable_ofReal.sub_const w).aemeasurable).aestronglyMeasurable

lemma aestronglyMeasurable_derivative_kernel {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (w : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => f t/((t:ℂ)-w)^2) μ := by
  exact (hf.aestronglyMeasurable.aemeasurable.div
    ((Complex.measurable_ofReal.sub_const w).pow_const 2).aemeasurable).aestronglyMeasurable

lemma integrable_kernel {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (w : ℂ) (hw : 0<w.im) :
    Integrable (fun t : ℝ => f t/((t:ℂ)-w)) μ := by
  apply (hf.norm.div_const w.im).mono' (aestronglyMeasurable_kernel hf w)
  filter_upwards [] with t
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg (f t)) hw (im_le_norm_real_sub t w hw)

lemma hasDerivAt_kernel (f : ℝ → ℂ) (t : ℝ) (w : ℂ) (hw : 0<w.im) :
    HasDerivAt (fun z : ℂ => f t/((t:ℂ)-z)) (f t/((t:ℂ)-w)^2) w := by
  have hd : HasDerivAt (fun z : ℂ => (t:ℂ)-z) (-1) w :=
    (hasDerivAt_id w).const_sub (t:ℂ)
  convert! (hasDerivAt_const w (f t)).div hd (real_sub_ne_zero t w hw) using 1
  simp only [zero_mul,mul_neg_one,zero_sub,neg_neg]

lemma im_lower_on_ball (z w : ℂ) (_hz : 0<z.im)
    (hw : w ∈ ball z (z.im/2)) : z.im/2<w.im := by
  have hnorm : ‖w-z‖<z.im/2 := by simpa only [mem_ball,dist_eq_norm] using hw
  have him : |w.im-z.im|<z.im/2 := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (w-z)).trans_lt hnorm
  have hleft := (abs_lt.mp him).1
  linarith

lemma norm_derivative_kernel_le (f : ℝ → ℂ) (t : ℝ) (z w : ℂ)
    (hz : 0<z.im) (hw : w ∈ ball z (z.im/2)) :
    ‖f t/((t:ℂ)-w)^2‖ ≤ (4/z.im^2)*‖f t‖ := by
  have hhalf : 0<z.im/2 := by linarith
  have hwim : 0<w.im := hhalf.trans (im_lower_on_ball z w hz hw)
  have hden : z.im/2≤‖(t:ℂ)-w‖ :=
    (im_lower_on_ball z w hz hw).le.trans (im_le_norm_real_sub t w hwim)
  have hsq : (z.im/2)^2≤‖(t:ℂ)-w‖^2 := pow_le_pow_left₀ hhalf.le hden 2
  rw [norm_div,norm_pow]
  calc
    _ ≤ ‖f t‖/(z.im/2)^2 :=
      div_le_div_of_nonneg_left (norm_nonneg (f t)) (sq_pos_of_pos hhalf) hsq
    _ = _ := by field_simp; ring

/-- Differentiation of the Cauchy integral for an arbitrary complex L1 density
in the upper half-plane, together with integrability of its derivative kernel. -/
theorem integrable_derivative_and_hasDerivAt_cauchy {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (z : ℂ) (hz : 0<z.im) :
    Integrable (fun t : ℝ => f t/((t:ℂ)-z)^2) μ ∧
      HasDerivAt (fun w : ℂ => ∫ t, f t/((t:ℂ)-w) ∂μ)
        (∫ t, f t/((t:ℂ)-z)^2 ∂μ) z := by
  have hhalf : 0<z.im/2 := by linarith
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun w : ℂ => fun t : ℝ => f t/((t:ℂ)-w))
    (F':=fun w : ℂ => fun t : ℝ => f t/((t:ℂ)-w)^2)
    (bound:=fun t : ℝ => (4/z.im^2)*‖f t‖)
    (ball_mem_nhds z hhalf) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (fun w => aestronglyMeasurable_kernel hf w)
  · exact integrable_kernel hf z hz
  · exact aestronglyMeasurable_derivative_kernel hf z
  · filter_upwards [] with t w hw
    exact norm_derivative_kernel_le f t z w hz hw
  · exact hf.norm.const_mul _
  · filter_upwards [] with t w hw
    exact hasDerivAt_kernel f t w (hhalf.trans (im_lower_on_ball z w hz hw))

theorem integrable_derivative_kernel {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (z : ℂ) (hz : 0<z.im) :
    Integrable (fun t : ℝ => f t/((t:ℂ)-z)^2) μ :=
  (integrable_derivative_and_hasDerivAt_cauchy hf z hz).1

theorem hasDerivAt_cauchy {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (z : ℂ) (hz : 0<z.im) :
    HasDerivAt (fun w : ℂ => ∫ t, f t/((t:ℂ)-w) ∂μ)
      (∫ t, f t/((t:ℂ)-z)^2 ∂μ) z :=
  (integrable_derivative_and_hasDerivAt_cauchy hf z hz).2

theorem hasDerivAt_cauchy_real_density {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : Integrable f μ) (z : ℂ) (hz : 0<z.im) :
    HasDerivAt (fun w : ℂ => ∫ t, (f t:ℂ)/((t:ℂ)-w) ∂μ)
      (∫ t, (f t:ℂ)/((t:ℂ)-z)^2 ∂μ) z :=
  hasDerivAt_cauchy hf.ofReal z hz

end IntegralCauchyParametric


namespace IntegralCauchyPositiveSquare

open MeasureTheory Filter Set IntegralTruncatedPower IntegralTruncatedPowerCauchy
open IntegralStieltjesTransform
open scoped BigOperators

lemma positive_kernelSq_decomposition (p : ℝ) (a : ℂ) (ha : a.im<0)
    (u : ℝ) (hu : 0<u) :
    ((u^p:ℝ):ℂ)/((u:ℂ)+a)^2 = kernel (p-1) a u - a*kernelSq (p-1) a u := by
  have hp : u^p=u^(p-1)*u := by
    calc
      _=u^((p-1)+1) := by rw [sub_add_cancel]
      _=_ := by rw [Real.rpow_add hu,Real.rpow_one]
  unfold kernel kernelSq
  rw [hp,Complex.ofReal_mul]
  field_simp [IntegralStieltjesIBP.add_ofReal_ne_zero a ha u]
  ring

lemma integrable_positive_kernelSq (p : ℝ) (hp : 0<p) (hp1 : p<1)
    (a : ℂ) (ha : a.im<0) :
    IntegrableOn (fun u : ℝ => ((u^p:ℝ):ℂ)/((u:ℂ)+a)^2) (Ioi 0) := by
  have hq : -1<p-1 := by linarith
  have hq0 : p-1<0 := by linarith
  apply ((integrable_kernel (p-1) hq hq0 a ha).sub
    ((integrable_kernelSq (p-1) hq hq0 a ha).const_mul a)).congr
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
    (positive_kernelSq_decomposition p a ha u hu).symm

lemma integral_positive_kernelSq_eq (p : ℝ) (hp : 0<p) (hp1 : p<1)
    (a : ℂ) (ha : a.im<0) :
    (∫ u : ℝ in Ioi 0, ((u^p:ℝ):ℂ)/((u:ℂ)+a)^2) = (p:ℂ)*S (p-1) a := by
  have hq : -1<p-1 := by linarith
  have hq0 : p-1<0 := by linarith
  have hK := integrable_kernel (p-1) hq hq0 a ha
  have hK2 := integrable_kernelSq (p-1) hq hq0 a ha
  have hIBP : (∫ u : ℝ in Ioi 0, kernelSq (p-1) a u)=
      -(((p-1:ℝ):ℂ)/a)*S (p-1) a :=
    IntegralStieltjesIBP.integral_kernel_sq_eq (p-1) a hq hq0 ha hK hK2
  calc
    _=(∫ u : ℝ in Ioi 0, kernel (p-1) a u-a*kernelSq (p-1) a u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact positive_kernelSq_decomposition p a ha u hu
    _=S (p-1) a-a*(∫ u : ℝ in Ioi 0, kernelSq (p-1) a u) := by
      rw [integral_sub hK (hK2.const_mul a),integral_const_mul]
      rfl
    _=_ := by
      rw [hIBP]
      have hane := IntegralStieltjesIBP.parameter_ne_zero a ha
      push_cast
      field_simp [hane]
      ring

lemma shifted_kernelSq_eq_indicator (p : ℝ) (j : ℕ) (z : ℂ) (t : ℝ) :
    (truncatedPower p (t-(j:ℝ)):ℂ)/((t:ℂ)-z)^2 =
      (Ioi (0:ℝ)).indicator
        (fun u : ℝ => ((u^p:ℝ):ℂ)/((u:ℂ)+((j:ℂ)-z))^2) (t-(j:ℝ)) := by
  by_cases ht : 0<t-(j:ℝ)
  · rw [truncatedPower_of_pos p ht,
      indicator_of_mem (show t-(j:ℝ) ∈ Ioi 0 from ht)]
    congr 1
    push_cast
    ring
  · rw [truncatedPower_of_nonpos p (le_of_not_gt ht),
      indicator_of_notMem (show t-(j:ℝ) ∉ Ioi 0 from ht)]
    simp

lemma integrable_shifted_kernelSq (p : ℝ) (hp : 0<p) (hp1 : p<1)
    (j : ℕ) (z : ℂ) (hz : 0<z.im) :
    Integrable (fun t : ℝ => (truncatedPower p (t-(j:ℝ)):ℂ)/((t:ℂ)-z)^2) := by
  have ha : ((j:ℂ)-z).im<0 := by simpa using neg_lt_zero.mpr hz
  have hk := integrable_positive_kernelSq p hp hp1 ((j:ℂ)-z) ha
  have hi := hk.integrable_indicator measurableSet_Ioi
  have ht := hi.comp_add_right (-(j:ℝ))
  have he : (fun t : ℝ => (truncatedPower p (t-(j:ℝ)):ℂ)/((t:ℂ)-z)^2)=
      (fun t : ℝ => (Ioi (0:ℝ)).indicator
        (fun u : ℝ => ((u^p:ℝ):ℂ)/((u:ℂ)+((j:ℂ)-z))^2) (t+ -(j:ℝ))) := by
    funext t
    rw [shifted_kernelSq_eq_indicator]
    simp only [sub_eq_add_neg]
  rw [he]
  exact ht

lemma integral_shifted_kernelSq_eq (p : ℝ) (hp : 0<p) (hp1 : p<1)
    (j : ℕ) (z : ℂ) (hz : 0<z.im) :
    (∫ t : ℝ in Ioi 0, (truncatedPower p (t-(j:ℝ)):ℂ)/((t:ℂ)-z)^2) =
      (p:ℂ)*S (p-1) ((j:ℂ)-z) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
    have hnonpos : t-(j:ℝ)≤0 := by
      have ht0 : t≤0 := le_of_not_gt ht
      have hj0 : 0≤(j:ℝ) := Nat.cast_nonneg j
      linarith
    rw [truncatedPower_of_nonpos p hnonpos]
    simp)]
  simp_rw [shifted_kernelSq_eq_indicator]
  have he := integral_add_right_eq_self
    ((Ioi (0:ℝ)).indicator
      (fun u : ℝ => ((u^p:ℝ):ℂ)/((u:ℂ)+((j:ℂ)-z))^2)) (-(j:ℝ)) (μ:=volume)
  have he' : (∫ t : ℝ, (Ioi (0:ℝ)).indicator
      (fun u : ℝ => ((u^p:ℝ):ℂ)/((u:ℂ)+((j:ℂ)-z))^2) (t-(j:ℝ))) =
      ∫ u : ℝ, (Ioi (0:ℝ)).indicator
        (fun u : ℝ => ((u^p:ℝ):ℂ)/((u:ℂ)+((j:ℂ)-z))^2) u := by
    simpa only [sub_eq_add_neg] using he
  rw [he',integral_indicator measurableSet_Ioi]
  exact integral_positive_kernelSq_eq p hp hp1 _ (by simpa using neg_lt_zero.mpr hz)

lemma square_integrand_eq_sum (n : ℕ) (p : ℝ) (z : ℂ) (t : ℝ) :
    (T n p t:ℂ)/((t:ℂ)-z)^2 =
      ∑ j ∈ Finset.range (n+1), (((-1:ℝ)^j*(n.choose j:ℝ)):ℂ)*
        ((truncatedPower p (t-(j:ℝ)):ℂ)/((t:ℂ)-z)^2) := by
  simp only [T,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_div,mul_div_assoc,
    Complex.ofReal_pow]

lemma integrable_T_kernelSq (n : ℕ) (p : ℝ) (hp : 0<p) (hp1 : p<1)
    (z : ℂ) (hz : 0<z.im) :
    IntegrableOn (fun t : ℝ => (T n p t:ℂ)/((t:ℂ)-z)^2) (Ioi 0) := by
  simp_rw [square_integrand_eq_sum]
  apply integrable_finsetSum
  intro j hj
  exact ((integrable_shifted_kernelSq p hp hp1 j z hz).integrableOn).const_mul _

/-- The actual first-positive-strip Cauchy identity. All individual shifted
kernels and both sides' integrals are genuine integrable functions. -/
theorem integral_T_kernelSq_eq_C (n : ℕ) (p : ℝ) (hp : 0<p) (hp1 : p<1)
    (z : ℂ) (hz : 0<z.im) :
    (∫ t : ℝ in Ioi 0, (T n p t:ℂ)/((t:ℂ)-z)^2) =
      (p:ℂ)*C n (p-1) z := by
  simp_rw [square_integrand_eq_sum]
  rw [integral_finsetSum]
  · rw [C_negative_eq_sum_S n (p-1) (by linarith) (by linarith) z hz,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul,integral_shifted_kernelSq_eq p hp hp1 j z hz]
    ring
  · intro j hj
    exact ((integrable_shifted_kernelSq p hp hp1 j z hz).integrableOn).const_mul _

end IntegralCauchyPositiveSquare


namespace IntegralCauchyPowerDecay

noncomputable def difference (n : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ j * (n.choose j : ℂ) * f (x + (j : ℝ))

lemma difference_succ (n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    difference (n + 1) f x = difference n f x - difference n f (x + 1) := by
  have h := Finset.sum_choose_succ_mul
    (fun (j : ℕ) (_ : ℕ) => (-1 : ℂ) ^ j * f (x + (j : ℝ))) n
  have hleft : difference (n + 1) f x =
      ∑ j ∈ Finset.range (n + 2), ((n + 1).choose j : ℂ) *
        ((-1 : ℂ) ^ j * f (x + (j : ℝ))) := by
    unfold difference
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hleft, h]
  have hfirst : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
      ((-1 : ℂ) ^ j * f (x + (j : ℝ)))) = difference n f x := by
    unfold difference
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfirst]
  have hsecond : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
      ((-1 : ℂ) ^ (j + 1) * f (x + ((j + 1 : ℕ) : ℝ)))) =
      - difference n f (x + 1) := by
    rw [difference, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    have he : x + ((j + 1 : ℕ) : ℝ) = x + 1 + (j : ℝ) := by push_cast; ring
    rw [he]
    ring
  rw [hsecond]
  ring

lemma hasDerivAt_difference (n : ℕ) (f g : ℝ → ℂ) (x : ℝ)
    (h : ∀ j ∈ Finset.range (n + 1), HasDerivAt f (g (x + (j : ℝ))) (x + (j : ℝ))) :
    HasDerivAt (difference n f) (difference n g x) x := by
  unfold difference
  apply HasDerivAt.fun_sum
  intro j hj
  have hh : HasDerivAt (fun y : ℝ => f (y + (j : ℝ)))
      (g (x + (j : ℝ))) x := by
    simpa only [Function.comp_apply, id_eq, one_smul] using!
      ((h j hj).scomp x ((hasDerivAt_id x).add_const (j : ℝ)))
  simpa only [] using! hh.const_mul ((-1 : ℂ) ^ j * (n.choose j : ℂ))

lemma norm_difference_le (n : ℕ) (f : ℕ → ℝ → ℂ) (x M : ℝ)
    (hderiv : ∀ k : ℕ, k < n → ∀ y ∈ Icc x (x + (n : ℝ)),
      HasDerivAt (f k) (f (k + 1) y) y)
    (hbound : ∀ y ∈ Icc x (x + (n : ℝ)), ‖f n y‖ ≤ M) :
    ‖difference n (f 0) x‖ ≤ M := by
  induction n generalizing f x with
  | zero => simpa [difference] using hbound x (by simp)
  | succ n ih =>
      have hd : ∀ y ∈ Icc x (x + 1),
          HasDerivAt (difference n (f 0)) (difference n (f 1) y) y := by
        intro y hy
        apply hasDerivAt_difference
        intro j hj
        have hjn : (j : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        apply hderiv 0 (Nat.zero_lt_succ n)
        constructor
        · linarith [hy.1, show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j]
        · push_cast
          linarith [hy.2]
      have hb : ∀ y ∈ Icc x (x + 1), ‖difference n (f 1) y‖ ≤ M := by
        intro y hy
        apply ih (fun k => f (k + 1)) y
        · intro k hk v hv
          apply hderiv (k + 1) (Nat.succ_lt_succ hk)
          constructor
          · linarith [hv.1, hy.1]
          · push_cast
            linarith [hv.2, hy.2]
        · intro v hv
          apply hbound
          constructor
          · linarith [hv.1, hy.1]
          · push_cast
            linarith [hv.2, hy.2]
      have hm := norm_image_sub_le_of_norm_deriv_le_segment'
        (fun y hy => (hd y hy).hasDerivWithinAt)
        (fun y hy => hb y ⟨hy.1, hy.2.le⟩)
        (x + 1) (by constructor <;> linarith : x + 1 ∈ Icc x (x + 1))
      rw [difference_succ, norm_sub_rev]
      simpa only [add_sub_cancel_left, mul_one] using hm


noncomputable def coefficient (p : ℝ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, ((p : ℂ) - (k : ℂ))

noncomputable def powerDerivative (p Y : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  coefficient p n * ((x : ℂ) - Complex.I * (Y : ℂ)) ^ ((p : ℂ) - (n : ℂ))

lemma coefficient_succ (p : ℝ) (n : ℕ) :
    coefficient p (n + 1) = coefficient p n * ((p : ℂ) - (n : ℂ)) := by
  exact Finset.prod_range_succ _ _

lemma hasDerivAt_powerDerivative (p Y : ℝ) (hY : 0 < Y) (n : ℕ) (x : ℝ) :
    HasDerivAt (powerDerivative p Y n) (powerDerivative p Y (n + 1) x) x := by
  have hs : (x : ℂ) - Complex.I * (Y : ℂ) ∈ Complex.slitPlane := by
    right
    simpa only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, add_zero, zero_add, zero_sub] using
      (neg_ne_zero.mpr hY.ne')
  have hc := ((hasDerivAt_id (x : ℂ)).sub_const (Complex.I * (Y : ℂ))).cpow_const
    (c := (p : ℂ) - (n : ℂ)) hs
  have hr : HasDerivAt
      (fun v : ℝ => ((v : ℂ) - Complex.I * (Y : ℂ)) ^ ((p : ℂ) - (n : ℂ)))
      (((p : ℂ) - (n : ℂ)) *
        ((x : ℂ) - Complex.I * (Y : ℂ)) ^ (((p : ℂ) - (n : ℂ)) - 1)) x := by
    simpa only [id_eq, mul_one] using! hc.comp_ofReal
  have he : ((p : ℂ) - (n : ℂ)) - 1 = (p : ℂ) - ((n + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  simpa only [powerDerivative, coefficient_succ, he, mul_assoc] using!
    hr.const_mul (coefficient p n)

lemma rpow_le_scaled_of_le_double (q : ℝ) {Y x : ℝ}
    (hY : 0 < Y) (hlo : Y ≤ x) (hhi : x ≤ 2 * Y) :
    x ^ q ≤ (1 + (2 : ℝ) ^ q) * Y ^ q := by
  have hx : 0 < x := hY.trans_le hlo
  have hp : 0 < Y ^ q := Real.rpow_pos_of_pos hY _
  have hk : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) _
  by_cases hq : 0 ≤ q
  · have h := Real.rpow_le_rpow hx.le hhi hq
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hY.le] at h
    nlinarith
  · have h := Real.rpow_le_rpow_of_nonpos hY hlo (le_of_not_ge hq)
    nlinarith

lemma norm_powerDerivative_le (n : ℕ) (p Y : ℝ) (hY : 0 < Y)
    (hnY : (n : ℝ) ≤ Y) {x : ℝ} (hx : x ∈ Icc 0 (n : ℝ)) :
    ‖powerDerivative p Y n x‖ ≤
      ‖coefficient p n‖ * (1 + (2 : ℝ) ^ (p - (n : ℝ))) * Y ^ (p - (n : ℝ)) := by
  have hlo : Y ≤ ‖(x : ℂ) - Complex.I * (Y : ℂ)‖ := by
    have h := Complex.abs_im_le_norm ((x : ℂ) - Complex.I * (Y : ℂ))
    simpa only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, add_zero, zero_add, zero_sub,
      abs_neg, abs_of_pos hY] using h
  have hhi : ‖(x : ℂ) - Complex.I * (Y : ℂ)‖ ≤ 2 * Y := by
    have h := norm_sub_le (x : ℂ) (Complex.I * (Y : ℂ))
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx.1, abs_of_pos hY] at h
    linarith [hx.2]
  have he : (p : ℂ) - (n : ℂ) = ((p - (n : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [powerDerivative, norm_mul, he, Complex.norm_cpow_real]
  have h := mul_le_mul_of_nonneg_left
    (rpow_le_scaled_of_le_double (p - (n : ℝ)) hY hlo hhi) (norm_nonneg (coefficient p n))
  simpa only [mul_assoc] using h

lemma F_eq_difference (n : ℕ) (p Y : ℝ) :
    IntegralTruncatedPowerCauchy.F n p (Complex.I * (Y : ℂ)) =
      difference n (powerDerivative p Y 0) 0 := by
  unfold IntegralTruncatedPowerCauchy.F difference powerDerivative coefficient
  simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, sub_zero, one_mul, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  rfl

lemma norm_F_imag_le (n : ℕ) (p Y : ℝ) (hY : 0 < Y) (hnY : (n : ℝ) ≤ Y) :
    ‖IntegralTruncatedPowerCauchy.F n p (Complex.I * (Y : ℂ))‖ ≤
      ‖coefficient p n‖ * (1 + (2 : ℝ) ^ (p - (n : ℝ))) * Y ^ (p - (n : ℝ)) := by
  rw [F_eq_difference]
  apply norm_difference_le n (powerDerivative p Y) 0
  · intro k hk x hx
    exact hasDerivAt_powerDerivative p Y hY k x
  · intro x hx
    apply norm_powerDerivative_le n p Y hY hnY
    simpa only [zero_add] using hx

lemma F_imag_isBigO (n : ℕ) (p : ℝ) :
    (fun Y : ℝ => IntegralTruncatedPowerCauchy.F n p (Complex.I * (Y : ℂ))) =O[atTop]
      (fun Y : ℝ => Y ^ (p - (n : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound (‖coefficient p n‖ * (1 + (2 : ℝ) ^ (p - (n : ℝ))))
  filter_upwards [eventually_ge_atTop (max 1 (n : ℝ))] with Y hY
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hY)
  have hnY : (n : ℝ) ≤ Y := (le_max_right _ _).trans hY
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hY0.le _)] using
    norm_F_imag_le n p Y hY0 hnY

lemma F_tendsto_zero (n : ℕ) (p : ℝ) (hpn : p < (n : ℝ)) :
    Tendsto (fun Y : ℝ => IntegralTruncatedPowerCauchy.F n p (Complex.I * (Y : ℂ)))
      atTop (𝓝 0) := by
  apply (F_imag_isBigO n p).trans_tendsto
  simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hpn)

end IntegralCauchyPowerDecay


namespace IntegralTruncatedPowerCauchyInduction

open IntegralTruncatedPower IntegralTruncatedPowerCauchy
open IntegralTruncatedPowerMoments IntegralCauchyParametric

lemma integrable_T_positive (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hpn : p < (n : ℝ) - 1) :
    Integrable (fun t : ℝ => (T n p t : ℂ)) (volume.restrict (Ioi 0)) := by
  have hi : Integrable (T n p) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [IntegrableOn, pow_zero, one_mul] using!
      integrableOn_moment n 0 hp (by simpa only [Nat.cast_zero, add_zero] using
        (show p + 1 < (n : ℝ) by linarith))
  exact hi.ofReal

lemma integrable_C_positive (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hpn : p < (n : ℝ) - 1) (z : ℂ) (hz : 0 < z.im) :
    IntegrableOn (fun t : ℝ => (T n p t : ℂ) / ((t : ℂ) - z)) (Ioi 0) :=
  IntegralCauchyParametric.integrable_kernel (integrable_T_positive n hp hpn) z hz

lemma integrable_C_square_positive (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hpn : p < (n : ℝ) - 1) (z : ℂ) (hz : 0 < z.im) :
    IntegrableOn (fun t : ℝ => (T n p t : ℂ) / ((t : ℂ) - z) ^ 2) (Ioi 0) :=
  IntegralCauchyParametric.integrable_derivative_kernel
    (integrable_T_positive n hp hpn) z hz

lemma hasDerivAt_C_raw (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hpn : p < (n : ℝ) - 1) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (C n p)
      (∫ t : ℝ in Ioi 0, (T n p t : ℂ) / ((t : ℂ) - z) ^ 2) z := by
  simpa only [IntegralTruncatedPowerCauchy.C] using!
    IntegralCauchyParametric.hasDerivAt_cauchy (integrable_T_positive n hp hpn) z hz

lemma norm_T_kernel_le (n : ℕ) (p t : ℝ) (z : ℂ) (hz : 0 < z.im) :
    ‖(T n p t : ℂ) / ((t : ℂ) - z)‖ ≤ ‖T n p t‖ / z.im := by
  rw [norm_div, Complex.norm_real]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hz (im_le_norm_real_sub t z hz)

lemma tendsto_T_kernel_zero (n : ℕ) (p : ℝ) (hpn : p < (n : ℝ))
    (z : ℂ) (hz : 0 < z.im) :
    Tendsto (fun t : ℝ => (T n p t : ℂ) / ((t : ℂ) - z)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun t => norm_T_kernel_le n p t z hz)
  simpa only [norm_zero, zero_div] using (T_tendsto_zero n p hpn).norm.div_const z.im

lemma integral_C_square_eq_previous_of_one_lt (n : ℕ) {p : ℝ} (hp : 1 < p)
    (hpn : p < (n : ℝ) - 1) (z : ℂ) (hz : 0 < z.im) :
    (∫ t : ℝ in Ioi 0, (T n p t : ℂ) / ((t : ℂ) - z) ^ 2) =
      (p : ℂ) * C n (p - 1) z := by
  have hprev := integrable_C_positive n (by linarith : 0 < p - 1)
    (by linarith : p - 1 < (n : ℝ) - 1) z hz
  have hsq := integrable_C_square_positive n (by linarith : 0 < p) hpn z hz
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt
      (fun t : ℝ => (T n p t : ℂ) / ((t : ℂ) - z))
      ((p : ℂ) * ((T n (p - 1) t : ℂ) / ((t : ℂ) - z)) -
        (T n p t : ℂ) / ((t : ℂ) - z) ^ 2) t := by
    intro t ht
    have hn := (hasDerivAt_T n hp t).ofReal_comp
    have hden : HasDerivAt (fun t : ℝ => (t : ℂ) - z) 1 t := by
      simpa only [Complex.ofReal_one, id_eq] using!
        (hasDerivAt_id t).ofReal_comp.sub_const z
    convert! hn.div hden (real_sub_ne_zero t z hz) using 1
    push_cast
    field_simp
  have hc : ContinuousAt (fun t : ℝ => (T n p t : ℂ) / ((t : ℂ) - z)) 0 := by
    exact ((Complex.continuous_ofReal.comp (continuous_T n (by linarith))).continuousAt).div
      (Complex.continuous_ofReal.sub continuous_const).continuousAt (real_sub_ne_zero 0 z hz)
  have hlim := tendsto_T_kernel_zero n p (by linarith) z hz
  have hi := (hprev.const_mul (p : ℂ)).sub hsq
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousWithinAt hd hi hlim
  simp only [T_eq_zero_of_nonpos n p (le_refl 0), Complex.ofReal_zero, zero_div,
    sub_zero] at hFTC
  rw [integral_sub (hprev.const_mul _) hsq, integral_const_mul] at hFTC
  exact (sub_eq_zero.mp hFTC).symm

lemma hasDerivAt_C_of_one_lt (n : ℕ) {p : ℝ} (hp : 1 < p)
    (hpn : p < (n : ℝ) - 1) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (C n p) ((p : ℂ) * C n (p - 1) z) z := by
  rw [← integral_C_square_eq_previous_of_one_lt n hp hpn z hz]
  exact hasDerivAt_C_raw n (by linarith) hpn z hz

lemma hasDerivAt_F (n : ℕ) (p : ℝ) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (F n p) (-(p : ℂ) * F n (p - 1) z) z := by
  have hsum : HasDerivAt (F n p)
      (∑ j ∈ Finset.range (n + 1),
        (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
          ((p : ℂ) * ((j : ℂ) - z) ^ ((p : ℂ) - 1) * (-1))) z := by
    apply HasDerivAt.fun_sum
    intro j hj
    have hs : (j : ℂ) - z ∈ Complex.slitPlane := by
      apply Or.inr
      have hi : ((j : ℂ) - z).im < 0 := by simpa using neg_lt_zero.mpr hz
      exact ne_of_lt hi
    have hlin : HasDerivAt (fun w : ℂ => (j : ℂ) - w) (-1) z := by
      simpa only [zero_sub] using! (hasDerivAt_const z (j : ℂ)).sub (hasDerivAt_id z)
    exact (hlin.cpow_const (c := (p : ℂ)) hs).const_mul _
  convert hsum using 1
  simp only [F, Complex.ofReal_sub, Complex.ofReal_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma tendsto_cauchy_imag_of_integrable {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) :
    Tendsto (fun Y : ℝ => ∫ t : ℝ, f t / ((t : ℂ) - Complex.I * (Y : ℂ)) ∂μ)
      atTop (𝓝 0) := by
  have hb : ∀ᶠ Y : ℝ in atTop,
      ‖∫ t : ℝ, f t / ((t : ℂ) - Complex.I * (Y : ℂ)) ∂μ‖ ≤
        (∫ t : ℝ, ‖f t‖ ∂μ) / Y := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    have hz : 0 < (Complex.I * (Y : ℂ)).im := by simpa using hY
    have h := norm_integral_le_of_norm_le (hf.norm.div_const Y)
      (Filter.Eventually.of_forall (fun t : ℝ => show
        ‖f t / ((t : ℂ) - Complex.I * (Y : ℂ))‖ ≤ ‖f t‖ / Y from by
          rw [norm_div]
          exact div_le_div_of_nonneg_left (norm_nonneg _) hY
            (by simpa using im_le_norm_real_sub t (Complex.I * (Y : ℂ)) hz)))
    simpa only [integral_div] using h
  apply squeeze_zero_norm' hb
  simpa only [div_eq_mul_inv, mul_zero] using!
    (tendsto_inv_atTop_zero.const_mul (∫ t : ℝ, ‖f t‖ ∂μ))

lemma C_tendsto_zero (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hpn : p < (n : ℝ) - 1) :
    Tendsto (fun Y : ℝ => C n p (Complex.I * (Y : ℂ))) atTop (𝓝 0) := by
  exact tendsto_cauchy_imag_of_integrable (integrable_T_positive n hp hpn)


lemma hasDerivAt_C_step (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hpn : p < (n : ℝ) - 1) (hp1 : p ≠ 1) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (C n p) ((p : ℂ) * C n (p - 1) z) z := by
  rcases lt_or_gt_of_ne hp1 with hlt | hgt
  · rw [← IntegralCauchyPositiveSquare.integral_T_kernelSq_eq_C n p hp hlt z hz]
    exact hasDerivAt_C_raw n hp hpn z hz
  · exact hasDerivAt_C_of_one_lt n hgt hpn z hz

lemma scalar_step (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hpn : p < (n : ℝ) - 1) (hp1 : p ≠ 1) (K : ℂ)
    (hprev : ∀ z : ℂ, 0 < z.im → C n (p - 1) z = K * F n (p - 1) z) :
    ∀ z : ℂ, 0 < z.im → C n p z = (-K) * F n p z := by
  let D : ℂ → ℂ := fun z => C n p z + K * F n p z
  have hd (z : ℂ) (hz : 0 < z.im) : HasDerivAt D 0 z := by
    have hc := (hasDerivAt_C_step n hp hpn hp1 z hz).add
      ((hasDerivAt_F n p z hz).const_mul K)
    convert! hc using 1
    rw [hprev z hz]
    ring
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have heq (z : ℂ) (hz : 0 < z.im) : D z = D Complex.I := by
    exact hopen.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
      (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hd w hw).deriv) hz (by simp)
  have hlim : Tendsto (fun Y : ℝ => D (Complex.I * (Y : ℂ))) atTop (𝓝 0) := by
    have hc := C_tendsto_zero n hp hpn
    have hf := IntegralCauchyPowerDecay.F_tendsto_zero n p (by linarith)
    simpa only [D, mul_zero, add_zero] using hc.add (hf.const_mul K)
  have hconst : Tendsto (fun Y : ℝ => D (Complex.I * (Y : ℂ)))
      atTop (𝓝 (D Complex.I)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    exact (heq (Complex.I * (Y : ℂ)) (by simpa using hY)).symm
  have hzero : D Complex.I = 0 := tendsto_nhds_unique hconst hlim
  intro z hz
  have h := (heq z hz).trans hzero
  change C n p z + K * F n p z = 0 at h
  exact (eq_neg_of_add_eq_zero_left h).trans (by ring)

lemma exists_nonzero_scalar_shift (n : ℕ) (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (k : ℕ) (hkn : q + (k : ℝ) < (n : ℝ) - 1) :
    ∃ K : ℂ, K ≠ 0 ∧ ∀ z : ℂ, 0 < z.im →
      C n (q + (k : ℝ)) z = K * F n (q + (k : ℝ)) z := by
  induction k with
  | zero =>
      obtain ⟨K, hK, heq⟩ := exists_positive_scalar_negative q hq hq0
      refine ⟨(K : ℂ), ?_, ?_⟩
      · exact_mod_cast (ne_of_gt hK)
      · intro z hz
        simpa only [Nat.cast_zero, add_zero] using heq n z hz
  | succ k ih =>
      simp only [Nat.cast_add, Nat.cast_one] at hkn ⊢
      obtain ⟨K, hK, heq⟩ := ih (by linarith)
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hp : 0 < q + ((k : ℝ) + 1) := by linarith
      have hp1 : q + ((k : ℝ) + 1) ≠ 1 := by
        by_cases hk : k = 0
        · simp only [hk, Nat.cast_zero, zero_add]
          linarith
        · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
          linarith
      have hprev : ∀ z : ℂ, 0 < z.im →
          C n (q + ((k : ℝ) + 1) - 1) z = K * F n (q + ((k : ℝ) + 1) - 1) z := by
        have hx : q + ((k : ℝ) + 1) - 1 = q + (k : ℝ) := by ring
        simpa only [hx] using heq
      exact ⟨-K, neg_ne_zero.mpr hK, scalar_step n hp hkn hp1 K hprev⟩

end IntegralTruncatedPowerCauchyInduction


namespace IntegralTruncatedPowerCauchyBoundary

open Filter Set Complex
open scoped Topology BigOperators

lemma tendsto_lower_path (a : ℝ) :
    Tendsto (fun ε : ℝ => (a : ℂ) - Complex.I * (ε : ℂ))
      (𝓝 0) (𝓝 (a : ℂ)) := by
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).ofReal
  simpa only [mul_zero, sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (a : ℂ)) (𝓝 0) (𝓝 (a : ℂ))).sub
      (hε.const_mul Complex.I)

lemma tendsto_lower_cpow_pos (a p : ℝ) (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ((a : ℂ) - Complex.I * (ε : ℂ)) ^ (p : ℂ))
      (𝓝 0) (𝓝 ((a ^ p : ℝ) : ℂ)) := by
  have hc := (continuousAt_cpow_const (a := (a : ℂ)) (b := (p : ℂ))
    (Or.inl ha)).tendsto.comp (tendsto_lower_path a)
  simpa only [Function.comp_def, ← Complex.ofReal_cpow ha.le p] using hc

/-- At a negative real node the approach is explicitly from the lower half-plane.
The logarithmic boundary theorem supplies log|a|-i*pi, not the principal value
log|a|+i*pi at the node itself. -/
lemma tendsto_lower_cpow_neg (a p : ℝ) (ha : a < 0) :
    Tendsto (fun ε : ℝ => ((a : ℂ) - Complex.I * (ε : ℂ)) ^ (p : ℂ))
      (𝓝[>] 0)
      (𝓝 (Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) *
        (((-a) ^ p : ℝ) : ℂ))) := by
  have hw : Tendsto (fun ε : ℝ => (a : ℂ) - Complex.I * (ε : ℂ))
      (𝓝[>] 0) (𝓝[{w : ℂ | w.im < 0}] (a : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(tendsto_lower_path a).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    simpa using neg_lt_zero.mpr hε
  have hl := (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (z := (a : ℂ)) (by simpa using ha) (by simp)).comp hw
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha] at hl
  have he := (Complex.continuous_exp.tendsto _).comp (hl.mul_const (p : ℂ))
  have heval :
      Complex.exp ((((Real.log (-a) : ℝ) : ℂ) - (Real.pi : ℂ) * Complex.I) *
        (p : ℂ)) =
      Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) *
        (((-a) ^ p : ℝ) : ℂ) := by
    have halg : ((((Real.log (-a) : ℝ) : ℂ) - (Real.pi : ℂ) * Complex.I) *
        (p : ℂ)) = -Complex.I * (Real.pi : ℂ) * (p : ℂ) +
          ((Real.log (-a) * p : ℝ) : ℂ) := by push_cast; ring
    rw [halg, Complex.exp_add, ← Complex.ofReal_exp,
      ← Real.rpow_def_of_pos (neg_pos.mpr ha)]
  rw [heval] at he
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  have hne : (a : ℂ) - Complex.I * (ε : ℂ) ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
      Complex.zero_im] at hi
    linarith
  exact (Complex.cpow_def_of_ne_zero hne (p : ℂ)).symm

lemma tendsto_lower_cpow_zero (p : ℝ) (hp : 0 < p) :
    Tendsto (fun ε : ℝ => ((0 : ℂ) - Complex.I * (ε : ℂ)) ^ (p : ℂ))
      (𝓝 0) (𝓝 0) := by
  have hc := (Complex.continuousAt_cpow_const_of_re_pos
    (z := (0 : ℂ)) (w := (p : ℂ)) (Or.inl le_rfl) (by simpa using hp)).tendsto.comp
      (tendsto_lower_path 0)
  simpa only [Function.comp_def, Complex.ofReal_zero, Complex.zero_cpow
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hp))] using hc

lemma tendsto_lower_cpow (a p : ℝ) (hp : 0 < p) :
    Tendsto (fun ε : ℝ => ((a : ℂ) - Complex.I * (ε : ℂ)) ^ (p : ℂ))
      (𝓝[>] 0)
      (𝓝 ((IntegralTruncatedPower.truncatedPower p a : ℂ) +
        Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) *
          (IntegralTruncatedPower.truncatedPower p (-a) : ℂ))) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [IntegralTruncatedPower.truncatedPower_of_nonpos p ha.le,
      IntegralTruncatedPower.truncatedPower_of_pos p (neg_pos.mpr ha)]
    simpa only [Complex.ofReal_zero, zero_add] using tendsto_lower_cpow_neg a p ha
  · simpa only [neg_zero, IntegralTruncatedPower.truncatedPower_of_nonpos p le_rfl,
      Complex.ofReal_zero, mul_zero, add_zero] using
      (tendsto_lower_cpow_zero p hp).mono_left nhdsWithin_le_nhds
  · rw [IntegralTruncatedPower.truncatedPower_of_pos p ha,
      IntegralTruncatedPower.truncatedPower_of_nonpos p (neg_nonpos.mpr ha.le)]
    simpa only [Complex.ofReal_zero, mul_zero, add_zero] using
      (tendsto_lower_cpow_pos a p ha).mono_left nhdsWithin_le_nhds

lemma sum_reflected_truncatedPower (n : ℕ) (p x : ℝ) :
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ j * (n.choose j : ℝ) *
        IntegralTruncatedPower.truncatedPower p ((j : ℝ) - x)) =
      (-1 : ℝ) ^ n * IntegralTruncatedPower.T n p ((n : ℝ) - x) := by
  rw [← Finset.sum_range_reflect (fun j : ℕ => (-1 : ℝ) ^ j * (n.choose j : ℝ) *
    IntegralTruncatedPower.truncatedPower p ((j : ℝ) - x)) (n + 1)]
  simp only [Nat.add_sub_cancel]
  rw [IntegralTruncatedPower.T, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsquare : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  have hsign : (-1 : ℝ) ^ (n - j) = (-1 : ℝ) ^ n * (-1 : ℝ) ^ j := by
    calc
      (-1 : ℝ) ^ (n - j) = (-1 : ℝ) ^ (n - j) *
          ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) := by rw [hsquare, mul_one]
      _ = ((-1 : ℝ) ^ (n - j) * (-1 : ℝ) ^ j) * (-1 : ℝ) ^ j := by ring
      _ = (-1 : ℝ) ^ n * (-1 : ℝ) ^ j := by
        rw [← pow_add, Nat.sub_add_cancel hjn]
  rw [Nat.choose_symm hjn, hsign, Nat.cast_sub hjn]
  have harg : ((n : ℝ) - (j : ℝ)) - x = ((n : ℝ) - x) - (j : ℝ) := by ring
  rw [harg]
  ring

lemma F_boundary_sum_eq (n : ℕ) (p x : ℝ) :
    (∑ j ∈ Finset.range (n + 1),
      (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        ((IntegralTruncatedPower.truncatedPower p ((j : ℝ) - x) : ℂ) +
          Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) *
            (IntegralTruncatedPower.truncatedPower p (x - (j : ℝ)) : ℂ))) =
      (((-1 : ℝ) ^ n : ℝ) : ℂ) *
        (IntegralTruncatedPower.T n p ((n : ℝ) - x) : ℂ) +
      Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) *
        (IntegralTruncatedPower.T n p x : ℂ) := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hrefl := congrArg (fun y : ℝ => (y : ℂ)) (sum_reflected_truncatedPower n p x)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow] at hrefl
  simp only [Complex.ofReal_pow]
  rw [hrefl]
  congr 1
  simp only [IntegralTruncatedPower.T, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The finite complex-power boundary on approach from above in the z variable. -/
theorem tendsto_F_positive (n : ℕ) (p : ℝ) (hp : 0 < p) (x : ℝ) :
    Tendsto (fun ε : ℝ => IntegralTruncatedPowerCauchy.F n p
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0)
      (𝓝 (((( -1 : ℝ) ^ n : ℝ) : ℂ) *
          (IntegralTruncatedPower.T n p ((n : ℝ) - x) : ℂ) +
        Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) *
          (IntegralTruncatedPower.T n p x : ℂ))) := by
  have hterm (j : ℕ) : Tendsto
      (fun ε : ℝ => (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        (((j : ℂ) - ((x : ℂ) + Complex.I * (ε : ℂ))) ^ (p : ℂ)))
      (𝓝[>] 0)
      (𝓝 ((((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        ((IntegralTruncatedPower.truncatedPower p ((j : ℝ) - x) : ℂ) +
          Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) *
            (IntegralTruncatedPower.truncatedPower p (x - (j : ℝ)) : ℂ)))) := by
    have h := (tendsto_lower_cpow ((j : ℝ) - x) p hp).const_mul
      (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ)
    convert h using 1
    · funext ε
      congr 2
      push_cast
      ring
    · simp only [neg_sub]
  have hsum := tendsto_finsetSum (Finset.range (n + 1)) (fun j _ => hterm j)
  rw [F_boundary_sum_eq] at hsum
  exact hsum

/-- A common zero of the two real tails gives zero finite-sum boundary. -/
theorem tendsto_F_zero_of_common_zeros (n : ℕ) (p : ℝ) (hp : 0 < p) (x : ℝ)
    (hx : IntegralTruncatedPower.T n p x = 0)
    (hnx : IntegralTruncatedPower.T n p ((n : ℝ) - x) = 0) :
    Tendsto (fun ε : ℝ => IntegralTruncatedPowerCauchy.F n p
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
  simpa only [hx, hnx, Complex.ofReal_zero, mul_zero, add_zero] using
    tendsto_F_positive n p hp x

end IntegralTruncatedPowerCauchyBoundary


namespace IntegralTruncatedPowerJointNonzero

open IntegralTruncatedPower IntegralTruncatedPowerCauchy

/-- Actual ordinary Cauchy boundary at a real zero, with the integrable quotient
provided by the positive-exponent finite-difference theorem. -/
theorem tendsto_C_at_real_root (n : ℕ) (p : ℝ) (hp : 0 < p)
    (hpn : p < (n : ℝ)) (x : ℝ) (hx : T n p x = 0) :
    Tendsto (fun ε : ℝ => C n p ((x : ℂ) + Complex.I * (ε : ℂ)))
      (𝓝 0) (𝓝 ((∫ t : ℝ in Ioi 0, T n p t / (t - x) : ℝ) : ℂ)) := by
  have hf : AEStronglyMeasurable (fun t : ℝ => (T n p t : ℂ))
      (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.comp (continuous_T n hp)).aestronglyMeasurable
  have hg := IntegralTruncatedPowerQuotient.integrableOn_T_quotient n hp hpn x hx
  have hlim := IntegralCauchyBoundary.tendsto_cauchy_boundary_of_integrable_quotient x hf hg
  have he (ε : ℝ) : C n p ((x : ℂ) + Complex.I * (ε : ℂ)) =
      ∫ t : ℝ in Ioi 0, (T n p t : ℂ) /
        (((t - x : ℝ) : ℂ) - Complex.I * (ε : ℂ)) := by
    unfold IntegralTruncatedPowerCauchy.C
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    congr 1
    push_cast
    ring
  exact hlim.congr' (Filter.Eventually.of_forall (fun ε => (he ε).symm))

/-- In the highest noninteger strip the exact root count is zero. -/
theorem T_ne_zero_top_strip (n : ℕ) (p : ℝ) (hp : 0 < p) (hpn : p < (n : ℝ))
    (hnot : p ≠ (Nat.floor p : ℝ)) (hstrip : (n : ℝ) - 1 ≤ p)
    (t : ℝ) (ht : 0 < t) : T n p t ≠ 0 := by
  have hn : 1 ≤ n := by
    have hnpos : (0 : ℝ) < n := hp.trans hpn
    have hn' : 0 < n := by exact_mod_cast hnpos
    omega
  have hfloor : n - 1 ≤ Nat.floor p := by
    apply Nat.le_floor
    simpa only [Nat.cast_sub hn, Nat.cast_one] using hstrip
  obtain ⟨Z, hZ, hcard⟩ :=
    IntegralTruncatedPowerNonintegerZeros.exists_positive_zero_finset n p hp hpn hnot
  have hzero : Z.card = 0 := by omega
  have hempty : Z = ∅ := Finset.card_eq_zero.mp hzero
  intro hz
  have hmem := (hZ t).mpr ⟨ht, hz⟩
  simpa [hempty] using hmem

/-- The actual positive noninteger finite difference has no simultaneous
reflected-tail zeros. Every analytic, zero-count, and limit input is discharged. -/
theorem no_common_zeros_noninteger (n : ℕ) (p : ℝ) (hp : 0 < p)
    (hpn : p < (n : ℝ)) (hnot : p ≠ (Nat.floor p : ℝ)) (x : ℝ) :
    ¬ (T n p x = 0 ∧ T n p ((n : ℝ) - x) = 0) := by
  rintro ⟨hx, hnx⟩
  by_cases hresidual : p < (n : ℝ) - 1
  · let k : ℕ := Nat.floor p + 1
    let q : ℝ := p - (k : ℝ)
    have hfloor : (Nat.floor p : ℝ) < p :=
      lt_of_le_of_ne (Nat.floor_le hp.le) (Ne.symm hnot)
    have hq : -1 < q := by
      dsimp only [q, k]
      push_cast
      linarith
    have hq0 : q < 0 := by
      dsimp only [q, k]
      push_cast
      linarith [Nat.lt_floor_add_one p]
    have hqp : q + (k : ℝ) = p := by dsimp only [q]; ring
    obtain ⟨K, _hK, hCF⟩ :=
      IntegralTruncatedPowerCauchyInduction.exists_nonzero_scalar_shift n q hq hq0 k
        (by rw [hqp]; exact hresidual)
    have hCFp : ∀ z : ℂ, 0 < z.im → C n p z = K * F n p z := by
      simpa only [hqp] using hCF
    have hF := IntegralTruncatedPowerCauchyBoundary.tendsto_F_zero_of_common_zeros
      n p hp x hx hnx
    have hzero : Tendsto (fun ε : ℝ => C n p ((x : ℂ) + Complex.I * (ε : ℂ)))
        (𝓝[>] 0) (𝓝 0) := by
      have hmul := hF.const_mul K
      simp only [mul_zero] at hmul
      apply hmul.congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε at hε
      exact (hCFp _ (by simpa using hε)).symm
    have hboundary := (tendsto_C_at_real_root n p hp hpn x hx).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have hzeroq := tendsto_nhds_unique hboundary hzero
    have hnonzero := IntegralTruncatedPowerCauchyNonzero.cauchy_nonzero_noninteger
      n p hp hpn hnot x hx
    exact hnonzero (Complex.ofReal_eq_zero.mp hzeroq)
  · have hstrip : (n : ℝ) - 1 ≤ p := le_of_not_gt hresidual
    by_cases hxpos : 0 < x
    · exact T_ne_zero_top_strip n p hp hpn hnot hstrip x hxpos hx
    · have hnpos : (0 : ℝ) < n := hp.trans hpn
      have hmirror : 0 < (n : ℝ) - x := by linarith
      exact T_ne_zero_top_strip n p hp hpn hnot hstrip ((n : ℝ) - x) hmirror hnx

end IntegralTruncatedPowerJointNonzero


namespace IntegralStieltjesNonreal

open IntegralStieltjesTransform

lemma kernel_conj (q : ℝ) (a : ℂ) (u : ℝ) :
    kernel q (starRingEnd ℂ a) u = starRingEnd ℂ (kernel q a u) := by
  simp [kernel]

lemma kernelSq_conj (q : ℝ) (a : ℂ) (u : ℝ) :
    kernelSq q (starRingEnd ℂ a) u = starRingEnd ℂ (kernelSq q a u) := by
  simp [kernelSq]

lemma S_conj (q : ℝ) (a : ℂ) :
    S q (starRingEnd ℂ a) = starRingEnd ℂ (S q a) := by
  unfold S
  simp_rw [kernel_conj]
  exact integral_conj

lemma integrable_kernel_nonreal (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (a : ℂ) (ha : a.im ≠ 0) : IntegrableOn (kernel q a) (Ioi 0) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · exact integrable_kernel q hq hq0 a hneg
  · have hlow : (starRingEnd ℂ a).im < 0 := by simpa using neg_neg_of_pos hpos
    have h := Complex.conjCLE.toContinuousLinearMap.integrable_comp
      (integrable_kernel q hq hq0 (starRingEnd ℂ a) hlow)
    change IntegrableOn (fun u => starRingEnd ℂ (kernel q (starRingEnd ℂ a) u))
      (Ioi 0) at h
    refine h.congr (Filter.Eventually.of_forall ?_)
    intro u
    simp [kernel]

lemma integrable_kernelSq_nonreal (q : ℝ) (hq : -1 < q) (hq0 : q < 0)
    (a : ℂ) (ha : a.im ≠ 0) : IntegrableOn (kernelSq q a) (Ioi 0) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · exact integrable_kernelSq q hq hq0 a hneg
  · have hlow : (starRingEnd ℂ a).im < 0 := by simpa using neg_neg_of_pos hpos
    have h := Complex.conjCLE.toContinuousLinearMap.integrable_comp
      (integrable_kernelSq q hq hq0 (starRingEnd ℂ a) hlow)
    change IntegrableOn (fun u => starRingEnd ℂ (kernelSq q (starRingEnd ℂ a) u))
      (Ioi 0) at h
    refine h.congr (Filter.Eventually.of_forall ?_)
    intro u
    simp [kernelSq]

lemma conj_cpow_real (a : ℂ) (q : ℝ) (ha : a.im ≠ 0) :
    starRingEnd ℂ ((starRingEnd ℂ a) ^ (q : ℂ)) = a ^ (q : ℂ) := by
  have harg : a.arg ≠ Real.pi :=
    Complex.slitPlane_arg_ne_pi (Complex.mem_slitPlane_iff.mpr (Or.inr ha))
  simpa only [Complex.conj_ofReal] using (Complex.cpow_conj a (q : ℂ) harg).symm

/-- The actual transform has one positive real scalar on both nonreal half-planes. -/
theorem exists_positive_cpow_scalar_nonreal (q : ℝ) (hq : -1 < q) (hq0 : q < 0) :
    ∃ k : ℝ, 0 < k ∧ ∀ a : ℂ, a.im ≠ 0 → S q a = (k : ℂ) * a ^ (q : ℂ) := by
  obtain ⟨k, hk, hform⟩ := exists_positive_cpow_scalar q hq hq0
  refine ⟨k, hk, ?_⟩
  intro a ha
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · exact hform a hneg
  · have hlow : (starRingEnd ℂ a).im < 0 := by simpa using neg_neg_of_pos hpos
    calc
      S q a = starRingEnd ℂ (S q (starRingEnd ℂ a)) := by rw [S_conj]; simp
      _ = starRingEnd ℂ ((k : ℂ) * (starRingEnd ℂ a) ^ (q : ℂ)) :=
        congrArg (starRingEnd ℂ) (hform (starRingEnd ℂ a) hlow)
      _ = (k : ℂ) * a ^ (q : ℂ) := by
        rw [map_mul, Complex.conj_ofReal, conj_cpow_real a q ha]

end IntegralStieltjesNonreal


namespace IntegralRationalRecurrence

open Finset

theorem sum_div_pow_remainder {ι : Type*} (S : Finset ι)
    (c a : ι → ℂ) (s : ℂ) (r : ℕ)
    (ha : ∀ j ∈ S, s + a j ≠ 0)
    (hjet : ∀ k < r, ∑ j ∈ S, c j * (-a j) ^ k = 0) :
    (∑ j ∈ S, c j / (s + a j)) * s ^ r =
      ∑ j ∈ S, c j * (-a j) ^ r / (s + a j) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc, ih (fun k hk => hjet k (Nat.lt_succ_of_lt hk)), sum_mul]
    calc
      (∑ j ∈ S, c j * (-a j) ^ r / (s + a j) * s) =
          ∑ j ∈ S, (c j * (-a j) ^ r +
            c j * (-a j) ^ (r + 1) / (s + a j)) := by
        apply sum_congr rfl
        intro j hj
        rw [pow_succ]
        field_simp [ha j hj]
        ring
      _ = _ := by rw [sum_add_distrib, hjet r (Nat.lt_succ_self r), zero_add]

theorem weighted_rational_recurrence {ι : Type*} (S : Finset ι)
    (c a : ι → ℂ) (s p : ℝ) (r : ℕ) (hs : 0 < s)
    (ha : ∀ j ∈ S, (s : ℂ) + a j ≠ 0)
    (hjet : ∀ k < r, ∑ j ∈ S, c j * (-a j) ^ k = 0) :
    ((s ^ p : ℝ) : ℂ) * (∑ j ∈ S, c j / ((s : ℂ) + a j)) =
      ((s ^ (p - (r : ℝ)) : ℝ) : ℂ) *
        (∑ j ∈ S, c j * (-a j) ^ r / ((s : ℂ) + a j)) := by
  have he := sum_div_pow_remainder S c a (s : ℂ) r ha hjet
  have hp : s ^ p = s ^ (p - (r : ℝ)) * s ^ r := by
    rw [← Real.rpow_natCast s r, ← Real.rpow_add hs]
    congr 1
    ring
  rw [← he, hp, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

theorem norm_sum_div_le_of_jets {ι : Type*} (S : Finset ι)
    (c a : ι → ℂ) (s : ℝ) (r : ℕ) (hs : 0 < s)
    (ha : ∀ j ∈ S, 0 ≤ (a j).re)
    (hjet : ∀ k < r, ∑ j ∈ S, c j * (-a j) ^ k = 0) :
    ‖∑ j ∈ S, c j / ((s : ℂ) + a j)‖ ≤
      (∑ j ∈ S, ‖c j‖ * ‖a j‖ ^ r) / s ^ (r + 1) := by
  have hd (j : ι) (hj : j ∈ S) : s ≤ ‖(s : ℂ) + a j‖ := by
    calc
      s ≤ ((s : ℂ) + a j).re := by
        simp only [Complex.add_re, Complex.ofReal_re]
        exact le_add_of_nonneg_right (ha j hj)
      _ ≤ _ := Complex.re_le_norm _
  have hne (j : ι) (hj : j ∈ S) : (s : ℂ) + a j ≠ 0 :=
    norm_pos_iff.mp (hs.trans_le (hd j hj))
  have he := sum_div_pow_remainder S c a (s : ℂ) r hne hjet
  have hnorm : ‖∑ j ∈ S, c j / ((s : ℂ) + a j)‖ * s ^ r =
      ‖∑ j ∈ S, c j * (-a j) ^ r / ((s : ℂ) + a j)‖ := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      using congrArg norm he
  have hb : ‖∑ j ∈ S, c j * (-a j) ^ r / ((s : ℂ) + a j)‖ ≤
      (∑ j ∈ S, ‖c j‖ * ‖a j‖ ^ r) / s := by
    calc
      _ ≤ ∑ j ∈ S, ‖c j * (-a j) ^ r / ((s : ℂ) + a j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ S, (‖c j‖ * ‖a j‖ ^ r) / s := by
        apply sum_le_sum
        intro j hj
        rw [norm_div, norm_mul, norm_pow, norm_neg]
        exact div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
          hs (hd j hj)
      _ = _ := by simp only [div_eq_mul_inv, sum_mul]
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  rw [pow_succ, ← mul_assoc, hnorm]
  exact (mul_le_mul_of_nonneg_right hb hs.le).trans_eq (div_mul_cancel₀ _ hs.ne')

end IntegralRationalRecurrence


namespace IntegralRationalRecurrence

open Finset

open MeasureTheory Set Filter

lemma continuousOn_sum_div_near_zero {ι : Type*} (S : Finset ι)
    (c a : ι → ℂ) (ha : ∀ j ∈ S, 0 ≤ (a j).re)
    (hzero : ∀ j ∈ S, a j = 0 → c j = 0) :
    ContinuousOn (fun s : ℝ => ∑ j ∈ S, c j / ((s : ℂ) + a j)) (Icc 0 1) := by
  apply continuousOn_finsetSum
  intro j hj
  by_cases haj : a j = 0
  · simp only [hzero j hj haj, zero_div]
    exact continuousOn_const
  · apply ContinuousOn.div continuousOn_const
      (Complex.continuous_ofReal.add_const (a j)).continuousOn
    intro s hs hz
    have hre := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    have hs0 : s = 0 := by linarith [hs.1, ha j hj]
    exact haj (by simpa only [hs0, Complex.ofReal_zero, zero_add] using hz)

/-- The rational logarithmic base is absolutely integrable. Zero poles are
permitted precisely when their coefficients vanish. -/
theorem integrableOn_sum_div {ι : Type*} (S : Finset ι)
    (c a : ι → ℂ) (ha : ∀ j ∈ S, 0 ≤ (a j).re)
    (hzero : ∀ j ∈ S, a j = 0 → c j = 0)
    (hc : ∑ j ∈ S, c j = 0) :
    IntegrableOn (fun s : ℝ => ∑ j ∈ S, c j / ((s : ℂ) + a j)) (Ioi 0) := by
  have hm : Measurable (fun s : ℝ => ∑ j ∈ S, c j / ((s : ℂ) + a j)) := by
    apply Finset.measurable_sum
    intro j hj
    exact measurable_const.div (Complex.continuous_ofReal.measurable.add_const _)
  have hnear : IntegrableOn
      (fun s : ℝ => ∑ j ∈ S, c j / ((s : ℂ) + a j)) (Ioo 0 1) :=
    (continuousOn_sum_div_near_zero S c a ha hzero).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  let B : ℝ := ∑ j ∈ S, ‖c j‖ * ‖a j‖
  have hjet : ∀ k < 1, ∑ j ∈ S, c j * (-a j) ^ k = 0 := by
    intro k hk
    have hk0 : k = 0 := Nat.lt_one_iff.mp hk
    simpa only [hk0, pow_zero, mul_one] using hc
  have htail : IntegrableOn
      (fun s : ℝ => ∑ j ∈ S, c j / ((s : ℂ) + a j)) (Ioi 1) := by
    have hb : IntegrableOn (fun s : ℝ => B * s ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).const_mul B
    apply hb.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := zero_lt_one.trans hs
    have h := norm_sum_div_le_of_jets S c a s 1 hs0 ha hjet
    have he : B * s ^ (-2 : ℝ) = B / s ^ 2 := by
      rw [Real.rpow_neg hs0.le, Real.rpow_ofNat]
      rfl
    rw [he]
    simpa only [pow_one, show 1 + 1 = 2 from rfl, B] using h
  have htail' : IntegrableOn
      (fun s : ℝ => ∑ j ∈ S, c j / ((s : ℂ) + a j)) (Ici 1) := by
    rwa [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa only [Ioo_union_Ici_eq_Ioi zero_lt_one] using hnear.union htail'

end IntegralRationalRecurrence


namespace IntegralPositiveMellinPower

open MeasureTheory Set Finset
open IntegralStieltjesTransform IntegralStieltjesNonreal IntegralRationalRecurrence

/-- The rational Mellin recurrence can be integrated term by term after its
exponent has reached (-1,0). No oscillatory integration-by-parts premise remains. -/
theorem exists_positive_scalar_integral_shift {ι : Type*} (S : Finset ι)
    (c a : ι → ℂ) (q : ℝ) (hq : -1 < q) (hq0 : q < 0) (r : ℕ)
    (ha : ∀ j ∈ S, (a j).im ≠ 0 ∨ a j = 0)
    (hzero : ∀ j ∈ S, a j = 0 → c j * (-a j) ^ r = 0)
    (hjet : ∀ k < r, ∑ j ∈ S, c j * (-a j) ^ k = 0) :
    ∃ k : ℝ, 0 < k ∧
      (∫ s : ℝ in Set.Ioi 0, ((s ^ (q + (r : ℝ)) : ℝ) : ℂ) *
        (∑ j ∈ S, c j / ((s : ℂ) + a j))) =
      (k : ℂ) * ∑ j ∈ S, c j * (-a j) ^ r * (a j) ^ (q : ℂ) := by
  obtain ⟨k, hk, hform⟩ := exists_positive_cpow_scalar_nonreal q hq hq0
  have hi (j : ι) (hj : j ∈ S) :
      IntegrableOn (fun s : ℝ => (c j * (-a j) ^ r) * kernel q (a j) s) (Set.Ioi 0) := by
    rcases ha j hj with hnonreal | hzeroa
    · exact (integrable_kernel_nonreal q hq hq0 (a j) hnonreal).const_mul _
    · simp only [hzero j hj hzeroa, zero_mul]
      exact integrableOn_zero
  have heq (s : ℝ) (hs : s ∈ Set.Ioi (0 : ℝ)) :
      ((s ^ (q + (r : ℝ)) : ℝ) : ℂ) * (∑ j ∈ S, c j / ((s : ℂ) + a j)) =
        ∑ j ∈ S, (c j * (-a j) ^ r) * kernel q (a j) s := by
    have hden (j : ι) (hj : j ∈ S) : (s : ℂ) + a j ≠ 0 := by
      rcases ha j hj with hnonreal | hzeroa
      · intro hz
        apply hnonreal
        have h := congrArg Complex.im hz
        simpa only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] using h
      · simpa only [hzeroa, add_zero] using Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
    rw [weighted_rational_recurrence S c a s (q + (r : ℝ)) r hs hden hjet]
    simp only [add_sub_cancel_right]
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    dsimp only [kernel]
    ring
  refine ⟨k, hk, ?_⟩
  calc
    _ = ∫ s : ℝ in Set.Ioi 0, ∑ j ∈ S, (c j * (-a j) ^ r) * kernel q (a j) s :=
      setIntegral_congr_fun measurableSet_Ioi heq
    _ = ∑ j ∈ S, (c j * (-a j) ^ r) * IntegralStieltjesTransform.S q (a j) := by
      rw [integral_finsetSum S hi]
      apply sum_congr rfl
      intro j hj
      exact integral_const_mul _ _
    _ = ∑ j ∈ S, (k : ℂ) * (c j * (-a j) ^ r * (a j) ^ (q : ℂ)) := by
      apply sum_congr rfl
      intro j hj
      rcases ha j hj with hnonreal | hzeroa
      · rw [hform (a j) hnonreal]
        ring
      · rw [hzero j hj hzeroa]
        ring
    _ = _ := (mul_sum _ _ _).symm

end IntegralPositiveMellinPower


namespace IntegralOriginalConvergence

open MeasureTheory Filter Topology Set

noncomputable def g (n : ℕ) (a t : ℝ) : ℂ :=
  Complex.exp (Complex.I * a * t) *
    (Complex.exp (Complex.I * t) - Complex.exp (-(Complex.I * t))) ^ n

noncomputable def pLow (n : ℕ) (a : ℝ) : ℝ :=
  open Classical in if ∃ j ≤ n, a = 2 * (j : ℝ) - n then 0 else -1

lemma norm_exp_phase (a t : ℝ) : ‖Complex.exp (Complex.I * a * t)‖ = 1 := by
  simpa only [Complex.ofReal_mul, mul_assoc] using Complex.norm_exp_I_mul_ofReal (a * t)

lemma norm_exp_difference_le_two (t : ℝ) :
    ‖Complex.exp (Complex.I * t) - Complex.exp (-(Complex.I * t))‖ ≤ 2 := by
  have he : -(Complex.I * (t : ℂ)) = Complex.I * ((-t : ℝ) : ℂ) := by
    push_cast; ring
  calc
    _ ≤ ‖Complex.exp (Complex.I * t)‖ + ‖Complex.exp (-(Complex.I * t))‖ :=
      norm_sub_le _ _
    _ = 2 := by rw [he, Complex.norm_exp_I_mul_ofReal,
      Complex.norm_exp_I_mul_ofReal]; norm_num

lemma norm_exp_difference_le_two_mul (t : ℝ) :
    ‖Complex.exp (Complex.I * t) - Complex.exp (-(Complex.I * t))‖ ≤ 2 * ‖t‖ := by
  have he : -(Complex.I * (t : ℂ)) = Complex.I * ((-t : ℝ) : ℂ) := by
    push_cast; ring
  calc
    _ = ‖(Complex.exp (Complex.I * t) - 1) -
        (Complex.exp (-(Complex.I * t)) - 1)‖ := by congr 1; ring
    _ ≤ ‖Complex.exp (Complex.I * t) - 1‖ +
        ‖Complex.exp (-(Complex.I * t)) - 1‖ := norm_sub_le _ _
    _ ≤ ‖t‖ + ‖-t‖ := by
      rw [he]
      exact add_le_add Real.norm_exp_I_mul_ofReal_sub_one_le
        Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * ‖t‖ := by rw [norm_neg]; ring

lemma norm_g_le (n : ℕ) (a t : ℝ) : ‖g n a t‖ ≤ (2 : ℝ) ^ n := by
  rw [g, norm_mul, norm_exp_phase, one_mul, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_exp_difference_le_two t) n

lemma norm_g_le_mul_pow (n : ℕ) (a t : ℝ) (ht : 0 ≤ t) :
    ‖g n a t‖ ≤ (2 : ℝ) ^ n * t ^ n := by
  rw [g, norm_mul, norm_exp_phase, one_mul, norm_pow, ← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  simpa [Real.norm_eq_abs, abs_of_nonneg ht] using norm_exp_difference_le_two_mul t

lemma continuousOn_integrand (n : ℕ) (p a : ℝ) :
    ContinuousOn (fun t : ℝ => g n a t / ((t ^ (p + 1) : ℝ) : ℂ)) (Ioi 0) := by
  apply ContinuousOn.div
  · unfold g
    fun_prop
  · exact Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))
  · intro t ht
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne'

lemma norm_integrand_le_at_zero (n : ℕ) (p a t : ℝ) (ht : 0 < t) :
    ‖g n a t / ((t ^ (p + 1) : ℝ) : ℂ)‖ ≤
      (2 : ℝ) ^ n * t ^ ((n : ℝ) - p - 1) := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _)]
  calc
    _ ≤ ((2 : ℝ) ^ n * t ^ n) / t ^ (p + 1) :=
      div_le_div_of_nonneg_right (norm_g_le_mul_pow n a t ht.le)
        (Real.rpow_nonneg ht.le _)
    _ = _ := by rw [mul_div_assoc, ← Real.rpow_natCast t n,
      ← Real.rpow_sub ht]; congr 2; ring

lemma norm_integrand_le_at_infty (n : ℕ) (p a t : ℝ) (ht : 0 < t) :
    ‖g n a t / ((t ^ (p + 1) : ℝ) : ℂ)‖ ≤
      (2 : ℝ) ^ n * t ^ (-(p + 1)) := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _), Real.rpow_neg ht.le]
  simpa [div_eq_mul_inv] using
    div_le_div_of_nonneg_right (norm_g_le n a t) (Real.rpow_nonneg ht.le (p + 1))

theorem integrableOn_near_zero (n : ℕ) (p a : ℝ) (hp : p < n) :
    IntegrableOn (fun t : ℝ => g n a t / ((t ^ (p + 1) : ℝ) : ℂ)) (Ioo 0 1) := by
  have hb : IntegrableOn (fun t : ℝ => (2 : ℝ) ^ n * t ^ ((n : ℝ) - p - 1))
      (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)).const_mul _
  apply hb.mono'
    ((continuousOn_integrand n p a).mono Ioo_subset_Ioi_self |>.aestronglyMeasurable
      measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact norm_integrand_le_at_zero n p a t ht.1

theorem integrableOn_tail_of_pos (n : ℕ) (p a : ℝ) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => g n a t / ((t ^ (p + 1) : ℝ) : ℂ)) (Ioi 1) := by
  have hb : IntegrableOn (fun t : ℝ => (2 : ℝ) ^ n * t ^ (-(p + 1))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(p + 1) < -1) zero_lt_one).const_mul _
  apply hb.mono'
    ((continuousOn_integrand n p a).mono (Ioi_subset_Ioi zero_le_one)
      |>.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_integrand_le_at_infty n p a t (zero_lt_one.trans ht)

theorem integrableOn_of_pos (n : ℕ) (p a : ℝ) (hp : 0 < p) (hpn : p < n) :
    IntegrableOn (fun t : ℝ => g n a t / ((t ^ (p + 1) : ℝ) : ℂ)) (Ioi 0) := by
  have ht := integrableOn_tail_of_pos n p a hp
  have ht' : IntegrableOn (fun t : ℝ => g n a t / ((t ^ (p + 1) : ℝ) : ℂ)) (Ici 1) := by
    rwa [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa only [Ioo_union_Ici_eq_Ioi zero_lt_one] using
    (integrableOn_near_zero n p a hpn).union ht'

theorem exists_limit_of_pos (n : ℕ) (p a : ℝ) (hp : 0 < p) (hpn : p < n) :
    ∃ L : ℂ, Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T, g n a t / ((t ^ (p + 1) : ℝ) : ℂ))
      atTop (𝓝 L) := by
  exact ⟨_, intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_of_pos n p a hp hpn) tendsto_id⟩

lemma continuousOn_exp_mul_rpow (w r : ℝ) :
    ContinuousOn (fun t : ℝ => Complex.exp (Complex.I * w * t) * (t ^ r : ℝ)) (Ioi 0) := by
  apply ContinuousOn.mul
  · fun_prop
  · exact Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))

lemma integrableOn_exp_mul_rpow (w r : ℝ) (hr : r < -1) :
    IntegrableOn (fun t : ℝ => Complex.exp (Complex.I * w * t) * (t ^ r : ℝ)) (Ioi 1) := by
  apply (integrableOn_Ioi_rpow_of_lt hr zero_lt_one).mono'
    ((continuousOn_exp_mul_rpow w r).mono (Ioi_subset_Ioi zero_le_one)
      |>.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, norm_exp_phase, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans ht).le _)]

lemma hasDerivAt_exp_phase (w t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * w * u))
      (Complex.exp (Complex.I * w * t) * (Complex.I * w)) t := by
  simpa only [id_eq, Complex.ofReal_one, mul_one] using
    (((hasDerivAt_id t).ofReal_comp).const_mul (Complex.I * w)).cexp

/-- A single nonzero Fourier frequency has a convergent power-weighted tail.
This includes the genuinely conditional range `0 < q ≤ 1`. -/
theorem exists_limit_exp_mul_rpow (w q : ℝ) (hw : w ≠ 0) (hq : 0 < q) :
    ∃ L : ℂ, Tendsto
      (fun T : ℝ => ∫ t in (1 : ℝ)..T,
        Complex.exp (Complex.I * w * t) * (t ^ (-q) : ℝ)) atTop (𝓝 L) := by
  let c : ℂ := Complex.I * w
  have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hw)
  let F : ℝ → ℂ := fun t =>
    Complex.exp (Complex.I * w * t) * (t ^ (-q) : ℝ) / c
  let R : ℝ → ℂ := fun t =>
    ((-q : ℝ) : ℂ) / c * (Complex.exp (Complex.I * w * t) * (t ^ (-q - 1) : ℝ))
  have hR : IntegrableOn R (Ioi 1) :=
    (integrableOn_exp_mul_rpow w (-q - 1) (by linarith)).const_mul _
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt F
      (Complex.exp (Complex.I * w * t) * (t ^ (-q) : ℝ) + R t) t := by
    have hp := (Real.hasDerivAt_rpow_const (p := -q) (Or.inl ht.ne')).ofReal_comp
    apply (((hasDerivAt_exp_phase w t).mul hp).div_const c).congr_deriv
    dsimp only [R]
    push_cast
    change ((Complex.exp (Complex.I * w * t) * c) * (t ^ (-q) : ℝ) +
      Complex.exp (Complex.I * w * t) * (-(q : ℂ) * (t ^ (-q - 1) : ℝ))) / c = _
    field_simp [hc]
  have hF : Tendsto F atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht := (tendsto_rpow_neg_atTop hq).div_const ‖c‖
    simp only [zero_div] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [F, norm_exp_phase,
      abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  have hRlim := intervalIntegral_tendsto_integral_Ioi 1 hR tendsto_id
  refine ⟨_, ((hF.sub_const (F 1)).sub hRlim).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hi : IntervalIntegrable
      (fun t : ℝ => Complex.exp (Complex.I * w * t) * (t ^ (-q) : ℝ)) volume 1 T := by
    apply ((continuousOn_exp_mul_rpow w (-q)).mono ?_).intervalIntegrable
    rw [uIcc_of_le hT]
    exact fun t ht => lt_of_lt_of_le zero_lt_one ht.1
  have hRi : IntervalIntegrable R volume 1 T := by
    apply (((continuousOn_exp_mul_rpow w (-q - 1)).const_mul ((-q : ℝ) / c)).mono ?_)
      |>.intervalIntegrable
    rw [uIcc_of_le hT]
    exact fun t ht => lt_of_lt_of_le zero_lt_one ht.1
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by rw [uIcc_of_le hT] at ht; linarith [ht.1])) (hi.add hRi)
  rw [intervalIntegral.integral_add hi hRi] at heq
  exact (eq_sub_of_add_eq heq).symm

lemma g_eq_sum_range (n : ℕ) (a t : ℝ) :
    g n a t = ∑ j ∈ Finset.range (n + 1),
      (-1 : ℂ)^j * (n.choose j : ℂ) *
        Complex.exp (Complex.I * (a + n - 2 * (j : ℝ)) * t) := by
  unfold g
  have hs : Complex.exp (Complex.I * t) - Complex.exp (-(Complex.I * t)) =
      -Complex.exp (-(Complex.I * t)) + Complex.exp (Complex.I * t) := by ring
  rw [hs, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  rw [neg_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have he : Complex.exp (Complex.I * a * t) *
      Complex.exp ((j : ℂ) * -(Complex.I * t)) *
      Complex.exp (((n-j : ℕ) : ℂ) * (Complex.I * t)) =
      Complex.exp (Complex.I * (a + n - 2 * (j : ℝ)) * t) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast [Nat.cast_sub hjn]
    ring
  calc
    _ = (-1 : ℂ)^j * (n.choose j : ℂ) *
        (Complex.exp (Complex.I * a * t) *
          Complex.exp ((j : ℂ) * -(Complex.I * t)) *
          Complex.exp (((n-j : ℕ) : ℂ) * (Complex.I * t))) := by ring
    _ = _ := by rw [he]

lemma g_eq_sum (n : ℕ) (a t : ℝ) :
    g n a t = ∑ j : Fin (n + 1),
      (-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ) *
        Complex.exp (Complex.I * (a + n - 2 * (j : ℝ)) * t) := by
  exact (g_eq_sum_range n a t).trans (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (-1 : ℂ)^j * (n.choose j : ℂ) *
      Complex.exp (Complex.I * (a + n - 2 * (j : ℝ)) * t)) (n + 1)).symm

lemma integrand_eq_sum (n : ℕ) (p a t : ℝ) (ht : 0 < t) :
    g n a t / ((t ^ (p + 1) : ℝ) : ℂ) = ∑ j : Fin (n + 1),
      ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
        (Complex.exp (Complex.I * (a + n - 2 * (j : ℝ)) * t) *
          (t ^ (-(p + 1)) : ℝ)) := by
  rw [g_eq_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.rpow_neg ht.le, Complex.ofReal_inv]
  ring

theorem exists_limit_tail_of_nonresonant (n : ℕ) (p a : ℝ)
    (hp : -1 < p) (ha : ¬ ∃ j ≤ n, a = 2 * (j : ℝ) - n) :
    ∃ L : ℂ, Tendsto
      (fun T : ℝ => ∫ t in (1 : ℝ)..T, g n a t / ((t ^ (p + 1) : ℝ) : ℂ))
      atTop (𝓝 L) := by
  classical
  have hw (j : Fin (n + 1)) : a + n - 2 * (j : ℝ) ≠ 0 := by
    intro h
    apply ha
    exact ⟨j, Nat.le_of_lt_succ j.isLt, by linarith⟩
  have hex (j : Fin (n + 1)) :=
    exists_limit_exp_mul_rpow (a + n - 2 * (j : ℝ)) (p + 1) (hw j) (by linarith)
  choose L hL using hex
  have hsum := tendsto_finsetSum Finset.univ (fun j _ =>
    (hL j).const_mul ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)))
  refine ⟨_, hsum.congr' ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    symm
    simpa only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_natCast, Complex.ofReal_ofNat] using
      integrand_eq_sum n p a t (lt_of_lt_of_le zero_lt_one ht.1)
  · intro j _
    apply ((continuousOn_exp_mul_rpow (a + n - 2 * (j : ℝ)) (-(p + 1))).const_mul
      ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ))).mono ?_ |>.intervalIntegrable
    rw [uIcc_of_le hT]
    exact fun t ht => lt_of_lt_of_le zero_lt_one ht.1

theorem exists_limit (n : ℕ) (p a : ℝ) (hp : pLow n a < p) (hpn : p < n) :
    ∃ L : ℂ, Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T, g n a t / ((t ^ (p + 1) : ℝ) : ℂ))
      atTop (𝓝 L) := by
  by_cases hpos : 0 < p
  · exact exists_limit_of_pos n p a hpos hpn
  have ha : ¬ ∃ j ≤ n, a = 2 * (j : ℝ) - n := by
    intro ha
    simp only [pLow, if_pos ha] at hp
    exact hpos hp
  have hp' : -1 < p := by simpa only [pLow, if_neg ha] using hp
  obtain ⟨L, hL⟩ := exists_limit_tail_of_nonresonant n p a hp' ha
  have hi : IntervalIntegrable
      (fun t : ℝ => g n a t / ((t ^ (p + 1) : ℝ) : ℂ)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact integrableOn_near_zero n p a hpn
  refine ⟨_, (hL.const_add (∫ t in (0 : ℝ)..1,
    g n a t / ((t ^ (p + 1) : ℝ) : ℂ))).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have ht : IntervalIntegrable
      (fun t : ℝ => g n a t / ((t ^ (p + 1) : ℝ) : ℂ)) volume 1 T := by
    apply ((continuousOn_integrand n p a).mono ?_).intervalIntegrable
    rw [uIcc_of_le hT]
    exact fun t ht => lt_of_lt_of_le zero_lt_one ht.1
  exact intervalIntegral.integral_add_adjacent_intervals hi ht

end IntegralOriginalConvergence


namespace IntegralOriginalRepresentation

open MeasureTheory Filter Topology Set

lemma integral_gamma_kernel (p t : ℝ) (hp : -1 < p) (ht : 0 < t) :
    (∫ s : ℝ in Ioi 0, s ^ p * Real.exp (-(t * s))) =
      t ^ (-(p + 1)) * Real.Gamma (p + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := p + 1) (r := t) (by linarith) ht
  simpa only [add_sub_cancel_right, one_div, ← Real.rpow_neg_eq_inv_rpow] using h

lemma integrable_gamma_kernel (p t : ℝ) (hp : -1 < p) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => s ^ p * Real.exp (-(t * s))) (Ioi 0) := by
  have hbase : IntegrableOn (fun s : ℝ => Real.exp (-s) * s ^ p) (Ioi 0) := by
    simpa only [add_sub_cancel_right] using
      Real.GammaIntegral_convergent (s := p + 1) (by linarith)
  have hscaled := (integrableOn_Ioi_comp_mul_left_iff
    (fun s : ℝ => Real.exp (-s) * s ^ p) 0 ht).mpr (by simpa using hbase)
  apply (hscaled.const_mul ((t ^ p)⁻¹)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.mul_rpow ht.le hs.le]
  field_simp [(Real.rpow_pos_of_pos ht p).ne']

/-- Tonelli/Fubini bridge from the actual weighted integral to its Laplace
transform. The weighted absolute-integrability hypothesis is discharged by
`IntegralOriginalConvergence.integrableOn_of_pos` in the original positive range,
and by exponential damping in the conditional range. -/
theorem gamma_mul_integral_eq_laplace (f : ℝ → ℂ) (p : ℝ) (hp : -1 < p)
    (hf : Measurable f)
    (hi : IntegrableOn (fun t : ℝ => f t * (t ^ (-(p + 1)) : ℝ)) (Ioi 0)) :
    (Real.Gamma (p + 1) : ℂ) *
        (∫ t : ℝ in Ioi 0, f t * (t ^ (-(p + 1)) : ℝ)) =
      ∫ s : ℝ in Ioi 0, (s ^ p : ℝ) *
        (∫ t : ℝ in Ioi 0, f t * (Real.exp (-(s * t)) : ℝ)) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let K : ℝ × ℝ → ℂ := fun z => f z.1 * (z.2 ^ p * Real.exp (-(z.1 * z.2)) : ℝ)
  have hmeas : AEStronglyMeasurable K (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    dsimp [K]
    fun_prop
  have hnorm (t : ℝ) (ht : 0 < t) :
      (∫ s, ‖K (t, s)‖ ∂μ) =
        Real.Gamma (p + 1) * ‖f t * (t ^ (-(p + 1)) : ℝ)‖ := by
    dsimp only [K, μ]
    simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he (s : ℝ) (hs : s ∈ Ioi 0) :
        |s ^ p * Real.exp (-(t * s))| = s ^ p * Real.exp (-(t * s)) :=
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_pos _).le)
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => congrArg (fun u => ‖f t‖ * u) (he s hs)),
      integral_const_mul, integral_gamma_kernel p t hp ht,
      abs_of_nonneg (Real.rpow_nonneg ht.le _)]
    ring
  have hK : Integrable K (μ.prod μ) := by
    apply (integrable_prod_iff hmeas).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact ((integrable_gamma_kernel p t hp ht).ofReal).const_mul (f t)
    · apply (hi.norm.const_mul (Real.Gamma (p + 1))).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hnorm t ht).symm
  have hswap := integral_integral_swap (f := fun t s => K (t, s)) hK
  have hleft : (∫ t, ∫ s, K (t, s) ∂μ ∂μ) =
      (Real.Gamma (p + 1) : ℂ) *
        (∫ t : ℝ in Ioi 0, f t * (t ^ (-(p + 1)) : ℝ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp only [K, μ]
    rw [integral_const_mul, integral_complex_ofReal, integral_gamma_kernel p t hp ht]
    push_cast
    ring
  rw [hleft] at hswap
  rw [hswap]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  dsimp only [K, μ]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  push_cast
  rw [mul_comm (t : ℂ) (s : ℂ)]
  ring

lemma phase_mul_real_exp (w s t : ℝ) :
    Complex.exp (Complex.I * w * t) * (Real.exp (-(s * t)) : ℝ) =
      Complex.exp ((Complex.I * w - s) * t) := by
  rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, ← Complex.exp_add]
  congr 1
  ring

lemma integrable_phase_laplace (w s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Complex.exp (Complex.I * w * t) *
      (Real.exp (-(s * t)) : ℝ)) (Ioi 0) := by
  have hre : (Complex.I * (w : ℂ) - s).re < 0 := by simpa using neg_neg_of_pos hs
  exact (integrableOn_exp_mul_complex_Ioi hre 0).congr_fun
    (fun t _ => (phase_mul_real_exp w s t).symm) measurableSet_Ioi

lemma integral_phase_laplace (w s : ℝ) (hs : 0 < s) :
    (∫ t : ℝ in Ioi 0, Complex.exp (Complex.I * w * t) *
      (Real.exp (-(s * t)) : ℝ)) = 1 / ((s : ℂ) - Complex.I * w) := by
  have hre : (Complex.I * (w : ℂ) - s).re < 0 := by simpa using neg_neg_of_pos hs
  calc
    _ = ∫ t : ℝ in Ioi 0, Complex.exp ((Complex.I * w - s) * t) :=
      setIntegral_congr_fun measurableSet_Ioi (fun t _ => phase_mul_real_exp w s t)
    _ = -1 / (Complex.I * w - s) := by
      simpa using integral_exp_mul_complex_Ioi hre 0
    _ = _ := by
      rw [show Complex.I * (w : ℂ) - s = -(s - Complex.I * w) by ring]
      simp only [neg_div_neg_eq, one_div]

theorem integral_g_laplace (n : ℕ) (a s : ℝ) (hs : 0 < s) :
    (∫ t : ℝ in Ioi 0, IntegralOriginalConvergence.g n a t *
      (Real.exp (-(s * t)) : ℝ)) =
        ∑ j : Fin (n + 1),
          ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
            (1 / ((s : ℂ) - Complex.I * (a + n - 2 * (j : ℝ)))) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, ∑ j : Fin (n + 1),
        ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
          (Complex.exp (Complex.I * (a + n - 2 * (j : ℝ)) * t) *
            (Real.exp (-(s * t)) : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [IntegralOriginalConvergence.g_eq_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    _ = ∑ j : Fin (n + 1), ∫ t : ℝ in Ioi 0,
        ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
          (Complex.exp (Complex.I * (a + n - 2 * (j : ℝ)) * t) *
            (Real.exp (-(s * t)) : ℝ)) := by
      refine integral_finsetSum Finset.univ (fun j _ => ?_)
      simpa only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_natCast, Complex.ofReal_ofNat] using
        (integrable_phase_laplace (a + n - 2 * (j : ℝ)) s hs).const_mul
          ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
      apply congrArg (fun z : ℂ => ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) * z)
      simpa only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_natCast, Complex.ofReal_ofNat] using
        integral_phase_laplace (a + n - 2 * (j : ℝ)) s hs

/-- The exact original integral has a proved rational Mellin representation
throughout `0 < p < n`. This theorem does not yet evaluate that Mellin integral
as a finite principal-power sum. -/
theorem gamma_mul_original_integral_of_pos (n : ℕ) (p a : ℝ)
    (hp : 0 < p) (hpn : p < n) :
    (Real.Gamma (p + 1) : ℂ) *
        (∫ t : ℝ in Ioi 0, IntegralOriginalConvergence.g n a t /
          ((t ^ (p + 1) : ℝ) : ℂ)) =
      ∫ s : ℝ in Ioi 0, (s ^ p : ℝ) *
        (∑ j : Fin (n + 1),
          ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
            (1 / ((s : ℂ) - Complex.I * (a + n - 2 * (j : ℝ))))) := by
  have heq (t : ℝ) (ht : 0 < t) :
      IntegralOriginalConvergence.g n a t * (t ^ (-(p + 1)) : ℝ) =
        IntegralOriginalConvergence.g n a t / ((t ^ (p + 1) : ℝ) : ℂ) := by
    rw [Real.rpow_neg ht.le, Complex.ofReal_inv, div_eq_mul_inv]
  have hi : IntegrableOn
      (fun t : ℝ => IntegralOriginalConvergence.g n a t * (t ^ (-(p + 1)) : ℝ))
      (Ioi 0) :=
    (IntegralOriginalConvergence.integrableOn_of_pos n p a hp hpn).congr_fun
      (fun t ht => (heq t ht).symm) measurableSet_Ioi
  have hm : Measurable (IntegralOriginalConvergence.g n a) := by
    unfold IntegralOriginalConvergence.g
    fun_prop
  have h := gamma_mul_integral_eq_laplace (IntegralOriginalConvergence.g n a) p
    (by linarith) hm hi
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => heq t ht)] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  rw [integral_g_laplace n a s hs]

end IntegralOriginalRepresentation


namespace IntegralFrequencyCancellation

open Polynomial Finset

/-- An nth alternating binomial sum kills every affine power of degree below n. -/
theorem alternating_choose_affine_power_sum {R : Type*} [CommRing R]
    (n m : ℕ) (hm : m < n) (a b : R) :
    (∑ j ∈ Finset.range (n+1), (-1 : R)^j * (n.choose j : R) * (a+b*(j : R))^m) = 0 := by
  let P : R[X] := (C a + C b * X)^m
  have hlin : (C a + C b * X).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simp) (by simpa only [pow_one] using natDegree_C_mul_X_pow_le b 1)
  have hP : P.natDegree < n := by
    exact (show P.natDegree ≤ m by simpa only [mul_one] using natDegree_pow_le_of_le m hlin).trans_lt hm
  have hz := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP) (0 : R)
  rw [fwdDiff_iter_eq_sum_shift] at hz
  have hstd : (∑ j ∈ Finset.range (n+1),
      (-1 : R)^(n-j) * (n.choose j : R) * (a+b*(j : R))^m) = 0 := by
    simpa only [P, eval_pow, eval_add, eval_C, eval_mul, eval_X, zsmul_eq_mul,
      Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
      nsmul_eq_mul, mul_one, zero_add, Pi.zero_apply] using hz
  have hsign (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (-1 : R)^j = (-1 : R)^n * (-1 : R)^(n-j) := by
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hp : (-1 : R)^n = (-1 : R)^(n-j) * (-1 : R)^j := by
      rw [← pow_add, Nat.sub_add_cancel hjn]
    have hs : (-1 : R)^(n-j) * (-1 : R)^(n-j) = 1 := by
      rw [← mul_pow]
      simp
    rw [hp]
    calc
      (-1 : R)^j = 1 * (-1 : R)^j := by ring
      _ = ((-1 : R)^(n-j) * (-1 : R)^(n-j)) * (-1 : R)^j := by rw [hs]
      _ = _ := by ring
  calc
    _ = (-1 : R)^n * (∑ j ∈ Finset.range (n+1),
        (-1 : R)^(n-j) * (n.choose j : R) * (a+b*(j : R))^m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsign j hj]
      ring
    _ = 0 := by rw [hstd, mul_zero]

/-- Frequency moments for the exact Fourier expansion in the approved question. -/
theorem frequency_power_sum (n r : ℕ) (hr : r < n) (a : ℝ) :
    (∑ j ∈ Finset.range (n+1),
      ((-1 : ℂ)^j * (n.choose j : ℂ)) *
        (Complex.I * (((a+(n : ℝ)-2*(j : ℝ)) : ℝ) : ℂ))^r) = 0 := by
  have h := alternating_choose_affine_power_sum n r hr
    (Complex.I * ((a+(n : ℝ) : ℝ) : ℂ)) (-2*Complex.I)
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  congr 1
  push_cast
  ring

theorem frequency_power_sum_fin (n r : ℕ) (hr : r < n) (a : ℝ) :
    (∑ j : Fin (n+1),
      ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
        (Complex.I * (((a+(n : ℝ)-2*((j : ℕ) : ℝ)) : ℝ) : ℂ))^r) = 0 := by
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    ((-1 : ℂ)^j * (n.choose j : ℂ)) *
      (Complex.I * (((a+(n : ℝ)-2*(j : ℝ)) : ℝ) : ℂ))^r) (n+1)).trans
    (frequency_power_sum n r hr a)

end IntegralFrequencyCancellation


namespace IntegralPositiveOriginalPower

open MeasureTheory Set

lemma shifted_cpow_merge (c a : ℂ) (q : ℝ) (r : ℕ)
    (hq : -1 < q) (hr : 1 ≤ r) :
    c * (-a) ^ r * a ^ (q : ℂ) =
      (-1 : ℂ) ^ r * c * a ^ ((q + (r : ℝ) : ℝ) : ℂ) := by
  by_cases ha : a = 0
  · have hrne : r ≠ 0 := by omega
    have hp : 0 < q + (r : ℝ) := by
      have hrc : (1 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    have hzero : (0 : ℂ) ^ ((q + (r : ℝ) : ℝ) : ℂ) = 0 :=
      Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hp.ne')
    simp only [ha, neg_zero, zero_pow hrne, mul_zero, zero_mul, hzero]
  · rw [neg_pow, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.cpow_add _ _ ha, Complex.cpow_natCast]
    ring

/-- Exact positive noninteger source integral, up to an explicitly nonzero
scalar, evaluated without oscillatory Gamma integrals or an assumed formula. -/
theorem gamma_mul_original_integral_noninteger (n : ℕ) (p a : ℝ)
    (hp : 0 < p) (hpn : p < (n : ℝ)) (hnot : p ≠ (Nat.floor p : ℝ)) :
    ∃ K : ℂ, K ≠ 0 ∧
      (Real.Gamma (p + 1) : ℂ) *
        (∫ t : ℝ in Set.Ioi 0, IntegralOriginalConvergence.g n a t /
          ((t ^ (p + 1) : ℝ) : ℂ)) =
      K * ∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
        (-(Complex.I * ((a+(n : ℝ)-2*(j : ℝ) : ℝ) : ℂ))) ^ (p : ℂ) := by
  let r : ℕ := Nat.floor p + 1
  let q : ℝ := p - (r : ℝ)
  let c : Fin (n+1) → ℂ := fun j => (-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)
  let b : Fin (n+1) → ℂ := fun j => -(Complex.I * ((a+(n : ℝ)-2*(j : ℝ) : ℝ) : ℂ))
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hrn : r ≤ n := by
    have hfl : Nat.floor p < n := (Nat.floor_lt hp.le).mpr hpn
    dsimp [r]
    omega
  have hq : -1 < q := by
    have hfl : (Nat.floor p : ℝ) < p :=
      lt_of_le_of_ne (Nat.floor_le hp.le) (Ne.symm hnot)
    dsimp only [q, r]
    push_cast
    linarith
  have hq0 : q < 0 := by
    dsimp only [q, r]
    push_cast
    linarith [Nat.lt_floor_add_one p]
  have hqr : q + (r : ℝ) = p := by dsimp [q]; ring
  have ha : ∀ j ∈ (Finset.univ : Finset (Fin (n+1))), (b j).im ≠ 0 ∨ b j = 0 := by
    intro j hj
    by_cases hb : b j = 0
    · exact Or.inr hb
    · left
      intro him
      apply hb
      apply Complex.ext
      · simp [b]
      · simpa only [Complex.zero_im] using him
  have hz : ∀ j ∈ (Finset.univ : Finset (Fin (n+1))),
      b j = 0 → c j * (-b j) ^ r = 0 := by
    intro j hj hb
    rw [hb, neg_zero, zero_pow (by omega : r ≠ 0), mul_zero]
  have hjets : ∀ k < r,
      ∑ j ∈ (Finset.univ : Finset (Fin (n+1))), c j * (-b j)^k = 0 := by
    intro k hk
    simpa only [c, b, neg_neg] using
      IntegralFrequencyCancellation.frequency_power_sum_fin n k (lt_of_lt_of_le hk hrn) a
  obtain ⟨k, hk, heval⟩ :=
    IntegralPositiveMellinPower.exists_positive_scalar_integral_shift
      Finset.univ c b q hq hq0 r ha hz hjets
  have hGamma :
      (Real.Gamma (p + 1) : ℂ) *
        (∫ t : ℝ in Set.Ioi 0, IntegralOriginalConvergence.g n a t /
          ((t ^ (p + 1) : ℝ) : ℂ)) =
      ∫ s : ℝ in Set.Ioi 0, ((s ^ p : ℝ) : ℂ) *
        (∑ j : Fin (n+1), c j / ((s : ℂ) + b j)) := by
    rw [IntegralOriginalRepresentation.gamma_mul_original_integral_of_pos n p a hp hpn]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [c, b]
    push_cast
    ring
  refine ⟨(k : ℂ) * (-1 : ℂ)^r,
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hk.ne') (pow_ne_zero _ (by norm_num)), ?_⟩
  rw [hGamma, ← hqr, heval]
  change (k : ℂ) * (∑ j : Fin (n+1), c j * (-b j)^r * (b j)^(q : ℂ)) =
    ((k : ℂ) * (-1 : ℂ)^r) *
      (∑ j : Fin (n+1), c j * (b j)^((q + (r : ℝ) : ℝ) : ℂ))
  conv_rhs => rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [mul_assoc] using shifted_cpow_merge (c j) (b j) q r hq hr

end IntegralPositiveOriginalPower


namespace IntegralPowerPhase

lemma log_ofReal_neg {y : ℝ} (hy : y < 0) :
    Complex.log (y : ℂ) = (Real.log (-y) : ℂ) + (Real.pi : ℂ) * Complex.I := by
  have he : (y : ℂ) = ((-y : ℝ) : ℂ) * (-1) := by push_cast; ring
  rw [he, Complex.log_ofReal_mul (neg_pos.mpr hy) (by norm_num), Complex.log_neg_one]

lemma log_I_mul_ofReal (y : ℝ) (hy : y ≠ 0) :
    Complex.log (Complex.I * (y : ℂ)) =
      Complex.log Complex.I + conj (Complex.log (y : ℂ)) := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · have he : Complex.I * (y : ℂ) = (-Complex.I) * ((-y : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.log_mul_ofReal (-y) (neg_pos.mpr hneg) (-Complex.I)
      (neg_ne_zero.mpr Complex.I_ne_zero), log_ofReal_neg hneg,
      Complex.log_I, Complex.log_neg_I]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  · rw [Complex.log_mul_ofReal y hpos Complex.I Complex.I_ne_zero,
      ← Complex.ofReal_log hpos.le]
    simp only [Complex.conj_ofReal]
    ring

lemma cpow_I_mul_ofReal (p y : ℝ) :
    (Complex.I * (y : ℂ))^(p : ℂ) =
      Complex.I^(p : ℂ) * conj ((y : ℂ)^(p : ℂ)) := by
  by_cases hy : y = 0
  · subst y
    by_cases hp : p = 0
    · subst p; simp
    · simp [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hp)]
  · rw [Complex.cpow_def_of_ne_zero (mul_ne_zero Complex.I_ne_zero
        (Complex.ofReal_ne_zero.mpr hy)),
      Complex.cpow_def_of_ne_zero Complex.I_ne_zero,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy),
      ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      log_I_mul_ofReal y hy, add_mul, Complex.exp_add]

lemma cpow_pos_real_mul (p b : ℝ) (hb : 0 < b) (z : ℂ) :
    ((b : ℂ) * z)^(p : ℂ) = (b : ℂ)^(p : ℂ) * z^(p : ℂ) := by
  by_cases hz : z = 0
  · subst z
    by_cases hp : p = 0
    · subst p; simp
    · simp [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hp)]
  · rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne') hz),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne'),
      Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hb hz,
      ← Complex.ofReal_log hb.le, add_mul, Complex.exp_add]

lemma cpow_two_I_mul_ofReal (p y : ℝ) :
    ((2 : ℂ) * Complex.I * (y : ℂ))^(p : ℂ) =
      ((2 : ℂ) * Complex.I)^(p : ℂ) * conj ((y : ℂ)^(p : ℂ)) := by
  calc
    _ = (2 : ℂ)^(p : ℂ) * (Complex.I * (y : ℂ))^(p : ℂ) := by
      simpa only [Complex.ofReal_ofNat, mul_assoc] using
        cpow_pos_real_mul p 2 (by norm_num) (Complex.I * (y : ℂ))
    _ = ((2 : ℂ)^(p : ℂ) * Complex.I^(p : ℂ)) * conj ((y : ℂ)^(p : ℂ)) := by
      rw [cpow_I_mul_ofReal]
      ring
    _ = _ := by
      have h := cpow_pos_real_mul p 2 (by norm_num) Complex.I
      simp only [Complex.ofReal_ofNat] at h
      rw [h]

lemma log_two_I_mul_ofReal (y : ℝ) (hy : y ≠ 0) :
    Complex.log ((2 : ℂ) * Complex.I * (y : ℂ)) =
      Complex.log ((2 : ℂ) * Complex.I) + conj (Complex.log (y : ℂ)) := by
  have hiy : Complex.I * (y : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hy)
  have h1 := Complex.log_ofReal_mul (r := (2 : ℝ)) (by norm_num) hiy
  have h2 := Complex.log_ofReal_mul (r := (2 : ℝ)) (by norm_num) Complex.I_ne_zero
  simp only [Complex.ofReal_ofNat] at h1 h2
  rw [mul_assoc, h1, h2, log_I_mul_ofReal y hy]
  ring

end IntegralPowerPhase


namespace IntegralFinitePowerPhase

open ComplexConjugate
open IntegralPowerPhase IntegralTruncatedPower

lemma conj_cpow_eq_truncatedPower (p y : ℝ) (hp : p ≠ 0) :
    conj ((y : ℂ)^(p : ℂ)) = (truncatedPower p y : ℂ) +
      Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) * (truncatedPower p (-y) : ℂ) := by
  rcases lt_trichotomy y 0 with hneg | rfl | hpos
  · rw [Complex.ofReal_cpow_of_nonpos hneg.le, map_mul, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (neg_pos.mpr hneg).le, Complex.conj_ofReal, ← Complex.exp_conj,
      truncatedPower_of_nonpos p hneg.le, truncatedPower_of_pos p (neg_pos.mpr hneg)]
    simp only [Complex.ofReal_zero, zero_add]
    have he : conj ((Real.pi : ℂ) * Complex.I * (p : ℂ)) =
        -Complex.I * (Real.pi : ℂ) * (p : ℂ) := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [he]
    ring
  · simp [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hp), truncatedPower_of_nonpos p le_rfl]
  · rw [truncatedPower_of_pos p hpos,
      truncatedPower_of_nonpos p (neg_nonpos.mpr hpos.le), ← Complex.ofReal_cpow hpos.le]
    simp

/-- The finite imaginary-axis power sum is the actual reflected-tail boundary. -/
theorem imag_power_sum_eq_boundary (n : ℕ) (p x : ℝ) (hp : p ≠ 0) :
    (∑ j ∈ Finset.range (n+1), ((-1 : ℂ)^j * (n.choose j : ℂ)) *
      ((2 : ℂ) * Complex.I * (((j : ℝ)-x : ℝ) : ℂ))^(p : ℂ)) =
    ((2 : ℂ) * Complex.I)^(p : ℂ) *
      (((-1 : ℂ)^n) * (T n p ((n : ℝ)-x) : ℂ) +
        Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) * (T n p x : ℂ)) := by
  have hF := IntegralTruncatedPowerCauchyBoundary.F_boundary_sum_eq n p x
  simp only [Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast] at hF
  calc
    _ = ((2 : ℂ) * Complex.I)^(p : ℂ) *
        (∑ j ∈ Finset.range (n+1), ((-1 : ℂ)^j * (n.choose j : ℂ)) *
          ((truncatedPower p ((j : ℝ)-x) : ℂ) +
            Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) *
              (truncatedPower p (x-(j : ℝ)) : ℂ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [cpow_two_I_mul_ofReal, conj_cpow_eq_truncatedPower p ((j : ℝ)-x) hp]
      have he : -((j : ℝ)-x) = x-(j : ℝ) := by ring
      rw [he]
      ring
    _ = _ := by rw [hF]

lemma pow_log_two_I_mul_ofReal (r : ℕ) (y : ℝ) (h : y ≠ 0 ∨ r ≠ 0) :
    ((2 : ℂ) * Complex.I * (y : ℂ))^r * Complex.log ((2 : ℂ) * Complex.I * (y : ℂ)) =
      ((2 : ℂ) * Complex.I)^r *
        ((y : ℂ)^r * (Complex.log ((2 : ℂ) * Complex.I) + conj (Complex.log (y : ℂ)))) := by
  by_cases hy : y = 0
  · have hr : r ≠ 0 := h.resolve_left (fun hne => hne hy)
    subst y
    simp [hr]
  · rw [mul_pow, log_two_I_mul_ofReal y hy]
    ring

/-- A vanishing polynomial moment cancels the constant logarithmic phase. -/
theorem sum_pow_log_two_I {ι : Type*} (s : Finset ι) (c y : ι → ℝ) (r : ℕ)
    (hnodes : ∀ i ∈ s, y i ≠ 0 ∨ r ≠ 0)
    (hmom : (∑ i ∈ s, (c i : ℂ) * (y i : ℂ)^r) = 0) :
    (∑ i ∈ s, (c i : ℂ) * ((2 : ℂ) * Complex.I * (y i : ℂ))^r *
      Complex.log ((2 : ℂ) * Complex.I * (y i : ℂ))) =
      ((2 : ℂ) * Complex.I)^r *
        conj (∑ i ∈ s, (c i : ℂ) * (y i : ℂ)^r * Complex.log (y i : ℂ)) := by
  have he : (∑ i ∈ s, (c i : ℂ) * ((2 : ℂ) * Complex.I * (y i : ℂ))^r *
      Complex.log ((2 : ℂ) * Complex.I * (y i : ℂ))) =
      ((2 : ℂ) * Complex.I)^r *
        (Complex.log ((2 : ℂ) * Complex.I) * (∑ i ∈ s, (c i : ℂ) * (y i : ℂ)^r) +
          ∑ i ∈ s, (c i : ℂ) * (y i : ℂ)^r * conj (Complex.log (y i : ℂ))) := by
    rw [mul_add]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have ht := congrArg (fun z : ℂ => (c i : ℂ) * z) (pow_log_two_I_mul_ofReal r (y i) (hnodes i hi))
    calc
      _ = (c i : ℂ) * (((2 : ℂ) * Complex.I * (y i : ℂ))^r *
          Complex.log ((2 : ℂ) * Complex.I * (y i : ℂ))) := by ring
      _ = _ := ht
      _ = _ := by ring
  rw [he, hmom, mul_zero, zero_add]
  congr 1
  simp only [map_sum, map_mul, map_pow, Complex.conj_ofReal]

end IntegralFinitePowerPhase


namespace IntegralBinomialLogPhase

open ComplexConjugate
open IntegralFrequencyCancellation IntegralFinitePowerPhase IntegralTruncatedPower

/-- The logarithmic Mellin phase has no constant-log remainder below degree n. -/
theorem binomial_log_sum_phase (n r : ℕ) (hr : r < n) (x : ℝ)
    (hnodes : r ≠ 0 ∨ ∀ j ∈ Finset.range (n+1), x ≠ (j : ℝ)) :
    (∑ j ∈ Finset.range (n+1), ((-1 : ℂ)^j * (n.choose j : ℂ)) *
      ((2 : ℂ) * Complex.I * (((j : ℝ)-x : ℝ) : ℂ))^r *
        Complex.log ((2 : ℂ) * Complex.I * (((j : ℝ)-x : ℝ) : ℂ))) =
    ((2 : ℂ) * Complex.I)^r * conj
      (∑ j ∈ Finset.range (n+1), ((-1 : ℂ)^j * (n.choose j : ℂ)) *
        ((((j : ℝ)-x : ℝ) : ℂ))^r * Complex.log ((((j : ℝ)-x : ℝ) : ℂ))) := by
  let c (j : ℕ) : ℝ := (-1 : ℝ)^j * (n.choose j : ℝ)
  let y (j : ℕ) : ℝ := (j : ℝ)-x
  have hmom : (∑ j ∈ Finset.range (n+1), (c j : ℂ) * (y j : ℂ)^r) = 0 := by
    have h := alternating_choose_affine_power_sum (R := ℂ) n r hr (-(x : ℂ)) 1
    convert h using 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [c, y]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
      Complex.ofReal_one, Complex.ofReal_natCast, one_mul]
    congr 1
    congr 1
    push_cast
    ring
  have hn (j : ℕ) (hj : j ∈ Finset.range (n+1)) : y j ≠ 0 ∨ r ≠ 0 := by
    rcases hnodes with hrzero | hknots
    · exact Or.inr hrzero
    · exact Or.inl (sub_ne_zero.mpr (Ne.symm (hknots j hj)))
  have h := sum_pow_log_two_I (Finset.range (n+1)) c y r hn hmom
  simpa only [c, y, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_natCast] using h

theorem binomial_log_sum_phase_fin (n r : ℕ) (hr : r < n) (x : ℝ)
    (hnodes : r ≠ 0 ∨ ∀ j ∈ Finset.range (n+1), x ≠ (j : ℝ)) :
    (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
      ((2 : ℂ) * Complex.I * ((((j : ℕ) : ℝ)-x : ℝ) : ℂ))^r *
        Complex.log ((2 : ℂ) * Complex.I * ((((j : ℕ) : ℝ)-x : ℝ) : ℂ))) =
    ((2 : ℂ) * Complex.I)^r * conj
      (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
        (((((j : ℕ) : ℝ)-x : ℝ) : ℂ))^r * Complex.log (((((j : ℕ) : ℝ)-x : ℝ) : ℂ))) := by
  let f (j : ℕ) : ℂ := ((-1 : ℂ)^j * (n.choose j : ℂ)) *
    ((2 : ℂ) * Complex.I * (((j : ℝ)-x : ℝ) : ℂ))^r *
      Complex.log ((2 : ℂ) * Complex.I * (((j : ℝ)-x : ℝ) : ℂ))
  let g (j : ℕ) : ℂ := ((-1 : ℂ)^j * (n.choose j : ℂ)) *
    ((((j : ℝ)-x : ℝ) : ℂ))^r * Complex.log ((((j : ℝ)-x : ℝ) : ℂ))
  change (∑ j : Fin (n+1), f j) = ((2 : ℂ)*Complex.I)^r * conj (∑ j : Fin (n+1), g j)
  rw [Fin.sum_univ_eq_sum_range f (n+1), Fin.sum_univ_eq_sum_range g (n+1)]
  exact binomial_log_sum_phase n r hr x hnodes

theorem imag_power_sum_eq_boundary_fin (n : ℕ) (p x : ℝ) (hp : p ≠ 0) :
    (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
      ((2 : ℂ) * Complex.I * ((((j : ℕ) : ℝ)-x : ℝ) : ℂ))^(p : ℂ)) =
    ((2 : ℂ) * Complex.I)^(p : ℂ) *
      (((-1 : ℂ)^n) * (T n p ((n : ℝ)-x) : ℂ) +
        Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) * (T n p x : ℂ)) := by
  let f (j : ℕ) : ℂ := ((-1 : ℂ)^j * (n.choose j : ℂ)) *
    ((2 : ℂ)*Complex.I*(((j : ℝ)-x : ℝ) : ℂ))^(p : ℂ)
  change (∑ j : Fin (n+1), f j) = _
  rw [Fin.sum_univ_eq_sum_range f (n+1)]
  exact imag_power_sum_eq_boundary n p x hp

/-- The exact frequencies from the approved question, with all casts explicit. -/
theorem frequency_cpow_sum_eq_boundary (n : ℕ) (p a : ℝ) (hp : p ≠ 0) :
    (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
      (-Complex.I * (((a+(n : ℝ)-2*((j : ℕ) : ℝ)) : ℝ) : ℂ))^(p : ℂ)) =
    ((2 : ℂ)*Complex.I)^(p : ℂ) *
      (((-1 : ℂ)^n) * (T n p ((n : ℝ)-((n : ℝ)+a)/2) : ℂ) +
        Complex.exp (-Complex.I*(Real.pi : ℂ)*(p : ℂ)) * (T n p (((n : ℝ)+a)/2) : ℂ)) := by
  have h := imag_power_sum_eq_boundary_fin n p (((n : ℝ)+a)/2) hp
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  congr 1
  push_cast
  ring

end IntegralBinomialLogPhase


namespace IntegralTruncatedPowerNegativeBoundary

open IntegralTruncatedPower IntegralTruncatedPowerCauchyBoundary

noncomputable def boundaryValue (n : ℕ) (p x : ℝ) : ℂ :=
  (((-1 : ℝ) ^ n : ℝ) : ℂ) * (T n p ((n : ℝ) - x) : ℂ) +
    Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) * (T n p x : ℂ)

lemma tendsto_lower_cpow_of_ne_zero (a p : ℝ) (ha : a ≠ 0) :
    Tendsto (fun ε : ℝ => ((a : ℂ) - Complex.I * (ε : ℂ)) ^ (p : ℂ))
      (𝓝[>] 0) (𝓝 ((truncatedPower p a : ℂ) +
        Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) *
          (truncatedPower p (-a) : ℂ))) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · rw [truncatedPower_of_nonpos p ha.le, truncatedPower_of_pos p (neg_pos.mpr ha)]
    simpa only [Complex.ofReal_zero, zero_add] using tendsto_lower_cpow_neg a p ha
  · rw [truncatedPower_of_pos p ha, truncatedPower_of_nonpos p (neg_nonpos.mpr ha.le)]
    simpa only [Complex.ofReal_zero, mul_zero, add_zero] using
      (tendsto_lower_cpow_pos a p ha).mono_left nhdsWithin_le_nhds

/-- Every real exponent is allowed when the boundary point avoids all nodes. -/
theorem tendsto_F_of_no_knots (n : ℕ) (p x : ℝ)
    (hknots : ∀ j ∈ Finset.range (n + 1), x ≠ (j : ℝ)) :
    Tendsto (fun ε : ℝ => IntegralTruncatedPowerCauchy.F n p
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0) (𝓝 (boundaryValue n p x)) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) : Tendsto
      (fun ε : ℝ => (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        (((j : ℂ) - ((x : ℂ) + Complex.I * (ε : ℂ))) ^ (p : ℂ)))
      (𝓝[>] 0)
      (𝓝 ((((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        ((truncatedPower p ((j : ℝ) - x) : ℂ) +
          Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) *
            (truncatedPower p (x - (j : ℝ)) : ℂ)))) := by
    have h := (tendsto_lower_cpow_of_ne_zero ((j : ℝ) - x) p
      (sub_ne_zero.mpr (Ne.symm (hknots j hj)))).const_mul
        (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ)
    convert h using 1
    · funext ε
      congr 2
      push_cast
      ring
    · simp only [neg_sub]
  have hsum := tendsto_finsetSum (Finset.range (n + 1)) hterm
  rw [F_boundary_sum_eq] at hsum
  exact hsum

/-- A genuinely two-dimensional phase cannot cancel two real coefficients. -/
theorem phase_eq_zero_iff (p A B : ℝ) (hsin : Real.sin (Real.pi * p) ≠ 0) :
    (A : ℂ) + Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) * (B : ℂ) = 0 ↔
      A = 0 ∧ B = 0 := by
  constructor
  · intro hz
    have hp : (Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ))).im =
        -Real.sin (Real.pi * p) := by
      simp [Complex.exp_im, Complex.mul_re, Complex.mul_im, Real.sin_neg]
    have hi := congrArg Complex.im hz
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, mul_zero,
      zero_add, Complex.ofReal_re, Complex.zero_im] at hi
    rw [hp] at hi
    have hB : B = 0 := (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr hsin)
    have hA : A = 0 := by simpa only [hB, Complex.ofReal_zero, mul_zero, add_zero,
      Complex.ofReal_eq_zero] using hz
    exact ⟨hA, hB⟩
  · rintro ⟨rfl, rfl⟩
    simp

lemma T_negative_ne_zero_of_pos (n : ℕ) (p t : ℝ) (hp : p < 0) (ht : 0 < t)
    (hknots : ∀ j ∈ Finset.range (n + 1), t ≠ (j : ℝ)) : T n p t ≠ 0 := by
  have hsign : ∃ j : ℕ, 0 < (-1 : ℝ) ^ j * T n p t := by
    by_cases hnt : (n : ℝ) < t
    · exact ⟨n, IntegralTruncatedPowerSign.signed_T_neg_above_pos n p t hp hnt⟩
    · have htn : t < (n : ℝ) := lt_of_le_of_ne (le_of_not_gt hnt)
        (hknots n (by simp))
      let j : ℕ := Nat.floor t
      have hjn : j < n := (Nat.floor_lt ht.le).mpr htn
      have hjle : (j : ℝ) ≤ t := Nat.floor_le ht.le
      have hjlt : (j : ℝ) < t := lt_of_le_of_ne hjle
        (Ne.symm (hknots j (Finset.mem_range.mpr (Nat.lt_succ_of_lt hjn))))
      exact ⟨j, IntegralTruncatedPowerSign.signed_T_nonpos_cell_pos n j hjn p t
        hp.le hjlt (Nat.lt_floor_add_one t)⟩
  obtain ⟨j, hj⟩ := hsign
  intro hz
  simp only [hz, mul_zero, lt_self_iff_false] at hj

/-- The negative-power strip has a nonzero reflected tail, without moment assumptions. -/
theorem negative_tails_not_both_zero (n : ℕ) (p x : ℝ) (hp : p < 0)
    (hknots : ∀ j ∈ Finset.range (n + 1), x ≠ (j : ℝ)) :
    T n p x ≠ 0 ∨ T n p ((n : ℝ) - x) ≠ 0 := by
  by_cases hx : 0 < x
  · exact Or.inl (T_negative_ne_zero_of_pos n p x hp hx hknots)
  · right
    have hxne : x ≠ 0 := by simpa only [Nat.cast_zero] using hknots 0 (by simp)
    have hx0 : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hxne
    have hpos := IntegralTruncatedPowerSign.signed_T_neg_above_pos n p ((n : ℝ) - x)
      hp (by linarith)
    intro hz
    simp only [hz, mul_zero, lt_self_iff_false] at hpos

theorem boundaryValue_ne_zero_negative (n : ℕ) (p x : ℝ) (hp : -1 < p) (hp0 : p < 0)
    (hknots : ∀ j ∈ Finset.range (n + 1), x ≠ (j : ℝ)) : boundaryValue n p x ≠ 0 := by
  have hsin : Real.sin (Real.pi * p) ≠ 0 := by
    apply (Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])).ne
  intro hz
  have hphase : ((((-1 : ℝ) ^ n * T n p ((n : ℝ) - x) : ℝ) : ℂ) +
      Complex.exp (-Complex.I * (Real.pi : ℂ) * (p : ℂ)) * (T n p x : ℂ)) = 0 := by
    simpa only [boundaryValue, Complex.ofReal_mul] using hz
  obtain ⟨hA, hB⟩ := (phase_eq_zero_iff p _ _ hsin).mp hphase
  have hnx : T n p ((n : ℝ) - x) = 0 :=
    (mul_eq_zero.mp hA).resolve_left (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))
  exact (negative_tails_not_both_zero n p x hp0 hknots).elim (fun h => h hB) (fun h => h hnx)

theorem not_tendsto_F_zero_negative (n : ℕ) (p x : ℝ) (hp : -1 < p) (hp0 : p < 0)
    (hknots : ∀ j ∈ Finset.range (n + 1), x ≠ (j : ℝ)) :
    ¬ Tendsto (fun ε : ℝ => IntegralTruncatedPowerCauchy.F n p
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
  intro hz
  exact boundaryValue_ne_zero_negative n p x hp hp0 hknots
    (tendsto_nhds_unique (tendsto_F_of_no_knots n p x hknots) hz)

end IntegralTruncatedPowerNegativeBoundary


namespace IntegralOriginalPositiveNoninteger

open IntegralTruncatedPower IntegralBinomialLogPhase

lemma sin_pi_mul_ne_zero (p : ℝ) (hp : 0 < p) (hnot : p ≠ (Nat.floor p : ℝ)) :
    Real.sin (Real.pi*p) ≠ 0 := by
  have hfloor : (Nat.floor p : ℝ) < p :=
    lt_of_le_of_ne (Nat.floor_le hp.le) (Ne.symm hnot)
  have hδ : 0 < p-(Nat.floor p : ℝ) := sub_pos.mpr hfloor
  have hδ' : p-(Nat.floor p : ℝ) < 1 := by linarith [Nat.lt_floor_add_one p]
  have hsin : 0 < Real.sin (Real.pi * (p-(Nat.floor p : ℝ))) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hδ)
      (by simpa only [mul_one] using mul_lt_mul_of_pos_left hδ' Real.pi_pos)
  have he : Real.pi*p = Real.pi*(p-(Nat.floor p : ℝ)) + (Nat.floor p : ℝ)*Real.pi := by ring
  rw [he, Real.sin_add_nat_mul_pi]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)) hsin.ne'

lemma boundary_value_ne_zero (n : ℕ) (p : ℝ) (hp : 0 < p) (hpn : p < (n : ℝ))
    (hnot : p ≠ (Nat.floor p : ℝ)) (x : ℝ) :
    ((-1 : ℂ)^n * (T n p ((n : ℝ)-x) : ℂ) +
      Complex.exp (-Complex.I*(Real.pi : ℂ)*(p : ℂ)) * (T n p x : ℂ)) ≠ 0 := by
  intro hz
  let A : ℝ := (-1 : ℝ)^n * T n p ((n : ℝ)-x)
  let B : ℝ := T n p x
  have hphase : (A : ℂ) + Complex.exp (-Complex.I*(Real.pi : ℂ)*(p : ℂ)) * (B : ℂ) = 0 := by
    simpa only [A, B, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
      Complex.ofReal_one] using hz
  have hAB := (IntegralTruncatedPowerNegativeBoundary.phase_eq_zero_iff p A B
    (sin_pi_mul_ne_zero p hp hnot)).mp hphase
  have hA : (-1 : ℝ)^n * T n p ((n : ℝ)-x) = 0 := hAB.1
  have hB : T n p x = 0 := hAB.2
  have hnx : T n p ((n : ℝ)-x) = 0 :=
    (mul_eq_zero.mp hA).resolve_left (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))
  exact IntegralTruncatedPowerJointNonzero.no_common_zeros_noninteger n p hp hpn hnot x ⟨hB, hnx⟩

/-- Nonvanishing of the actual source integral in the full positive noninteger subdomain. -/
theorem integral_ne_zero (n : ℕ) (p a : ℝ) (hp : 0 < p) (hpn : p < (n : ℝ))
    (hnot : p ≠ (Nat.floor p : ℝ)) :
    (∫ t : ℝ in Set.Ioi 0, IntegralOriginalConvergence.g n a t /
      ((t^(p+1) : ℝ) : ℂ)) ≠ 0 := by
  obtain ⟨K, hK, hGI⟩ := IntegralPositiveOriginalPower.gamma_mul_original_integral_noninteger
    n p a hp hpn hnot
  have hscalar : ((2 : ℂ)*Complex.I)^(p : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (by norm_num) Complex.I_ne_zero))
  have hfreq := frequency_cpow_sum_eq_boundary n p a hp.ne'
  have hsum0 :
      (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
        (-Complex.I * (((a+(n : ℝ)-2*((j : ℕ) : ℝ)) : ℝ) : ℂ))^(p : ℂ)) ≠ 0 := by
    rw [hfreq]
    exact mul_ne_zero hscalar (boundary_value_ne_zero n p hp hpn hnot (((n : ℝ)+a)/2))
  have hsum :
      (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
        (-(Complex.I * ((a+(n : ℝ)-2*(j : ℝ) : ℝ) : ℂ)))^(p : ℂ)) ≠ 0 := by
    simpa only [neg_mul] using hsum0
  intro hz
  rw [hz, mul_zero] at hGI
  exact (mul_ne_zero hK hsum) hGI.symm

/-- The complete approved integrand has a nonzero ordinary improper limit
for every positive noninteger admissible exponent. -/
theorem exists_nonzero_limit (n : ℕ) (p a : ℝ) (hp : 0 < p) (hpn : p < (n : ℝ))
    (hnot : p ≠ (Nat.floor p : ℝ)) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto
      (fun R : ℝ => ∫ t in (0 : ℝ)..R, IntegralOriginalConvergence.g n a t /
        ((t^(p+1) : ℝ) : ℂ)) atTop (𝓝 L) := by
  refine ⟨_, integral_ne_zero n p a hp hpn hnot, ?_⟩
  exact intervalIntegral_tendsto_integral_Ioi 0
    (IntegralOriginalConvergence.integrableOn_of_pos n p a hp hpn) tendsto_id

end IntegralOriginalPositiveNoninteger


namespace IntegralExponentialAbel

open MeasureTheory Set Filter Topology

lemma norm_exp_mul_le_one (c : ℂ) (t : ℝ) (hc : c.re ≤ 0) (ht : 0 ≤ t) :
    ‖Complex.exp (c * t)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simpa using mul_nonpos_of_nonpos_of_nonneg hc ht

lemma continuousOn_weighted_exp (c : ℂ) (r : ℝ) :
    ContinuousOn (fun t : ℝ => Complex.exp (c * t) * (t ^ r : ℝ)) (Ioi 0) := by
  apply ContinuousOn.mul
  · fun_prop
  · exact Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const fun t ht => Or.inl ht.ne')

lemma norm_weighted_exp_le (c : ℂ) (r t : ℝ) (hc : c.re ≤ 0) (ht : 0 ≤ t) :
    ‖Complex.exp (c * t) * (t ^ r : ℝ)‖ ≤ t ^ r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg ht _) (norm_exp_mul_le_one c t hc ht)

lemma integrableOn_tail (c : ℂ) (r : ℝ) (hc : c.re ≤ 0) (hr : r < -1) :
    IntegrableOn (fun t : ℝ => Complex.exp (c * t) * (t ^ r : ℝ)) (Ioi 1) := by
  apply (integrableOn_Ioi_rpow_of_lt hr zero_lt_one).mono'
    ((continuousOn_weighted_exp c r).mono (Ioi_subset_Ioi zero_le_one)
      |>.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_weighted_exp_le c r t hc (zero_lt_one.trans ht).le

lemma integrableOn_zero_one (c : ℂ) (r : ℝ) (hc : c.re ≤ 0) (hr : -1 < r) :
    IntervalIntegrable (fun t : ℝ => Complex.exp (c * t) * (t ^ r : ℝ)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  apply ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr hr).mono'
    ((continuousOn_weighted_exp c r).mono Ioo_subset_Ioi_self
      |>.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact norm_weighted_exp_le c r t hc ht.1.le

lemma hasDerivAt_exp_mul (c : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (c * u)) (Complex.exp (c * t) * c) t := by
  simpa only [id_eq, Complex.ofReal_one, mul_one] using
    (((hasDerivAt_id t).ofReal_comp).const_mul c).cexp

/-- Explicit integration-by-parts value of the power-weighted exponential tail,
valid also on the imaginary boundary of the closed left half-plane. -/
theorem weighted_tail_tendsto (c : ℂ) (α : ℝ) (hc : c ≠ 0)
    (hre : c.re ≤ 0) (hα : 0 < α) :
    Tendsto (fun T : ℝ => ∫ t in (1 : ℝ)..T,
      Complex.exp (c * t) * (t ^ (-α) : ℝ)) atTop
      (𝓝 (-Complex.exp c / c + (α : ℂ) / c *
        (∫ t : ℝ in Ioi 1, Complex.exp (c * t) * (t ^ (-α - 1) : ℝ)))) := by
  let F : ℝ → ℂ := fun t => Complex.exp (c * t) * (t ^ (-α) : ℝ) / c
  let R : ℝ → ℂ := fun t => ((-α : ℝ) : ℂ) / c *
    (Complex.exp (c * t) * (t ^ (-α - 1) : ℝ))
  have hR : IntegrableOn R (Ioi 1) :=
    (integrableOn_tail c (-α - 1) hre (by linarith)).const_mul _
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt F
      (Complex.exp (c * t) * (t ^ (-α) : ℝ) + R t) t := by
    have hp := (Real.hasDerivAt_rpow_const (p := -α) (Or.inl ht.ne')).ofReal_comp
    apply (((hasDerivAt_exp_mul c t).mul hp).div_const c).congr_deriv
    dsimp only [R]
    push_cast
    field_simp [hc]
  have hF : Tendsto F atTop (𝓝 0) := by
    have hp0 : Tendsto (fun t : ℝ => t ^ (-α) / ‖c‖) atTop (𝓝 0) := by
      simpa only [zero_div] using (tendsto_rpow_neg_atTop hα).div_const ‖c‖
    apply squeeze_zero_norm' _ hp0
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp only [F]
    rw [norm_div]
    exact div_le_div_of_nonneg_right (norm_weighted_exp_le c (-α) t hre ht.le) (norm_nonneg _)
  have hRlim := intervalIntegral_tendsto_integral_Ioi 1 hR tendsto_id
  have hlim := (hF.sub_const (F 1)).sub hRlim
  have hvalue : (0 - F 1) - (∫ t : ℝ in Ioi 1, R t) =
      -Complex.exp c / c + (α : ℂ) / c *
        (∫ t : ℝ in Ioi 1, Complex.exp (c * t) * (t ^ (-α - 1) : ℝ)) := by
    simp only [F, R, Real.one_rpow, Complex.ofReal_one, mul_one,
      integral_const_mul, Complex.ofReal_neg, zero_sub]
    ring
  rw [hvalue] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hi : IntervalIntegrable
      (fun t : ℝ => Complex.exp (c * t) * (t ^ (-α) : ℝ)) volume 1 T := by
    apply ((continuousOn_weighted_exp c (-α)).mono ?_).intervalIntegrable
    rw [uIcc_of_le hT]
    exact fun t ht => lt_of_lt_of_le zero_lt_one ht.1
  have hRi : IntervalIntegrable R volume 1 T := by
    apply (((continuousOn_weighted_exp c (-α - 1)).const_mul ((-α : ℝ) / c)).mono ?_)
      |>.intervalIntegrable
    rw [uIcc_of_le hT]
    exact fun t ht => lt_of_lt_of_le zero_lt_one ht.1
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by rw [uIcc_of_le hT] at ht; linarith [ht.1])) (hi.add hRi)
  rw [intervalIntegral.integral_add hi hRi] at heq
  exact (eq_sub_of_add_eq heq).symm


/-- Dominated damping continuity whenever the undamped real-power envelope is
integrable. This is applied separately near zero and to the integration-by-parts
correction at infinity. -/
theorem integral_damped_tendsto (μ : Measure ℝ) (w r : ℝ)
    (hpos : ∀ᵐ t : ℝ ∂μ, 0 ≤ t) (hi : Integrable (fun t : ℝ => t ^ r) μ) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ, Complex.exp ((Complex.I * w - ε) * t) * (t ^ r : ℝ) ∂μ)
      (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, Complex.exp (Complex.I * w * t) * (t ^ r : ℝ) ∂μ)) := by
  have hm (ε : ℝ) : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp ((Complex.I * w - ε) * t) * (t ^ r : ℝ)) μ := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ t : ℝ ∂μ,
      ‖Complex.exp ((Complex.I * w - ε) * t) * (t ^ r : ℝ)‖ ≤ t ^ r := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [hpos] with t ht
    apply norm_weighted_exp_le _ r t _ ht
    simpa using neg_nonpos.mpr (show (0 : ℝ) ≤ ε from le_of_lt hε)
  have hlim : ∀ᵐ t : ℝ ∂μ, Tendsto
      (fun ε : ℝ => Complex.exp ((Complex.I * w - ε) * t) * (t ^ r : ℝ))
      (𝓝[>] 0) (𝓝 (Complex.exp (Complex.I * w * t) * (t ^ r : ℝ))) := by
    apply Eventually.of_forall
    intro t
    have hc : Continuous
        (fun ε : ℝ => Complex.exp ((Complex.I * w - ε) * t) * (t ^ r : ℝ)) := by
      fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  exact tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => t ^ r)
    (Eventually.of_forall hm) hb hi hlim

noncomputable def value (c : ℂ) (α : ℝ) : ℂ :=
  (∫ t in (0 : ℝ)..1, Complex.exp (c * t) * (t ^ (-α) : ℝ)) -
    Complex.exp c / c + (α : ℂ) / c *
      (∫ t : ℝ in Ioi 1, Complex.exp (c * t) * (t ^ (-α - 1) : ℝ))

theorem weighted_tendsto (c : ℂ) (α : ℝ) (hc : c ≠ 0)
    (hre : c.re ≤ 0) (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      Complex.exp (c * t) * (t ^ (-α) : ℝ)) atTop (𝓝 (value c α)) := by
  have hi := integrableOn_zero_one c (-α) hre (by linarith)
  have h := (weighted_tail_tendsto c α hc hre hα).const_add
    (∫ t in (0 : ℝ)..1, Complex.exp (c * t) * (t ^ (-α) : ℝ))
  have he : (∫ t in (0 : ℝ)..1, Complex.exp (c * t) * (t ^ (-α) : ℝ)) +
      (-Complex.exp c / c + (α : ℂ) / c *
        (∫ t : ℝ in Ioi 1, Complex.exp (c * t) * (t ^ (-α - 1) : ℝ))) = value c α := by
    unfold value
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have ht : IntervalIntegrable
      (fun t : ℝ => Complex.exp (c * t) * (t ^ (-α) : ℝ)) volume 1 T := by
    apply ((continuousOn_weighted_exp c (-α)).mono ?_).intervalIntegrable
    rw [uIcc_of_le hT]
    exact fun t ht => lt_of_lt_of_le zero_lt_one ht.1
  exact intervalIntegral.integral_add_adjacent_intervals hi ht

lemma integrable_weighted_exp_of_re_neg (c : ℂ) (α : ℝ)
    (hc : c.re < 0) (hα1 : α < 1) :
    IntegrableOn (fun t : ℝ => Complex.exp (c * t) * (t ^ (-α) : ℝ)) (Ioi 0) := by
  apply (IntegralOriginalRepresentation.integrable_gamma_kernel (-α) (-c.re)
    (by linarith) (neg_pos.mpr hc)).mono'
    ((continuousOn_weighted_exp c (-α)).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  rw [neg_mul, neg_neg]
  exact le_of_eq (mul_comm _ _)

theorem integral_weighted_exp_eq_value (c : ℂ) (α : ℝ)
    (hc : c.re < 0) (hα : 0 < α) (hα1 : α < 1) :
    (∫ t : ℝ in Ioi 0, Complex.exp (c * t) * (t ^ (-α) : ℝ)) = value c α := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 0
      (integrable_weighted_exp_of_re_neg c α hc hα1) tendsto_id)
    (weighted_tendsto c α hc0 hc.le hα hα1)

theorem value_tendsto_damping (w α : ℝ) (hw : w ≠ 0) (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun ε : ℝ => value (Complex.I * w - ε) α) (𝓝[>] 0)
      (𝓝 (value (Complex.I * w) α)) := by
  have hc0 : Complex.I * (w : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hw)
  have hnear := integral_damped_tendsto (volume.restrict (Ioc (0 : ℝ) 1)) w (-α)
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ht.1.le))
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -α) (a := 0) (b := 1)).1
  have hnear' : Tendsto
      (fun ε : ℝ => ∫ t in (0 : ℝ)..1,
        Complex.exp ((Complex.I * w - ε) * t) * (t ^ (-α) : ℝ))
      (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, Complex.exp (Complex.I * w * t) * (t ^ (-α) : ℝ))) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one] using hnear
  have htail := integral_damped_tendsto (volume.restrict (Ioi (1 : ℝ))) w (-α - 1)
    (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => (zero_lt_one.trans ht).le))
    (integrableOn_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) zero_lt_one)
  have hc : Tendsto (fun ε : ℝ => Complex.I * w - (ε : ℂ)) (𝓝[>] 0)
      (𝓝 (Complex.I * w)) := by
    have h : Continuous (fun ε : ℝ => Complex.I * w - (ε : ℂ)) := by fun_prop
    simpa using (h.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have he := hc.cexp.div hc hc0
  have hcoef := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (α : ℂ))
    (𝓝[>] 0) (𝓝 (α : ℂ))).div hc hc0
  simpa only [value, Pi.div_apply] using (hnear'.sub he).add (hcoef.mul htail)

/-- Abel convergence for the actual single-frequency power integral in the
conditional range. No general Abel theorem or oscillatory Gamma formula is
assumed. -/
theorem exists_limit_and_abel (w α : ℝ) (hw : w ≠ 0) (hα : 0 < α) (hα1 : α < 1) :
    ∃ L : ℂ,
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        Complex.exp (Complex.I * w * t) * (t ^ (-α) : ℝ)) atTop (𝓝 L) ∧
      Tendsto (fun ε : ℝ => ∫ t : ℝ in Ioi 0,
        Complex.exp ((Complex.I * w - ε) * t) * (t ^ (-α) : ℝ))
        (𝓝[>] 0) (𝓝 L) := by
  have hc0 : Complex.I * (w : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hw)
  refine ⟨value (Complex.I * w) α,
    weighted_tendsto _ _ hc0 (by simp) hα hα1, ?_⟩
  apply (value_tendsto_damping w α hw hα hα1).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  symm
  apply integral_weighted_exp_eq_value _ α _ hα hα1
  simpa using neg_neg_of_pos (show (0 : ℝ) < ε from hε)

end IntegralExponentialAbel


namespace IntegralOriginalSourceBase

open MeasureTheory Filter Topology Set

lemma integral_damped_phase_laplace (w s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    (∫ t : ℝ in Ioi 0, Complex.exp ((Complex.I * w - ε) * t) *
      (Real.exp (-(s * t)) : ℝ)) =
        1 / (((s + ε : ℝ) : ℂ) - Complex.I * w) := by
  have hre : (Complex.I * (w : ℂ) - (s + ε : ℝ)).re < 0 := by
    simpa using neg_neg_of_pos (add_pos hs hε)
  calc
    _ = ∫ t : ℝ in Ioi 0, Complex.exp ((Complex.I * w - (s + ε : ℝ)) * t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = -1 / (Complex.I * w - (s + ε : ℝ)) := by
      simpa using integral_exp_mul_complex_Ioi hre 0
    _ = _ := by
      rw [show Complex.I * (w : ℂ) - (s + ε : ℝ) =
        -((s + ε : ℝ) - Complex.I * w) by ring]
      simp only [neg_div_neg_eq, one_div]

/-- Exact damped Gamma--Stieltjes identity in the negative parameter base. -/
theorem gamma_damped_phase_eq_stieltjes (p w ε : ℝ)
    (hp : -1 < p) (hp0 : p < 0) (hε : 0 < ε) :
    (Real.Gamma (p + 1) : ℂ) *
        (∫ t : ℝ in Ioi 0, Complex.exp ((Complex.I * w - ε) * t) *
          (t ^ (-(p + 1)) : ℝ)) =
      ∫ s : ℝ in Ioi 0, (s ^ p : ℝ) /
        (((s + ε : ℝ) : ℂ) - Complex.I * w) := by
  have hre : (Complex.I * (w : ℂ) - ε).re < 0 := by simpa using neg_neg_of_pos hε
  have hi := IntegralExponentialAbel.integrable_weighted_exp_of_re_neg
    (Complex.I * w - ε) (p + 1) hre (by linarith)
  have hm : Measurable (fun t : ℝ => Complex.exp ((Complex.I * w - ε) * t)) := by
    fun_prop
  have h := IntegralOriginalRepresentation.gamma_mul_integral_eq_laplace
    (fun t : ℝ => Complex.exp ((Complex.I * w - ε) * t)) p hp hm hi
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  rw [integral_damped_phase_laplace w s ε hs hε]
  ring

/-- The original conditional single-frequency integral and the deformed
Stieltjes transform have the exact same limit, up to the positive real Gamma
factor. No principal-power source formula is assumed. -/
theorem exists_limit_stieltjes (p w : ℝ)
    (hp : -1 < p) (hp0 : p < 0) (hw : w ≠ 0) :
    ∃ L : ℂ,
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        Complex.exp (Complex.I * w * t) * (t ^ (-(p + 1)) : ℝ)) atTop (𝓝 L) ∧
      Tendsto (fun ε : ℝ => ∫ s : ℝ in Ioi 0,
        (s ^ p : ℝ) / (((s + ε : ℝ) : ℂ) - Complex.I * w))
        (𝓝[>] 0) (𝓝 ((Real.Gamma (p + 1) : ℂ) * L)) := by
  obtain ⟨L, hL, hAbel⟩ := IntegralExponentialAbel.exists_limit_and_abel
    w (p + 1) hw (by linarith) (by linarith)
  refine ⟨L, hL, ?_⟩
  apply (hAbel.const_mul (Real.Gamma (p + 1) : ℂ)).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact gamma_damped_phase_eq_stieltjes p w ε hp hp0 hε

/-- Assembly interface: continuity of the actual Stieltjes transform at the
nonreal frequency point turns the proved deformed-transform limit into an exact
identity for the ordinary improper integral. The continuity input is separate
from the original integral and can be supplied by the actual Stieltjes ODE layer. -/
theorem exists_limit_eq_stieltjes_of_continuous (p w : ℝ)
    (hp : -1 < p) (hp0 : p < 0) (hw : w ≠ 0)
    (hS : ContinuousAt
      (fun z : ℂ => ∫ s : ℝ in Ioi 0, (s ^ p : ℝ) / ((s : ℂ) + z))
      (-(Complex.I * w))) :
    ∃ L : ℂ,
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        Complex.exp (Complex.I * w * t) * (t ^ (-(p + 1)) : ℝ)) atTop (𝓝 L) ∧
      (Real.Gamma (p + 1) : ℂ) * L =
        ∫ s : ℝ in Ioi 0, (s ^ p : ℝ) / ((s : ℂ) - Complex.I * w) := by
  obtain ⟨L, hL, hM⟩ := exists_limit_stieltjes p w hp hp0 hw
  refine ⟨L, hL, ?_⟩
  have hz : Tendsto (fun ε : ℝ => (ε : ℂ) - Complex.I * w) (𝓝[>] 0)
      (𝓝 (-(Complex.I * w))) := by
    have hc : Continuous (fun ε : ℝ => (ε : ℂ) - Complex.I * w) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hM' := hS.tendsto.comp hz
  have heq : Tendsto (fun ε : ℝ => ∫ s : ℝ in Ioi 0,
      (s ^ p : ℝ) / (((s + ε : ℝ) : ℂ) - Complex.I * w))
      (𝓝[>] 0)
      (𝓝 (∫ s : ℝ in Ioi 0, (s ^ p : ℝ) / ((s : ℂ) - Complex.I * w))) := by
    simpa only [Function.comp_def, Complex.ofReal_add, sub_eq_add_neg, add_assoc] using hM'
  exact tendsto_nhds_unique hM heq

end IntegralOriginalSourceBase


namespace IntegralOriginalNegative

open MeasureTheory Filter Topology Set

/-- An actual single-frequency conditional power integral, with its finite-power
value derived from the proved Stieltjes identity and direct Abel convergence. -/
theorem single_frequency_power_limit (p w K : ℝ)
    (hp : -1 < p) (hp0 : p < 0) (hw : w ≠ 0)
    (hscalar : ∀ a : ℂ, a.im ≠ 0 →
      IntegralStieltjesTransform.S p a = (K : ℂ) * a ^ (p : ℂ)) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      Complex.exp (Complex.I * w * t) * (t ^ (-(p + 1)) : ℝ)) atTop
      (𝓝 (((K : ℂ) / (Real.Gamma (p + 1) : ℂ)) *
        (-(Complex.I * w)) ^ (p : ℂ))) := by
  obtain ⟨L, hL, hAbel⟩ := IntegralExponentialAbel.exists_limit_and_abel
    w (p + 1) hw (by linarith) (by linarith)
  have harg : Tendsto (fun ε : ℝ => (ε : ℂ) - Complex.I * w) (𝓝[>] 0)
      (𝓝 (-(Complex.I * w))) := by
    have hc : Continuous (fun ε : ℝ => (ε : ℂ) - Complex.I * w) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hslit : -(Complex.I * (w : ℂ)) ∈ Complex.slitPlane := by
    right
    simpa using neg_ne_zero.mpr hw
  have hpow := ((continuousAt_cpow_const (b := (p : ℂ)) hslit).tendsto.comp harg).const_mul (K : ℂ)
  have hgamma : Tendsto (fun ε : ℝ => (K : ℂ) *
      ((ε : ℂ) - Complex.I * w) ^ (p : ℂ)) (𝓝[>] 0)
      (𝓝 ((Real.Gamma (p + 1) : ℂ) * L)) := by
    apply (hAbel.const_mul (Real.Gamma (p + 1) : ℂ)).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    calc
      _ = ∫ s : ℝ in Ioi 0, (s ^ p : ℝ) /
          (((s + ε : ℝ) : ℂ) - Complex.I * w) :=
        IntegralOriginalSourceBase.gamma_damped_phase_eq_stieltjes p w ε hp hp0 hε
      _ = IntegralStieltjesTransform.S p ((ε : ℂ) - Complex.I * w) := by
        simp only [IntegralStieltjesTransform.S, IntegralStieltjesTransform.kernel,
          Complex.ofReal_add, sub_eq_add_neg, add_assoc]
      _ = _ := hscalar _ (by simpa using neg_ne_zero.mpr hw)
  have heq := tendsto_nhds_unique hgamma hpow
  have hΓ : (Real.Gamma (p + 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos (by linarith : 0 < p + 1)).ne'
  have hv : L = ((K : ℂ) * (-(Complex.I * w)) ^ (p : ℂ)) /
      (Real.Gamma (p + 1) : ℂ) := by
    apply (eq_div_iff hΓ).mpr
    simpa only [mul_comm] using heq
  rw [hv] at hL
  simpa only [div_mul_eq_mul_div] using hL

/-- Literal approved original integrand in the full negative-parameter strip.
The same positive real scalar works for every n and a at fixed p. -/
theorem original_negative_power_representation (p : ℝ) (hp : -1 < p) (hp0 : p < 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (a : ℝ),
      IntegralOriginalConvergence.pLow n a < p →
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        IntegralOriginalConvergence.g n a t / ((t ^ (p + 1) : ℝ) : ℂ)) atTop
        (𝓝 (((K : ℂ) / (Real.Gamma (p + 1) : ℂ)) *
          (∑ j : Fin (n + 1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
            (-(Complex.I * (((a + (n : ℝ) - 2 * ((j : ℕ) : ℝ)) : ℝ) : ℂ))) ^ (p : ℂ)))) := by
  classical
  obtain ⟨K, hK, hscalar⟩ :=
    IntegralStieltjesNonreal.exists_positive_cpow_scalar_nonreal p hp hp0
  refine ⟨K, hK, ?_⟩
  intro n a hpa
  let d : Fin (n + 1) → ℂ := fun j => (-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)
  let w : Fin (n + 1) → ℝ := fun j => a + (n : ℝ) - 2 * ((j : ℕ) : ℝ)
  have ha : ¬ ∃ j ≤ n, a = 2 * (j : ℝ) - n := by
    intro ha
    simp only [IntegralOriginalConvergence.pLow, if_pos ha] at hpa
    linarith
  have hw (j : Fin (n + 1)) : w j ≠ 0 := by
    intro h
    apply ha
    exact ⟨j, Nat.le_of_lt_succ j.isLt, by dsimp [w] at h; linarith⟩
  have hsum := tendsto_finsetSum Finset.univ (fun j _ =>
    (single_frequency_power_limit p (w j) K hp hp0 (hw j) hscalar).const_mul (d j))
  have hvalue : (∑ j, d j * (((K : ℂ) / (Real.Gamma (p + 1) : ℂ)) *
      (-(Complex.I * w j)) ^ (p : ℂ))) =
      ((K : ℂ) / (Real.Gamma (p + 1) : ℂ)) *
        (∑ j, d j * (-(Complex.I * w j)) ^ (p : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hvalue] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr_ae
    apply Eventually.of_forall
    intro t ht
    rw [uIoc_of_le (zero_le_one.trans hT)] at ht
    symm
    simpa only [d, w, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_natCast, Complex.ofReal_ofNat] using
      IntegralOriginalConvergence.integrand_eq_sum n p a t ht.1
  · intro j _
    have hnear := IntegralExponentialAbel.integrableOn_zero_one
      (Complex.I * w j) (-(p + 1)) (by simp) (by linarith)
    have htail : IntervalIntegrable (fun t : ℝ =>
        Complex.exp (Complex.I * w j * t) * (t ^ (-(p + 1)) : ℝ)) volume 1 T := by
      apply ((IntegralExponentialAbel.continuousOn_weighted_exp
        (Complex.I * w j) (-(p + 1))).mono ?_).intervalIntegrable
      rw [uIcc_of_le hT]
      exact fun t ht => lt_of_lt_of_le zero_lt_one ht.1
    exact (hnear.trans htail).const_mul (d j)

end IntegralOriginalNegative


namespace IntegralOriginalNegativeNonzero

open IntegralOriginalConvergence

lemma no_knots_of_negative_pLow (n : ℕ) (p a : ℝ) (hp0 : p < 0)
    (hpa : pLow n a < p) :
    ∀ j ∈ Finset.range (n + 1), ((n : ℝ) + a) / 2 ≠ (j : ℝ) := by
  intro j hj heq
  have hres : ∃ j ≤ n, a = 2 * (j : ℝ) - n :=
    ⟨j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), by linarith⟩
  have hpos : 0 < p := by
    simpa only [pLow, if_pos hres] using hpa
  exact (not_lt_of_gt hp0) hpos

/-- The exact finite frequency sum in the original negative-power formula is
nonzero by its actual reflected-tail boundary value. -/
theorem frequency_cpow_sum_ne_zero_negative (n : ℕ) (p a : ℝ)
    (hp : -1 < p) (hp0 : p < 0) (hpa : pLow n a < p) :
    (∑ j : Fin (n + 1), ((-1 : ℂ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
      (-Complex.I * (((a + (n : ℝ) - 2 * ((j : ℕ) : ℝ)) : ℝ) : ℂ)) ^ (p : ℂ)) ≠ 0 := by
  rw [IntegralBinomialLogPhase.frequency_cpow_sum_eq_boundary n p a (ne_of_lt hp0)]
  apply mul_ne_zero
  · apply Complex.cpow_ne_zero_iff.mpr
    left
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  · have hb := IntegralTruncatedPowerNegativeBoundary.boundaryValue_ne_zero_negative
      n p (((n : ℝ) + a) / 2) hp hp0 (no_knots_of_negative_pLow n p a hp0 hpa)
    simpa only [IntegralTruncatedPowerNegativeBoundary.boundaryValue,
      Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one] using hb

/-- The original ordinary improper integral has a nonzero limit throughout the
negative exponent subdomain. The original g and pLow definitions are literal. -/
theorem exists_nonzero_limit_negative (n : ℕ) (_hn : 1 ≤ n) (p a : ℝ)
    (hp : -1 < p) (hp0 : p < 0) (hpa : pLow n a < p) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        g n a t / ((t ^ (p + 1) : ℝ) : ℂ)) atTop (𝓝 L) := by
  obtain ⟨K, hK, hlim⟩ := IntegralOriginalNegative.original_negative_power_representation p hp hp0
  refine ⟨_, ?_, hlim n a hpa⟩
  apply mul_ne_zero
  · apply div_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (ne_of_gt hK)
    · exact Complex.ofReal_ne_zero.mpr
        (Real.Gamma_pos_of_pos (by linarith : 0 < p + 1)).ne'
  · simpa only [neg_mul] using frequency_cpow_sum_ne_zero_negative n p a hp hp0 hpa

end IntegralOriginalNegativeNonzero


namespace IntegralCauchyIntegerLog

open IntegralTruncatedPower IntegralTruncatedPowerCauchy Polynomial

lemma real_sub_ne_zero (z : ℂ) (hz : 0 < z.im) (t : ℝ) :
    (t : ℂ) - z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at hi
  linarith

lemma continuous_power_kernel (r : ℕ) (j : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Continuous (fun t : ℝ => ((t : ℂ) - (j : ℂ)) ^ r / ((t : ℂ) - z)) := by
  exact ((Complex.continuous_ofReal.sub continuous_const).pow r).div
    (Complex.continuous_ofReal.sub continuous_const) (real_sub_ne_zero z hz)

lemma integral_power_kernel_zero (j R : ℝ) (z : ℂ) (hz : 0 < z.im) :
    (∫ t in j..R, ((t : ℂ) - (j : ℂ)) ^ (0 : ℕ) / ((t : ℂ) - z)) =
      Complex.log ((R : ℂ) - z) - Complex.log ((j : ℂ) - z) := by
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => Complex.log ((u : ℂ) - z))
      (1 / ((t : ℂ) - z)) t := by
    apply ((hasDerivAt_id t).ofReal_comp.sub_const z).clog_real
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub]
    exact neg_ne_zero.mpr (ne_of_gt hz)
  simpa only [pow_zero] using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) ((continuous_power_kernel 0 j z hz).intervalIntegrable j R)

lemma integral_shifted_power (r : ℕ) (j R : ℝ) :
    (∫ t in j..R, ((t : ℂ) - (j : ℂ)) ^ r) =
      ((R : ℂ) - (j : ℂ)) ^ (r + 1) / ((r + 1 : ℕ) : ℂ) := by
  have hne : ((r + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  have hd (t : ℝ) : HasDerivAt
      (fun u : ℝ => ((u : ℂ) - (j : ℂ)) ^ (r + 1) / ((r + 1 : ℕ) : ℂ))
      (((t : ℂ) - (j : ℂ)) ^ r) t := by
    convert! (((hasDerivAt_id t).ofReal_comp.sub_const (j : ℂ)).pow (r+1)).div_const
      ((r + 1 : ℕ) : ℂ) using 1
    simp only [Nat.add_sub_cancel, id_eq, Complex.ofReal_one, mul_one]
    field_simp
  have hi : IntervalIntegrable (fun t : ℝ => ((t : ℂ) - (j : ℂ)) ^ r) volume j R :=
    ((Complex.continuous_ofReal.sub continuous_const).pow r).intervalIntegrable j R
  simpa only [sub_self, zero_pow (Nat.succ_ne_zero r), zero_div, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi

lemma integral_power_kernel_succ (r : ℕ) (j R : ℝ) (z : ℂ) (hz : 0 < z.im) :
    (∫ t in j..R, ((t : ℂ) - (j : ℂ)) ^ (r+1) / ((t : ℂ) - z)) =
      ((R : ℂ) - (j : ℂ)) ^ (r+1) / ((r+1 : ℕ) : ℂ) +
        (z - (j : ℂ)) * (∫ t in j..R,
          ((t : ℂ) - (j : ℂ)) ^ r / ((t : ℂ) - z)) := by
  have he (t : ℝ) : ((t : ℂ) - (j : ℂ)) ^ (r+1) / ((t : ℂ) - z) =
      ((t : ℂ) - (j : ℂ)) ^ r +
        (z - (j : ℂ)) * (((t : ℂ) - (j : ℂ)) ^ r / ((t : ℂ) - z)) := by
    rw [pow_succ]
    field_simp [real_sub_ne_zero z hz t]
    ring
  simp_rw [he]
  have hi : IntervalIntegrable (fun t : ℝ => ((t : ℂ)-(j : ℂ))^r) volume j R :=
    ((Complex.continuous_ofReal.sub continuous_const).pow r).intervalIntegrable j R
  have hj : IntervalIntegrable (fun t : ℝ =>
      (z-(j : ℂ))*(((t : ℂ)-(j : ℂ))^r/((t : ℂ)-z))) volume j R :=
    ((continuous_power_kernel r j z hz).const_mul (z-(j : ℂ))).intervalIntegrable j R
  rw [intervalIntegral.integral_add hi hj,
    intervalIntegral.integral_const_mul, integral_shifted_power]

lemma alternating_choose_polynomial_sum (n : ℕ) (P : ℂ[X]) (hP : P.natDegree < n) :
    (∑ j ∈ Finset.range (n+1), (-1 : ℂ)^j * (n.choose j : ℂ) * P.eval (j : ℂ)) = 0 := by
  have hz := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP) (0 : ℂ)
  rw [fwdDiff_iter_eq_sum_shift] at hz
  have hstd : (∑ j ∈ Finset.range (n+1),
      (-1 : ℂ)^(n-j) * (n.choose j : ℂ) * P.eval (j : ℂ)) = 0 := by
    simpa only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, nsmul_eq_mul, mul_one, zero_add, Pi.zero_apply] using hz
  have hsign (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (-1 : ℂ)^j = (-1 : ℂ)^n * (-1 : ℂ)^(n-j) := by
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hp : (-1 : ℂ)^n = (-1 : ℂ)^(n-j) * (-1 : ℂ)^j := by
      rw [← pow_add, Nat.sub_add_cancel hjn]
    have hs : (-1 : ℂ)^(n-j) * (-1 : ℂ)^(n-j) = 1 := by
      rw [← mul_pow]
      simp
    rw [hp]
    calc
      (-1 : ℂ)^j = 1 * (-1 : ℂ)^j := by ring
      _ = ((-1 : ℂ)^(n-j) * (-1 : ℂ)^(n-j)) * (-1 : ℂ)^j := by rw [hs]
      _ = _ := by ring
  calc
    _ = (-1 : ℂ)^n * (∑ j ∈ Finset.range (n+1),
        (-1 : ℂ)^(n-j) * (n.choose j : ℂ) * P.eval (j : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsign j hj]
      ring
    _ = 0 := by rw [hstd, mul_zero]

lemma alternating_choose_mixed_power_sum (n k r : ℕ) (hkr : k+r<n) (a b : ℂ) :
    (∑ j ∈ Finset.range (n+1), (-1 : ℂ)^j * (n.choose j : ℂ) *
      (a-(j : ℂ))^k * (b-(j : ℂ))^r) = 0 := by
  let P : ℂ[X] := (C a - X)^k * (C b - X)^r
  have hlin (c : ℂ) : (C c - (X : ℂ[X])).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hdeg : P.natDegree ≤ k+r := by
    exact (natDegree_mul_le).trans (Nat.add_le_add
      (by simpa using natDegree_pow_le_of_le k (hlin a))
      (by simpa using natDegree_pow_le_of_le r (hlin b)))
  simpa only [P, eval_mul, eval_pow, eval_sub, eval_C, eval_X, mul_assoc] using
    alternating_choose_polynomial_sum n P (hdeg.trans_lt hkr)

lemma alternating_choose_power_sum (n k : ℕ) (hk : k<n) (z : ℂ) :
    (∑ j ∈ Finset.range (n+1), (-1 : ℂ)^j * (n.choose j : ℂ) *
      (z-(j : ℂ))^k) = 0 := by
  simpa only [pow_zero, mul_one] using
    alternating_choose_mixed_power_sum n k 0 (by simpa using hk) z 0

lemma weighted_cutoff_identity (n r : ℕ) (R : ℝ) (z : ℂ) (hz : 0 < z.im) :
    ∀ k : ℕ, k+r<n →
      (∑ j ∈ Finset.range (n+1),
        ((-1 : ℂ)^j * (n.choose j : ℂ)) * (z-(j : ℂ))^k *
          (∫ t in (j : ℝ)..R, ((t : ℂ)-(j : ℂ))^r / ((t : ℂ)-z))) =
      -(∑ j ∈ Finset.range (n+1),
        ((-1 : ℂ)^j * (n.choose j : ℂ)) * (z-(j : ℂ))^(k+r) *
          Complex.log ((j : ℂ)-z)) := by
  induction r with
  | zero =>
    intro k hk
    simp only [Nat.add_zero] at hk ⊢
    have hbase (j : ℕ) :
        (∫ t in (j : ℝ)..R, ((t : ℂ)-(j : ℂ))^(0 : ℕ) / ((t : ℂ)-z)) =
          Complex.log ((R : ℂ)-z) - Complex.log ((j : ℂ)-z) := by
      simpa only [Complex.ofReal_natCast] using integral_power_kernel_zero (j : ℝ) R z hz
    simp_rw [hbase]
    calc
      _ = (∑ j ∈ Finset.range (n+1), (-1 : ℂ)^j * (n.choose j : ℂ) *
            (z-(j : ℂ))^k) * Complex.log ((R : ℂ)-z) -
          ∑ j ∈ Finset.range (n+1), (-1 : ℂ)^j * (n.choose j : ℂ) *
            (z-(j : ℂ))^k * Complex.log ((j : ℂ)-z) := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [alternating_choose_power_sum n k hk z, zero_mul, zero_sub]
  | succ r ih =>
    intro k hk
    have hk' : (k+1)+r<n := by omega
    have hpoly := alternating_choose_mixed_power_sum n k (r+1) hk z (R : ℂ)
    calc
      _ = (∑ j ∈ Finset.range (n+1), (-1 : ℂ)^j * (n.choose j : ℂ) *
          (z-(j : ℂ))^k * ((R : ℂ)-(j : ℂ))^(r+1)) / ((r+1 : ℕ) : ℂ) +
        ∑ j ∈ Finset.range (n+1), (-1 : ℂ)^j * (n.choose j : ℂ) *
          (z-(j : ℂ))^(k+1) *
            (∫ t in (j : ℝ)..R, ((t : ℂ)-(j : ℂ))^r / ((t : ℂ)-z)) := by
        rw [Finset.sum_div, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have hstep := integral_power_kernel_succ r (j : ℝ) R z hz
        simp only [Complex.ofReal_natCast] at hstep
        rw [hstep]
        simp only [pow_succ]
        ring
      _ = _ := by
        rw [hpoly, zero_div, zero_add, ih (k+1) hk']
        simp only [Nat.add_left_comm, Nat.add_comm]

lemma shifted_nat_kernel_eq_indicator (r : ℕ) (j : ℝ) (z : ℂ) (t : ℝ) :
    ((truncatedPower (r : ℝ) (t-j) : ℝ) : ℂ) / ((t : ℂ)-z) =
      (Ioi j).indicator (fun u : ℝ => ((u : ℂ)-(j : ℂ))^r / ((u : ℂ)-z)) t := by
  by_cases ht : j<t
  · rw [Set.indicator_of_mem (show t ∈ Ioi j from ht), truncatedPower_of_pos (r : ℝ) (sub_pos.mpr ht)]
    simp only [Real.rpow_natCast, Complex.ofReal_pow, Complex.ofReal_sub]
  · rw [Set.indicator_of_notMem (show t ∉ Ioi j from ht),
      truncatedPower_of_nonpos (r : ℝ) (sub_nonpos.mpr (le_of_not_gt ht))]
    simp

lemma intervalIntegrable_shifted_nat_kernel (r : ℕ) (j : ℝ) (z : ℂ)
    (hz : 0<z.im) (A B : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      ((truncatedPower (r : ℝ) (t-j) : ℝ) : ℂ) / ((t : ℂ)-z)) volume A B := by
  have he : (fun t : ℝ => ((truncatedPower (r : ℝ) (t-j) : ℝ) : ℂ) / ((t : ℂ)-z)) =
      (Ioi j).indicator (fun t : ℝ => ((t : ℂ)-(j : ℂ))^r / ((t : ℂ)-z)) :=
    funext (shifted_nat_kernel_eq_indicator r j z)
  rw [he]
  have hi : IntervalIntegrable (fun t : ℝ => ((t : ℂ)-(j : ℂ))^r / ((t : ℂ)-z))
      volume A B := (continuous_power_kernel r j z hz).intervalIntegrable A B
  exact ⟨hi.1.indicator measurableSet_Ioi, hi.2.indicator measurableSet_Ioi⟩

lemma integral_shifted_nat_kernel (r : ℕ) (j R : ℝ) (hj : 0≤j) (hjR : j≤R)
    (z : ℂ) (hz : 0<z.im) :
    (∫ t in (0 : ℝ)..R,
      ((truncatedPower (r : ℝ) (t-j) : ℝ) : ℂ) / ((t : ℂ)-z)) =
      ∫ t in j..R, ((t : ℂ)-(j : ℂ))^r / ((t : ℂ)-z) := by
  have hzero : (∫ t in (0 : ℝ)..j,
      ((truncatedPower (r : ℝ) (t-j) : ℝ) : ℂ) / ((t : ℂ)-z)) = 0 := by
    calc
      _ = ∫ _t in (0 : ℝ)..j, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hj] at ht
        dsimp only
        rw [truncatedPower_of_nonpos (r : ℝ) (sub_nonpos.mpr ht.2)]
        simp
      _ = 0 := by simp
  have hright : (∫ t in j..R,
      ((truncatedPower (r : ℝ) (t-j) : ℝ) : ℂ) / ((t : ℂ)-z)) =
      ∫ t in j..R, ((t : ℂ)-(j : ℂ))^r / ((t : ℂ)-z) := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [uIoc_of_le hjR] at ht
    rw [shifted_nat_kernel_eq_indicator,
      Set.indicator_of_mem (show t ∈ Ioi j from ht.1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_shifted_nat_kernel r j z hz 0 j)
    (intervalIntegrable_shifted_nat_kernel r j z hz j R), hzero, zero_add, hright]

lemma T_nat_eq_zero_above (n r : ℕ) (hrn : r<n) (t : ℝ) (ht : (n : ℝ)<t) :
    T n (r : ℝ) t = 0 := by
  have h := alternating_choose_mixed_power_sum n 0 r (by simpa using hrn) 0 (t : ℂ)
  simp only [pow_zero, mul_one] at h
  have hreal : (∑ j ∈ Finset.range (n+1), (-1 : ℝ)^j * (n.choose j : ℝ) *
      (t-(j : ℝ))^r) = 0 := by exact_mod_cast h
  rw [T]
  convert hreal using 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : (j : ℝ)≤(n : ℝ) := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [truncatedPower_of_pos (r : ℝ) (by linarith : 0<t-(j : ℝ)), Real.rpow_natCast]

lemma C_nat_eq_cutoff (n r : ℕ) (hrn : r<n) (R : ℝ) (hR : (n : ℝ)<R) (z : ℂ) :
    C n (r : ℝ) z = ∫ t in (0 : ℝ)..R, (T n (r : ℝ) t : ℂ) / ((t : ℂ)-z) := by
  let f : ℝ → ℂ := fun t => (T n (r : ℝ) t : ℂ) / ((t : ℂ)-z)
  have hnonpos (t : ℝ) (ht : t≤0) : f t=0 := by
    simp only [f, T_eq_zero_of_nonpos n (r : ℝ) ht, Complex.ofReal_zero, zero_div]
  have hsupp : Function.support f ⊆ Ioc (0 : ℝ) R := by
    intro t ht
    have ht0 : 0<t := by
      by_contra h
      exact ht (hnonpos t (le_of_not_gt h))
    refine ⟨ht0, ?_⟩
    by_contra h
    have htR : R<t := lt_of_not_ge h
    have hzero := T_nat_eq_zero_above n r hrn t (hR.trans htR)
    exact ht (by simp only [f, hzero, Complex.ofReal_zero, zero_div])
  have hIoi : (∫ t in Ioi (0 : ℝ), f t) = ∫ t, f t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact hnonpos t (le_of_not_gt ht)
  change (∫ t in Ioi (0 : ℝ), f t) = ∫ t in (0 : ℝ)..R, f t
  rw [hIoi]
  exact (intervalIntegral.integral_eq_integral_of_support_subset hsupp).symm

/-- Exact off-real logarithmic formula for every integer exponent below n. -/
theorem C_nat_eq_log_sum (n r : ℕ) (hrn : r<n) (z : ℂ) (hz : 0<z.im) :
    C n (r : ℝ) z =
      -(∑ j ∈ Finset.range (n+1),
        (((-1 : ℝ)^j * (n.choose j : ℝ)) : ℂ) *
          (z-(j : ℂ))^r * Complex.log ((j : ℂ)-z)) := by
  let R : ℝ := (n : ℝ)+1
  have hR : (n : ℝ)<R := by dsimp only [R]; linarith
  rw [C_nat_eq_cutoff n r hrn R hR]
  simp_rw [cauchy_integrand_eq_sum]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul]
    calc
      _ = ∑ j ∈ Finset.range (n+1),
          ((-1 : ℂ)^j * (n.choose j : ℂ)) * (z-(j : ℂ))^(0 : ℕ) *
            (∫ t in (j : ℝ)..R, ((t : ℂ)-(j : ℂ))^r / ((t : ℂ)-z)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : (j : ℝ)≤(n : ℝ) := by
          exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        rw [integral_shifted_nat_kernel r (j : ℝ) R (Nat.cast_nonneg j)
          (hjn.trans hR.le) z hz]
        simp only [pow_zero, mul_one,
          Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_natCast]
      _ = _ := by
        have h := weighted_cutoff_identity n r R z hz 0 (by simpa using hrn)
        simpa only [Nat.zero_add, Complex.ofReal_mul, Complex.ofReal_pow,
          Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_natCast] using h
  · intro j hj
    exact (intervalIntegrable_shifted_nat_kernel r (j : ℝ) z hz 0 R).const_mul _

end IntegralCauchyIntegerLog


namespace IntegralTruncatedPowerZeroMoments

open IntegralTruncatedPower Set MeasureTheory

lemma truncatedPower_zero (x : ℝ) : truncatedPower 0 x = if 0 < x then 1 else 0 := by
  simp [truncatedPower]

lemma T_zero_eq_zero_above (n : ℕ) (hn : 0<n) (t : ℝ) (ht : (n:ℝ)<t) :
    T n 0 t = 0 := by
  have hactive (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      truncatedPower 0 (t-(j:ℝ))=1 := by
    have hjn : j≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [truncatedPower_zero,if_pos (by exact sub_pos.mpr ((Nat.cast_le.mpr hjn).trans_lt ht))]
  have heq : T n 0 t = ∑ j ∈ Finset.range (n+1), (-1:ℝ)^j*(n.choose j:ℝ) := by
    unfold T
    apply Finset.sum_congr rfl
    intro j hj
    rw [hactive j hj,mul_one]
  rw [heq]
  have h := Int.alternating_sum_range_choose_of_ne (Nat.ne_of_gt hn)
  exact_mod_cast h

lemma integrableOn_moment_Icc (n k : ℕ) (a b : ℝ) :
    IntegrableOn (fun t : ℝ => t^k*T n 0 t) (Icc a b) := by
  have hpoly : IntegrableOn (fun t : ℝ => t^k) (Icc a b) :=
    (continuous_id.pow k).integrableOn_Icc
  have hstep (j : ℕ) :
      IntegrableOn (fun t : ℝ => t^k*truncatedPower 0 (t-(j:ℝ))) (Icc a b) := by
    have heq : (fun t : ℝ => t^k*truncatedPower 0 (t-(j:ℝ))) =
        (Ioi (j:ℝ)).indicator (fun t : ℝ => t^k) := by
      funext t
      by_cases h : (j:ℝ)<t
      · simp [truncatedPower_zero,sub_pos.mpr h,h]
      · simp [truncatedPower_zero,show ¬0<t-(j:ℝ) by linarith,h]
    rw [heq]
    exact hpoly.indicator measurableSet_Ioi
  have hsum : IntegrableOn (fun t : ℝ => ∑ j ∈ Finset.range (n+1),
      ((-1:ℝ)^j*(n.choose j:ℝ))*(t^k*truncatedPower 0 (t-(j:ℝ)))) (Icc a b) :=
    integrable_finsetSum _ (fun j _ => (hstep j).const_mul _)
  convert hsum using 1
  funext t
  rw [T,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma support_moment_subset (n k : ℕ) (hn : 0<n) :
    Function.support (fun t : ℝ => t^k*T n 0 t) ⊆ Icc 0 (n:ℝ) := by
  intro t ht
  change t^k*T n 0 t ≠ 0 at ht
  constructor
  · by_contra hnot
    have he := T_eq_zero_of_nonpos n (0:ℝ) (le_of_not_ge hnot)
    exact ht (by rw [he,mul_zero])
  · by_contra hnot
    have he := T_zero_eq_zero_above n hn t (lt_of_not_ge hnot)
    exact ht (by rw [he,mul_zero])

lemma integrable_moment (n k : ℕ) (hn : 0<n) :
    Integrable (fun t : ℝ => t^k*T n 0 t) :=
  (integrableOn_iff_integrable_of_support_subset (support_moment_subset n k hn)).mp
    (integrableOn_moment_Icc n k 0 n)

lemma integrableOn_moment (n k : ℕ) (hn : 0<n) :
    IntegrableOn (fun t : ℝ => t^k*T n 0 t) (Ioi 0) :=
  (integrable_moment n k hn).integrableOn

end IntegralTruncatedPowerZeroMoments


namespace IntegralTruncatedPowerZeroMoments
open IntegralTruncatedPower Set MeasureTheory

lemma alternating_choose_power_sum (n m : ℕ) (hm : m<n) :
    (∑ j ∈ Finset.range (n+1), (-1:ℝ)^j*(n.choose j:ℝ)*(j:ℝ)^m)=0 := by
  have hz := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R:=ℝ) hm) (0:ℝ)
  rw [fwdDiff_iter_eq_sum_shift] at hz
  have hstd : (∑ j ∈ Finset.range (n+1),
      (-1:ℝ)^(n-j)*(n.choose j:ℝ)*(j:ℝ)^m)=0 := by
    simpa only [zsmul_eq_mul,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,
      Int.cast_natCast,nsmul_eq_mul,mul_one,zero_add,Pi.zero_apply] using hz
  have hsign (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (-1:ℝ)^j=(-1:ℝ)^n*(-1:ℝ)^(n-j) := by
    have hjn : j≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hp : (-1:ℝ)^n=(-1:ℝ)^(n-j)*(-1:ℝ)^j := by
      rw [←pow_add,Nat.sub_add_cancel hjn]
    have hs : (-1:ℝ)^(n-j)*(-1:ℝ)^(n-j)=1 := by
      rw [←mul_pow]
      norm_num
    rw [hp]
    calc
      (-1:ℝ)^j=1*(-1:ℝ)^j := by ring
      _=((-1:ℝ)^(n-j)*(-1:ℝ)^(n-j))*(-1:ℝ)^j := by rw [hs]
      _=_ := by ring
  calc
    _=(-1:ℝ)^n*(∑ j ∈ Finset.range (n+1),
        (-1:ℝ)^(n-j)*(n.choose j:ℝ)*(j:ℝ)^m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsign j hj]
      ring
    _=0 := by rw [hstd,mul_zero]

lemma intervalIntegral_nat_pow (k : ℕ) (a b : ℝ) :
    (∫ t in a..b, t^k)=(b^(k+1)-a^(k+1))/(k+1:ℝ) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t^(k+1)) ((k+1:ℝ)*t^k) t := by
    simpa only [Pi.pow_apply,id_eq,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,mul_one] using
      hasDerivAt_pow (k+1) t
  have hi : IntervalIntegrable (fun t : ℝ => (k+1:ℝ)*t^k) volume a b :=
    (continuous_const.mul (continuous_id.pow k)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at h
  apply (eq_div_iff (by positivity : (k+1:ℝ)≠0)).mpr
  nlinarith

lemma step_moment_eq_sub_indicator (k : ℕ) (j : ℝ) :
    (fun t : ℝ => t^k*truncatedPower 0 (t-j)) =
      (fun t : ℝ => t^k-(Iic j).indicator (fun t : ℝ => t^k) t) := by
  funext t
  by_cases h : t≤j
  · simp [truncatedPower_zero,show ¬0<t-j by linarith,h]
  · simp [truncatedPower_zero,show 0<t-j by linarith,h]

lemma intervalIntegral_step_moment (k : ℕ) (j R : ℝ) (hj : 0≤j) (hjR : j≤R) :
    (∫ t in (0:ℝ)..R, t^k*truncatedPower 0 (t-j)) =
      (R^(k+1)-j^(k+1))/(k+1:ℝ) := by
  have hp : IntervalIntegrable (fun t : ℝ => t^k) volume 0 R :=
    (continuous_id.pow k).intervalIntegrable 0 R
  have hi : IntervalIntegrable ((Iic j).indicator (fun t : ℝ => t^k)) volume 0 R :=
    intervalIntegrable_iff.mpr (hp.def'.indicator measurableSet_Iic)
  rw [step_moment_eq_sub_indicator,intervalIntegral.integral_sub hp hi]
  have he : (∫ t in (0:ℝ)..R, (Iic j).indicator (fun t : ℝ => t^k) t)=
      ∫ t in (0:ℝ)..j, t^k := by
    exact intervalIntegral.integral_indicator ⟨hj,hjR⟩
  rw [he,intervalIntegral_nat_pow,intervalIntegral_nat_pow]
  ring

lemma intervalIntegral_moment_zero (n k : ℕ) (hkn : k+1<n) :
    (∫ t in (0:ℝ)..((n:ℝ)+1), t^k*T n 0 t)=0 := by
  let R : ℝ := (n:ℝ)+1
  have heq : (fun t : ℝ => t^k*T n 0 t)=
      (fun t : ℝ => ∑ j ∈ Finset.range (n+1),
        ((-1:ℝ)^j*(n.choose j:ℝ))*(t^k*truncatedPower 0 (t-(j:ℝ)))) := by
    funext t
    rw [T,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hi (j : ℕ) : IntervalIntegrable
      (fun t : ℝ => ((-1:ℝ)^j*(n.choose j:ℝ))*(t^k*truncatedPower 0 (t-(j:ℝ))))
      volume 0 R := by
    have hp : IntervalIntegrable (fun t : ℝ => t^k) volume 0 R :=
      (continuous_id.pow k).intervalIntegrable 0 R
    have hi : IntervalIntegrable ((Iic (j:ℝ)).indicator (fun t : ℝ => t^k)) volume 0 R :=
      intervalIntegrable_iff.mpr (hp.def'.indicator measurableSet_Iic)
    have hstep : IntervalIntegrable
        (fun t : ℝ => t^k*truncatedPower 0 (t-(j:ℝ))) volume 0 R := by
      rw [step_moment_eq_sub_indicator]
      exact hp.sub hi
    exact hstep.const_mul _
  rw [heq,intervalIntegral.integral_finsetSum (fun j _ => hi j)]
  simp_rw [intervalIntegral.integral_const_mul]
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∫ t in (0:ℝ)..R, t^k*truncatedPower 0 (t-(j:ℝ)))=
        (R^(k+1)-(j:ℝ)^(k+1))/(k+1:ℝ) := by
    apply intervalIntegral_step_moment
    · exact Nat.cast_nonneg j
    · have hjn : j≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      dsimp [R]
      exact (Nat.cast_le.mpr hjn).trans (by linarith)
  have hsum : (∑ j ∈ Finset.range (n+1),
      ((-1:ℝ)^j*(n.choose j:ℝ))*(∫ t in (0:ℝ)..R,
        t^k*truncatedPower 0 (t-(j:ℝ)))) =
      (R^(k+1)*(∑ j ∈ Finset.range (n+1),(-1:ℝ)^j*(n.choose j:ℝ))-
        ∑ j ∈ Finset.range (n+1),(-1:ℝ)^j*(n.choose j:ℝ)*(j:ℝ)^(k+1))/(k+1:ℝ) := by
    have heqsum : (∑ j ∈ Finset.range (n+1),
        ((-1:ℝ)^j*(n.choose j:ℝ))*(∫ t in (0:ℝ)..R,
          t^k*truncatedPower 0 (t-(j:ℝ)))) =
        ∑ j ∈ Finset.range (n+1),
          (((-1:ℝ)^j*(n.choose j:ℝ))*(R^(k+1)-(j:ℝ)^(k+1)))/(k+1:ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hterm j hj]
      ring
    rw [heqsum]
    rw [←Finset.sum_div]
    congr 1
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul]
    ring
  change (∑ j ∈ Finset.range (n+1),
      ((-1:ℝ)^j*(n.choose j:ℝ))*(∫ t in (0:ℝ)..R,
        t^k*truncatedPower 0 (t-(j:ℝ))))=0
  rw [hsum,alternating_choose_power_sum n (k+1) hkn]
  have hzero : (∑ j ∈ Finset.range (n+1),(-1:ℝ)^j*(n.choose j:ℝ))=0 := by
    simpa only [pow_zero,mul_one] using alternating_choose_power_sum n 0 (by omega)
  rw [hzero,mul_zero,sub_self,zero_div]

end IntegralTruncatedPowerZeroMoments


namespace IntegralTruncatedPowerZeroMoments
open IntegralTruncatedPower Set MeasureTheory

lemma integral_moment_zero_global (n k : ℕ) (hkn : k+1<n) :
    (∫ t : ℝ, t^k*T n 0 t)=0 := by
  have hs : Function.support (fun t : ℝ => t^k*T n 0 t) ⊆ Ioc 0 ((n:ℝ)+1) := by
    intro t ht
    have hbound := support_moment_subset n k (by omega) ht
    refine ⟨?_,by linarith [hbound.2]⟩
    by_contra hnot
    change t^k*T n 0 t ≠ 0 at ht
    exact ht (by rw [T_eq_zero_of_nonpos n (0:ℝ) (le_of_not_gt hnot),mul_zero])
  have he := intervalIntegral.integral_eq_integral_of_support_subset (μ:=volume) hs
  rw [←he]
  exact intervalIntegral_moment_zero n k hkn

lemma integral_moment_zero (n k : ℕ) (hkn : k+1<n) :
    (∫ t in Ioi (0:ℝ), t^k*T n 0 t)=0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_moment_zero_global n k hkn
  · intro t ht
    rw [T_eq_zero_of_nonpos n (0:ℝ) (le_of_not_gt ht),mul_zero]

/-- The actual step-exponent boundary supplies every admissible polynomial
moment, including integrability, without an auxiliary moment hypothesis. -/
lemma monomial_moments (n d : ℕ) (hd : d<n) :
    ∀ k<d, Integrable (fun t : ℝ => T n 0 t*t^k) (volume.restrict (Ioi (0:ℝ))) ∧
      (∫ t in Ioi (0:ℝ), T n 0 t*t^k)=0 := by
  intro k hkd
  have hn : 0<n := by omega
  have hkn : k+1<n := by omega
  constructor
  · simpa only [IntegrableOn,mul_comm] using integrableOn_moment n k hn
  · simpa only [mul_comm] using integral_moment_zero n k hkn

end IntegralTruncatedPowerZeroMoments


namespace IntegralTruncatedPowerZeroSign

open Polynomial
open scoped BigOperators

noncomputable def signPolynomial (n : ℕ) : ℝ[X] :=
  Polynomial.C ((-1 : ℝ) ^ (n - 1)) *
    ∏ j ∈ Finset.range (n - 1),
      (Polynomial.X - Polynomial.C ((j + 1 : ℕ) : ℝ))

lemma signPolynomial_ne_zero (n : ℕ) : signPolynomial n ≠ 0 := by
  classical
  unfold signPolynomial
  apply mul_ne_zero
  · exact Polynomial.C_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  · exact Finset.prod_ne_zero_iff.mpr (fun j _ => Polynomial.X_sub_C_ne_zero _)

lemma signPolynomial_natDegree_le (n : ℕ) :
    (signPolynomial n).natDegree ≤ n - 1 := by
  calc
    (signPolynomial n).natDegree ≤
        (∏ j ∈ Finset.range (n - 1),
          (Polynomial.X - Polynomial.C ((j + 1 : ℕ) : ℝ) : ℝ[X])).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ ∑ j ∈ Finset.range (n - 1),
        (Polynomial.X - Polynomial.C ((j + 1 : ℕ) : ℝ) : ℝ[X]).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ = n - 1 := by
      simp only [Polynomial.natDegree_X_sub_C]
      simp

lemma signPolynomial_degree_le (n : ℕ) :
    (signPolynomial n).degree ≤ ((n - 1 : ℕ) : WithBot ℕ) :=
  Polynomial.degree_le_natDegree.trans
    (WithBot.coe_le_coe.mpr (signPolynomial_natDegree_le n))

lemma signPolynomial_eval (n : ℕ) (t : ℝ) :
    (signPolynomial n).eval t = (-1 : ℝ) ^ (n - 1) *
      ∏ j ∈ Finset.range (n - 1), (t - ((j + 1 : ℕ) : ℝ)) := by
  simp only [signPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]

lemma signPolynomial_eval_nat_zero (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    (signPolynomial n).eval (k : ℝ) = 0 := by
  classical
  rw [signPolynomial_eval]
  have hmem : k - 1 ∈ Finset.range (n - 1) := Finset.mem_range.mpr (by omega)
  have hz : (k : ℝ) - (((k - 1) + 1 : ℕ) : ℝ) = 0 := by
    rw [Nat.sub_add_cancel hk]
    exact sub_self _
  rw [Finset.prod_eq_zero hmem hz, mul_zero]

/-- On the kth unit cell the prefactored root product has sign (-1)^k. -/
lemma signed_root_product_cell_pos (m k : ℕ) (hk : k ≤ m) (t : ℝ)
    (ht : (k : ℝ) < t) (ht' : t < (k : ℝ) + 1) :
    0 < (-1 : ℝ) ^ k * ((-1 : ℝ) ^ m *
      ∏ j ∈ Finset.range m, (t - ((j + 1 : ℕ) : ℝ))) := by
  induction m generalizing k t with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      norm_num
  | succ m ih =>
      by_cases hkm : k ≤ m
      · have hp := ih k hkm t ht ht'
        have hcast : (k : ℝ) + 1 ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hkm 1
        have hfac : 0 < ((m + 1 : ℕ) : ℝ) - t := by linarith
        have he :
            (-1 : ℝ) ^ k * ((-1 : ℝ) ^ (m + 1) *
              ∏ j ∈ Finset.range (m + 1), (t - ((j + 1 : ℕ) : ℝ))) =
            ((-1 : ℝ) ^ k * ((-1 : ℝ) ^ m *
              ∏ j ∈ Finset.range m, (t - ((j + 1 : ℕ) : ℝ)))) *
                (((m + 1 : ℕ) : ℝ) - t) := by
          rw [Finset.prod_range_succ, pow_succ (-1 : ℝ) m]
          ring
        rw [he]
        exact mul_pos hp hfac
      · have he : k = m + 1 := by omega
        subst k
        have hsquare : (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (m + 1) = 1 := by
          rw [← mul_pow]
          norm_num
        have hp : 0 < ∏ j ∈ Finset.range (m + 1),
            (t - ((j + 1 : ℕ) : ℝ)) := by
          apply Finset.prod_pos
          intro j hj
          have hjm : j + 1 ≤ m + 1 := Finset.mem_range.mp hj
          have hc : ((j + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hjm
          exact sub_pos.mpr (hc.trans_lt ht)
        rw [← mul_assoc, hsquare, one_mul]
        exact hp

lemma signed_signPolynomial_cell_pos (n k : ℕ) (hk : k < n) (t : ℝ)
    (ht : (k : ℝ) < t) (ht' : t < (k : ℝ) + 1) :
    0 < (-1 : ℝ) ^ k * (signPolynomial n).eval t := by
  rw [signPolynomial_eval]
  exact signed_root_product_cell_pos (n - 1) k (by omega) t ht ht'

/-- The explicit polynomial is a genuine nonnegative sign witness, including
all internal integer nodes, where one of its linear factors vanishes. -/
theorem T_mul_signPolynomial_nonneg (n : ℕ) (_hn : 1 ≤ n) (t : ℝ)
    (ht : 0 < t) (htn : t < (n : ℝ)) :
    0 ≤ IntegralTruncatedPower.T n 0 t * (signPolynomial n).eval t := by
  let k : ℕ := Nat.floor t
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht.le
  have hkn : k < n := by exact_mod_cast hkt.trans_lt htn
  obtain he | hlt := hkt.eq_or_lt
  · have hkpos : 1 ≤ k := by
      have hc : (0 : ℝ) < (k : ℝ) := by linarith
      have h : 0 < k := by exact_mod_cast hc
      omega
    rw [← he, signPolynomial_eval_nat_zero n k hkpos hkn, mul_zero]
  · have hupper : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
    have hT := IntegralTruncatedPowerSign.signed_T_nonpos_cell_pos n k hkn 0 t
      le_rfl hlt hupper
    have hP := signed_signPolynomial_cell_pos n k hkn t hlt hupper
    have hp := mul_pos hT hP
    have hsquare : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    have heq : ((-1 : ℝ) ^ k * IntegralTruncatedPower.T n 0 t) *
        ((-1 : ℝ) ^ k * (signPolynomial n).eval t) =
        IntegralTruncatedPower.T n 0 t * (signPolynomial n).eval t := by
      calc
        _ = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
            (IntegralTruncatedPower.T n 0 t * (signPolynomial n).eval t) := by ring
        _ = _ := by rw [hsquare, one_mul]
    rw [heq] at hp
    exact hp.le

theorem T_mul_signPolynomial_pos_of_lt_one (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    0 < IntegralTruncatedPower.T n 0 t * (signPolynomial n).eval t := by
  have hkn : 0 < n := by omega
  have hT := IntegralTruncatedPowerSign.signed_T_nonpos_cell_pos n 0 hkn 0 t
    le_rfl (by simpa using ht) (by simpa using ht1)
  have hP := signed_signPolynomial_cell_pos n 0 hkn t
    (by simpa using ht) (by simpa using ht1)
  simpa only [pow_zero, one_mul] using mul_pos hT hP

end IntegralTruncatedPowerZeroSign


namespace IntegralTruncatedPowerZeroCauchy

open IntegralTruncatedPower

lemma integrable_quotient_exterior (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x < 0 ∨ (n : ℝ) < x) :
    IntegrableOn (fun t : ℝ => T n 0 t / (t - x)) (Ioi 0) := by
  have hT : Integrable (T n 0) := by
    simpa only [pow_zero, one_mul] using IntegralTruncatedPowerZeroMoments.integrable_moment n 0 hn
  have hsupp : Function.support (T n 0) ⊆ Icc 0 (n : ℝ) := by
    simpa only [pow_zero, one_mul] using IntegralTruncatedPowerZeroMoments.support_moment_subset n 0 hn
  obtain ⟨c, hc, hdist⟩ : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc (0 : ℝ) (n : ℝ), c ≤ |t - x| := by
    rcases hx with hx | hx
    · refine ⟨-x, by linarith, ?_⟩
      intro t ht
      rw [abs_of_pos (by linarith [ht.1] : 0 < t - x)]
      linarith [ht.1]
    · refine ⟨x - (n : ℝ), sub_pos.mpr hx, ?_⟩
      intro t ht
      rw [abs_of_neg (by linarith [ht.2] : t - x < 0)]
      linarith [ht.2]
  have hmeas : AEStronglyMeasurable (fun t : ℝ => T n 0 t / (t - x)) volume :=
    hT.aestronglyMeasurable.div₀ (continuous_id.sub continuous_const).aestronglyMeasurable
  have hglobal : Integrable (fun t : ℝ => T n 0 t / (t - x)) := by
    apply (hT.norm.const_mul (1 / c)).mono' hmeas
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) (n : ℝ)
    · rw [Real.norm_eq_abs, abs_div]
      calc
        |T n 0 t| / |t - x| ≤ |T n 0 t| / c :=
          div_le_div_of_nonneg_left (abs_nonneg _) hc (hdist t ht)
        _ = (1 / c) * ‖T n 0 t‖ := by rw [Real.norm_eq_abs]; ring
    · have hz : T n 0 t = 0 := by
        by_contra hnot
        exact ht (hsupp hnot)
      simp [hz]
  exact hglobal.integrableOn

lemma C_zero_ofReal_eq (n : ℕ) (x : ℝ) :
    IntegralTruncatedPowerCauchy.C n 0 (x : ℂ) =
      ((∫ t : ℝ in Ioi 0, T n 0 t / (t - x) : ℝ) : ℂ) := by
  unfold IntegralTruncatedPowerCauchy.C
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  push_cast
  rfl


lemma real_quotient_ne_zero_of_sign_polynomial (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x < 0 ∨ (n : ℝ) < x) (P : ℝ[X]) (hPne : P ≠ 0)
    (hPdeg : P.degree ≤ ((n - 1 : ℕ) : WithBot ℕ))
    (hPnonneg : ∀ t : ℝ, 0 < t → t < (n : ℝ) → 0 ≤ T n 0 t * P.eval t)
    (hPpos : ∀ t : ℝ, 0 < t → t < 1 → 0 < T n 0 t * P.eval t) :
    (∫ t : ℝ in Ioi 0, T n 0 t / (t - x)) ≠ 0 := by
  let Q : ℝ[X] := if x < 0 then P else -P
  have hQne : Q ≠ 0 := by
    dsimp [Q]
    split_ifs
    · exact hPne
    · exact neg_ne_zero.mpr hPne
  have hQdeg : Q.degree ≤ ((n - 1 : ℕ) : WithBot ℕ) := by
    dsimp [Q]
    split_ifs
    · exact hPdeg
    · simpa only [Polynomial.degree_neg] using hPdeg
  have hquot (t : ℝ) : T n 0 t / (t - x) * Q.eval t =
      if x < 0 then (T n 0 t * P.eval t) / (t - x) else
        (T n 0 t * P.eval t) / (x - t) := by
    dsimp [Q]
    split_ifs
    · ring
    · rw [Polynomial.eval_neg, show x - t = -(t - x) by ring, div_neg]
      ring
  have hnonneg_inside (t : ℝ) (ht : 0 < t) (htn : t < (n : ℝ)) :
      0 ≤ T n 0 t / (t - x) * Q.eval t := by
    rw [hquot]
    by_cases hx0 : x < 0
    · rw [if_pos hx0]
      exact div_nonneg (hPnonneg t ht htn) (by linarith)
    · rw [if_neg hx0]
      have hnx := hx.resolve_left hx0
      exact div_nonneg (hPnonneg t ht htn) (by linarith)
  have hpositive_first (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
      0 < T n 0 t / (t - x) * Q.eval t := by
    rw [hquot]
    by_cases hx0 : x < 0
    · rw [if_pos hx0]
      exact div_pos (hPpos t ht ht1) (by linarith)
    · rw [if_neg hx0]
      have hnx := hx.resolve_left hx0
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact div_pos (hPpos t ht ht1) (by linarith)
  have hg := integrable_quotient_exterior n hn x hx
  have hmom := IntegralTruncatedPowerZeroMoments.monomial_moments n (n - 1) (by omega)
  have hdivdeg : (Q /ₘ (X - Polynomial.C x)).degree < Q.degree :=
    Polynomial.degree_divByMonic_lt _ _ hQne (by simp)
  have hr := (IntegralOrthogonalCauchy.polynomial_moments_of_monomial_moments
    hmom (Q /ₘ (X - Polynomial.C x)) (hdivdeg.trans_le hQdeg)).1
  have hw := IntegralOrthogonalCauchy.integrable_polynomial_weighted_quotient x Q hg hr
  have hnonneg : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      0 ≤ T n 0 t / (t - x) * Q.eval t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (volume.restrict (Ioi (0 : ℝ))).ae_ne (n : ℝ)] with t ht htn
    by_cases hlt : t < (n : ℝ)
    · exact hnonneg_inside t ht hlt
    · have hgt : (n : ℝ) < t := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm htn)
      rw [IntegralTruncatedPowerZeroMoments.T_zero_eq_zero_above n hn t hgt,
        zero_div, zero_mul]
  have hs : Ioo (0 : ℝ) 1 ⊆ Function.support (fun t => T n 0 t / (t - x) * Q.eval t) := by
    intro t ht
    exact (hpositive_first t ht.1 ht.2).ne'
  have hm : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioo 0 1) := by
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Ioi_self]
    norm_num
  exact IntegralOrthogonalCauchy.cauchy_ne_zero_of_moments_and_sign_witness
    x Q hQne hQdeg hg hmom hw hnonneg (hm.trans_le (measure_mono hs))


lemma tendsto_C_zero_exterior (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x < 0 ∨ (n : ℝ) < x) :
    Tendsto (fun ε : ℝ => IntegralTruncatedPowerCauchy.C n 0
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝 0)
      (𝓝 (IntegralTruncatedPowerCauchy.C n 0 (x : ℂ))) := by
  have hT : IntegrableOn (T n 0) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using IntegralTruncatedPowerZeroMoments.integrableOn_moment n 0 hn
  have hf : AEStronglyMeasurable (fun t : ℝ => (T n 0 t : ℂ)) (volume.restrict (Ioi 0)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hT.aestronglyMeasurable
  have h := IntegralCauchyBoundary.tendsto_cauchy_boundary_of_integrable_quotient
    x hf (integrable_quotient_exterior n hn x hx)
  rw [C_zero_ofReal_eq]
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro ε
  unfold IntegralTruncatedPowerCauchy.C
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  have he : (((t - x : ℝ) : ℂ) - Complex.I * (ε : ℂ)) =
      ((t : ℂ) - ((x : ℂ) + Complex.I * (ε : ℂ))) := by
    push_cast
    ring
  rw [he]


/-- The actual p=0 exterior quotient cannot vanish. -/
theorem real_quotient_ne_zero_exterior (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x < 0 ∨ (n : ℝ) < x) :
    (∫ t : ℝ in Ioi 0, T n 0 t / (t - x)) ≠ 0 := by
  exact real_quotient_ne_zero_of_sign_polynomial n hn x hx
    (IntegralTruncatedPowerZeroSign.signPolynomial n)
    (IntegralTruncatedPowerZeroSign.signPolynomial_ne_zero n)
    (IntegralTruncatedPowerZeroSign.signPolynomial_degree_le n)
    (fun t ht htn => IntegralTruncatedPowerZeroSign.T_mul_signPolynomial_nonneg
      n (Nat.succ_le_iff.mpr hn) t ht htn)
    (fun t ht ht1 => IntegralTruncatedPowerZeroSign.T_mul_signPolynomial_pos_of_lt_one
      n (Nat.succ_le_iff.mpr hn) t ht ht1)

/-- The real-axis Bochner Cauchy transform is used only exterior to the support. -/
theorem C_zero_ne_zero_exterior (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x < 0 ∨ (n : ℝ) < x) :
    IntegralTruncatedPowerCauchy.C n 0 (x : ℂ) ≠ 0 := by
  rw [C_zero_ofReal_eq]
  exact Complex.ofReal_ne_zero.mpr (real_quotient_ne_zero_exterior n hn x hx)

theorem not_tendsto_C_zero_exterior (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x < 0 ∨ (n : ℝ) < x) :
    ¬ Tendsto (fun ε : ℝ => IntegralTruncatedPowerCauchy.C n 0
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
  intro hz
  have hlim := (tendsto_C_zero_exterior n hn x hx).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  exact C_zero_ne_zero_exterior n hn x hx (tendsto_nhds_unique hlim hz)

end IntegralTruncatedPowerZeroCauchy


namespace IntegralComplexPowerLog

lemma norm_mul_log_le (z : ℂ) :
    ‖z * Complex.log z‖ ≤ |‖z‖ * Real.log ‖z‖| + Real.pi * ‖z‖ := by
  rw [Complex.log, mul_add]
  calc
    ‖z * (Real.log ‖z‖ : ℂ) + z * ((Complex.arg z : ℂ) * Complex.I)‖ ≤
        ‖z * (Real.log ‖z‖ : ℂ)‖ + ‖z * ((Complex.arg z : ℂ) * Complex.I)‖ :=
      norm_add_le _ _
    _ = ‖z‖ * |Real.log ‖z‖| + ‖z‖ * |Complex.arg z| := by
      simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    _ ≤ ‖z‖ * |Real.log ‖z‖| + ‖z‖ * Real.pi :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi z) (norm_nonneg z))
    _ = |‖z‖ * Real.log ‖z‖| + Real.pi * ‖z‖ := by
      rw [abs_mul, abs_of_nonneg (norm_nonneg z)]
      ring

lemma tendsto_mul_log_zero :
    Tendsto (fun z : ℂ => z * Complex.log z) (𝓝 0) (𝓝 0) := by
  apply squeeze_zero_norm (fun z => norm_mul_log_le z)
  have h₁ := ((Real.continuous_mul_log.comp continuous_norm).abs).tendsto (0 : ℂ)
  have h₂ := (continuous_norm.const_mul Real.pi).tendsto (0 : ℂ)
  simpa only [Function.comp_def, norm_zero, zero_mul, abs_zero, mul_zero, add_zero] using! h₁.add h₂

lemma continuousAt_mul_log_zero :
    ContinuousAt (fun z : ℂ => z * Complex.log z) 0 := by
  simpa only [ContinuousAt, zero_mul] using tendsto_mul_log_zero

lemma tendsto_pow_log_zero (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun z : ℂ => z ^ r * Complex.log z) (𝓝 0) (𝓝 0) := by
  cases r with
  | zero => simp at hr
  | succ k =>
      simpa only [Nat.succ_eq_add_one, pow_succ, mul_assoc, mul_zero] using!
        ((continuous_pow k).tendsto (0 : ℂ)).mul tendsto_mul_log_zero

lemma continuousAt_pow_log_zero (r : ℕ) (hr : 1 ≤ r) :
    ContinuousAt (fun z : ℂ => z ^ r * Complex.log z) 0 := by
  simpa only [ContinuousAt, Complex.log_zero, mul_zero] using
    tendsto_pow_log_zero r hr

lemma tendsto_pow_log_of_tendsto_zero {α : Type*} {l : Filter α} {f : α → ℂ}
    (hf : Tendsto f l (𝓝 0)) (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun t => f t ^ r * Complex.log (f t)) l (𝓝 0) := by
  simpa only [Function.comp_def] using (tendsto_pow_log_zero r hr).comp hf

lemma tendsto_neg_imag_pow_log_zero (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun ε : ℝ => (-Complex.I * (ε : ℂ)) ^ r *
      Complex.log (-Complex.I * (ε : ℂ))) (𝓝 0) (𝓝 0) := by
  apply tendsto_pow_log_of_tendsto_zero (r := r) (hr := hr)
  simpa only [Complex.ofReal_zero, mul_zero] using
    (Complex.continuous_ofReal.const_mul (-Complex.I)).tendsto (0 : ℝ)

lemma tendsto_imag_pow_log_neg_imag_zero (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun ε : ℝ => (Complex.I * (ε : ℂ)) ^ r *
      Complex.log (-Complex.I * (ε : ℂ))) (𝓝 0) (𝓝 0) := by
  have h := (tendsto_neg_imag_pow_log_zero r hr).const_mul ((-1 : ℂ) ^ r)
  have h' : Tendsto (fun ε : ℝ => (-1 : ℂ) ^ r *
      ((-Complex.I * (ε : ℂ)) ^ r * Complex.log (-Complex.I * (ε : ℂ))))
      (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using h
  apply h'.congr'
  apply Filter.Eventually.of_forall
  intro ε
  change (-1 : ℂ) ^ r * ((-Complex.I * (ε : ℂ)) ^ r *
    Complex.log (-Complex.I * (ε : ℂ))) =
    (Complex.I * (ε : ℂ)) ^ r * Complex.log (-Complex.I * (ε : ℂ))
  have he : Complex.I * (ε : ℂ) = (-1 : ℂ) * (-Complex.I * (ε : ℂ)) := by ring
  have hpow : (Complex.I * (ε : ℂ)) ^ r =
      (-1 : ℂ) ^ r * (-Complex.I * (ε : ℂ)) ^ r := by rw [he, mul_pow]
  rw [hpow, mul_assoc]

lemma tendsto_imag_pow_log_neg_imag_zero_right (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun ε : ℝ => (Complex.I * (ε : ℂ)) ^ r *
      Complex.log (-Complex.I * (ε : ℂ))) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_imag_pow_log_neg_imag_zero r hr).mono_left nhdsWithin_le_nhds

lemma tendsto_real_pow_log_zero (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun ε : ℝ => (ε : ℂ) ^ r * Complex.log (ε : ℂ)) (𝓝 0) (𝓝 0) := by
  apply tendsto_pow_log_of_tendsto_zero (r := r) (hr := hr)
  simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.tendsto (0 : ℝ)

end IntegralComplexPowerLog


namespace IntegralIntegerLogBoundary

noncomputable def weightedTerm (r : ℕ) (a ε : ℝ) : ℂ :=
  ((a : ℂ) + Complex.I * (ε : ℂ)) ^ r *
    Complex.log ((-a : ℝ) - Complex.I * (ε : ℂ))

noncomputable def scalarBoundary (r : ℕ) (a : ℝ) : ℂ :=
  (a : ℂ) ^ r * (((Real.log |a| : ℝ) : ℂ) -
    if 0 < a then Complex.I * (Real.pi : ℂ) else 0)

noncomputable def logSum (n r : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
      (z - (j : ℂ)) ^ r * Complex.log ((j : ℂ) - z)

noncomputable def realLogSum (n r : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ j * (n.choose j : ℝ) * (x - (j : ℝ)) ^ r * Real.log |x - (j : ℝ)|

noncomputable def leftTail (n r : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    if (j : ℝ) < x then (-1 : ℝ) ^ j * (n.choose j : ℝ) * (x - (j : ℝ)) ^ r else 0

lemma tendsto_lower_path (a : ℝ) :
    Tendsto (fun ε : ℝ => (a : ℂ) - Complex.I * (ε : ℂ)) (𝓝 0) (𝓝 (a : ℂ)) := by
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).ofReal
  simpa only [mul_zero, sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (a : ℂ)) (𝓝 0) (𝓝 (a : ℂ))).sub
      (hε.const_mul Complex.I)

lemma tendsto_lower_log_pos (a : ℝ) (ha : 0 < a) :
    Tendsto (fun ε : ℝ => Complex.log ((a : ℂ) - Complex.I * (ε : ℂ)))
      (𝓝 0) (𝓝 ((Real.log a : ℝ) : ℂ)) := by
  have h := (tendsto_lower_path a).clog (Or.inl ha)
  simpa only [← Complex.ofReal_log ha.le] using h

lemma tendsto_lower_log_neg (a : ℝ) (ha : a < 0) :
    Tendsto (fun ε : ℝ => Complex.log ((a : ℂ) - Complex.I * (ε : ℂ)))
      (𝓝[>] 0) (𝓝 (((Real.log (-a) : ℝ) : ℂ) - (Real.pi : ℂ) * Complex.I)) := by
  have hw : Tendsto (fun ε : ℝ => (a : ℂ) - Complex.I * (ε : ℂ))
      (𝓝[>] 0) (𝓝[{w : ℂ | w.im < 0}] (a : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(tendsto_lower_path a).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    simpa using neg_lt_zero.mpr hε
  have h := (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (z := (a : ℂ)) (by simpa using ha) (by simp)).comp hw
  simpa only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha] using h

lemma tendsto_log_weight_factor (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun ε : ℝ => Complex.log ((-a : ℝ) - Complex.I * (ε : ℂ)))
      (𝓝[>] 0) (𝓝 (((Real.log |a| : ℝ) : ℂ) -
        if 0 < a then Complex.I * (Real.pi : ℂ) else 0)) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · simpa only [abs_of_neg ha, if_neg (not_lt.mpr ha.le), sub_zero] using
      (tendsto_lower_log_pos (-a) (neg_pos.mpr ha)).mono_left nhdsWithin_le_nhds
  · simpa only [neg_neg, abs_of_pos ha, if_pos ha, mul_comm] using
      tendsto_lower_log_neg (-a) (neg_lt_zero.mpr ha)

lemma tendsto_weightedTerm_of_ne_zero (r : ℕ) (a : ℝ) (ha : a ≠ 0) :
    Tendsto (weightedTerm r a) (𝓝[>] 0) (𝓝 (scalarBoundary r a)) := by
  have hupper : Tendsto (fun ε : ℝ => (a : ℂ) + Complex.I * (ε : ℂ))
      (𝓝 0) (𝓝 (a : ℂ)) := by
    have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).ofReal
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (a : ℂ)) (𝓝 0) (𝓝 (a : ℂ))).add
        (hε.const_mul Complex.I)
  exact ((hupper.pow r).mono_left nhdsWithin_le_nhds).mul (tendsto_log_weight_factor a ha)

lemma sum_scalarBoundary_eq (n r : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range (n + 1), (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
      scalarBoundary r (x - (j : ℝ))) =
      (realLogSum n r x : ℂ) - Complex.I * (Real.pi : ℂ) * (leftTail n r x : ℂ) := by
  have hL : (∑ j ∈ Finset.range (n + 1),
      (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        ((x - (j : ℝ) : ℝ) : ℂ) ^ r * (Real.log |x - (j : ℝ)| : ℂ)) =
      (realLogSum n r x : ℂ) := by
    unfold realLogSum
    push_cast
    rfl
  have hN : (∑ j ∈ Finset.range (n + 1),
      (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        ((x - (j : ℝ) : ℝ) : ℂ) ^ r *
          (if 0 < x - (j : ℝ) then Complex.I * (Real.pi : ℂ) else 0)) =
      Complex.I * (Real.pi : ℂ) * (leftTail n r x : ℂ) := by
    unfold leftTail
    rw [Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : (j : ℝ) < x
    · rw [if_pos h, if_pos (sub_pos.mpr h)]
      push_cast
      ring
    · rw [if_neg h, if_neg (by simpa only [sub_pos] using h)]
      simp
  calc
    _ = (∑ j ∈ Finset.range (n + 1),
        (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
          ((x - (j : ℝ) : ℝ) : ℂ) ^ r * (Real.log |x - (j : ℝ)| : ℂ)) -
      (∑ j ∈ Finset.range (n + 1),
        (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
          ((x - (j : ℝ) : ℝ) : ℂ) ^ r *
            (if 0 < x - (j : ℝ) then Complex.I * (Real.pi : ℂ) else 0)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      unfold scalarBoundary
      ring
    _ = _ := by rw [hL, hN]

lemma logSum_term_eq (n r j : ℕ) (x ε : ℝ) :
    (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
      (((x : ℂ) + Complex.I * (ε : ℂ)) - (j : ℂ)) ^ r *
        Complex.log ((j : ℂ) - ((x : ℂ) + Complex.I * (ε : ℂ))) =
      (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) * weightedTerm r (x - (j : ℝ)) ε := by
  unfold weightedTerm
  have he1 : ((x : ℂ) + Complex.I * (ε : ℂ)) - (j : ℂ) =
      ((x - (j : ℝ) : ℝ) : ℂ) + Complex.I * (ε : ℂ) := by push_cast; ring
  have he2 : (j : ℂ) - ((x : ℂ) + Complex.I * (ε : ℂ)) =
      ((-(x - (j : ℝ)) : ℝ) : ℂ) - Complex.I * (ε : ℂ) := by push_cast; ring
  rw [he1, he2]
  ring

lemma tendsto_logSum_of_term_limits (n r : ℕ) (x : ℝ)
    (hterms : ∀ j ∈ Finset.range (n + 1), Tendsto (weightedTerm r (x - (j : ℝ)))
      (𝓝[>] 0) (𝓝 (scalarBoundary r (x - (j : ℝ))))) :
    Tendsto (fun ε : ℝ => logSum n r ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0)
      (𝓝 ((realLogSum n r x : ℂ) - Complex.I * (Real.pi : ℂ) * (leftTail n r x : ℂ))) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) : Tendsto
      (fun ε : ℝ => (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        (((x : ℂ) + Complex.I * (ε : ℂ)) - (j : ℂ)) ^ r *
          Complex.log ((j : ℂ) - ((x : ℂ) + Complex.I * (ε : ℂ)))) (𝓝[>] 0)
      (𝓝 ((((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) * scalarBoundary r (x - (j : ℝ)))) := by
    apply ((hterms j hj).const_mul (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ)).congr'
    exact Filter.Eventually.of_forall fun ε => (logSum_term_eq n r j x ε).symm
  have hsum := tendsto_finsetSum (Finset.range (n + 1)) hterm
  rw [sum_scalarBoundary_eq] at hsum
  exact hsum

theorem tendsto_logSum_of_no_knots (n r : ℕ) (x : ℝ)
    (hknots : ∀ j ∈ Finset.range (n + 1), x ≠ (j : ℝ)) :
    Tendsto (fun ε : ℝ => logSum n r ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0)
      (𝓝 ((realLogSum n r x : ℂ) - Complex.I * (Real.pi : ℂ) * (leftTail n r x : ℂ))) := by
  apply tendsto_logSum_of_term_limits
  intro j hj
  exact tendsto_weightedTerm_of_ne_zero r (x - (j : ℝ)) (sub_ne_zero.mpr (hknots j hj))


/-- Positive integer degree removes the logarithmic singularity at a node. -/
lemma tendsto_weightedTerm_pos_degree (r : ℕ) (hr : 1 ≤ r) (a : ℝ) :
    Tendsto (weightedTerm r a) (𝓝[>] 0) (𝓝 (scalarBoundary r a)) := by
  by_cases ha : a = 0
  · subst a
    have hr0 : r ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr)
    have he : weightedTerm r 0 = (fun ε : ℝ =>
        (Complex.I * (ε : ℂ)) ^ r * Complex.log (-Complex.I * (ε : ℂ))) := by
      funext ε
      simp [weightedTerm]
    rw [he]
    have hb : scalarBoundary r 0 = 0 := by simp [scalarBoundary, hr0]
    rw [hb]
    exact IntegralComplexPowerLog.tendsto_imag_pow_log_neg_imag_zero_right r hr
  · exact tendsto_weightedTerm_of_ne_zero r a ha

/-- The integer logarithmic finite-sum boundary, including every zero node. -/
theorem tendsto_logSum_pos_degree (n r : ℕ) (hr : 1 ≤ r) (x : ℝ) :
    Tendsto (fun ε : ℝ => logSum n r ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0)
      (𝓝 ((realLogSum n r x : ℂ) - Complex.I * (Real.pi : ℂ) * (leftTail n r x : ℂ))) := by
  apply tendsto_logSum_of_term_limits
  intro j hj
  exact tendsto_weightedTerm_pos_degree r hr (x - (j : ℝ))

end IntegralIntegerLogBoundary


namespace IntegralIntegerLogNonzero

open IntegralTruncatedPower IntegralIntegerLogBoundary

lemma leftTail_eq_T (n r : ℕ) (x : ℝ) :
    leftTail n r x = T n (r : ℝ) x := by
  unfold leftTail T
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hx : (j : ℝ)<x
  · rw [if_pos hx, truncatedPower_of_pos (r : ℝ) (sub_pos.mpr hx), Real.rpow_natCast]
  · rw [if_neg hx, truncatedPower_of_nonpos (r : ℝ)
      (sub_nonpos.mpr (le_of_not_gt hx)), mul_zero]

lemma T_eq_zero_of_boundary_eq_zero (n r : ℕ) (x : ℝ)
    (hzero : (realLogSum n r x : ℂ) -
      Complex.I * (Real.pi : ℂ) * (leftTail n r x : ℂ) = 0) :
    T n (r : ℝ) x = 0 := by
  have him : -(Real.pi * leftTail n r x) = 0 := by
    simpa [Complex.mul_im, Complex.mul_re] using congrArg Complex.im hzero
  have ht : leftTail n r x = 0 :=
    (mul_eq_zero.mp (neg_eq_zero.mp him)).resolve_left Real.pi_ne_zero
  simpa only [leftTail_eq_T] using ht

lemma tendsto_C_zero_of_logSum_zero (n r : ℕ) (hrn : r<n) (x : ℝ)
    (hlim : Tendsto (fun ε : ℝ => logSum n r
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => IntegralTruncatedPowerCauchy.C n (r : ℝ)
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
  have hneg : Tendsto (fun ε : ℝ => -(logSum n r
      ((x : ℂ) + Complex.I * (ε : ℂ)))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [neg_zero] using hlim.neg
  apply hneg.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  have him : 0 < ((x : ℂ) + Complex.I * (ε : ℂ)).im := by simpa using hε
  simpa only [logSum] using
    (IntegralCauchyIntegerLog.C_nat_eq_log_sum n r hrn
      ((x : ℂ) + Complex.I * (ε : ℂ)) him).symm

lemma tendsto_C_at_integer_root (n r : ℕ) (hr : 1≤r) (hrn : r<n) (x : ℝ)
    (hx : T n (r : ℝ) x=0) :
    Tendsto (fun ε : ℝ => IntegralTruncatedPowerCauchy.C n (r : ℝ)
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝 0)
      (𝓝 ((∫ t in Ioi (0 : ℝ), T n (r : ℝ) t / (t-x) : ℝ) : ℂ)) := by
  have hp : (0 : ℝ)<r := by exact_mod_cast (show 0<r from Nat.zero_lt_of_lt hr)
  have hpn : (r : ℝ)<n := by exact_mod_cast hrn
  have hf : AEStronglyMeasurable (fun t : ℝ => (T n (r : ℝ) t : ℂ))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Complex.continuous_ofReal.comp (continuous_T n hp)).aestronglyMeasurable
  have hg := IntegralTruncatedPowerQuotient.integrableOn_T_quotient n hp hpn x hx
  have h := IntegralCauchyBoundary.tendsto_cauchy_boundary_of_integrable_quotient x hf hg
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro ε
  unfold IntegralTruncatedPowerCauchy.C
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  have hden : (((t-x : ℝ) : ℂ) - Complex.I * (ε : ℂ)) =
      ((t : ℂ) - ((x : ℂ) + Complex.I * (ε : ℂ))) := by push_cast; ring
  rw [hden]

lemma not_tendsto_C_zero_at_integer_root (n r : ℕ) (hr : 1≤r) (hrn : r<n) (x : ℝ)
    (hx : T n (r : ℝ) x=0) :
    ¬ Tendsto (fun ε : ℝ => IntegralTruncatedPowerCauchy.C n (r : ℝ)
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
  intro hzero
  have hlim := (tendsto_C_at_integer_root n r hr hrn x hx).mono_left
    (show 𝓝[>] (0 : ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
  have hne := IntegralTruncatedPowerCauchyNonzero.cauchy_nonzero_integer n r hr hrn x hx
  exact (Complex.ofReal_ne_zero.mpr hne) (tendsto_nhds_unique hlim hzero)

/-- The actual integer logarithmic boundary is nonzero at every real point. -/
theorem boundary_pos_degree_ne_zero (n r : ℕ) (hr : 1≤r) (hrn : r<n) (x : ℝ) :
    (realLogSum n r x : ℂ) -
      Complex.I * (Real.pi : ℂ) * (leftTail n r x : ℂ) ≠ 0 := by
  intro hzero
  have hx := T_eq_zero_of_boundary_eq_zero n r x hzero
  have hlim : Tendsto (fun ε : ℝ => logSum n r
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [hzero] using tendsto_logSum_pos_degree n r hr x
  exact not_tendsto_C_zero_at_integer_root n r hr hrn x hx
    (tendsto_C_zero_of_logSum_zero n r hrn x hlim)

lemma zero_degree_root_is_exterior (n : ℕ) (hn : 0<n) (x : ℝ)
    (hknots : ∀ j ∈ Finset.range (n+1), x ≠ (j : ℝ))
    (hx : T n 0 x=0) : x<0 ∨ (n : ℝ)<x := by
  by_cases hx0 : x<0
  · exact Or.inl hx0
  by_cases hxn : (n : ℝ)<x
  · exact Or.inr hxn
  have hxne0 : x≠0 := by simpa using hknots 0 (Finset.mem_range.mpr (by omega))
  have hxnen : x≠(n : ℝ) := hknots n (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have hxpos : 0<x := lt_of_le_of_ne (le_of_not_gt hx0) (Ne.symm hxne0)
  have hxlt : x<(n : ℝ) := lt_of_le_of_ne (le_of_not_gt hxn) hxnen
  have hjn : Nat.floor x<n := (Nat.floor_lt hxpos.le).mpr hxlt
  have hxj : (Nat.floor x : ℝ)<x :=
    lt_of_le_of_ne (Nat.floor_le hxpos.le)
      (Ne.symm (hknots (Nat.floor x) (Finset.mem_range.mpr (Nat.lt_succ_of_lt hjn))))
  have hsign := IntegralTruncatedPowerSign.signed_T_nonpos_cell_pos
    n (Nat.floor x) hjn 0 x le_rfl hxj (Nat.lt_floor_add_one x)
  rw [hx, mul_zero] at hsign
  exact False.elim (lt_irrefl 0 hsign)

/-- Degree zero is nonzero away from its finitely many logarithmic nodes. -/
theorem boundary_zero_degree_ne_zero (n : ℕ) (hn : 0<n) (x : ℝ)
    (hknots : ∀ j ∈ Finset.range (n+1), x ≠ (j : ℝ)) :
    (realLogSum n 0 x : ℂ) -
      Complex.I * (Real.pi : ℂ) * (leftTail n 0 x : ℂ) ≠ 0 := by
  intro hzero
  have hx : T n 0 x=0 := by
    simpa only [Nat.cast_zero] using T_eq_zero_of_boundary_eq_zero n 0 x hzero
  have hside := zero_degree_root_is_exterior n hn x hknots hx
  have hlim : Tendsto (fun ε : ℝ => logSum n 0
      ((x : ℂ) + Complex.I * (ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [hzero] using tendsto_logSum_of_no_knots n 0 x hknots
  have hC := tendsto_C_zero_of_logSum_zero n 0 hn x hlim
  exact IntegralTruncatedPowerZeroCauchy.not_tendsto_C_zero_exterior n hn x hside
    (by simpa only [Nat.cast_zero] using hC)

end IntegralIntegerLogNonzero


namespace IntegralRationalLogIntegral

lemma shift_ne_zero {a : ℂ} (ha : 0 ≤ a.re) (ha0 : a ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) : (s : ℂ) + a ≠ 0 := by
  intro h
  have hr : s + a.re = 0 := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] using congrArg Complex.re h
  have hi : a.im = 0 := by
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] using
      congrArg Complex.im h
  apply ha0
  apply Complex.ext
  · simpa only [Complex.zero_re] using (show a.re = 0 by linarith)
  · simpa only [Complex.zero_im] using hi

lemma shift_mem_slitPlane {a : ℂ} (ha : 0 ≤ a.re) (ha0 : a ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) : (s : ℂ) + a ∈ Complex.slitPlane := by
  have hn := shift_ne_zero ha ha0 hs
  by_cases hi : a.im = 0
  · left
    have hr : 0 ≤ ((s : ℂ) + a).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
    have hre : ((s : ℂ) + a).re ≠ 0 := by
      intro hre
      apply hn
      apply Complex.ext
      · simpa using hre
      · simp [hi]
    exact lt_of_le_of_ne hr (Ne.symm hre)
  · right
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hi

lemma hasDerivAt_weighted_log (d a : ℂ) (ha : 0 ≤ a.re)
    (hz : a = 0 → d = 0) (s : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (fun s : ℝ => d * Complex.log ((s : ℂ) + a))
      (d / ((s : ℂ) + a)) s := by
  by_cases ha0 : a = 0
  · have hd := hz ha0
    simpa only [hd, zero_mul, zero_div] using hasDerivAt_const s (0 : ℂ)
  · have hd : HasDerivAt (fun s : ℝ => (s : ℂ) + a) 1 s := by
      simpa only [Complex.ofReal_one, id_eq] using! (hasDerivAt_id s).ofReal_comp.add_const a
    simpa only [mul_one_div] using!
      (hd.clog_real (shift_mem_slitPlane ha ha0 hs)).const_mul d

lemma continuousOn_weighted_rational (d a : ℂ) (ha : 0 ≤ a.re)
    (hz : a = 0 → d = 0) :
    ContinuousOn (fun s : ℝ => d / ((s : ℂ) + a)) (Ici 0) := by
  by_cases ha0 : a = 0
  · have hd := hz ha0
    simpa only [hd, zero_div] using continuousOn_const (c := (0 : ℂ))
  · exact continuousOn_const.div
      (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun s hs => shift_ne_zero ha ha0 hs)

lemma intervalIntegral_eq_log_difference {ι : Type*} [Fintype ι]
    (d a : ι → ℂ) (ha : ∀ i, 0 ≤ (a i).re) (hz : ∀ i, a i = 0 → d i = 0)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ s in (0 : ℝ)..T, ∑ i, d i / ((s : ℂ) + a i)) =
      (∑ i, d i * Complex.log ((T : ℂ) + a i)) -
        ∑ i, d i * Complex.log (a i) := by
  have hc : ContinuousOn (fun s : ℝ => ∑ i, d i / ((s : ℂ) + a i)) (Ici 0) := by
    apply continuousOn_finsetSum
    intro i hi
    exact continuousOn_weighted_rational (d i) (a i) (ha i) (hz i)
  have hsub : uIcc (0 : ℝ) T ⊆ Ici 0 := by
    rw [uIcc_of_le hT]
    exact Icc_subset_Ici_self
  have hi : IntervalIntegrable (fun s : ℝ => ∑ i, d i / ((s : ℂ) + a i)) volume 0 T :=
    (hc.mono hsub).intervalIntegrable
  have hd : ∀ s ∈ uIcc (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => ∑ i, d i * Complex.log ((s : ℂ) + a i))
        (∑ i, d i / ((s : ℂ) + a i)) s := by
    intro s hs
    apply HasDerivAt.fun_sum
    intro i hi
    exact hasDerivAt_weighted_log (d i) (a i) (ha i) (hz i) s (hsub hs)
  simpa only [Complex.ofReal_zero, zero_add] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

lemma log_shift_split {a : ℂ} (ha : 0 ≤ a.re) {T : ℝ} (hT : 0 < T) :
    Complex.log ((T : ℂ) + a) =
      (Real.log T : ℂ) + Complex.log (1 + a / (T : ℂ)) := by
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hT)
  have he : (T : ℂ) * (1 + a / (T : ℂ)) = (T : ℂ) + a := by
    field_simp
  have hn : (T : ℂ) + a ≠ 0 := by
    intro h
    have hr : T + a.re = 0 := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] using congrArg Complex.re h
    linarith
  have hx : 1 + a / (T : ℂ) ≠ 0 := by
    intro h
    apply hn
    rw [← he, h, mul_zero]
  rw [← he, Complex.log_ofReal_mul hT hx]

lemma weighted_log_sum_eq_remainder {ι : Type*} [Fintype ι]
    (d a : ι → ℂ) (ha : ∀ i, 0 ≤ (a i).re) (hsum : ∑ i, d i = 0)
    {T : ℝ} (hT : 0 < T) :
    (∑ i, d i * Complex.log ((T : ℂ) + a i)) =
      ∑ i, d i * Complex.log (1 + a i / (T : ℂ)) := by
  simp_rw [log_shift_split (ha _) hT, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul, zero_add]

lemma tendsto_log_remainder_zero (a : ℂ) :
    Tendsto (fun T : ℝ => Complex.log (1 + a / (T : ℂ))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun T : ℝ => (T : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0)).ofReal
  have harg : Tendsto (fun T : ℝ => 1 + a / (T : ℂ)) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using (hinv.const_mul a).const_add 1
  have hc : ContinuousAt Complex.log (1 : ℂ) :=
    continuousAt_clog (by simp [Complex.mem_slitPlane_iff])
  simpa only [Function.comp_def, Complex.log_one] using! hc.tendsto.comp harg

lemma tendsto_weighted_log_sum_zero {ι : Type*} [Fintype ι]
    (d a : ι → ℂ) (ha : ∀ i, 0 ≤ (a i).re) (hsum : ∑ i, d i = 0) :
    Tendsto (fun T : ℝ => ∑ i, d i * Complex.log ((T : ℂ) + a i)) atTop (𝓝 0) := by
  have hlim := tendsto_finsetSum Finset.univ (fun i _ =>
    (tendsto_log_remainder_zero (a i)).const_mul (d i))
  have hlim' : Tendsto (fun T : ℝ => ∑ i, d i * Complex.log (1 + a i / (T : ℂ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using hlim
  apply hlim'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact (weighted_log_sum_eq_remainder d a ha hsum hT).symm

theorem tendsto_intervalIntegral_eq_neg_log_sum {ι : Type*} [Fintype ι]
    (d a : ι → ℂ) (ha : ∀ i, 0 ≤ (a i).re) (hz : ∀ i, a i = 0 → d i = 0)
    (hsum : ∑ i, d i = 0) :
    Tendsto (fun T : ℝ => ∫ s in (0 : ℝ)..T, ∑ i, d i / ((s : ℂ) + a i))
      atTop (𝓝 (-(∑ i, d i * Complex.log (a i)))) := by
  have hlim := (tendsto_weighted_log_sum_zero d a ha hsum).sub_const
    (∑ i, d i * Complex.log (a i))
  have hlim' : Tendsto (fun T : ℝ =>
      (∑ i, d i * Complex.log ((T : ℂ) + a i)) - ∑ i, d i * Complex.log (a i))
      atTop (𝓝 (-(∑ i, d i * Complex.log (a i)))) := by
    simpa only [zero_sub] using hlim
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (intervalIntegral_eq_log_difference d a ha hz T hT).symm

theorem integral_Ioi_eq_neg_log_sum {ι : Type*} [Fintype ι]
    (d a : ι → ℂ) (ha : ∀ i, 0 ≤ (a i).re) (hz : ∀ i, a i = 0 → d i = 0)
    (hsum : ∑ i, d i = 0)
    (hi : IntegrableOn (fun s : ℝ => ∑ i, d i / ((s : ℂ) + a i)) (Ioi 0)) :
    (∫ s in Ioi (0 : ℝ), ∑ i, d i / ((s : ℂ) + a i)) =
      -(∑ i, d i * Complex.log (a i)) := by
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id)
    (tendsto_intervalIntegral_eq_neg_log_sum d a ha hz hsum)

end IntegralRationalLogIntegral


namespace IntegralPositiveIntegerOriginal

/-- The exact positive-integer original integral, with zero frequencies allowed. -/
theorem gamma_mul_original_integral_nat (n r : ℕ) (hr : 1 ≤ r) (hrn : r < n) (a : ℝ) :
    (Real.Gamma ((r : ℝ) + 1) : ℂ) *
        (∫ t : ℝ in Set.Ioi 0, IntegralOriginalConvergence.g n a t /
          ((t ^ ((r : ℝ) + 1) : ℝ) : ℂ)) =
      -(∑ j : Fin (n + 1), ((-1 : ℂ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
        (Complex.I * ((a + (n : ℝ) - 2 * (j : ℝ) : ℝ) : ℂ)) ^ r *
          Complex.log (-(Complex.I * ((a + (n : ℝ) - 2 * (j : ℝ) : ℝ) : ℂ)))) := by
  let c : Fin (n + 1) → ℂ := fun j => (-1 : ℂ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℂ)
  let b : Fin (n + 1) → ℂ := fun j => -(Complex.I * ((a + (n : ℝ) - 2 * (j : ℝ) : ℝ) : ℂ))
  let d : Fin (n + 1) → ℂ := fun j => c j * (-b j) ^ r
  have hr0 : r ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hp : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hpn : (r : ℝ) < n := by exact_mod_cast hrn
  have hre : ∀ j : Fin (n + 1), 0 ≤ (b j).re := by intro j; simp [b]
  have hzero : ∀ j : Fin (n + 1), b j = 0 → d j = 0 := by
    intro j hj
    simp only [d, hj, neg_zero, zero_pow hr0, mul_zero]
  have hsum : (∑ j : Fin (n + 1), d j) = 0 := by
    simpa only [d, c, b, neg_neg] using
      IntegralFrequencyCancellation.frequency_power_sum_fin n r hrn a
  have hjets : ∀ k < r,
      ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))), c j * (-b j) ^ k = 0 := by
    intro k hk
    simpa only [c, b, neg_neg] using
      IntegralFrequencyCancellation.frequency_power_sum_fin n k (hk.trans hrn) a
  have hden (s : ℝ) (hs : 0 < s) (j : Fin (n + 1)) : (s : ℂ) + b j ≠ 0 := by
    intro hz
    have hs0 : s = 0 := by simpa [b] using congrArg Complex.re hz
    exact hs.ne' hs0
  have hi := IntegralRationalRecurrence.integrableOn_sum_div Finset.univ d b
    (fun j _ => hre j) (fun j _ => hzero j) hsum
  have hlog := IntegralRationalLogIntegral.integral_Ioi_eq_neg_log_sum d b hre hzero hsum hi
  have hGamma :
      (Real.Gamma ((r : ℝ) + 1) : ℂ) *
        (∫ t : ℝ in Set.Ioi 0, IntegralOriginalConvergence.g n a t /
          ((t ^ ((r : ℝ) + 1) : ℝ) : ℂ)) =
      ∫ s : ℝ in Set.Ioi 0, ((s ^ (r : ℝ) : ℝ) : ℂ) *
        (∑ j : Fin (n + 1), c j / ((s : ℂ) + b j)) := by
    rw [IntegralOriginalRepresentation.gamma_mul_original_integral_of_pos n (r : ℝ) a hp hpn]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [c, b]
    push_cast
    ring
  rw [hGamma]
  calc
    _ = ∫ s : ℝ in Set.Ioi 0, ∑ j : Fin (n + 1), d j / ((s : ℂ) + b j) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hrec := IntegralRationalRecurrence.weighted_rational_recurrence Finset.univ c b
        s (r : ℝ) r hs (fun j _ => hden s hs j) hjets
      simpa only [sub_self, Real.rpow_zero, Complex.ofReal_one, one_mul, d] using hrec
    _ = -(∑ j : Fin (n + 1), d j * Complex.log (b j)) := hlog
    _ = _ := by simp only [d, c, b, neg_neg]

end IntegralPositiveIntegerOriginal


namespace IntegralExponentialJets

open MeasureTheory Filter Topology Set

lemma polynomial_part_eq_zero {ι : Type*} [Fintype ι]
    (d β : ι → ℂ) (N : ℕ)
    (hm : ∀ k : ℕ, k < N → (∑ i, d i * (β i)^k) = 0) (t : ℝ) :
    (∑ i, d i * (∑ k ∈ Finset.range N,
      (β i * (t : ℂ))^k / (k.factorial : ℂ))) = 0 := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  calc
    _ = (∑ i, d i * (β i)^k) * ((t : ℂ)^k / (k.factorial : ℂ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow]
      ring
    _ = 0 := by rw [hm k (Finset.mem_range.mp hk), zero_mul]

/-- A finite exponential sum with `N` vanished moments is bounded by `C*t^N`
on `[0,1]`, with an explicit nonnegative constant. -/
theorem norm_exp_sum_le_pow {ι : Type*} [Fintype ι]
    (d β : ι → ℂ) (N : ℕ)
    (hm : ∀ k : ℕ, k < N → (∑ i, d i * (β i)^k) = 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖∑ i, d i * Complex.exp (β i * t)‖ ≤
      (∑ i, ‖d i‖ * (‖β i‖^N * Real.exp ‖β i‖)) * t^N := by
  classical
  have hrem (i : ι) :
      ‖Complex.exp (β i * t) - ∑ k ∈ Finset.range N,
        (β i * (t : ℂ))^k / (k.factorial : ℂ)‖ ≤
          (‖β i‖^N * Real.exp ‖β i‖) * t^N := by
    calc
      _ ≤ ‖β i * (t : ℂ)‖^N * Real.exp ‖β i * (t : ℂ)‖ :=
        Complex.norm_exp_sub_sum_le_norm_mul_exp _ N
      _ = (‖β i‖^N * t^N) * Real.exp (‖β i‖ * t) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1, mul_pow]
      _ ≤ (‖β i‖^N * t^N) * Real.exp ‖β i‖ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg (norm_nonneg _) _)
          (pow_nonneg ht.1 _))
        exact Real.exp_le_exp.mpr (mul_le_of_le_one_right (norm_nonneg _) ht.2)
      _ = _ := by ring
  have heq : (∑ i, d i * Complex.exp (β i * t)) =
      ∑ i, d i * (Complex.exp (β i * t) -
        ∑ k ∈ Finset.range N, (β i * (t : ℂ))^k / (k.factorial : ℂ)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, polynomial_part_eq_zero d β N hm t, sub_zero]
  rw [heq]
  calc
    _ ≤ ∑ i, ‖d i‖ * ‖Complex.exp (β i * t) -
        ∑ k ∈ Finset.range N, (β i * (t : ℂ))^k / (k.factorial : ℂ)‖ := by
      simpa only [norm_mul] using norm_sum_le (s := Finset.univ)
        (f := fun i => d i * (Complex.exp (β i * t) -
          ∑ k ∈ Finset.range N, (β i * (t : ℂ))^k / (k.factorial : ℂ)))
    _ ≤ ∑ i, ‖d i‖ * ((‖β i‖^N * Real.exp ‖β i‖) * t^N) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrem i) (norm_nonneg _))
    _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

lemma exp_sum_bound_nonneg {ι : Type*} [Fintype ι] (d β : ι → ℂ) (N : ℕ) :
    0 ≤ ∑ i, ‖d i‖ * (‖β i‖^N * Real.exp ‖β i‖) := by positivity

lemma hasDerivAt_exp_sum {ι : Type*} [Fintype ι] (d β : ι → ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∑ i, d i * Complex.exp (β i * u))
      (∑ i, (d i * β i) * Complex.exp (β i * t)) t := by
  classical
  have hd (i : ι) : HasDerivAt (fun u : ℝ => d i * Complex.exp (β i * u))
      (d i * (Complex.exp (β i * t) * β i)) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using
      (((((hasDerivAt_id t).ofReal_comp).const_mul (β i)).cexp).const_mul (d i))
  apply (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)).congr_deriv
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma norm_exp_sum_le_coeff {ι : Type*} [Fintype ι] (d β : ι → ℂ)
    (hre : ∀ i, (β i).re = 0) (t : ℝ) :
    ‖∑ i, d i * Complex.exp (β i * t)‖ ≤ ∑ i, ‖d i‖ := by
  classical
  calc
    _ ≤ ∑ i, ‖d i * Complex.exp (β i * t)‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Complex.norm_exp, Complex.mul_re, hre i]

lemma continuousOn_weighted_exp_sum {ι : Type*} [Fintype ι] (d β : ι → ℂ) (r : ℝ) :
    ContinuousOn (fun t : ℝ => (∑ i, d i * Complex.exp (β i * t)) * (t ^ r : ℝ))
      (Ioi 0) := by
  apply ContinuousOn.mul
  · fun_prop
  · exact Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const fun t ht => Or.inl ht.ne')

lemma norm_weighted_exp_sum_le_pow {ι : Type*} [Fintype ι]
    (d β : ι → ℂ) (N : ℕ)
    (hm : ∀ k : ℕ, k < N → (∑ i, d i * (β i)^k) = 0)
    (r t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖(∑ i, d i * Complex.exp (β i * t)) * (t ^ r : ℝ)‖ ≤
      (∑ i, ‖d i‖ * (‖β i‖^N * Real.exp ‖β i‖)) * t^((N : ℝ) + r) := by
  classical
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  calc
    _ ≤ ((∑ i, ‖d i‖ * (‖β i‖^N * Real.exp ‖β i‖)) * t^N) * t^r :=
      mul_le_mul_of_nonneg_right (norm_exp_sum_le_pow d β N hm t ⟨ht.1.le, ht.2⟩)
        (Real.rpow_nonneg ht.1.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_natCast t N, ← Real.rpow_add ht.1]

theorem intervalIntegrable_weighted_exp_sum {ι : Type*} [Fintype ι]
    (d β : ι → ℂ) (N : ℕ)
    (hm : ∀ k : ℕ, k < N → (∑ i, d i * (β i)^k) = 0)
    (r : ℝ) (hr : -1 < (N : ℝ) + r) (T : ℝ) (hT : 0 < T) :
    IntervalIntegrable
      (fun t : ℝ => (∑ i, d i * Complex.exp (β i * t)) * (t ^ r : ℝ)) volume 0 T := by
  classical
  have hnear : IntervalIntegrable
      (fun t : ℝ => (∑ i, d i * Complex.exp (β i * t)) * (t ^ r : ℝ)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    have hb := ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr hr).const_mul
      (∑ i, ‖d i‖ * (‖β i‖^N * Real.exp ‖β i‖))
    apply hb.mono'
      ((continuousOn_weighted_exp_sum d β r).mono Ioo_subset_Ioi_self
        |>.aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact norm_weighted_exp_sum_le_pow d β N hm r t ⟨ht.1, ht.2.le⟩
  by_cases hT1 : T ≤ 1
  · apply hnear.mono_set
    rw [uIcc_of_le hT.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hT1
  · apply hnear.trans
    apply ((continuousOn_weighted_exp_sum d β r).mono ?_).intervalIntegrable
    rw [uIcc_of_le (le_of_lt (lt_of_not_ge hT1))]
    exact fun t ht => lt_of_lt_of_le zero_lt_one ht.1

theorem tendsto_weighted_exp_sum_zero {ι : Type*} [Fintype ι]
    (d β : ι → ℂ) (N : ℕ)
    (hm : ∀ k : ℕ, k < N → (∑ i, d i * (β i)^k) = 0)
    (r : ℝ) (hr : 0 < (N : ℝ) + r) :
    Tendsto (fun t : ℝ => (∑ i, d i * Complex.exp (β i * t)) * (t ^ r : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
  classical
  have hpow : Tendsto (fun t : ℝ => t^((N : ℝ) + r)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hr.ne'] using
      ((Real.continuous_rpow_const hr.le).continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hb := hpow.const_mul (∑ i, ‖d i‖ * (‖β i‖^N * Real.exp ‖β i‖))
  simp only [mul_zero] at hb
  apply squeeze_zero_norm' _ hb
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with t ht
  exact norm_weighted_exp_sum_le_pow d β N hm r t ht

theorem tendsto_weighted_exp_sum_infty {ι : Type*} [Fintype ι]
    (d β : ι → ℂ) (hre : ∀ i, (β i).re = 0) (r : ℝ) (hr : r < 0) :
    Tendsto (fun t : ℝ => (∑ i, d i * Complex.exp (β i * t)) * (t ^ r : ℝ))
      atTop (𝓝 0) := by
  classical
  have hpow : Tendsto (fun t : ℝ => t^r) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hr)
  have hb := hpow.const_mul (∑ i, ‖d i‖)
  simp only [mul_zero] at hb
  apply squeeze_zero_norm' _ hb
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  exact mul_le_mul_of_nonneg_right (norm_exp_sum_le_coeff d β hre t)
    (Real.rpow_nonneg ht.le _)

end IntegralExponentialJets


namespace IntegralOriginalAbel

open MeasureTheory Filter Topology Set

noncomputable def phaseSum {ι : Type*} [Fintype ι] (d : ι → ℂ) (w : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i, d i * Complex.exp (Complex.I * w i * t)

noncomputable def weightedPhaseSum {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (t : ℝ) : ℂ := phaseSum d w t * (t ^ (-1 : ℝ) : ℝ)

noncomputable def tailValue (c : ℂ) : ℂ :=
  -Complex.exp c / c + 1 / c *
    (∫ t : ℝ in Ioi 1, Complex.exp (c * t) * (t ^ (-2 : ℝ) : ℝ))

lemma damping_norm_le_one (ε t : ℝ) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    ‖((Real.exp (-(ε * t)) : ℝ) : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hε ht))

lemma integrable_mul_damping {μ : Measure ℝ} (f : ℝ → ℂ)
    (hi : Integrable f μ) (hpos : ∀ᵐ t : ℝ ∂μ, 0 ≤ t) (ε : ℝ) (hε : 0 ≤ ε) :
    Integrable (fun t : ℝ => f t * (Real.exp (-(ε * t)) : ℝ)) μ := by
  apply hi.norm.mono' (hi.aestronglyMeasurable.mul (by fun_prop))
  filter_upwards [hpos] with t ht
  dsimp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (damping_norm_le_one ε t hε ht)

theorem integral_mul_damping_tendsto {μ : Measure ℝ} (f : ℝ → ℂ)
    (hi : Integrable f μ) (hpos : ∀ᵐ t : ℝ ∂μ, 0 ≤ t) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ, f t * (Real.exp (-(ε * t)) : ℝ) ∂μ)
      (𝓝[>] 0) (𝓝 (∫ t : ℝ, f t ∂μ)) := by
  have hm (ε : ℝ) : AEStronglyMeasurable
      (fun t : ℝ => f t * (Real.exp (-(ε * t)) : ℝ)) μ :=
    hi.aestronglyMeasurable.mul (by fun_prop)
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ t : ℝ ∂μ,
      ‖f t * (Real.exp (-(ε * t)) : ℝ)‖ ≤ ‖f t‖ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [hpos] with t ht
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (damping_norm_le_one ε t (le_of_lt hε) ht)
  have hlim : ∀ᵐ t : ℝ ∂μ, Tendsto
      (fun ε : ℝ => f t * (Real.exp (-(ε * t)) : ℝ)) (𝓝[>] 0) (𝓝 (f t)) := by
    apply Eventually.of_forall
    intro t
    have hc : Continuous (fun ε : ℝ => f t * (Real.exp (-(ε * t)) : ℝ)) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  exact tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖)
    (Eventually.of_forall hm) hb hi.norm hlim

lemma integrable_tail_weighted_exp (c : ℂ) (hc : c.re < 0) :
    IntegrableOn (fun t : ℝ => Complex.exp (c * t) * (t ^ (-1 : ℝ) : ℝ)) (Ioi 1) := by
  apply (integrableOn_exp_mul_Ioi hc 1).mono'
    ((IntegralExponentialAbel.continuousOn_weighted_exp c (-1)).mono
      (Ioi_subset_Ioi zero_le_one) |>.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans ht).le _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le
    (Real.rpow_le_one_of_one_le_of_nonpos ht.le (by norm_num))

lemma tail_tendsto (c : ℂ) (hc : c ≠ 0) (hre : c.re ≤ 0) :
    Tendsto (fun T : ℝ => ∫ t in (1 : ℝ)..T,
      Complex.exp (c * t) * (t ^ (-1 : ℝ) : ℝ)) atTop (𝓝 (tailValue c)) := by
  simpa only [tailValue, Complex.ofReal_one, show (-1 : ℝ) - 1 = -2 by norm_num] using
    IntegralExponentialAbel.weighted_tail_tendsto c 1 hc hre zero_lt_one

lemma tail_integral_eq (c : ℂ) (hc : c.re < 0) :
    (∫ t : ℝ in Ioi 1, Complex.exp (c * t) * (t ^ (-1 : ℝ) : ℝ)) = tailValue c := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 1 (integrable_tail_weighted_exp c hc) tendsto_id)
    (tail_tendsto c hc0 hc.le)

theorem tailValue_tendsto_damping (w : ℝ) (hw : w ≠ 0) :
    Tendsto (fun ε : ℝ => tailValue (Complex.I * w - ε)) (𝓝[>] 0)
      (𝓝 (tailValue (Complex.I * w))) := by
  have hc0 : Complex.I * (w : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hw)
  have htail := IntegralExponentialAbel.integral_damped_tendsto
    (volume.restrict (Ioi (1 : ℝ))) w (-2)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => (zero_lt_one.trans ht).le))
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one)
  have hc : Tendsto (fun ε : ℝ => Complex.I * w - (ε : ℂ)) (𝓝[>] 0)
      (𝓝 (Complex.I * w)) := by
    have h : Continuous (fun ε : ℝ => Complex.I * w - (ε : ℂ)) := by fun_prop
    simpa using (h.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have he := hc.cexp.div hc hc0
  have hcoef := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ))
    (𝓝[>] 0) (𝓝 (1 : ℂ))).div hc hc0
  simpa only [tailValue, Pi.div_apply, neg_div] using he.neg.add (hcoef.mul htail)

lemma damped_weighted_eq_sum {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (ε t : ℝ) :
    weightedPhaseSum d w t * (Real.exp (-(ε * t)) : ℝ) =
      ∑ i, d i * (Complex.exp ((Complex.I * w i - ε) * t) * (t ^ (-1 : ℝ) : ℝ)) := by
  classical
  unfold weightedPhaseSum phaseSum
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← IntegralOriginalRepresentation.phase_mul_real_exp (w i) ε t]
  ring

lemma integrable_damped_tail {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => weightedPhaseSum d w t *
      (Real.exp (-(ε * t)) : ℝ)) (Ioi 1) := by
  classical
  have hm (i : ι) : (Complex.I * (w i : ℂ) - ε).re < 0 := by simpa using neg_neg_of_pos hε
  have h : Integrable (fun t : ℝ => ∑ i, d i *
      (Complex.exp ((Complex.I * w i - ε) * t) * (t ^ (-1 : ℝ) : ℝ)))
      (volume.restrict (Ioi (1 : ℝ))) :=
    integrable_finsetSum Finset.univ (fun i _ => (integrable_tail_weighted_exp _ (hm i)).const_mul (d i))
  exact h.congr (Eventually.of_forall (fun t => (damped_weighted_eq_sum d w ε t).symm))

lemma integral_damped_tail {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∫ t : ℝ in Ioi 1, weightedPhaseSum d w t * (Real.exp (-(ε * t)) : ℝ)) =
      ∑ i, d i * tailValue (Complex.I * w i - ε) := by
  classical
  simp_rw [damped_weighted_eq_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, tail_integral_eq _ (by simpa using neg_neg_of_pos hε)]
  · intro i _
    exact (integrable_tail_weighted_exp _ (by simpa using neg_neg_of_pos hε)).const_mul (d i)

lemma intervalIntegrable_weighted_zero_one {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (hsum : (∑ i, d i) = 0) :
    IntervalIntegrable (weightedPhaseSum d w) volume 0 1 := by
  have hm : ∀ k : ℕ, k < 1 → (∑ i, d i * (Complex.I * w i)^k) = 0 := by
    intro k hk
    have hk0 : k = 0 := by omega
    simpa only [hk0, pow_zero, mul_one] using hsum
  exact IntegralExponentialJets.intervalIntegrable_weighted_exp_sum
    d (fun i => Complex.I * w i) 1 hm (-1) (by norm_num) 1 zero_lt_one

lemma integrable_damped_weighted {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (hsum : (∑ i, d i) = 0) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => weightedPhaseSum d w t *
      (Real.exp (-(ε * t)) : ℝ)) (Ioi 0) := by
  have hnear := integrable_mul_damping (weightedPhaseSum d w)
    (intervalIntegrable_weighted_zero_one d w hsum).1
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ht.1.le)) ε hε.le
  have hnear' : IntegrableOn (fun t : ℝ => weightedPhaseSum d w t *
      (Real.exp (-(ε * t)) : ℝ)) (Ioc 0 1) := hnear
  simpa only [Ioc_union_Ioi_eq_Ioi zero_le_one] using
    hnear'.union (integrable_damped_tail d w ε hε)

/-- Actual whole finite-sum Abel convergence at exponent zero. Cancellation of
its constant frequency moment supplies integrability at zero; nonzero real
frequencies supply the conditionally convergent tails. -/
theorem exists_limit_and_abel_pzero {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (hsum : (∑ i, d i) = 0) (hw : ∀ i, w i ≠ 0) :
    ∃ L : ℂ,
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, weightedPhaseSum d w t) atTop (𝓝 L) ∧
      Tendsto (fun ε : ℝ => ∫ t : ℝ in Ioi 0,
        weightedPhaseSum d w t * (Real.exp (-(ε * t)) : ℝ)) (𝓝[>] 0) (𝓝 L) := by
  classical
  have hnear := intervalIntegrable_weighted_zero_one d w hsum
  let Lnear : ℂ := ∫ t : ℝ in Ioc 0 1, weightedPhaseSum d w t
  let Ltail : ℂ := ∑ i, d i * tailValue (Complex.I * w i)
  have hparam := tendsto_finsetSum Finset.univ (fun i _ =>
    (tailValue_tendsto_damping (w i) (hw i)).const_mul (d i))
  have hnearparam := integral_mul_damping_tendsto (weightedPhaseSum d w) hnear.1
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ht.1.le))
  have htail := tendsto_finsetSum Finset.univ (fun i _ =>
    (tail_tendsto (Complex.I * w i)
      (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hw i))) (by simp)).const_mul (d i))
  have htail' : Tendsto (fun T : ℝ => ∫ t in (1 : ℝ)..T, weightedPhaseSum d w t)
      atTop (𝓝 Ltail) := by
    apply htail.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    simp_rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro t _
      dsimp [weightedPhaseSum, phaseSum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · intro i _
      have hc := (IntegralExponentialAbel.continuousOn_weighted_exp
        (Complex.I * w i) (-1)).const_mul (d i)
      apply (hc.mono ?_).intervalIntegrable
      rw [uIcc_of_le hT]
      exact fun t ht => lt_of_lt_of_le zero_lt_one ht.1
  refine ⟨Lnear + Ltail, ?_, ?_⟩
  · apply (htail'.const_add Lnear).congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hti : IntervalIntegrable (weightedPhaseSum d w) volume 1 T := by
      apply ((IntegralExponentialJets.continuousOn_weighted_exp_sum d
        (fun i => Complex.I * w i) (-1)).mono ?_).intervalIntegrable
      rw [uIcc_of_le hT]
      exact fun t ht => lt_of_lt_of_le zero_lt_one ht.1
    change (∫ t : ℝ in Ioc 0 1, weightedPhaseSum d w t) + _ = _
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_add_adjacent_intervals hnear hti
  · apply (hnearparam.add hparam).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hiNear := integrable_mul_damping (weightedPhaseSum d w) hnear.1
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ht.1.le)) ε (le_of_lt hε)
    have hiTail := integrable_damped_tail d w ε hε
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hiNear hiTail,
      integral_damped_tail d w ε hε]

lemma integrable_damped_phase_laplace (w s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => Complex.exp ((Complex.I * w - ε) * t) *
      (Real.exp (-(s * t)) : ℝ)) (Ioi 0) := by
  have hre : (Complex.I * (w : ℂ) - ε - s).re < 0 := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub]
    linarith
  apply (integrableOn_exp_mul_complex_Ioi hre 0).congr_fun _ measurableSet_Ioi
  intro t _
  dsimp only
  rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, ← Complex.exp_add]
  congr 1
  ring

/-- The exact damped finite sum has the rational Mellin integral at exponent
zero. The only cancellation premise is the actual constant moment `Σ d = 0`. -/
theorem damped_mellin_pzero {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (hsum : (∑ i, d i) = 0) (ε : ℝ) (hε : 0 < ε) :
    (∫ t : ℝ in Ioi 0, weightedPhaseSum d w t * (Real.exp (-(ε * t)) : ℝ)) =
      ∫ s : ℝ in Ioi 0, ∑ i, d i *
        (1 / (((s + ε : ℝ) : ℂ) - Complex.I * w i)) := by
  classical
  let f : ℝ → ℂ := fun t => ∑ i, d i * Complex.exp ((Complex.I * w i - ε) * t)
  have heq (t : ℝ) : f t * (t ^ (-1 : ℝ) : ℝ) =
      weightedPhaseSum d w t * (Real.exp (-(ε * t)) : ℝ) := by
    rw [damped_weighted_eq_sum]
    dsimp only [f]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hi : IntegrableOn (fun t : ℝ => f t * (t ^ (-(0 + 1 : ℝ)) : ℝ)) (Ioi 0) := by
    exact (integrable_damped_weighted d w hsum ε hε).congr_fun
      (fun t _ => by simpa only [zero_add] using (heq t).symm) measurableSet_Ioi
  have hm : Measurable f := by dsimp [f]; fun_prop
  have h := IntegralOriginalRepresentation.gamma_mul_integral_eq_laplace f 0
    (by norm_num) hm hi
  simp only [Real.Gamma_one, Complex.ofReal_one, one_mul, Real.rpow_zero, zero_add] at h
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => heq t)] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  calc
    _ = ∫ t : ℝ in Ioi 0, ∑ i, d i *
        (Complex.exp ((Complex.I * w i - ε) * t) * (Real.exp (-(s * t)) : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only [f]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, ∫ t : ℝ in Ioi 0, d i *
        (Complex.exp ((Complex.I * w i - ε) * t) * (Real.exp (-(s * t)) : ℝ)) :=
      integral_finsetSum Finset.univ (fun i _ =>
        (integrable_damped_phase_laplace (w i) s ε hs hε).const_mul (d i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul, IntegralOriginalSourceBase.integral_damped_phase_laplace (w i) s ε hs hε]

/-- Conditional ordinary convergence is linked to the actual deformed rational
Mellin integral at `p=0`; all integrals and Abel steps are proved above. -/
theorem exists_limit_mellin_pzero {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (hsum : (∑ i, d i) = 0) (hw : ∀ i, w i ≠ 0) :
    ∃ L : ℂ,
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, weightedPhaseSum d w t) atTop (𝓝 L) ∧
      Tendsto (fun ε : ℝ => ∫ s : ℝ in Ioi 0,
        ∑ i, d i * (1 / (((s + ε : ℝ) : ℂ) - Complex.I * w i)))
        (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨L, hL, hAbel⟩ := exists_limit_and_abel_pzero d w hsum hw
  refine ⟨L, hL, hAbel.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact damped_mellin_pzero d w hsum ε hε

end IntegralOriginalAbel


namespace IntegralOriginalPZero

open MeasureTheory Filter Topology Set

lemma rational_damped_eq_log {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (hsum : (∑ i, d i) = 0) (ε : ℝ) (hε : 0 < ε) :
    (∫ s : ℝ in Ioi 0, ∑ i, d i *
      (1 / (((s + ε : ℝ) : ℂ) - Complex.I * w i))) =
        -(∑ i, d i * Complex.log ((ε : ℂ) - Complex.I * w i)) := by
  classical
  let a : ι → ℂ := fun i => (ε : ℂ) - Complex.I * w i
  have ha : ∀ i, 0 ≤ (a i).re := by intro i; simpa [a] using hε.le
  have hz : ∀ i, a i = 0 → d i = 0 := by
    intro i hi
    have hre := congrArg Complex.re hi
    have : ε = 0 := by simpa [a] using hre
    exact False.elim (hε.ne' this)
  have hi := IntegralRationalRecurrence.integrableOn_sum_div Finset.univ d a
    (fun i _ => ha i) (fun i _ => hz i) hsum
  have heq := IntegralRationalLogIntegral.integral_Ioi_eq_neg_log_sum d a ha hz hsum hi
  convert heq using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp only [a]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

lemma log_sum_tendsto {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (hw : ∀ i, w i ≠ 0) :
    Tendsto (fun ε : ℝ => -(∑ i, d i * Complex.log ((ε : ℂ) - Complex.I * w i)))
      (𝓝[>] 0) (𝓝 (-(∑ i, d i * Complex.log (-(Complex.I * w i))))) := by
  classical
  apply Tendsto.neg
  apply tendsto_finsetSum Finset.univ
  intro i _
  have harg : Tendsto (fun ε : ℝ => (ε : ℂ) - Complex.I * w i) (𝓝[>] 0)
      (𝓝 (-(Complex.I * w i))) := by
    have hc : Continuous (fun ε : ℝ => (ε : ℂ) - Complex.I * w i) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hslit : -(Complex.I * (w i : ℂ)) ∈ Complex.slitPlane := by
    right
    simpa using neg_ne_zero.mpr (hw i)
  exact ((continuousAt_clog hslit).tendsto.comp harg).const_mul (d i)

/-- Actual ordinary improper integral at p=0, including its full logarithmic
value. This is a proved finite-frequency formula, not a source assumption. -/
theorem tendsto_pzero_log {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (w : ι → ℝ) (hsum : (∑ i, d i) = 0) (hw : ∀ i, w i ≠ 0) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      IntegralOriginalAbel.weightedPhaseSum d w t) atTop
      (𝓝 (-(∑ i, d i * Complex.log (-(Complex.I * w i))))) := by
  obtain ⟨L, hL, hM⟩ := IntegralOriginalAbel.exists_limit_mellin_pzero d w hsum hw
  have hlog : Tendsto (fun ε : ℝ => ∫ s : ℝ in Ioi 0,
      ∑ i, d i * (1 / (((s + ε : ℝ) : ℂ) - Complex.I * w i)))
      (𝓝[>] 0) (𝓝 (-(∑ i, d i * Complex.log (-(Complex.I * w i))))) := by
    apply (log_sum_tendsto d w hw).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (rational_damped_eq_log d w hsum ε hε).symm
  have heq : L = -(∑ i, d i * Complex.log (-(Complex.I * w i))) :=
    tendsto_nhds_unique hM hlog
  rwa [heq] at hL

/-- The literal p=0 specialization of the approved original integrand has the
finite logarithmic value displayed here. The only domain restriction is the
actual approved nodal restriction `pLow n a < 0`. -/
theorem tendsto_original_pzero_log (n : ℕ) (a : ℝ) (hn : 1 ≤ n)
    (hp : IntegralOriginalConvergence.pLow n a < 0) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      IntegralOriginalConvergence.g n a t / ((t ^ (0 + 1 : ℝ) : ℝ) : ℂ)) atTop
      (𝓝 (-(∑ j : Fin (n + 1),
        ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
          Complex.log (-(Complex.I *
            (((a + (n : ℝ) - 2 * ((j : ℕ) : ℝ)) : ℝ) : ℂ)))))) := by
  classical
  let d : Fin (n + 1) → ℂ := fun j => (-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)
  let w : Fin (n + 1) → ℝ := fun j => a + (n : ℝ) - 2 * ((j : ℕ) : ℝ)
  have hsum : (∑ j, d j) = 0 := by
    simpa only [pow_zero, mul_one, d] using
      IntegralFrequencyCancellation.frequency_power_sum_fin n 0 (by omega) a
  have ha : ¬ ∃ j ≤ n, a = 2 * (j : ℝ) - n := by
    intro ha
    simp only [IntegralOriginalConvergence.pLow, if_pos ha] at hp
    exact lt_irrefl _ hp
  have hw (j : Fin (n + 1)) : w j ≠ 0 := by
    intro h
    apply ha
    exact ⟨j, Nat.le_of_lt_succ j.isLt, by dsimp [w] at h; linarith⟩
  have h := tendsto_pzero_log d w hsum hw
  apply h.congr'
  apply Eventually.of_forall
  intro T
  apply intervalIntegral.integral_congr
  intro t _
  unfold IntegralOriginalAbel.weightedPhaseSum IntegralOriginalAbel.phaseSum
  have hg : (∑ j, d j * Complex.exp (Complex.I * w j * t)) =
      IntegralOriginalConvergence.g n a t := by
    simpa only [d, w, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_natCast, Complex.ofReal_ofNat] using
      (IntegralOriginalConvergence.g_eq_sum n a t).symm
  rw [hg, Real.rpow_neg_one, Complex.ofReal_inv]
  simp only [zero_add, Real.rpow_one, div_eq_mul_inv]

end IntegralOriginalPZero


namespace IntegralFrequencyLogPhase

open ComplexConjugate IntegralBinomialLogPhase

/-- Exact original Fourier frequencies match the integer Cauchy logarithmic boundary.
The outer minus sign from the Mellin cutoff is deliberately not built in. -/
theorem frequency_pow_log_phase (n r : ℕ) (hr : r < n) (a : ℝ)
    (hnodes : r ≠ 0 ∨ ∀ j ∈ Finset.range (n+1), ((n : ℝ)+a)/2 ≠ (j : ℝ)) :
    (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
      (Complex.I * (((a+(n : ℝ)-2*((j : ℕ) : ℝ)) : ℝ) : ℂ))^r *
        Complex.log (-Complex.I * (((a+(n : ℝ)-2*((j : ℕ) : ℝ)) : ℝ) : ℂ))) =
    ((2 : ℂ)*Complex.I)^r * conj
      (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
        (((((n : ℝ)+a)/2-((j : ℕ) : ℝ)) : ℝ) : ℂ)^r *
          Complex.log (((((j : ℕ) : ℝ)-((n : ℝ)+a)/2) : ℝ) : ℂ)) := by
  let x : ℝ := ((n : ℝ)+a)/2
  have harg (j : ℕ) : -Complex.I * (((a+(n : ℝ)-2*(j : ℝ)) : ℝ) : ℂ) =
      (2 : ℂ)*Complex.I*(((j : ℝ)-x : ℝ) : ℂ) := by
    dsimp only [x]
    push_cast
    ring
  have hβ (j : ℕ) : Complex.I * (((a+(n : ℝ)-2*(j : ℝ)) : ℝ) : ℂ) =
      -((2 : ℂ)*Complex.I*(((j : ℝ)-x : ℝ) : ℂ)) := by
    dsimp only [x]
    push_cast
    ring
  have hsource :
      (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
        (Complex.I * (((a+(n : ℝ)-2*((j : ℕ) : ℝ)) : ℝ) : ℂ))^r *
          Complex.log (-Complex.I * (((a+(n : ℝ)-2*((j : ℕ) : ℝ)) : ℝ) : ℂ))) =
      (-1 : ℂ)^r *
        (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
          ((2 : ℂ)*Complex.I*((((j : ℕ) : ℝ)-x : ℝ) : ℂ))^r *
            Complex.log ((2 : ℂ)*Complex.I*((((j : ℕ) : ℝ)-x : ℝ) : ℂ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [harg, hβ, neg_pow ((2 : ℂ)*Complex.I*((((j : ℕ) : ℝ)-x : ℝ) : ℂ)) r]
    ring
  have hflip :
      (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
        (((x-((j : ℕ) : ℝ)) : ℝ) : ℂ)^r *
          Complex.log (((((j : ℕ) : ℝ)-x) : ℝ) : ℂ)) =
      (-1 : ℂ)^r *
        (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
          (((((j : ℕ) : ℝ)-x) : ℝ) : ℂ)^r *
            Complex.log (((((j : ℕ) : ℝ)-x) : ℝ) : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have he : (((x-((j : ℕ) : ℝ)) : ℝ) : ℂ) =
        -(((((j : ℕ) : ℝ)-x) : ℝ) : ℂ) := by push_cast; ring
    rw [he, neg_pow (((((j : ℕ) : ℝ)-x) : ℝ) : ℂ) r]
    ring
  change _ = ((2 : ℂ)*Complex.I)^r * conj
    (∑ j : Fin (n+1), ((-1 : ℂ)^(j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
      (((x-((j : ℕ) : ℝ)) : ℝ) : ℂ)^r * Complex.log (((((j : ℕ) : ℝ)-x) : ℝ) : ℂ))
  rw [hsource, binomial_log_sum_phase_fin n r hr x hnodes, hflip, map_mul, map_pow]
  simp only [map_neg, map_one]
  ring

end IntegralFrequencyLogPhase


namespace IntegralOriginalIntegerNonzero

open IntegralIntegerLogBoundary IntegralOriginalConvergence

lemma conj_principal_term_eq_scalarBoundary (r : ℕ) (u : ℝ) :
    conj ((u : ℂ) ^ r * Complex.log ((-u : ℝ) : ℂ)) = scalarBoundary r u := by
  rcases lt_trichotomy u 0 with hneg | rfl | hpos
  · rw [← Complex.ofReal_log (by linarith : 0 ≤ -u)]
    simp only [map_mul, map_pow, Complex.conj_ofReal, scalarBoundary,
      if_neg (not_lt.mpr hneg.le), sub_zero, abs_of_neg hneg]
  · simp [scalarBoundary]
  · rw [IntegralPowerPhase.log_ofReal_neg (neg_lt_zero.mpr hpos)]
    simp only [map_mul, map_pow, map_add, Complex.conj_ofReal, Complex.conj_I,
      neg_neg, scalarBoundary, if_pos hpos, abs_of_pos hpos]
    ring

lemma conj_principal_sum_eq_boundary (n r : ℕ) (x : ℝ) :
    conj (∑ j : Fin (n + 1), ((-1 : ℂ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
      (((x - ((j : ℕ) : ℝ)) : ℝ) : ℂ) ^ r *
        Complex.log (((((j : ℕ) : ℝ) - x) : ℝ) : ℂ)) =
      (realLogSum n r x : ℂ) - Complex.I * (Real.pi : ℂ) * (leftTail n r x : ℂ) := by
  rw [map_sum]
  calc
    _ = ∑ j : Fin (n + 1), (((-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ)) : ℂ) *
        scalarBoundary r (x - ((j : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hc : ((-1 : ℂ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℂ)) =
          (((-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ)) : ℂ) := by
        push_cast
        rfl
      have he : (((j : ℕ) : ℝ) - x) = -(x - ((j : ℕ) : ℝ)) := by ring
      rw [hc, he, mul_assoc, map_mul, conj_principal_term_eq_scalarBoundary]
      simp only [map_mul, map_pow, Complex.conj_ofReal]
    _ = ∑ j ∈ Finset.range (n + 1), (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        scalarBoundary r (x - (j : ℝ)) :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => (((-1 : ℝ) ^ j * (n.choose j : ℝ)) : ℂ) *
        scalarBoundary r (x - (j : ℝ))) (n + 1)
    _ = _ := sum_scalarBoundary_eq n r x

lemma frequency_pow_log_eq_boundary (n r : ℕ) (hrn : r < n) (a : ℝ)
    (hnodes : r ≠ 0 ∨ ∀ j ∈ Finset.range (n + 1), ((n : ℝ) + a) / 2 ≠ (j : ℝ)) :
    (∑ j : Fin (n + 1), ((-1 : ℂ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
      (Complex.I * (((a + (n : ℝ) - 2 * ((j : ℕ) : ℝ)) : ℝ) : ℂ)) ^ r *
        Complex.log (-Complex.I * (((a + (n : ℝ) - 2 * ((j : ℕ) : ℝ)) : ℝ) : ℂ))) =
      ((2 : ℂ) * Complex.I) ^ r *
        ((realLogSum n r (((n : ℝ) + a) / 2) : ℂ) -
          Complex.I * (Real.pi : ℂ) * (leftTail n r (((n : ℝ) + a) / 2) : ℂ)) := by
  rw [IntegralFrequencyLogPhase.frequency_pow_log_phase n r hrn a hnodes,
    conj_principal_sum_eq_boundary]

lemma frequency_pow_log_ne_zero (n r : ℕ) (hrn : r < n) (a : ℝ)
    (hnodes : r ≠ 0 ∨ ∀ j ∈ Finset.range (n + 1), ((n : ℝ) + a) / 2 ≠ (j : ℝ)) :
    (∑ j : Fin (n + 1), ((-1 : ℂ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
      (Complex.I * (((a + (n : ℝ) - 2 * ((j : ℕ) : ℝ)) : ℝ) : ℂ)) ^ r *
        Complex.log (-Complex.I * (((a + (n : ℝ) - 2 * ((j : ℕ) : ℝ)) : ℝ) : ℂ))) ≠ 0 := by
  rw [frequency_pow_log_eq_boundary n r hrn a hnodes]
  apply mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) Complex.I_ne_zero))
  by_cases hr0 : r = 0
  · subst r
    exact IntegralIntegerLogNonzero.boundary_zero_degree_ne_zero n hrn _
      (hnodes.resolve_left (fun h => h rfl))
  · exact IntegralIntegerLogNonzero.boundary_pos_degree_ne_zero n r
      (Nat.one_le_iff_ne_zero.mpr hr0) hrn _

lemma no_knots_of_pLow_lt_zero (n : ℕ) (a : ℝ) (hp : pLow n a < 0) :
    ∀ j ∈ Finset.range (n + 1), ((n : ℝ) + a) / 2 ≠ (j : ℝ) := by
  intro j hj he
  have hnode : ∃ j ≤ n, a = 2 * (j : ℝ) - n :=
    ⟨j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), by linarith⟩
  simp only [pLow, if_pos hnode] at hp
  exact (lt_irrefl (0 : ℝ)) hp

lemma integral_ne_zero_positive_integer (n r : ℕ) (hr : 1 ≤ r) (hrn : r < n) (a : ℝ) :
    (∫ t : ℝ in Ioi 0, g n a t / ((t ^ ((r : ℝ) + 1) : ℝ) : ℂ)) ≠ 0 := by
  have hfreq := frequency_pow_log_ne_zero n r hrn a
    (Or.inl (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr)))
  have hGI := IntegralPositiveIntegerOriginal.gamma_mul_original_integral_nat n r hr hrn a
  intro hzero
  rw [hzero, mul_zero] at hGI
  apply hfreq
  simpa only [neg_mul] using neg_eq_zero.mp hGI.symm

lemma exists_nonzero_limit_positive_integer (n r : ℕ) (hr : 1 ≤ r) (hrn : r < n) (a : ℝ) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto
      (fun R : ℝ => ∫ t in (0 : ℝ)..R, g n a t / ((t ^ ((r : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝 L) := by
  have hp : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hpn : (r : ℝ) < n := by exact_mod_cast hrn
  refine ⟨_, integral_ne_zero_positive_integer n r hr hrn a, ?_⟩
  exact intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_of_pos n (r : ℝ) a hp hpn) tendsto_id

lemma exists_nonzero_limit_zero (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (hp : pLow n a < 0) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto
      (fun R : ℝ => ∫ t in (0 : ℝ)..R, g n a t / ((t ^ (0 + 1 : ℝ) : ℝ) : ℂ))
      atTop (𝓝 L) := by
  have hnodes := no_knots_of_pLow_lt_zero n a hp
  have hfreq := frequency_pow_log_ne_zero n 0 (by omega : 0 < n) a (Or.inr hnodes)
  have hne :
      -(∑ j : Fin (n + 1), ((-1 : ℂ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℂ)) *
        Complex.log (-(Complex.I *
          (((a + (n : ℝ) - 2 * ((j : ℕ) : ℝ)) : ℝ) : ℂ)))) ≠ 0 := by
    apply neg_ne_zero.mpr
    simpa only [pow_zero, mul_one, neg_mul] using hfreq
  exact ⟨_, hne, IntegralOriginalPZero.tendsto_original_pzero_log n a hn hp⟩

/-- The literal approved integrand has a nonzero ordinary improper limit
for every admissible integer exponent. -/
theorem exists_nonzero_limit_integer (n r : ℕ) (hn : 1 ≤ n) (hrn : r < n) (a : ℝ)
    (hp : pLow n a < (r : ℝ)) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto
      (fun R : ℝ => ∫ t in (0 : ℝ)..R, g n a t / ((t ^ ((r : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝 L) := by
  by_cases hr0 : r = 0
  · subst r
    simpa only [Nat.cast_zero] using exists_nonzero_limit_zero n hn a (by simpa only [Nat.cast_zero] using hp)
  · exact exists_nonzero_limit_positive_integer n r (Nat.one_le_iff_ne_zero.mpr hr0) hrn a

end IntegralOriginalIntegerNonzero

/-!
Complete target assembly for MathOverflow 204459. The case split uses the
ordinary improper integral throughout, including its conditional range.
-/

theorem OMA.solution : type_of% @OMA.S_mo_204459.main := by
  classical
  intro n p a hn hpa hpn
  have hpa' : IntegralOriginalConvergence.pLow n a < p := by
    simpa only [OMA.S_mo_204459.pLow, IntegralOriginalConvergence.pLow] using hpa
  rcases lt_trichotomy p 0 with hneg | hzero | hpos
  · have hlow : (-1 : ℝ) ≤ IntegralOriginalConvergence.pLow n a := by
      unfold IntegralOriginalConvergence.pLow
      split_ifs <;> norm_num
    have hp : -1 < p := lt_of_le_of_lt hlow hpa'
    obtain ⟨L, hL, hlim⟩ :=
      IntegralOriginalNegativeNonzero.exists_nonzero_limit_negative n hn p a hp hneg hpa'
    refine ⟨L, hL, ?_⟩
    simpa only [OMA.S_mo_204459.g, IntegralOriginalConvergence.g] using hlim
  · subst p
    obtain ⟨L, hL, hlim⟩ :=
      IntegralOriginalIntegerNonzero.exists_nonzero_limit_integer n 0 hn
        (by omega : 0 < n) a (by simpa only [Nat.cast_zero] using hpa')
    refine ⟨L, hL, ?_⟩
    simpa only [Nat.cast_zero, OMA.S_mo_204459.g, IntegralOriginalConvergence.g] using hlim
  · by_cases hint : p = (Nat.floor p : ℝ)
    · have hrn : Nat.floor p < n := (Nat.floor_lt hpos.le).mpr hpn
      have hpar : IntegralOriginalConvergence.pLow n a < (Nat.floor p : ℝ) := by
        simpa only [← hint] using hpa'
      obtain ⟨L, hL, hlim⟩ :=
        IntegralOriginalIntegerNonzero.exists_nonzero_limit_integer n (Nat.floor p) hn hrn a hpar
      refine ⟨L, hL, ?_⟩
      simpa only [← hint, OMA.S_mo_204459.g, IntegralOriginalConvergence.g] using hlim
    · obtain ⟨L, hL, hlim⟩ :=
        IntegralOriginalPositiveNoninteger.exists_nonzero_limit n p a hpos hpn hint
      refine ⟨L, hL, ?_⟩
      simpa only [OMA.S_mo_204459.g, IntegralOriginalConvergence.g] using hlim
