import OMAReductions.R_Erdos114_erdos_114_R1_H2_R1
import Mathlib

/-!
# Structural Reduction of Erdős Problem 114 Step R1.H2.R1.H2 (Effective Line Deficit for n ≥ 256)

Following Teng Zhang (arXiv:2611.12830, Sections 3–7, Theorem `thm:line256`), we reduce the
effective affine-line Cauchy–Crofton deficit bound `> 4/5` for all degrees `n ≥ 256` into four
self-contained analytic hypotheses (each under the single-file size cap), proving all algebraic,
measure-theoretic, Maclaurin-binomial, Bernstein-growth, and critical-value assembly theorems
directly in this module:

1. **Affine target-line reduction to the real axis (`affine_line_slice_integral_eq`)**:
   Rotating `z ↦ e^{iψ/n} z` and translating/rotating the target line `(w₀, ψ) ↦ (0, 0)` preserves
   monicity, degree `n`, centering `coeff (n - 1) = 0`, and critical-value diameter `2`, while
   `π`-periodicity of the inner slice integral under `(x, h) ↦ (-x, -h)` makes the outer Bochner
   integral over `(0, π)` unconditionally invariant under angular shift `θ ↦ θ + ψ/n`.
2. **Maclaurin inequality and iterated-derivative high-part growth (`highPart_large_growth`)**:
   Using `Finset.prod_add` over `powersetCard`, we prove Vieta's centered root-sum identity and
   Maclaurin's symmetric-mean inequality, together with the falling-factorial coefficient ratio
   relating `G` to its monic `k`-th derivative, yielding `‖T_k(G)(z)‖ < 500 ρ^n` on `‖z‖ ≤ ρ`
   for `ρ ≥ 23/48` whenever the derivative-root `ℓ¹` sum is `< 229/100`.
3. **Bernstein exterior disk growth & Lipschitz critical-value confinement**:
   Via the maximum modulus principle applied to reciprocal polynomials `p.reverse`, we prove
   Bernstein's exterior growth bound `‖P(z)‖ ≤ M (‖z‖/r)^d` (`‖z‖ ≥ r`), confine all critical
   points of `G` to `‖ζ‖ < 19/20` by comparing `H3` and `H4`, and confine all critical values of
   `G` to an open disk of radius `1/4` around `(G - T_k(G))(0)`, contradicting critical-value
   diameter `2`.
-/

namespace OMA.R_Erdos114_erdos_114_R1_H2_R1_H2_R1

open Polynomial Complex MeasureTheory Filter Set Metric
open scoped Topology ENNReal

section PeriodicSliceInvariance

lemma integral_comp_neg_real (f : ℝ → ℝ) :
    (∫ h : ℝ, f (-h)) = ∫ h : ℝ, f h := by
  have mp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have emb := (MeasurableEquiv.neg ℝ).measurableEmbedding
  have h := mp.setIntegral_preimage_emb emb f Set.univ
  simpa [Measure.restrict_univ] using h

lemma Ioo_split_ae_eq {P c : ℝ} (hc0 : 0 < c) (hcP : c < P) :
    (Set.Ioo 0 c ∪ Set.Ioo c P : Set ℝ) =ᵐ[volume] Set.Ioo 0 P := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · have hsub : (Set.Ioo 0 c ∪ Set.Ioo c P) \ Set.Ioo 0 P = ∅ := by
      ext x
      constructor
      · rintro ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, hnot⟩
        · exact hnot ⟨h1, by linarith⟩
        · exact hnot ⟨by linarith, h2⟩
      · rintro ⟨⟩
    simp [hsub]
  · apply measure_mono_null (t := ({c} : Set ℝ))
    · rintro x ⟨⟨hx0, hxP⟩, hnot⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hnot (Or.inl ⟨hx0, hlt⟩)
      · exact hnot (Or.inr ⟨hgt, hxP⟩)
    · simp

lemma integral_Ioo_periodic_add_unit {P : ℝ} (_hP : 0 < P) (φ : ℝ → ℝ)
    (hper : Function.Periodic φ P) {r : ℝ} (hr0 : 0 ≤ r) (hrP : r < P) :
    (∫ θ in Set.Ioo 0 P, φ (θ + r)) = ∫ θ in Set.Ioo 0 P, φ θ := by
  rcases eq_or_lt_of_le hr0 with rfl | hrpos
  · simp
  · have hPr0 : 0 < P - r := by linarith
    have hPrP : P - r < P := by linarith
    have hae1 := Ioo_split_ae_eq hPr0 hPrP
    have hae2 := Ioo_split_ae_eq hrpos hrP
    have hdisj1 : Disjoint (Set.Ioo 0 (P - r)) (Set.Ioo (P - r) P) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => by linarith [hx1.2, hx2.1]
    have hdisj2 : Disjoint (Set.Ioo 0 r) (Set.Ioo r P) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => by linarith [hx1.2, hx2.1]
    have mp1 := measurePreserving_add_right (volume : Measure ℝ) r
    have emb1 := (MeasurableEquiv.addRight r).measurableEmbedding
    have hpre1 : (fun x : ℝ => x + r) ⁻¹' Set.Ioo r P = Set.Ioo 0 (P - r) := by
      ext x; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;>
        exact ⟨by linarith, by linarith⟩
    have hint1 : IntegrableOn (fun θ => φ (θ + r)) (Set.Ioo 0 (P - r)) ↔
        IntegrableOn φ (Set.Ioo r P) := by
      rw [← hpre1]; exact mp1.integrableOn_comp_preimage emb1
    have hset1 : (∫ θ in Set.Ioo 0 (P - r), φ (θ + r)) = ∫ y in Set.Ioo r P, φ y := by
      rw [← hpre1]; exact mp1.setIntegral_preimage_emb emb1 φ (Set.Ioo r P)
    have mp2 := measurePreserving_add_right (volume : Measure ℝ) (r - P)
    have emb2 := (MeasurableEquiv.addRight (r - P)).measurableEmbedding
    have hpre2 : (fun x : ℝ => x + (r - P)) ⁻¹' Set.Ioo 0 r = Set.Ioo (P - r) P := by
      ext x; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;>
        exact ⟨by linarith, by linarith⟩
    have hfun2 : (fun θ : ℝ => φ (θ + r)) = (fun θ : ℝ => φ (θ + (r - P))) := by
      funext θ
      have hp := hper (θ + (r - P))
      have heq : θ + (r - P) + P = θ + r := by ring
      rw [heq] at hp
      exact hp
    have hint2 : IntegrableOn (fun θ => φ (θ + r)) (Set.Ioo (P - r) P) ↔
        IntegrableOn φ (Set.Ioo 0 r) := by
      rw [hfun2, ← hpre2]; exact mp2.integrableOn_comp_preimage emb2
    have hset2 : (∫ θ in Set.Ioo (P - r) P, φ (θ + r)) = ∫ y in Set.Ioo 0 r, φ y := by
      rw [hfun2, ← hpre2]; exact mp2.setIntegral_preimage_emb emb2 φ (Set.Ioo 0 r)
    have hint_iff : IntegrableOn (fun θ => φ (θ + r)) (Set.Ioo 0 P) ↔
        IntegrableOn φ (Set.Ioo 0 P) := by
      rw [← integrableOn_congr_set_ae hae1, integrableOn_union, hint1, hint2,
        ← integrableOn_congr_set_ae hae2, integrableOn_union, and_comm]
    by_cases hint : IntegrableOn φ (Set.Ioo 0 P)
    · have hint_shift : IntegrableOn (fun θ => φ (θ + r)) (Set.Ioo 0 P) := hint_iff.mpr hint
      have hi12 : IntegrableOn (fun θ => φ (θ + r)) (Set.Ioo 0 (P - r)) ∧
          IntegrableOn (fun θ => φ (θ + r)) (Set.Ioo (P - r) P) := by
        rwa [← integrableOn_congr_set_ae hae1, integrableOn_union] at hint_shift
      have hj12 : IntegrableOn φ (Set.Ioo 0 r) ∧ IntegrableOn φ (Set.Ioo r P) := by
        rwa [← integrableOn_congr_set_ae hae2, integrableOn_union] at hint
      rw [← setIntegral_congr_set hae1, setIntegral_union hdisj1 measurableSet_Ioo hi12.1 hi12.2,
        hset1, hset2, add_comm, ← setIntegral_union hdisj2 measurableSet_Ioo hj12.1 hj12.2,
        setIntegral_congr_set hae2]
    · have hnot_shift : ¬ IntegrableOn (fun θ => φ (θ + r)) (Set.Ioo 0 P) :=
        fun h => hint (hint_iff.mp h)
      rw [MeasureTheory.integral_undef hnot_shift, MeasureTheory.integral_undef hint]

lemma integral_Ioo_periodic_add {P : ℝ} (hP : 0 < P) (φ : ℝ → ℝ)
    (hper : Function.Periodic φ P) (α : ℝ) :
    (∫ θ in Set.Ioo 0 P, φ (θ + α)) = ∫ θ in Set.Ioo 0 P, φ θ := by
  let m : ℤ := ⌊α / P⌋
  let r : ℝ := α - (m : ℝ) * P
  have hr0 : 0 ≤ r := by
    have h1 : (m : ℝ) ≤ α / P := Int.floor_le (α / P)
    have h2 : (m : ℝ) * P ≤ α := (le_div_iff₀ hP).mp h1
    dsimp [r]; linarith
  have hrP : r < P := by
    have h1 : α / P < (m : ℝ) + 1 := Int.lt_floor_add_one (α / P)
    have h2 : α < ((m : ℝ) + 1) * P := (div_lt_iff₀ hP).mp h1
    dsimp [r]; linarith
  have hfun : (fun θ : ℝ => φ (θ + α)) = (fun θ : ℝ => φ (θ + r)) := by
    funext θ
    have hm := hper.int_mul m (θ + r)
    have heq : θ + r + (m : ℝ) * P = θ + α := by dsimp [r]; ring
    rw [heq] at hm
    exact hm
  rw [hfun]
  exact integral_Ioo_periodic_add_unit hP φ hper hr0 hrP

lemma ncard_neg_preimage (Q : ℝ → Prop) :
    {x : ℝ | Q (-x)}.ncard = {x : ℝ | Q x}.ncard := by
  have heq : {x : ℝ | Q (-x)} = Neg.neg '' {x : ℝ | Q x} := by
    ext x
    change Q (-x) ↔ x ∈ Neg.neg '' {y : ℝ | Q y}
    rw [Set.mem_image]
    exact ⟨fun h => ⟨-x, h, neg_neg x⟩, fun ⟨y, hy, hyx⟩ => by rwa [← hyx, neg_neg]⟩
  rw [heq, Set.ncard_image_of_injective _ neg_injective]

lemma affine_line_slice_reduction {n : ℕ} (hn : 2 ≤ n) (F : ℂ[X]) (hF : F.Monic)
    (hdF : F.natDegree = n) (hcF : F.coeff (n - 1) = 0)
    (hmax : ∃ x y : ℂ, F.derivative.IsRoot x ∧ F.derivative.IsRoot y ∧ ‖F.eval x - F.eval y‖ = 2)
    (w₀ : ℂ) (ψ : ℝ) :
    ∃ G : ℂ[X], G.Monic ∧ G.natDegree = n ∧ G.coeff (n - 1) = 0 ∧
      (∃ x y : ℂ, G.derivative.IsRoot x ∧ G.derivative.IsRoot y ∧ ‖G.eval x - G.eval y‖ = 2) ∧
      ((1 / 2 : ℝ) * ∫ θ in Set.Ioo (0 : ℝ) Real.pi, ∫ h : ℝ, ((n : ℝ) -
        (({x : ℝ | (Complex.exp (-(ψ : ℂ) * Complex.I) *
          (F.eval (Complex.exp ((θ : ℂ) * Complex.I) * ((x : ℂ) + (h : ℂ) * Complex.I)) - w₀)).im = 0}).ncard : ℝ))) =
      ((1 / 2 : ℝ) * ∫ θ in Set.Ioo (0 : ℝ) Real.pi, ∫ h : ℝ, ((n : ℝ) -
        (({x : ℝ | (G.eval (Complex.exp ((θ : ℂ) * Complex.I) * ((x : ℂ) + (h : ℂ) * Complex.I))).im = 0}).ncard : ℝ))) := by
  have hn0 : n ≠ 0 := by omega
  have hn_pos : 0 < n := by omega
  have hnR0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  let α : ℝ := ψ / (n : ℝ)
  let u : ℂ := Complex.exp (-(ψ : ℂ) * Complex.I)
  let v : ℂ := Complex.exp ((α : ℂ) * Complex.I)
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [show -(ψ : ℂ) * Complex.I = ((-ψ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I (-ψ)
  have hv_norm : ‖v‖ = 1 := Complex.norm_exp_ofReal_mul_I α
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu_norm
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv_norm
  have hvn : u * v ^ n = 1 := by
    dsimp [u, v, α]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    have hexp0 : -(ψ : ℂ) * Complex.I + (n : ℕ) * (((ψ / (n : ℝ) : ℝ) : ℂ) * Complex.I) = 0 := by
      have hnC0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      push_cast
      field_simp
      ring
    rw [hexp0, Complex.exp_zero]
  let G : ℂ[X] := C u * (F - C w₀).comp (C v * X)
  have hFw_deg : (F - C w₀).natDegree = n := by
    rw [natDegree_sub_C, hdF]
  have hFw_lc : (F - C w₀).leadingCoeff = 1 := by
    have hlt : (C w₀).degree < F.degree :=
      degree_C_le.trans_lt (by rw [degree_eq_natDegree hF.ne_zero, hdF]; exact_mod_cast hn_pos)
    rw [leadingCoeff_sub_of_degree_lt hlt, hF.leadingCoeff]
  have hCvX_deg : (C v * X).natDegree = 1 := natDegree_C_mul_X v hv0
  have hG_deg : G.natDegree = n := by
    dsimp [G]
    rw [natDegree_C_mul hu0, natDegree_comp, hFw_deg, hCvX_deg, mul_one]
  have hG_monic : G.Monic := by
    change G.leadingCoeff = 1
    dsimp [G]
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp (by rw [hCvX_deg]; exact one_ne_zero),
      hFw_lc, hFw_deg, leadingCoeff_C_mul_X, one_mul, hvn]
  have hG_center : G.coeff (n - 1) = 0 := by
    dsimp [G]
    rw [coeff_C_mul, (F - C w₀).comp_eq_sum_left, Polynomial.sum_def, finsetSum_coeff]
    have hsum0 : ∑ i ∈ (F - C w₀).support,
        (C ((F - C w₀).coeff i) * (C v * X) ^ i).coeff (n - 1) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul, coeff_X_pow]
      split_ifs with hi
      · subst hi
        have hn1 : n - 1 ≠ 0 := by omega
        simp [coeff_sub, coeff_C, hn1, hcF]
      · ring
    rw [hsum0, mul_zero]
  have hG_eval : ∀ z : ℂ, G.eval z = u * (F.eval (v * z) - w₀) := by
    intro z
    simp [G, eval_comp]
  have hG_deriv_root : ∀ z : ℂ, G.derivative.IsRoot z ↔ F.derivative.IsRoot (v * z) := by
    intro z
    have hder : G.derivative = C (u * v) * F.derivative.comp (C v * X) := by
      dsimp [G]
      rw [derivative_C_mul, derivative_comp, derivative_sub, derivative_C, sub_zero,
        derivative_C_mul, derivative_X, mul_one, C_mul, mul_assoc]
    simp only [IsRoot.def, hder, eval_mul, eval_C, eval_comp, eval_X, mul_eq_zero,
      mul_ne_zero hu0 hv0, false_or]
  obtain ⟨x₀, y₀, hx₀, hy₀, hdist₀⟩ := hmax
  have hG_max : ∃ x y : ℂ, G.derivative.IsRoot x ∧ G.derivative.IsRoot y ∧
      ‖G.eval x - G.eval y‖ = 2 := by
    refine ⟨v⁻¹ * x₀, v⁻¹ * y₀, ?_, ?_, ?_⟩
    · rw [hG_deriv_root, mul_inv_cancel_left₀ hv0]; exact hx₀
    · rw [hG_deriv_root, mul_inv_cancel_left₀ hv0]; exact hy₀
    · rw [hG_eval, hG_eval, mul_inv_cancel_left₀ hv0, mul_inv_cancel_left₀ hv0]
      have hsub : u * (F.eval x₀ - w₀) - u * (F.eval y₀ - w₀) = u * (F.eval x₀ - F.eval y₀) := by
        ring
      rw [hsub, norm_mul, hu_norm, one_mul, hdist₀]
  refine ⟨G, hG_monic, hG_deg, hG_center, hG_max, ?_⟩
  let Φ : ℝ → ℝ := fun θ => ∫ h : ℝ, ((n : ℝ) -
    (({x : ℝ | (u * (F.eval (Complex.exp ((θ : ℂ) * Complex.I) *
      ((x : ℂ) + (h : ℂ) * Complex.I)) - w₀)).im = 0}).ncard : ℝ))
  have hΦ_per : Function.Periodic Φ Real.pi := by
    intro θ
    dsimp only [Φ]
    have hpt : ∀ h : ℝ,
        {x : ℝ | (u * (F.eval (Complex.exp (((θ + Real.pi : ℝ) : ℂ) * Complex.I) *
          ((x : ℂ) + (h : ℂ) * Complex.I)) - w₀)).im = 0}.ncard =
        {x : ℝ | (u * (F.eval (Complex.exp ((θ : ℂ) * Complex.I) *
          ((x : ℂ) + ((-h : ℝ) : ℂ) * Complex.I)) - w₀)).im = 0}.ncard := by
      intro h
      have hexp : ∀ x : ℝ,
          Complex.exp (((θ + Real.pi : ℝ) : ℂ) * Complex.I) * ((x : ℂ) + (h : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) * (((-x : ℝ) : ℂ) + ((-h : ℝ) : ℂ) * Complex.I) := by
        intro x
        push_cast
        rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
        ring
      simp_rw [hexp]
      exact ncard_neg_preimage (fun x : ℝ =>
        (u * (F.eval (Complex.exp ((θ : ℂ) * Complex.I) *
          ((x : ℂ) + ((-h : ℝ) : ℂ) * Complex.I)) - w₀)).im = 0)
    simp_rw [hpt]
    exact integral_comp_neg_real (fun h : ℝ => (n : ℝ) -
      (({x : ℝ | (u * (F.eval (Complex.exp ((θ : ℂ) * Complex.I) *
        ((x : ℂ) + (h : ℂ) * Complex.I)) - w₀)).im = 0}).ncard : ℝ))
  have hG_slice : ∀ θ : ℝ,
      (∫ h : ℝ, ((n : ℝ) -
        (({x : ℝ | (G.eval (Complex.exp ((θ : ℂ) * Complex.I) *
          ((x : ℂ) + (h : ℂ) * Complex.I))).im = 0}).ncard : ℝ))) = Φ (θ + α) := by
    intro θ
    dsimp only [Φ]
    congr 1; funext h; congr 1; congr 1; congr 1; ext x
    change (G.eval (Complex.exp ((θ : ℂ) * Complex.I) * ((x : ℂ) + (h : ℂ) * Complex.I))).im = 0 ↔
      (u * (F.eval (Complex.exp (((θ + α : ℝ) : ℂ) * Complex.I) *
        ((x : ℂ) + (h : ℂ) * Complex.I)) - w₀)).im = 0
    rw [hG_eval]
    have hvrot : v * (Complex.exp ((θ : ℂ) * Complex.I) * ((x : ℂ) + (h : ℂ) * Complex.I)) =
        Complex.exp (((θ + α : ℝ) : ℂ) * Complex.I) * ((x : ℂ) + (h : ℂ) * Complex.I) := by
      dsimp [v]
      rw [← mul_assoc]
      congr 1
      push_cast
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [hvrot]
  simp_rw [hG_slice]
  rw [integral_Ioo_periodic_add Real.pi_pos Φ hΦ_per α]

end PeriodicSliceInvariance

section MaclaurinAndHighPart

lemma esymm_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (k : ℕ) :
    0 ≤ ∑ t ∈ s.powersetCard k, ∏ i ∈ t, a i :=
  Finset.sum_nonneg fun _ ht =>
    Finset.prod_nonneg fun i hi => ha i ((Finset.mem_powersetCard.mp ht).1 hi)

lemma esymm_insert_succ {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    {i : ι} (hi : i ∉ s) (k : ℕ) :
    (∑ t ∈ (insert i s).powersetCard (k + 1), ∏ l ∈ t, a l) =
      (∑ t ∈ s.powersetCard (k + 1), ∏ l ∈ t, a l) +
        a i * ∑ t ∈ s.powersetCard k, ∏ l ∈ t, a l := by
  have hdisj : Disjoint (s.powersetCard (k + 1)) ((s.powersetCard k).image (insert i)) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    have hnot : i ∉ u := fun h => hi ((Finset.mem_powersetCard.mp hu1).1 h)
    rcases Finset.mem_image.mp hu2 with ⟨t, _, rfl⟩
    exact hnot (Finset.mem_insert_self i t)
  rw [Finset.powersetCard_succ_insert hi, show k.succ = k + 1 from rfl,
    Finset.sum_union hdisj, Finset.sum_image, Finset.mul_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro t ht
    have hit : i ∉ t := fun h => hi ((Finset.mem_powersetCard.mp ht).1 h)
    exact Finset.prod_insert hit
  · intro t₁ ht₁ t₂ ht₂ heq
    have hit₁ : i ∉ t₁ := fun h => hi ((Finset.mem_powersetCard.mp ht₁).1 h)
    have hit₂ : i ∉ t₂ := fun h => hi ((Finset.mem_powersetCard.mp ht₂).1 h)
    have h1 := congrArg (fun u : Finset ι => u.erase i) heq
    simpa [Finset.erase_insert hit₁, Finset.erase_insert hit₂] using h1

lemma esymm_erase_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) (k : ℕ) :
    (∑ i ∈ s, ∑ t ∈ (s.erase i).powersetCard k, ∏ l ∈ t, a l) =
      (((s.card - k : ℕ) : ℝ)) * ∑ t ∈ s.powersetCard k, ∏ l ∈ t, a l := by
  have h1 : ∀ i ∈ s,
      (∑ t ∈ (s.erase i).powersetCard k, ∏ l ∈ t, a l) =
      ∑ t ∈ s.powersetCard k, if i ∉ t then ∏ l ∈ t, a l else 0 := by
    intro i _
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext t
      simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_erase]
      exact ⟨fun ⟨⟨hts, hit⟩, hc⟩ => ⟨⟨hts, hc⟩, hit⟩,
             fun ⟨⟨hts, hc⟩, hit⟩ => ⟨⟨hts, hit⟩, hc⟩⟩
    · intros; rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨hts, htc⟩ := Finset.mem_powersetCard.mp ht
  have hfil : s.filter (fun i => i ∉ t) = s \ t := by
    ext i; simp [Finset.mem_sdiff]
  have hsub : (∑ x ∈ s, if x ∉ t then ∏ l ∈ t, a l else 0) =
      ((s \ t).card : ℝ) * ∏ l ∈ t, a l := by
    rw [← Finset.sum_filter, hfil, Finset.sum_const, nsmul_eq_mul]
  rw [hsub, Finset.card_sdiff, Finset.inter_eq_left.mpr hts, htc]

lemma esymm_weighted_erase_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) (k : ℕ) :
    (∑ i ∈ s, a i * ∑ t ∈ (s.erase i).powersetCard k, ∏ l ∈ t, a l) =
      ((k + 1 : ℕ) : ℝ) * ∑ u ∈ s.powersetCard (k + 1), ∏ l ∈ u, a l := by
  have h1 : ∀ i ∈ s,
      a i * (∑ t ∈ (s.erase i).powersetCard k, ∏ l ∈ t, a l) =
      ∑ u ∈ s.powersetCard (k + 1), if i ∈ u then ∏ l ∈ u, a l else 0 := by
    intro i hi
    rw [Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_bij (fun t _ => insert i t) ?_ ?_ ?_ ?_
    · intro t ht
      obtain ⟨hts, htc⟩ := Finset.mem_powersetCard.mp ht
      have hit : i ∉ t := (Finset.subset_erase.mp hts).2
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.insert_subset hi (Finset.subset_erase.mp hts).1,
        by rw [Finset.card_insert_of_notMem hit, htc]⟩, Finset.mem_insert_self i t⟩
    · intro t₁ ht₁ t₂ ht₂ heq
      have hit₁ : i ∉ t₁ := (Finset.subset_erase.mp (Finset.mem_powersetCard.mp ht₁).1).2
      have hit₂ : i ∉ t₂ := (Finset.subset_erase.mp (Finset.mem_powersetCard.mp ht₂).1).2
      have h' := congrArg (fun u : Finset ι => u.erase i) heq
      simpa [Finset.erase_insert hit₁, Finset.erase_insert hit₂] using h'
    · intro u hu
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hu
      obtain ⟨⟨hus, huc⟩, hiu⟩ := hu
      refine ⟨u.erase i, ?_, Finset.insert_erase hiu⟩
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.erase_subset_erase i hus, by rw [Finset.card_erase_of_mem hiu, huc]; omega⟩
    · intro t ht
      have hit : i ∉ t := (Finset.subset_erase.mp (Finset.mem_powersetCard.mp ht).1).2
      rw [Finset.prod_insert hit]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨hus, huc⟩ := Finset.mem_powersetCard.mp hu
  have hsub : (∑ i ∈ s, if i ∈ u then ∏ l ∈ u, a l else 0) =
      (u.card : ℝ) * ∏ l ∈ u, a l := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hus,
      Finset.sum_const, nsmul_eq_mul]
  rw [hsub, huc]

lemma esymm_erase_diff {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) (k : ℕ) :
    (∑ t ∈ (s.erase i).powersetCard (k + 1), ∏ l ∈ t, a l) -
      (∑ t ∈ (s.erase j).powersetCard (k + 1), ∏ l ∈ t, a l) =
      (a j - a i) * ∑ t ∈ ((s.erase i).erase j).powersetCard k, ∏ l ∈ t, a l := by
  have hji : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hij' : i ∈ s.erase j := Finset.mem_erase.mpr ⟨hij, hi⟩
  have h1 := esymm_insert_succ ((s.erase i).erase j) a (Finset.notMem_erase j (s.erase i)) k
  have h2 := esymm_insert_succ ((s.erase j).erase i) a (Finset.notMem_erase i (s.erase j)) k
  rw [Finset.insert_erase hji] at h1
  rw [Finset.insert_erase hij', Finset.erase_right_comm] at h2
  linear_combination h1 - h2

lemma esymm_mean_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (k : ℕ) (hk : k ≤ s.card) :
    (∑ t ∈ s.powersetCard k, ∏ i ∈ t, a i) ≤
      (s.card.choose k : ℝ) * ((∑ i ∈ s, a i) / (s.card : ℝ)) ^ k := by
  have hcard_pos : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  have hS : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ s.card := by omega
    have hkR : (k : ℝ) ≤ s.card := Nat.cast_le.mpr hk'
    have hi := ih hk'
    let e : ι → ℝ := fun i => ∑ t ∈ (s.erase i).powersetCard k, ∏ l ∈ t, a l
    have hp : ∀ i ∈ s, ∀ j ∈ s, (a i - a j) * (e i - e j) ≤ 0 := by
      intro i his j hjs
      by_cases hij : i = j
      · subst hij; simp
      · cases k with
        | zero => simp [e]
        | succ k' =>
          dsimp only [e]
          rw [esymm_erase_diff s a his hjs hij k']
          have hnn := esymm_nonneg ((s.erase i).erase j) a
            (fun l hl => ha l (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))) k'
          nlinarith [mul_nonneg (sq_nonneg (a i - a j)) hnn]
    have hcov0 := Finset.sum_nonpos fun i his => Finset.sum_nonpos fun j hjs => hp i his j hjs
    have hcov_id : (∑ i ∈ s, ∑ j ∈ s, (a i - a j) * (e i - e j)) =
        2 * ((s.card : ℝ) * (∑ i ∈ s, a i * e i) - (∑ i ∈ s, a i) * (∑ i ∈ s, e i)) := by
      simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring_nf
      rw [← Finset.mul_sum]
      ring
    rw [hcov_id] at hcov0
    have hcov : (s.card : ℝ) * (∑ i ∈ s, a i * e i) ≤ (∑ i ∈ s, a i) * (∑ i ∈ s, e i) := by
      linarith
    dsimp only [e] at hcov
    rw [esymm_weighted_erase_sum s a k, esymm_erase_sum s a k] at hcov
    push_cast [Nat.cast_sub hk'] at hcov
    have hchoose : ((k : ℝ) + 1) * (s.card.choose (k + 1) : ℝ) =
        ((s.card : ℝ) - k) * (s.card.choose k : ℝ) := by
      have hc := congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_succ_right_eq s.card k)
      push_cast [Nat.cast_sub hk'] at hc
      linarith
    have hmul := mul_le_mul_of_nonneg_left hi (mul_nonneg (sub_nonneg.mpr hkR) hS)
    have hstep : (s.card : ℝ) * (((k : ℝ) + 1) * ∑ u ∈ s.powersetCard (k + 1), ∏ l ∈ u, a l) ≤
        ((s.card : ℝ) - k) * (∑ i ∈ s, a i) *
          ((s.card.choose k : ℝ) * ((∑ i ∈ s, a i) / (s.card : ℝ)) ^ k) := by
      nlinarith
    have hrhs : ((s.card : ℝ) - k) * (∑ i ∈ s, a i) *
        ((s.card.choose k : ℝ) * ((∑ i ∈ s, a i) / (s.card : ℝ)) ^ k) =
        (s.card : ℝ) * ((k : ℝ) + 1) *
          ((s.card.choose (k + 1) : ℝ) * ((∑ i ∈ s, a i) / (s.card : ℝ)) ^ (k + 1)) := by
      rw [pow_succ]
      have h1 : (s.card : ℝ) * ((k : ℝ) + 1) *
          ((s.card.choose (k + 1) : ℝ) * (((∑ i ∈ s, a i) / (s.card : ℝ)) ^ k *
            ((∑ i ∈ s, a i) / (s.card : ℝ)))) =
          (((k : ℝ) + 1) * (s.card.choose (k + 1) : ℝ)) * (∑ i ∈ s, a i) *
            ((∑ i ∈ s, a i) / (s.card : ℝ)) ^ k := by
        field_simp
      rw [h1, hchoose]
      ring
    have hpos : 0 < (s.card : ℝ) * ((k : ℝ) + 1) := by positivity
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith

lemma monic_coeff_eq_powersetCard {m : ℕ} (p : ℂ[X]) (hp : p.Monic) (_hdeg : p.natDegree = m)
    (ξ : Fin m → ℂ) (hξ : (List.ofFn ξ : Multiset ℂ) = p.roots) (j : ℕ) (hj : j ≤ m) :
    p.coeff (m - j) = ∑ t ∈ (Finset.univ : Finset (Fin m)).powersetCard j, ∏ i ∈ t, (-ξ i) := by
  have hfac : p = ∏ i : Fin m, (X - C (ξ i)) := by
    have hs := (IsAlgClosed.splits p).eq_prod_roots_of_monic hp
    rw [← hξ, Multiset.map_coe, List.map_ofFn, Multiset.prod_coe, List.prod_ofFn] at hs
    exact hs
  rw [hfac]
  have hexp : (∏ i ∈ (Finset.univ : Finset (Fin m)), (C (-ξ i) + X)) =
      ∑ t ∈ (Finset.univ : Finset (Fin m)).powerset,
        C (∏ i ∈ t, (-ξ i)) * X ^ (m - t.card) := by
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    have hcard : ((Finset.univ : Finset (Fin m)) \ t).card = m - t.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ t),
        Finset.card_univ, Fintype.card_fin]
    rw [← map_prod C, Finset.prod_const, hcard]
  have hrew : (∏ i : Fin m, (X - C (ξ i))) =
      ∏ i ∈ (Finset.univ : Finset (Fin m)), (C (-ξ i) + X) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [map_neg, sub_eq_add_neg, add_comm]
  rw [hrew, hexp, finsetSum_coeff]
  simp_rw [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_powersetCard]
    have htle : t.card ≤ m := by
      simpa [Fintype.card_fin] using Finset.card_le_univ t
    omega
  · intros; rfl

lemma centered_roots_sum_zero {m : ℕ} (hm : 1 ≤ m) (p : ℂ[X]) (hp : p.Monic)
    (hdeg : p.natDegree = m) (hc : p.coeff (m - 1) = 0)
    (ξ : Fin m → ℂ) (hξ : (List.ofFn ξ : Multiset ℂ) = p.roots) :
    (∑ i : Fin m, ξ i) = 0 := by
  have h1 := monic_coeff_eq_powersetCard p hp hdeg ξ hξ 1 hm
  rw [hc, Finset.powersetCard_one, Finset.sum_map] at h1
  simp only [Function.Embedding.coeFn_mk, Finset.prod_singleton, Finset.sum_neg_distrib,
    eq_comm, neg_eq_zero] at h1
  exact h1

lemma monic_coeff_root_mean_bound {m : ℕ} (hm : 0 < m) (p : ℂ[X]) (hp : p.Monic)
    (hdeg : p.natDegree = m) (ξ : Fin m → ℂ) (hξ : (List.ofFn ξ : Multiset ℂ) = p.roots)
    (j : ℕ) (hj : j ≤ m) :
    ‖p.coeff (m - j)‖ ≤ (m.choose j : ℝ) * ((∑ i : Fin m, ‖ξ i‖) / (m : ℝ)) ^ j := by
  rw [monic_coeff_eq_powersetCard p hp hdeg ξ hξ j hj]
  have hs : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  calc ‖∑ t ∈ (Finset.univ : Finset (Fin m)).powersetCard j, ∏ i ∈ t, (-ξ i)‖
      ≤ ∑ t ∈ (Finset.univ : Finset (Fin m)).powersetCard j, ‖∏ i ∈ t, (-ξ i)‖ :=
        norm_sum_le _ _
    _ = ∑ t ∈ (Finset.univ : Finset (Fin m)).powersetCard j, ∏ i ∈ t, ‖ξ i‖ := by
        apply Finset.sum_congr rfl
        intro t _
        rw [norm_prod]
        exact Finset.prod_congr rfl fun i _ => norm_neg (ξ i)
    _ ≤ (m.choose j : ℝ) * ((∑ i : Fin m, ‖ξ i‖) / (m : ℝ)) ^ j := by
        simpa [Fintype.card_fin] using
          esymm_mean_bound (Finset.univ : Finset (Fin m)) hs (fun i => ‖ξ i‖)
            (fun i _ => norm_nonneg _) j (by simpa [Fintype.card_fin] using hj)

lemma descFactorial_choose_comm (n k j : ℕ) :
    (n - j).descFactorial k * n.choose j = n.descFactorial k * (n - k).choose j := by
  have h1 := Nat.descFactorial_mul_descFactorial (k := j) (m := j + k) (n := n) (by omega)
  have h2 := Nat.descFactorial_mul_descFactorial (k := k) (m := j + k) (n := n) (by omega)
  simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right] at h1 h2
  rw [Nat.descFactorial_eq_factorial_mul_choose n j] at h1
  rw [Nat.descFactorial_eq_factorial_mul_choose (n - k) j] at h2
  apply Nat.mul_left_cancel (Nat.factorial_pos j)
  calc j.factorial * ((n - j).descFactorial k * n.choose j)
      = (n - j).descFactorial k * (j.factorial * n.choose j) := by ring
    _ = n.descFactorial (j + k) := h1
    _ = (j.factorial * (n - k).choose j) * n.descFactorial k := h2.symm
    _ = j.factorial * (n.descFactorial k * (n - k).choose j) := by ring

lemma monicIteratedDerivative_props {n k : ℕ} (hk : k < n) (G : ℂ[X]) (hG : G.Monic)
    (hdG : G.natDegree = n) (hcG : G.coeff (n - 1) = 0) :
    let P := C (n.descFactorial k : ℂ)⁻¹ * Polynomial.derivative^[k] G
    P.Monic ∧ P.natDegree = n - k ∧ P.coeff (n - k - 1) = 0 ∧
      ∀ j ≤ n - k,
        ((n.choose j : ℂ) / ((n - k).choose j : ℂ)) * P.coeff (n - k - j) = G.coeff (n - j) := by
  intro P
  have hkle : k ≤ n := hk.le
  have hdf_ne : (n.descFactorial k : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hkle).ne'
  have htop : (Polynomial.derivative^[k] G).coeff (n - k) = (n.descFactorial k : ℂ) := by
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hkle, ← hdG, hG.coeff_natDegree,
      nsmul_eq_mul, mul_one]
  have hdeg : P.natDegree = n - k := by
    dsimp [P]
    rw [natDegree_C_mul (inv_ne_zero hdf_ne)]
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · simpa [hdG] using natDegree_iterate_derivative G k
    · rw [htop]; exact hdf_ne
  have hmonic : P.Monic := by
    change P.leadingCoeff = 1
    rw [← coeff_natDegree, hdeg]
    dsimp [P]
    rw [coeff_C_mul, htop, inv_mul_cancel₀ hdf_ne]
  have hcent : P.coeff (n - k - 1) = 0 := by
    dsimp [P]
    rw [coeff_C_mul, coeff_iterate_derivative, show n - k - 1 + k = n - 1 by omega,
      hcG, smul_zero, mul_zero]
  refine ⟨hmonic, hdeg, hcent, ?_⟩
  intro j hj
  have hch_ne : ((n - k).choose j : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hj).ne'
  have hidx : n - k - j + k = n - j := by omega
  have hidC : ((n - j).descFactorial k : ℂ) * (n.choose j : ℂ) =
      (n.descFactorial k : ℂ) * ((n - k).choose j : ℂ) := by
    exact_mod_cast descFactorial_choose_comm n k j
  dsimp [P]
  rw [coeff_C_mul, coeff_iterate_derivative, hidx, nsmul_eq_mul]
  field_simp
  linear_combination G.coeff (n - j) * hidC

lemma exists_root_tuple {m : ℕ} (P : ℂ[X]) (_hP : P.Monic) (hdeg : P.natDegree = m) :
    ∃ ξ : Fin m → ℂ, (List.ofFn ξ : Multiset ℂ) = P.roots := by
  let L := P.roots.toList
  have hcard : L.length = m := by
    rw [Multiset.length_toList, (IsAlgClosed.splits P).natDegree_eq_card_roots.symm, hdeg]
  refine ⟨fun i => L.get (i.cast hcard.symm), ?_⟩
  have hofFn : List.ofFn (fun i : Fin m => L.get (i.cast hcard.symm)) = L := by
    apply List.ext_get
    · simp [hcard]
    · intro i h1 h2; simp
  rw [hofFn, Multiset.coe_toList]

lemma exp_six_lt_five_hundred : Real.exp 6 < (500 : ℝ) := by
  have h1 : Real.exp 1 < (11 / 4 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
  have h6 : Real.exp 6 = (Real.exp 1) ^ 6 := by simp [← Real.exp_nat_mul]
  rw [h6]
  calc (Real.exp 1) ^ 6 ≤ (11 / 4 : ℝ) ^ 6 := by gcongr
    _ < 500 := by norm_num

lemma highPart_large_growth {n k : ℕ} (hn : 256 ≤ n) (hkn : 256 * k ≤ 33 * n)
    (G : ℂ[X]) (hG : G.Monic) (hdG : G.natDegree = n) (hcG : G.coeff (n - 1) = 0)
    (ξ : Fin (n - k) → ℂ)
    (hξ : (List.ofFn ξ : Multiset ℂ) =
      (C (n.descFactorial k : ℂ)⁻¹ * Polynomial.derivative^[k] G).roots)
    (hS : (∑ i : Fin (n - k), ‖ξ i‖) < (229 / 100 : ℝ))
    (ρ : ℝ) (hρ : (23 / 48 : ℝ) ≤ ρ) (z : ℂ) (hz : ‖z‖ ≤ ρ) :
    ‖(∑ j ∈ Finset.range (n - k + 1), C (G.coeff (n - j)) * X ^ (n - j)).eval z‖ <
      500 * ρ ^ n := by
  have hklt : k < n := by omega
  have hm_pos : 0 < n - k := by omega
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ
  obtain ⟨hP_mon, hP_deg, _, hratio_coeff⟩ := monicIteratedDerivative_props hklt G hG hdG hcG
  let S : ℝ := ∑ i : Fin (n - k), ‖ξ i‖
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcoeff_bd : ∀ j ≤ n - k,
      ‖G.coeff (n - j)‖ ≤ (n.choose j : ℝ) * (S / ((n - k : ℕ) : ℝ)) ^ j := by
    intro j hj
    have hbP := monic_coeff_root_mean_bound hm_pos _ hP_mon hP_deg ξ hξ j hj
    have hch_pos : (0 : ℝ) < ((n - k).choose j : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hj)
    rw [← hratio_coeff j hj, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    calc ((n.choose j : ℝ) / ((n - k).choose j : ℝ)) *
          ‖(C (n.descFactorial k : ℂ)⁻¹ * Polynomial.derivative^[k] G).coeff (n - k - j)‖
        ≤ ((n.choose j : ℝ) / ((n - k).choose j : ℝ)) *
            (((n - k).choose j : ℝ) * (S / ((n - k : ℕ) : ℝ)) ^ j) :=
          mul_le_mul_of_nonneg_left hbP (by positivity)
      _ = (n.choose j : ℝ) * (S / ((n - k : ℕ) : ℝ)) ^ j := by field_simp
  have hpoly_bd :
      ‖(∑ j ∈ Finset.range (n - k + 1), C (G.coeff (n - j)) * X ^ (n - j)).eval z‖ ≤
        (ρ + S / ((n - k : ℕ) : ℝ)) ^ n := by
    rw [eval_finsetSum]
    calc ‖∑ j ∈ Finset.range (n - k + 1), (C (G.coeff (n - j)) * X ^ (n - j)).eval z‖
        ≤ ∑ j ∈ Finset.range (n - k + 1), ‖(C (G.coeff (n - j)) * X ^ (n - j)).eval z‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (n - k + 1),
            (n.choose j : ℝ) * (S / ((n - k : ℕ) : ℝ)) ^ j * ρ ^ (n - j) := by
          apply Finset.sum_le_sum
          intro j hj
          have hbj := hcoeff_bd j (by have := Finset.mem_range.mp hj; omega)
          simp only [eval_mul, eval_C, eval_pow, eval_X, norm_mul, norm_pow]
          exact mul_le_mul hbj (pow_le_pow_left₀ (norm_nonneg z) hz _) (by positivity) (by positivity)
      _ ≤ ∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℝ) * (S / ((n - k : ℕ) : ℝ)) ^ j * ρ ^ (n - j) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          intros; positivity
      _ = (ρ + S / ((n - k : ℕ) : ℝ)) ^ n := by
          rw [add_comm ρ, add_pow]
          apply Finset.sum_congr rfl
          intros; ring
  have hmR : (0 : ℝ) < ((n - k : ℕ) : ℝ) := Nat.cast_pos.mpr hm_pos
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsplit : ρ + S / ((n - k : ℕ) : ℝ) = ρ * (1 + S / (((n - k : ℕ) : ℝ) * ρ)) := by
    field_simp
  have hexp_le : (ρ + S / ((n - k : ℕ) : ℝ)) ^ n ≤
      ρ ^ n * Real.exp ((n : ℝ) * S / (((n - k : ℕ) : ℝ) * ρ)) := by
    rw [hsplit, mul_pow]
    have h1 : 1 + S / (((n - k : ℕ) : ℝ) * ρ) ≤ Real.exp (S / (((n - k : ℕ) : ℝ) * ρ)) := by
      simpa only [add_comm] using Real.add_one_le_exp (S / (((n - k : ℕ) : ℝ) * ρ))
    have hpow : (1 + S / (((n - k : ℕ) : ℝ) * ρ)) ^ n ≤
        (Real.exp (S / (((n - k : ℕ) : ℝ) * ρ))) ^ n :=
      pow_le_pow_left₀ (by positivity) h1 n
    have hh := mul_le_mul_of_nonneg_left hpow (pow_nonneg hρ0.le n)
    rw [← Real.exp_nat_mul] at hh
    simpa only [mul_div_assoc] using hh
  have harg_lt : (n : ℝ) * S / (((n - k : ℕ) : ℝ) * ρ) < 6 := by
    apply (div_lt_iff₀ (mul_pos hmR hρ0)).mpr
    have hrat : (223 : ℝ) * (n : ℝ) ≤ 256 * ((n - k : ℕ) : ℝ) := by
      exact_mod_cast (show 223 * n ≤ 256 * (n - k) by omega)
    have hs1 := mul_lt_mul_of_pos_left hS hnR
    have hr1 := mul_le_mul_of_nonneg_left hρ hmR.le
    nlinarith
  have hexp_lt : Real.exp ((n : ℝ) * S / (((n - k : ℕ) : ℝ) * ρ)) < 500 :=
    (Real.exp_lt_exp.mpr harg_lt).trans exp_six_lt_five_hundred
  calc ‖(∑ j ∈ Finset.range (n - k + 1), C (G.coeff (n - j)) * X ^ (n - j)).eval z‖
      ≤ ρ ^ n * Real.exp ((n : ℝ) * S / (((n - k : ℕ) : ℝ) * ρ)) := hpoly_bd.trans hexp_le
    _ < ρ ^ n * 500 := mul_lt_mul_of_pos_left hexp_lt (pow_pos hρ0 n)
    _ = 500 * ρ ^ n := mul_comm _ _

end MaclaurinAndHighPart

section BernsteinAndCriticalValues

lemma reverse_eval_inv (p : ℂ[X]) {t : ℂ} (ht : t ≠ 0) :
    p.reverse.eval t * t⁻¹ ^ p.natDegree = p.eval t⁻¹ := by
  let _ : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht)
  simpa using p.eval₂_reverse_mul_pow (RingHom.id ℂ) t⁻¹

lemma polynomial_exterior_growth (p : ℂ[X]) {d : ℕ} (hd : p.natDegree ≤ d)
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M) (hbd : ∀ w : ℂ, ‖w‖ ≤ r → ‖p.eval w‖ ≤ M)
    {z : ℂ} (hz : r ≤ ‖z‖) :
    ‖p.eval z‖ ≤ M * (‖z‖ / r) ^ d := by
  have hz_pos : 0 < ‖z‖ := hr.trans_le hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hz_pos
  have hrev_sphere : ∀ w ∈ frontier (ball (0 : ℂ) r⁻¹),
      ‖p.reverse.eval w‖ ≤ M / r ^ p.natDegree := by
    intro w hw
    rw [frontier_ball (0 : ℂ) (inv_pos.mpr hr).ne', mem_sphere, dist_zero_right] at hw
    have hw0 : w ≠ 0 := norm_pos_iff.mp (by rw [hw]; positivity)
    have hwinv : ‖w⁻¹‖ = r := by rw [norm_inv, hw, inv_inv]
    have hb := hbd w⁻¹ hwinv.le
    rw [← reverse_eval_inv p hw0, norm_mul, norm_pow, hwinv] at hb
    exact (le_div_iff₀ (pow_pos hr _)).mpr hb
  have hz_mem : z⁻¹ ∈ closure (ball (0 : ℂ) r⁻¹) := by
    rw [closure_ball (0 : ℂ) (inv_pos.mpr hr).ne', mem_closedBall, dist_zero_right, norm_inv]
    exact inv_anti₀ hr hz
  have hrev_bd : ‖p.reverse.eval z⁻¹‖ ≤ M / r ^ p.natDegree :=
    Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := (0 : ℂ)) (r := r⁻¹))
      p.reverse.differentiable.diffContOnCl hrev_sphere hz_mem
  have heval : p.eval z = p.reverse.eval z⁻¹ * z ^ p.natDegree := by
    simpa only [inv_inv] using (reverse_eval_inv p (inv_ne_zero hz0)).symm
  have hrat : 1 ≤ ‖z‖ / r := (one_le_div hr).mpr hz
  rw [heval, norm_mul, norm_pow]
  calc ‖p.reverse.eval z⁻¹‖ * ‖z‖ ^ p.natDegree
      ≤ (M / r ^ p.natDegree) * ‖z‖ ^ p.natDegree :=
        mul_le_mul_of_nonneg_right hrev_bd (by positivity)
    _ = M * (‖z‖ / r) ^ p.natDegree := by rw [div_pow]; ring
    _ ≤ M * (‖z‖ / r) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hrat hd) hM

lemma polynomial_lipschitz_zero_disk (p : ℂ[X]) {R B : ℝ}
    (hbd : ∀ w : ℂ, ‖w‖ ≤ R → ‖p.derivative.eval w‖ ≤ B) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖p.eval z - p.eval 0‖ ≤ B * ‖z‖ := by
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hz
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun w => p.eval w) (f' := fun w => p.derivative.eval w) (s := closedBall (0 : ℂ) R)
    (x := (0 : ℂ)) (y := z)
    (fun v _ => (p.hasDerivAt v).hasDerivWithinAt)
    (fun v hv => hbd v (by simpa only [mem_closedBall, dist_zero_right] using hv))
    (convex_closedBall (0 : ℂ) R)
    (mem_closedBall_self hR0)
    (by simpa only [mem_closedBall, dist_zero_right] using hz)
  simpa only [sub_zero] using hh

lemma remainder_natDegree_le {n k : ℕ} (hk : 1 ≤ k) (hkle : k ≤ n)
    (G : ℂ[X]) (hdG : G.natDegree = n) :
    (G - ∑ j ∈ Finset.range (n - k + 1), C (G.coeff (n - j)) * X ^ (n - j)).natDegree ≤ k - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_sub, finsetSum_coeff]
  simp_rw [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hin : i ≤ n
  · rw [Finset.sum_eq_single_of_mem (n - i) (Finset.mem_range.mpr (by omega))]
    · simp [Nat.sub_sub_self hin]
    · intro b hb hbi
      have hbn := Finset.mem_range.mp hb
      have hne : i ≠ n - b := by omega
      simp [hne]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_sub, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro b _
    have hne : i ≠ n - b := by omega
    simp [hne]

lemma large_derivative_choice (n : ℕ) (hn : 256 ≤ n) :
    let k := Nat.ceil (2 * Real.sqrt (n : ℝ))
    2 ≤ k ∧ 256 * k ≤ 33 * n ∧ 4 * n ≤ k ^ 2 ∧ 223 ≤ n - k ∧ k + 2 ≤ n := by
  intro k
  have hnR : (256 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hs := Real.sqrt_nonneg (n : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hs16 : (16 : ℝ) ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hlow : 2 * Real.sqrt (n : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  have hupp : (k : ℝ) < 2 * Real.sqrt (n : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk32R : (32 : ℝ) ≤ k := by linarith
  have hk32 : 32 ≤ k := by exact_mod_cast hk32R
  have hratioR : 256 * (k : ℝ) ≤ 33 * (n : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs16) (show 0 ≤ 33 * Real.sqrt (n : ℝ) + 16 by positivity)]
  have hratio : 256 * k ≤ 33 * n := by exact_mod_cast hratioR
  have hsqR : 4 * (n : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hsq : 4 * n ≤ k ^ 2 := by exact_mod_cast hsqR
  exact ⟨by omega, hratio, hsq, by omega, by omega⟩

lemma large_pair_weight_bound {m : ℕ} (hm : 223 ≤ m) :
    (181 / 100 : ℝ) <
      2 * (((m : ℝ) - 2) / 2) / (1 + ((m : ℝ) - 2) / 2 + Real.sqrt (((m : ℝ) - 2) / 2)) := by
  let t : ℝ := ((m : ℝ) - 2) / 2
  have hmR : (223 : ℝ) ≤ m := Nat.cast_le.mpr hm
  have ht : (221 / 2 : ℝ) ≤ t := by dsimp [t]; linarith
  have htp : 0 ≤ t := by linarith
  have hs := Real.sqrt_nonneg t
  have hs2 := Real.sq_sqrt htp
  have hslow : (21 / 2 : ℝ) ≤ Real.sqrt t := by nlinarith
  change (181 / 100 : ℝ) < 2 * t / (1 + t + Real.sqrt t)
  apply (lt_div_iff₀ (show 0 < 1 + t + Real.sqrt t by positivity)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hslow) (show 0 ≤ 19 * Real.sqrt t + 37 / 2 by positivity)]

lemma large_critical_value_radius {n : ℕ} (hn : 256 ≤ n) :
    (500 + (n : ℝ) / 4) * (19 / 20 : ℝ) ^ n < 1 / 4 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnR : (256 : ℝ) ≤ n := Nat.cast_le.mpr hn
    have hdec : (500 + ((n : ℝ) + 1) / 4) * (19 / 20 : ℝ) ≤ 500 + (n : ℝ) / 4 := by linarith
    calc (500 + ((n + 1 : ℕ) : ℝ) / 4) * (19 / 20 : ℝ) ^ (n + 1)
        = ((500 + ((n : ℝ) + 1) / 4) * (19 / 20 : ℝ)) * (19 / 20 : ℝ) ^ n := by
          rw [Nat.cast_succ, pow_succ]; ring
      _ ≤ (500 + (n : ℝ) / 4) * (19 / 20 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right hdec (by positivity)
      _ < 1 / 4 := ih

end BernsteinAndCriticalValues

/-- Sampled iterated-derivative planar root-energy upper bound from a small real-axis slice deficit
(Zhang, Sections 5–6, `SampledDerivativeBound` + `SamplingErrorConstants`). -/
def H1 : Prop :=
  ∀ n k : ℕ, 256 ≤ n → 2 ≤ k → k + 2 ≤ n → 4 * n ≤ k ^ 2 →
    ∀ G : ℂ[X], G.Monic → G.natDegree = n → G.coeff (n - 1) = 0 →
      (1 / 2 : ℝ) * ∫ θ in Set.Ioo (0 : ℝ) Real.pi, ∫ h : ℝ, ((n : ℝ) -
        (({x : ℝ | (G.eval (Complex.exp ((θ : ℂ) * Complex.I) *
          ((x : ℂ) + (h : ℂ) * Complex.I))).im = 0}).ncard : ℝ)) ≤ (4 : ℝ) / 5 →
      ∀ ξ : Fin (n - k) → ℂ,
        (List.ofFn ξ : Multiset ℂ) =
          (C (n.descFactorial k : ℂ)⁻¹ * Polynomial.derivative^[k] G).roots →
        ∀ R : ℝ, 0 ≤ R → (∀ j : Fin (n - k), ‖ξ j‖ ≤ R) →
          ((ENNReal.ofReal Real.pi)⁻¹ * ∫⁻ z : ℂ, ENNReal.ofReal
            ((∑ j : Fin (n - k), ‖1 / (z - ξ j)‖) -
              ‖∑ j : Fin (n - k), (1 / (z - ξ j))‖)) < ⊤ ∧
          ((ENNReal.ofReal Real.pi)⁻¹ * ∫⁻ z : ℂ, ENNReal.ofReal
            ((∑ j : Fin (n - k), ‖1 / (z - ξ j)‖) -
              ‖∑ j : Fin (n - k), (1 / (z - ξ j))‖)).toReal ≤
            (4 : ℝ) / 5 + (423 / 1000 : ℝ) * R

/-- Pairwise distance and `ℓ¹` sum lower bounds for the planar root-triangle energy of centered
complex tuples (Zhang, Section 4, `DiameterRootEnergy` + `PairwiseRootEnergy` + `RootEnergyConstant`). -/
def H2 : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∀ ξ : Fin m → ℂ, (∑ j : Fin m, ξ j) = 0 →
    ((ENNReal.ofReal Real.pi)⁻¹ * ∫⁻ z : ℂ, ENNReal.ofReal
      ((∑ j : Fin m, ‖1 / (z - ξ j)‖) - ‖∑ j : Fin m, (1 / (z - ξ j))‖)) < ⊤ →
    (∀ i j : Fin m,
      (2 * (((m : ℝ) - 2) / 2) / (1 + ((m : ℝ) - 2) / 2 + Real.sqrt (((m : ℝ) - 2) / 2))) *
        ‖ξ i - ξ j‖ ≤
      ((ENNReal.ofReal Real.pi)⁻¹ * ∫⁻ z : ℂ, ENNReal.ofReal
        ((∑ j : Fin m, ‖1 / (z - ξ j)‖) - ‖∑ j : Fin m, (1 / (z - ξ j))‖)).toReal) ∧
    (913 / 1000 : ℝ) * (∑ j : Fin m, ‖ξ j‖) ≤
      2 * ((ENNReal.ofReal Real.pi)⁻¹ * ∫⁻ z : ℂ, ENNReal.ofReal
        ((∑ j : Fin m, ‖1 / (z - ξ j)‖) - ‖∑ j : Fin m, (1 / (z - ξ j))‖)).toReal

/-- Beta-integral exterior derivative lower bound on `‖z‖ ≥ 19/20` for the high-degree polynomial
part when the `k`-th derivative roots satisfy the radius and `ℓ¹` caps (Zhang, Section 3,
`BetaRootLowerBound`). -/
def H3 : Prop :=
  ∀ n k : ℕ, 256 ≤ n → 2 ≤ k → 256 * k ≤ 33 * n →
    ∀ G : ℂ[X], G.Monic → G.natDegree = n → G.coeff (n - 1) = 0 →
      ∀ ξ : Fin (n - k) → ℂ,
        (List.ofFn ξ : Multiset ℂ) =
          (C (n.descFactorial k : ℂ)⁻¹ * Polynomial.derivative^[k] G).roots →
        (∀ i : Fin (n - k), ‖ξ i‖ ≤ (577 / 1000 : ℝ)) →
        (∑ i : Fin (n - k), ‖ξ i‖) ≤ (229 / 100 : ℝ) →
        ∀ z : ℂ, (19 / 20 : ℝ) ≤ ‖z‖ →
          (24 / 25 : ℝ) * (n : ℝ) * ‖z‖ ^ (n - 1) * Real.exp (-(46 / 5 : ℝ)) ≤
            ‖(∑ j ∈ Finset.range (n - k + 1), C (G.coeff (n - j)) * X ^ (n - j)).derivative.eval z‖

/-- Two-height parallel-slice recovery bound for the derivative of the low-degree remainder on
`‖z‖ ≤ 19/20` under small real-axis slice deficit (Zhang, Section 7, `LargeLowPartDerivative`). -/
def H4 : Prop :=
  ∀ n k : ℕ, 256 ≤ n → 2 ≤ k → 256 * k ≤ 33 * n →
    ∀ G : ℂ[X], G.Monic → G.natDegree = n → G.coeff (n - 1) = 0 →
      (1 / 2 : ℝ) * ∫ θ in Set.Ioo (0 : ℝ) Real.pi, ∫ h : ℝ, ((n : ℝ) -
        (({x : ℝ | (G.eval (Complex.exp ((θ : ℂ) * Complex.I) *
          ((x : ℂ) + (h : ℂ) * Complex.I))).im = 0}).ncard : ℝ)) ≤ (4 : ℝ) / 5 →
      ∀ ξ : Fin (n - k) → ℂ,
        (List.ofFn ξ : Multiset ℂ) =
          (C (n.descFactorial k : ℂ)⁻¹ * Polynomial.derivative^[k] G).roots →
        (∑ i : Fin (n - k), ‖ξ i‖) < (229 / 100 : ℝ) →
        (∀ w : ℂ, ‖w‖ ≤ (23 / 48 : ℝ) →
          ‖(∑ j ∈ Finset.range (n - k + 1), C (G.coeff (n - j)) * X ^ (n - j)).eval w‖ ≤
            500 * (23 / 48 : ℝ) ^ n) →
        ∀ z : ℂ, ‖z‖ ≤ (19 / 20 : ℝ) →
          ‖(G - ∑ j ∈ Finset.range (n - k + 1), C (G.coeff (n - j)) * X ^ (n - j)).derivative.eval z‖ ≤
            (n : ℝ) * (19 / 20 : ℝ) ^ (n - 1) * Real.exp (-(46 / 5 : ℝ)) / 4

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos114_erdos_114_R1_H2_R1.H2 := by
  intro h1 h2 h3 h4 n hn F hF hdF hcF hmax _hle w₀ ψ
  obtain ⟨G, hG, hdG, hcG, ⟨x₁, x₂, hx₁, hx₂, hdist⟩, hslice_eq⟩ :=
    affine_line_slice_reduction (by omega : 2 ≤ n) F hF hdF hcF hmax w₀ ψ
  rw [hslice_eq]
  by_contra! hD
  let k : ℕ := Nat.ceil (2 * Real.sqrt (n : ℝ))
  obtain ⟨hk2, hkn, hksq, hm223, hk2n⟩ := large_derivative_choice n hn
  change 2 ≤ k at hk2
  change 256 * k ≤ 33 * n at hkn
  change 4 * n ≤ k ^ 2 at hksq
  change 223 ≤ n - k at hm223
  change k + 2 ≤ n at hk2n
  obtain ⟨hP_mon, hP_deg, hP_cent, _⟩ :=
    monicIteratedDerivative_props (by omega : k < n) G hG hdG hcG
  obtain ⟨ξ, hξ⟩ := exists_root_tuple _ hP_mon hP_deg
  have hsum_zero : (∑ j : Fin (n - k), ξ j) = 0 :=
    centered_roots_sum_zero (by omega) _ hP_mon hP_deg hP_cent ξ hξ
  have hfin_ne : (Finset.univ : Finset (Fin (n - k))).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, _, hmaxR⟩ := Finset.exists_max_image Finset.univ (fun j => ‖ξ j‖) hfin_ne
  let R : ℝ := ‖ξ i₀‖
  have hR0 : 0 ≤ R := norm_nonneg _
  have hRbd : ∀ j : Fin (n - k), ‖ξ j‖ ≤ R := fun j => hmaxR j (Finset.mem_univ _)
  obtain ⟨hE_fin, hE_upper⟩ := h1 n k hn hk2 hk2n hksq G hG hdG hcG hD ξ hξ R hR0 hRbd
  obtain ⟨hE_dist, hE_sum⟩ := h2 (n - k) (by omega) ξ hsum_zero hE_fin
  let E : ℝ := ((ENNReal.ofReal Real.pi)⁻¹ * ∫⁻ z : ℂ, ENNReal.ofReal
    ((∑ j : Fin (n - k), ‖1 / (z - ξ j)‖) - ‖∑ j : Fin (n - k), (1 / (z - ξ j))‖)).toReal
  change E ≤ (4 : ℝ) / 5 + (423 / 1000 : ℝ) * R at hE_upper
  change (913 / 1000 : ℝ) * (∑ j : Fin (n - k), ‖ξ j‖) ≤ 2 * E at hE_sum
  have hpair_dist : ∀ j : Fin (n - k), (181 / 100 : ℝ) * ‖ξ i₀ - ξ j‖ ≤ E := by
    intro j
    have hdj := hE_dist i₀ j
    change _ ≤ E at hdj
    have hcw := large_pair_weight_bound hm223
    exact (mul_le_mul_of_nonneg_right hcw.le (norm_nonneg (ξ i₀ - ξ j))).trans hdj
  have hm_posR : (0 : ℝ) < ((n - k : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hnorm_avg : ((n - k : ℕ) : ℝ) * R ≤ ∑ j : Fin (n - k), ‖ξ i₀ - ξ j‖ := by
    have hh := norm_sum_le (Finset.univ : Finset (Fin (n - k))) (fun j => ξ i₀ - ξ j)
    simpa [R, Finset.sum_sub_distrib, hsum_zero, norm_smul] using hh
  have hsum_dist : (∑ j : Fin (n - k), (181 / 100 : ℝ) * ‖ξ i₀ - ξ j‖) ≤
      ((n - k : ℕ) : ℝ) * E := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpair_dist j)
    simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul] using hs
  rw [← Finset.mul_sum] at hsum_dist
  have hR_le_E : (181 / 100 : ℝ) * R ≤ E := by
    have hh : ((n - k : ℕ) : ℝ) * ((181 / 100 : ℝ) * R) ≤ ((n - k : ℕ) : ℝ) * E := by nlinarith
    exact (mul_le_mul_iff_right₀ hm_posR).mp hh
  have hR_cap : R < (577 / 1000 : ℝ) := by linarith
  have hξ_R : ∀ j : Fin (n - k), ‖ξ j‖ ≤ (577 / 1000 : ℝ) :=
    fun j => (hRbd j).trans hR_cap.le
  have hξ_S : (∑ j : Fin (n - k), ‖ξ j‖) < (229 / 100 : ℝ) := by linarith
  let T : ℂ[X] := ∑ j ∈ Finset.range (n - k + 1), C (G.coeff (n - j)) * X ^ (n - j)
  let Q : ℂ[X] := G - T
  have hT_23 : ∀ w : ℂ, ‖w‖ ≤ (23 / 48 : ℝ) → ‖T.eval w‖ ≤ 500 * (23 / 48 : ℝ) ^ n :=
    fun w hw => (highPart_large_growth hn hkn G hG hdG hcG ξ hξ hξ_S (23 / 48) le_rfl w hw).le
  have hQ_low : ∀ z : ℂ, ‖z‖ ≤ (19 / 20 : ℝ) →
      ‖Q.derivative.eval z‖ ≤ (n : ℝ) * (19 / 20 : ℝ) ^ (n - 1) * Real.exp (-(46 / 5 : ℝ)) / 4 :=
    h4 n k hn hk2 hkn G hG hdG hcG hD ξ hξ hξ_S hT_23
  have hcrit_in_disk : ∀ ζ : ℂ, G.derivative.IsRoot ζ → ‖ζ‖ < (19 / 20 : ℝ) := by
    intro ζ hζ
    by_contra! hz_out
    have hQd_deg : Q.derivative.natDegree ≤ n - 1 := by
      have hQ_deg : Q.natDegree ≤ k - 1 := remainder_natDegree_le (by omega) (by omega) G hdG
      have hd1 := Polynomial.natDegree_derivative_le Q
      omega
    let W : ℝ := Real.exp (-(46 / 5 : ℝ))
    have hW_pos : 0 < W := Real.exp_pos _
    have hn_posR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hQ_ext := polynomial_exterior_growth Q.derivative hQd_deg (by norm_num : (0 : ℝ) < 19 / 20)
      (by positivity : 0 ≤ (n : ℝ) * (19 / 20 : ℝ) ^ (n - 1) * W / 4) hQ_low hz_out
    have hsimp_ext : ((n : ℝ) * (19 / 20 : ℝ) ^ (n - 1) * W / 4) * (‖ζ‖ / (19 / 20 : ℝ)) ^ (n - 1) =
        (n : ℝ) * ‖ζ‖ ^ (n - 1) * W / 4 := by
      have hp : (19 / 20 : ℝ) ^ (n - 1) * (‖ζ‖ / (19 / 20 : ℝ)) ^ (n - 1) = ‖ζ‖ ^ (n - 1) := by
        rw [← mul_pow, show (19 / 20 : ℝ) * (‖ζ‖ / (19 / 20 : ℝ)) = ‖ζ‖ by field_simp]
      linear_combination ((n : ℝ) * W / 4) * hp
    rw [hsimp_ext] at hQ_ext
    have hT_ext := h3 n k hn hk2 hkn G hG hdG hcG ξ hξ hξ_R hξ_S.le ζ hz_out
    have hQT_eq : ‖Q.derivative.eval ζ‖ = ‖T.derivative.eval ζ‖ := by
      have h0 : G.derivative.eval ζ = 0 := hζ
      simp only [Q, derivative_sub, eval_sub, h0, zero_sub, norm_neg]
    rw [hQT_eq] at hQ_ext
    change (24 / 25 : ℝ) * (n : ℝ) * ‖ζ‖ ^ (n - 1) * W ≤ ‖T.derivative.eval ζ‖ at hT_ext
    have hpos_factor : 0 < (n : ℝ) * ‖ζ‖ ^ (n - 1) * W := by
      have hz_pos : 0 < ‖ζ‖ := lt_of_lt_of_le (by norm_num) hz_out
      positivity
    linarith
  have hval_in_disk : ∀ ζ : ℂ, G.derivative.IsRoot ζ → ‖G.eval ζ - Q.eval 0‖ < (1 / 4 : ℝ) := by
    intro ζ hζ
    have hζ_lt := hcrit_in_disk ζ hζ
    have hT_bd := highPart_large_growth hn hkn G hG hdG hcG ξ hξ hξ_S (19 / 20)
      (by norm_num) ζ hζ_lt.le
    let B : ℝ := (n : ℝ) * (19 / 20 : ℝ) ^ (n - 1) / 4
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    have hW_le1 : Real.exp (-(46 / 5 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hQ_bdB : ∀ w : ℂ, ‖w‖ ≤ (19 / 20 : ℝ) → ‖Q.derivative.eval w‖ ≤ B := by
      intro w hw
      refine (hQ_low w hw).trans ?_
      dsimp [B]
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_right (by positivity) hW_le1) (by norm_num)
    have hQ_lip := polynomial_lipschitz_zero_disk Q hQ_bdB hζ_lt.le
    have hdecomp : G.eval ζ - Q.eval 0 = T.eval ζ + (Q.eval ζ - Q.eval 0) := by
      simp only [Q, eval_sub]; ring
    have hBr : B * (19 / 20 : ℝ) = (n : ℝ) * (19 / 20 : ℝ) ^ n / 4 := by
      dsimp [B]
      have hp : (19 / 20 : ℝ) ^ (n - 1) * (19 / 20 : ℝ) = (19 / 20 : ℝ) ^ n := by
        rw [← pow_succ, show n - 1 + 1 = n by omega]
      linear_combination ((n : ℝ) / 4) * hp
    rw [hdecomp]
    calc ‖T.eval ζ + (Q.eval ζ - Q.eval 0)‖
        ≤ ‖T.eval ζ‖ + ‖Q.eval ζ - Q.eval 0‖ := norm_add_le _ _
      _ < 500 * (19 / 20 : ℝ) ^ n + B * (19 / 20 : ℝ) :=
          add_lt_add_of_lt_of_le hT_bd (hQ_lip.trans (mul_le_mul_of_nonneg_left hζ_lt.le hB0))
      _ = (500 + (n : ℝ) / 4) * (19 / 20 : ℝ) ^ n := by rw [hBr]; ring
      _ < 1 / 4 := large_critical_value_radius hn
  have hv₁ := hval_in_disk x₁ hx₁
  have hv₂ := hval_in_disk x₂ hx₂
  have htri : ‖G.eval x₁ - G.eval x₂‖ ≤
      ‖G.eval x₁ - Q.eval 0‖ + ‖G.eval x₂ - Q.eval 0‖ := by
    calc ‖G.eval x₁ - G.eval x₂‖
        = ‖(G.eval x₁ - Q.eval 0) - (G.eval x₂ - Q.eval 0)‖ := by congr 1; ring
      _ ≤ ‖G.eval x₁ - Q.eval 0‖ + ‖G.eval x₂ - Q.eval 0‖ := norm_sub_le _ _
  linarith

end OMA.R_Erdos114_erdos_114_R1_H2_R1_H2_R1
