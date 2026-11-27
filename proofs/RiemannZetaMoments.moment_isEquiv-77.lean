import FormalConjectures.Paper.RiemannZetaMoments
import Mathlib

/-
Ported from an existing public Lean proof; the mathematics and the Lean proof are the original author's.
Original: https://github.com/ChironTheCentaur/rh-lab-zeta-second-moment/blob/02173eb934a76c5ca607a03fbc2eadef816b78fe/ZetaMomentsFC/Main.lean  (theorem RiemannZetaMoments.moment_isEquiv₁)
Original author: Sky (GitHub: ChironTheCentaur)   Licence: Apache-2.0 (LICENSE; Zeta23 parts: LICENSE.zeta23)
Submitted to lefttosolve.com by @senamakel; ported to Lean v4.33.1 / formal-conjectures 9097e2f.
Changes: the import closure of ZetaMomentsFC/Main.lean flattened into one file (each module in its own section) and
pruned to the declarations the result depends on; the copy of formal-conjectures' moment dropped in favour of the
imported one; local notations (ζ, ζ', ζ₀, Λ) expanded, the fun_prop attribute and two set_option lines removed
(one fun_prop call replaced by the explicit lemma), and API drift between Mathlib 56a00585 and the pin fixed
(Real.arctan made explicit in three lemmas, two RectangleIntegral rewrites closed with smul_add and abel).

NOTICE of the original package, retained as Apache-2.0 requires:

  ZetaSecondMoment (standalone package)
  Copyright 2026 Sky (GitHub: ChironTheCentaur)

  The original work in this package (ZetaMomentsFC/, LeanClassics/, ZetaSecondMoment.lean, check.py,
  AxiomAudit.lean, PlantedSorry.lean, controls/) is licensed under the Apache License, Version 2.0 (see LICENSE).

  The definition moment and the statement of moment_isEquiv₁ in ZetaMomentsFC/Main.lean are copied verbatim
  from google-deepmind/formal-conjectures (FormalConjectures/Paper/RiemannZetaMoments.lean, commit ea8e3e19),
  Copyright The Formal Conjectures Authors, licensed under the Apache License, Version 2.0.

  Zeta23/ is a subset of zeta-23-lean, Copyright 2026 Anthropic, PBC, licensed under the Apache License,
  Version 2.0 (LICENSE.zeta23, NOTICE.zeta23), as ported to Lean v4.35.0 / Mathlib 56a005855ea1.

NOTICE.zeta23 of the original package:

  Zeta23 - a Lean 4 formalization of critical-line zero-proportion theorems
  Copyright 2026 Anthropic, PBC

  This product is licensed under the Apache License, Version 2.0 (see LICENSE).

  This product includes software derived from PrimeNumberTheoremAnd
  (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
  Copyright the PrimeNumberTheoremAnd contributors, licensed under the Apache License, Version 2.0.
  The derived files are the ones under Zeta23/FromPNTPlus/; each carries its upstream notice
  (source file, upstream commit, original copyright line) and a description of the local modifications.
  Some of those files in turn derive from mathlib (https://github.com/leanprover-community/mathlib4),
  Copyright the mathlib contributors, Apache License, Version 2.0; their original headers are preserved.
-/

-- ===== LeanClassics.ZetaRealBounds =====
section
/-!
# For real `σ > 1`, `1/(σ − 1) ≤ ζ(σ) ≤ σ/(σ − 1)`

`one_div_sub_one_le_norm_zeta` and `norm_zeta_le_div_sub_one`: for real `σ > 1`,
`1/(σ − 1) ≤ |ζ(σ)| ≤ σ/(σ − 1)`.

Proof. Mathlib's `ZetaAsymptotics.termTSum_of_lt` gives
`T(σ) = 1/(σ − 1) − Z/σ`, where `Z = ∑ 1/(n + 1)^σ = ζ(σ)` and
`T(σ) = ∑_{n ≥ 1} ∫_n^{n+1} (x − n) x^{−σ−1} dx`. Each integrand is between `0` and `x^{−σ−1}`,
so `0 ≤ T(σ) ≤ ∫_1^∞ x^{−σ−1} dx = 1/σ`.
-/

open Complex Real Set Filter Topology ZetaAsymptotics

end

-- ===== LeanClassics.ZetaMeanSquare =====
section
/-!
# For `σ > 1`, `(1/T) ∫_0^T |ζ(σ + it)|² dt → ζ(2σ)`

`tendsto_mean_sq_zeta`: for `σ > 1`, `(1/T) ∫_0^T |ζ(σ + it)|² dt → |ζ(2σ)|` as `T → ∞`.

`tendsto_mean_sq` is the general statement it comes from: if `∑ |a_n| < ∞`, the real frequencies
`λ_n` are distinct and `F(t) = ∑ a_n e^{i λ_n t}` is continuous, then
`(1/T) ∫_0^T |F(t)|² dt → ∑ |a_n|²`.

Proof. For a finite sum, expanding `|F|²` leaves the diagonal `T ∑ |a_n|²` plus cross terms
`a_m ā_n ∫_0^T e^{i(λ_m − λ_n)t} dt`, each at most `2|a_m||a_n|/|λ_m − λ_n|` (`finite_mean`). The
tail beyond `N` is uniformly at most `∑_{n ≥ N} |a_n|`. For `ζ`, `a_n = (n + 1)^{−σ}` and
`λ_n = −log(n + 1)`.
-/

open Complex Real Set Filter Topology

noncomputable section

namespace LeanClassics.ZetaMeanSquare

lemma exp_mul_conj (x y t : ℝ) :
    cexp ((x : ℂ) * t * I) * (starRingEnd ℂ) (cexp ((y : ℂ) * t * I)) =
      cexp (((x - y : ℝ) : ℂ) * t * I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

lemma continuous_term (c : ℂ) (x : ℝ) : Continuous fun t : ℝ => c * cexp ((x : ℂ) * t * I) := by
  fun_prop

lemma norm_cexp_mul (x t : ℝ) : ‖cexp ((x : ℂ) * t * I)‖ = 1 := by
  rw [show (x : ℂ) * t * I = ((x * t : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

lemma term_eq (n : ℕ) (σ t : ℝ) :
    1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I) =
      ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * cexp (((-Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * t * I) := by
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [one_div, ← cpow_neg, hc, cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    Real.rpow_def_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.ofReal_log hx.le]
  congr 1
  push_cast; ring

end LeanClassics.ZetaMeanSquare
end
end

-- ===== Zeta23.MV.Spacing =====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 0 — spacing lemmas for admissible weights

For an injective `freq : ι → ℝ` on a finite index type with ADMISSIBLE weights `δ`
(`0 < δ r` and `δ r ≤ |freq r − freq s|` for all `s ≠ r` — the shape of Zeta23.MVHilbert),
the open intervals `I_t = (freq t − δ t/2, freq t + δ t/2)` are pairwise disjoint, giving
by comparison with `∫ |u − freq s|^{−σ} du`:

* `spacing_sq`   (σ = 2):  Σ_{t≠s} δ t/(freq s − freq t)²  ≤  9/δ s
* `spacing_four` (σ = 4):  Σ_{t≠s} δ t/(freq s − freq t)⁴  ≤  27/(δ s)³
* `two_point`:  Σ_{k≠ℓ,m} δ k/((freq k − freq ℓ)²(freq k − freq m)²)
                  ≤ 36(δ ℓ + δ m)/(δ ℓ · δ m · (freq ℓ − freq m)²)

These replace [Preissmann 1984, Lemmes 1 & 6] (cited without proof in arXiv:2203.14950)
with elementary arguments at worse constants — sufficient for the ∃C form.
-/

noncomputable section
open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Admissibility of weights (matches Zeta23.MVHilbert's hypotheses). -/
structure Adm (freq δ : ι → ℝ) : Prop where
  inj : Function.Injective freq
  pos : ∀ r, 0 < δ r
  le : ∀ r s, r ≠ s → δ r ≤ |freq r - freq s|

namespace Adm

variable {freq δ : ι → ℝ} (h : Adm freq δ)

/-- The interval `I_t`. -/
def itv (t : ι) : Set ℝ := Set.Ioo (freq t - δ t / 2) (freq t + δ t / 2)

omit [Fintype ι] [DecidableEq ι] in
/-- Centers are far apart: `(δ t + δ t')/2 ≤ |freq t − freq t'|` for `t ≠ t'`. -/
lemma centers_far (h : Adm freq δ) {t t' : ι} (htt : t ≠ t') :
    (δ t + δ t') / 2 ≤ |freq t - freq t'| := by
  have h1 := h.le t t' htt
  have h2 := h.le t' t htt.symm
  rw [abs_sub_comm] at h2
  rcases le_total (δ t) (δ t') with hd | hd <;> linarith

/-- The intervals are pairwise disjoint. -/
lemma itv_disjoint (h : Adm freq δ) :
    Set.univ.PairwiseDisjoint (fun t : ι => Adm.itv (freq := freq) (δ := δ) t) := by
  intro t _ t' _ htt
  have hfar := h.centers_far htt
  rw [Function.onFun, Set.disjoint_left]
  intro u hu hu'
  simp only [Adm.itv, Set.mem_Ioo] at hu hu'
  rcases abs_cases (freq t - freq t') with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hfar <;>
    linarith [hu.1, hu.2, hu'.1, hu'.2]

omit [Fintype ι] [DecidableEq ι] in
/-- For `u ∈ I_t`, `t ≠ s`: `|freq s − u| ≤ (3/2)|freq s − freq t|` and `δ s/2 ≤ |u − freq s|`. -/
lemma abs_le_of_mem_itv (h : Adm freq δ) {s t : ι} (hts : t ≠ s) {u : ℝ}
    (hu : u ∈ Adm.itv (freq := freq) (δ := δ) t) :
    |freq s - u| ≤ 3 / 2 * |freq s - freq t| ∧ δ s / 2 ≤ |u - freq s| := by
  simp only [Adm.itv, Set.mem_Ioo] at hu
  have hut : |u - freq t| ≤ δ t / 2 := by rw [abs_le]; constructor <;> linarith
  have hst : δ t ≤ |freq s - freq t| := by rw [abs_sub_comm]; exact h.le t s hts
  have hss : δ s ≤ |freq s - freq t| := h.le s t (Ne.symm hts)
  constructor
  · calc |freq s - u| = |(freq s - freq t) + (freq t - u)| := by ring_nf
      _ ≤ |freq s - freq t| + |freq t - u| := abs_add_le _ _
      _ = |freq s - freq t| + |u - freq t| := by rw [abs_sub_comm (freq t) u]
      _ ≤ |freq s - freq t| + δ t / 2 := by linarith
      _ ≤ 3 / 2 * |freq s - freq t| := by linarith
  · have key : |freq s - freq t| ≤ |freq s - u| + |u - freq t| := by
      calc |freq s - freq t| = |(freq s - u) + (u - freq t)| := by ring_nf
        _ ≤ |freq s - u| + |u - freq t| := abs_add_le _ _
    rw [abs_sub_comm u (freq s)]
    linarith

/-- Closed-form tail integrals: `∫_{Icc a b} (u−c)⁻² du = (a−c)⁻¹ − (b−c)⁻¹` for `c ∉ [a,b]`. -/
lemma integral_inv_sq_Icc {a b c : ℝ} (hab : a ≤ b) (hc : c < a ∨ b < c) :
    ∫ u in Set.Icc a b, ((u - c) ^ 2)⁻¹ = (a - c)⁻¹ - (b - c)⁻¹ := by
  have h0 : (0:ℝ) ∉ Set.uIcc (a - c) (b - c) := by
    rw [Set.mem_uIcc]
    rcases hc with hc | hc
    · push Not; constructor <;> intro <;> nlinarith
    · push Not; constructor <;> intro <;> nlinarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have e1 : ∀ u : ℝ, ((u - c) ^ 2)⁻¹ = (u - c) ^ (-2 : ℤ) := by
    intro u; rw [zpow_neg]; norm_cast
  simp_rw [e1]
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ (-2:ℤ)) c,
    integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num [zpow_neg]
  ring

/-- `∫_{Icc a b} (u−c)⁻⁴ du = ((a−c)⁻³ − (b−c)⁻³)/3` for `c ∉ [a,b]`. -/
lemma integral_inv_four_Icc {a b c : ℝ} (hab : a ≤ b) (hc : c < a ∨ b < c) :
    ∫ u in Set.Icc a b, ((u - c) ^ 4)⁻¹ = ((a - c) ^ (3:ℕ))⁻¹ / 3 - ((b - c) ^ (3:ℕ))⁻¹ / 3 := by
  have h0 : (0:ℝ) ∉ Set.uIcc (a - c) (b - c) := by
    rw [Set.mem_uIcc]
    rcases hc with hc | hc
    · push Not; constructor <;> intro <;> nlinarith
    · push Not; constructor <;> intro <;> nlinarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have e1 : ∀ u : ℝ, ((u - c) ^ 4)⁻¹ = (u - c) ^ (-4 : ℤ) := by
    intro u; rw [zpow_neg]; norm_cast
  simp_rw [e1]
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ (-4:ℤ)) c,
    integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num [zpow_neg]
  norm_cast
  push_cast
  set A := ((b - c) ^ (3:ℕ))⁻¹
  set B := ((a - c) ^ (3:ℕ))⁻¹
  linarith

section MainSpacing
variable (h : Adm freq δ) (s : ι)

/-- The two-sided tail window around `freq s`, radius `R`. -/
private def window (freq δ : ι → ℝ) (s : ι) (R : ℝ) : Set ℝ :=
  Set.Icc (freq s - R) (freq s - δ s / 2) ∪ Set.Icc (freq s + δ s / 2) (freq s + R)

private lemma mem_window (h : Adm freq δ) {s t : ι} (hts : t ≠ s) {R : ℝ}
    (hR : 3 / 2 * |freq s - freq t| ≤ R) {u : ℝ}
    (hu : u ∈ Adm.itv (freq := freq) (δ := δ) t) : u ∈ window freq δ s R := by
  have hb := h.abs_le_of_mem_itv hts hu
  have h1 : |u - freq s| ≤ R := by
    rw [abs_sub_comm]; exact hb.1.trans hR
  rcases le_total u (freq s) with hle | hle
  · left
    rw [abs_of_nonpos (by linarith : u - freq s ≤ 0)] at h1
    rw [abs_of_nonpos (by linarith : u - freq s ≤ 0)] at hb
    exact ⟨by linarith, by linarith [hb.2]⟩
  · right
    rw [abs_of_nonneg (by linarith : 0 ≤ u - freq s)] at h1
    rw [abs_of_nonneg (by linarith : 0 ≤ u - freq s)] at hb
    exact ⟨by linarith [hb.2], by linarith⟩

omit [Fintype ι] [DecidableEq ι] in
private lemma window_integrable {s : ι} {R : ℝ} (hδs : 0 < δ s) {k : ℕ} (_hk : k ≠ 0) :
    MeasureTheory.IntegrableOn (fun u => ((u - freq s) ^ k)⁻¹) (window freq δ s R) := by
  have hcompact : IsCompact (window freq δ s R) := (isCompact_Icc).union isCompact_Icc
  refine ContinuousOn.integrableOn_compact hcompact ?_
  have hne : ∀ u ∈ window freq δ s R, (u - freq s) ^ k ≠ 0 := by
    intro u hu
    apply pow_ne_zero
    rcases hu with hu | hu
    · simp only [Set.mem_Icc] at hu; intro hh; nlinarith [hu.2]
    · simp only [Set.mem_Icc] at hu; intro hh; nlinarith [hu.1]
  exact ((continuous_sub_right (freq s)).pow k).continuousOn.inv₀ hne

/-- **Spacing lemma, σ = 2**: `Σ_{t≠s} δ t/(freq s − freq t)² ≤ 9/δ s`. -/
theorem spacing_sq (h : Adm freq δ) (s : ι) :
    ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 2 ≤ 9 / δ s := by
  classical
  have hδs := h.pos s
  rcases Finset.eq_empty_or_nonempty (Finset.univ.erase s) with he | hne
  · rw [he, Finset.sum_empty]; positivity
  obtain ⟨t₀, ht₀⟩ := hne
  set g : ℝ → ℝ := fun u => ((u - freq s) ^ 2)⁻¹ with hg
  set M : ℝ := Finset.univ.sup' ⟨s, Finset.mem_univ s⟩ (fun t => |freq s - freq t|) with hM
  set R : ℝ := 3 / 2 * M + 1 with hR
  have hMle : ∀ t : ι, |freq s - freq t| ≤ M := fun t =>
    Finset.le_sup' (fun r => |freq s - freq r|) (Finset.mem_univ t)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMle s)
  have hδM : δ s ≤ M := (h.le s t₀ (Finset.ne_of_mem_erase ht₀).symm).trans (hMle t₀)
  have hRδ : δ s / 2 ≤ R := by linarith
  -- integrability on the window
  have hintW : MeasureTheory.IntegrableOn g (window freq δ s R) :=
    window_integrable (freq := freq) (δ := δ) hδs two_ne_zero
  -- each interval sits in the window
  have hsub : ∀ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t ⊆ window freq δ s R := by
    intro t ht u hu
    exact mem_window h (Finset.ne_of_mem_erase ht) (by linarith [hMle t]) hu
  -- per-term comparison
  have hper : ∀ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 2
      ≤ 9 / 4 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
    intro t ht
    have hts : t ≠ s := Finset.ne_of_mem_erase ht
    have hfst : (freq s - freq t) ≠ 0 := sub_ne_zero.2 fun hh => hts (h.inj hh.symm)
    have hpos2 : 0 < (freq s - freq t) ^ 2 := pow_two_pos_of_ne_zero hfst
    have hδt := h.pos t
    have hlow : ∀ u ∈ Adm.itv (freq := freq) (δ := δ) t,
        (9 / 4 * (freq s - freq t) ^ 2)⁻¹ ≤ g u := by
      intro u hu
      have hb := h.abs_le_of_mem_itv hts hu
      have hu0 : 0 < |u - freq s| := lt_of_lt_of_le (by linarith) hb.2
      have hsq : (u - freq s) ^ 2 ≤ 9 / 4 * (freq s - freq t) ^ 2 := by
        have h1 : |u - freq s| ≤ 3 / 2 * |freq s - freq t| := by
          rw [abs_sub_comm]; exact hb.1
        calc (u - freq s) ^ 2 = |u - freq s| ^ 2 := (sq_abs _).symm
          _ ≤ (3 / 2 * |freq s - freq t|) ^ 2 := by gcongr
          _ = 9 / 4 * |freq s - freq t| ^ 2 := by ring
          _ = 9 / 4 * (freq s - freq t) ^ 2 := by rw [sq_abs]
      have hupos : 0 < (u - freq s) ^ 2 := pow_two_pos_of_ne_zero (abs_pos.1 hu0)
      show _ ≤ ((u - freq s) ^ 2)⁻¹
      exact (inv_le_inv₀ (by positivity) hupos).2 hsq
    have hintT : MeasureTheory.IntegrableOn g (Adm.itv (freq := freq) (δ := δ) t) :=
      hintW.mono_set (hsub t ht)
    have h1 : ∫ _u in Adm.itv (freq := freq) (δ := δ) t, (9 / 4 * (freq s - freq t) ^ 2)⁻¹
        ≤ ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
      apply MeasureTheory.setIntegral_mono_on
      · exact MeasureTheory.integrableOn_const (by simp [Adm.itv])
      · exact hintT
      · exact measurableSet_Ioo
      · exact hlow
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at h1
    have hvol : (volume (Adm.itv (freq := freq) (δ := δ) t)).toReal = δ t := by
      rw [Adm.itv, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [MeasureTheory.measureReal_def, hvol] at h1
    calc δ t / (freq s - freq t) ^ 2
        = 9 / 4 * (δ t * (9 / 4 * (freq s - freq t) ^ 2)⁻¹) := by
          field_simp
      _ ≤ 9 / 4 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
          gcongr
  -- sum the comparisons, merge the disjoint intervals, pass to the window
  have hdisj : (↑(Finset.univ.erase s) : Set ι).PairwiseDisjoint
      (fun t => Adm.itv (freq := freq) (δ := δ) t) :=
    (h.itv_disjoint).subset (Set.subset_univ _)
  have hsum : ∑ t ∈ Finset.univ.erase s, ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u
      = ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u := by
    rw [MeasureTheory.integral_biUnion_finset]
    · exact fun t _ => measurableSet_Ioo
    · exact hdisj
    · exact fun t ht => hintW.mono_set (hsub t ht)
  have hUsub : (⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t)
      ⊆ window freq δ s R := by
    simp only [Set.iUnion_subset_iff]
    exact fun t ht => hsub t ht
  have hUmono : ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u
      ≤ ∫ u in window freq δ s R, g u := by
    apply MeasureTheory.setIntegral_mono_set hintW
    · exact Filter.Eventually.of_forall fun u => by positivity
    · exact Filter.Eventually.of_forall hUsub
  -- evaluate the window integral
  have hwindow : ∫ u in window freq δ s R, g u ≤ 4 / δ s := by
    have hd : Disjoint (Set.Icc (freq s - R) (freq s - δ s / 2))
        (Set.Icc (freq s + δ s / 2) (freq s + R)) := by
      rw [Set.disjoint_left]
      intro u hu hu'
      simp only [Set.mem_Icc] at hu hu'
      linarith [hu.2, hu'.1]
    have hil : MeasureTheory.IntegrableOn g (Set.Icc (freq s - R) (freq s - δ s / 2)) :=
      hintW.mono_set Set.subset_union_left
    have hir : MeasureTheory.IntegrableOn g (Set.Icc (freq s + δ s / 2) (freq s + R)) :=
      hintW.mono_set Set.subset_union_right
    rw [window, MeasureTheory.setIntegral_union hd measurableSet_Icc hil hir]
    have hleft : ∫ u in Set.Icc (freq s - R) (freq s - δ s / 2), g u
        = (- R)⁻¹ + (δ s / 2)⁻¹ := by
      rw [hg]
      rw [integral_inv_sq_Icc (by linarith) (Or.inr (by linarith))]
      have e1 : freq s - R - freq s = -R := by ring
      have e2 : freq s - δ s / 2 - freq s = -(δ s / 2) := by ring
      rw [e1, e2]
      rw [inv_neg]
      ring
    have hright : ∫ u in Set.Icc (freq s + δ s / 2) (freq s + R), g u
        = (δ s / 2)⁻¹ - R⁻¹ := by
      rw [hg]
      rw [integral_inv_sq_Icc (by linarith) (Or.inl (by linarith))]
      have e1 : freq s + δ s / 2 - freq s = δ s / 2 := by ring
      have e2 : freq s + R - freq s = R := by ring
      rw [e1, e2]
    rw [hleft, hright]
    have hR0 : 0 < R := by linarith
    have : (δ s / 2)⁻¹ = 2 / δ s := by field_simp
    rw [this, inv_neg]
    have hRi : 0 < R⁻¹ := by positivity
    have h4 : 4 / δ s = 2 / δ s + 2 / δ s := by ring
    linarith
  -- assemble
  calc ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 2
      ≤ ∑ t ∈ Finset.univ.erase s, 9 / 4 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u :=
        Finset.sum_le_sum hper
    _ = 9 / 4 * ∑ t ∈ Finset.univ.erase s, ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
        rw [Finset.mul_sum]
    _ = 9 / 4 * ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u := by
        rw [hsum]
    _ ≤ 9 / 4 * (4 / δ s) := by
        have := hUmono.trans hwindow
        gcongr
    _ = 9 / δ s := by field_simp

end MainSpacing


/-- **Spacing lemma, σ = 4**: `Σ_{t≠s} δ t/(freq s − freq t)⁴ ≤ 27/(δ s)³`. -/
theorem spacing_four (h : Adm freq δ) (s : ι) :
    ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 4 ≤ 27 / δ s ^ 3 := by
  classical
  have hδs := h.pos s
  rcases Finset.eq_empty_or_nonempty (Finset.univ.erase s) with he | hne
  · rw [he, Finset.sum_empty]; positivity
  obtain ⟨t₀, ht₀⟩ := hne
  set g : ℝ → ℝ := fun u => ((u - freq s) ^ 4)⁻¹ with hg
  set M : ℝ := Finset.univ.sup' ⟨s, Finset.mem_univ s⟩ (fun t => |freq s - freq t|) with hM
  set R : ℝ := 3 / 2 * M + 1 with hR
  have hMle : ∀ t : ι, |freq s - freq t| ≤ M := fun t =>
    Finset.le_sup' (fun r => |freq s - freq r|) (Finset.mem_univ t)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMle s)
  have hδM : δ s ≤ M := (h.le s t₀ (Finset.ne_of_mem_erase ht₀).symm).trans (hMle t₀)
  have hRδ : δ s / 2 ≤ R := by linarith
  have hintW : MeasureTheory.IntegrableOn g (window freq δ s R) :=
    window_integrable (freq := freq) (δ := δ) hδs four_ne_zero
  have hsub : ∀ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t ⊆ window freq δ s R := by
    intro t ht u hu
    exact mem_window h (Finset.ne_of_mem_erase ht) (by linarith [hMle t]) hu
  have hper : ∀ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 4
      ≤ 81 / 16 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
    intro t ht
    have hts : t ≠ s := Finset.ne_of_mem_erase ht
    have hfst : (freq s - freq t) ≠ 0 := sub_ne_zero.2 fun hh => hts (h.inj hh.symm)
    have hpos4 : 0 < (freq s - freq t) ^ 4 := by positivity
    have hδt := h.pos t
    have hlow : ∀ u ∈ Adm.itv (freq := freq) (δ := δ) t,
        (81 / 16 * (freq s - freq t) ^ 4)⁻¹ ≤ g u := by
      intro u hu
      have hb := h.abs_le_of_mem_itv hts hu
      have hu0 : 0 < |u - freq s| := lt_of_lt_of_le (by linarith) hb.2
      have hsq : (u - freq s) ^ 4 ≤ 81 / 16 * (freq s - freq t) ^ 4 := by
        have h1 : |u - freq s| ≤ 3 / 2 * |freq s - freq t| := by
          rw [abs_sub_comm]; exact hb.1
        calc (u - freq s) ^ 4 = |u - freq s| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
          _ ≤ (3 / 2 * |freq s - freq t|) ^ 4 := by gcongr
          _ = 81 / 16 * |freq s - freq t| ^ 4 := by ring
          _ = 81 / 16 * (freq s - freq t) ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      have hupos : 0 < (u - freq s) ^ 4 := by
        have := abs_pos.1 hu0; positivity
      show _ ≤ ((u - freq s) ^ 4)⁻¹
      exact (inv_le_inv₀ (by positivity) hupos).2 hsq
    have hintT : MeasureTheory.IntegrableOn g (Adm.itv (freq := freq) (δ := δ) t) :=
      hintW.mono_set (hsub t ht)
    have h1 : ∫ _u in Adm.itv (freq := freq) (δ := δ) t, (81 / 16 * (freq s - freq t) ^ 4)⁻¹
        ≤ ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
      apply MeasureTheory.setIntegral_mono_on
      · exact MeasureTheory.integrableOn_const (by simp [Adm.itv])
      · exact hintT
      · exact measurableSet_Ioo
      · exact hlow
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at h1
    have hvol : (volume (Adm.itv (freq := freq) (δ := δ) t)).toReal = δ t := by
      rw [Adm.itv, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [MeasureTheory.measureReal_def, hvol] at h1
    calc δ t / (freq s - freq t) ^ 4
        = 81 / 16 * (δ t * (81 / 16 * (freq s - freq t) ^ 4)⁻¹) := by
          field_simp
      _ ≤ 81 / 16 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
          gcongr
  have hdisj : (↑(Finset.univ.erase s) : Set ι).PairwiseDisjoint
      (fun t => Adm.itv (freq := freq) (δ := δ) t) :=
    (h.itv_disjoint).subset (Set.subset_univ _)
  have hsum : ∑ t ∈ Finset.univ.erase s, ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u
      = ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u := by
    rw [MeasureTheory.integral_biUnion_finset]
    · exact fun t _ => measurableSet_Ioo
    · exact hdisj
    · exact fun t ht => hintW.mono_set (hsub t ht)
  have hUsub : (⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t)
      ⊆ window freq δ s R := by
    simp only [Set.iUnion_subset_iff]
    exact fun t ht => hsub t ht
  have hUmono : ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u
      ≤ ∫ u in window freq δ s R, g u := by
    apply MeasureTheory.setIntegral_mono_set hintW
    · exact Filter.Eventually.of_forall fun u => by positivity
    · exact Filter.Eventually.of_forall hUsub
  have hwindow : ∫ u in window freq δ s R, g u ≤ 16 / (3 * δ s ^ 3) := by
    have hd : Disjoint (Set.Icc (freq s - R) (freq s - δ s / 2))
        (Set.Icc (freq s + δ s / 2) (freq s + R)) := by
      rw [Set.disjoint_left]
      intro u hu hu'
      simp only [Set.mem_Icc] at hu hu'
      linarith [hu.2, hu'.1]
    have hil : MeasureTheory.IntegrableOn g (Set.Icc (freq s - R) (freq s - δ s / 2)) :=
      hintW.mono_set Set.subset_union_left
    have hir : MeasureTheory.IntegrableOn g (Set.Icc (freq s + δ s / 2) (freq s + R)) :=
      hintW.mono_set Set.subset_union_right
    rw [window, MeasureTheory.setIntegral_union hd measurableSet_Icc hil hir]
    have hleft : ∫ u in Set.Icc (freq s - R) (freq s - δ s / 2), g u
        = -((R ^ (3:ℕ))⁻¹ / 3) + ((δ s / 2) ^ (3:ℕ))⁻¹ / 3 := by
      rw [hg, integral_inv_four_Icc (by linarith) (Or.inr (by linarith))]
      have e1 : freq s - R - freq s = -R := by ring
      have e2 : freq s - δ s / 2 - freq s = -(δ s / 2) := by ring
      rw [e1, e2]
      have e3 : (-R) ^ (3:ℕ) = -(R ^ (3:ℕ)) := by ring
      have e4 : (-(δ s / 2)) ^ (3:ℕ) = -((δ s / 2) ^ (3:ℕ)) := by ring
      rw [e3, e4, inv_neg, inv_neg]
      ring
    have hright : ∫ u in Set.Icc (freq s + δ s / 2) (freq s + R), g u
        = ((δ s / 2) ^ (3:ℕ))⁻¹ / 3 - (R ^ (3:ℕ))⁻¹ / 3 := by
      rw [hg, integral_inv_four_Icc (by linarith) (Or.inl (by linarith))]
      have e1 : freq s + δ s / 2 - freq s = δ s / 2 := by ring
      have e2 : freq s + R - freq s = R := by ring
      rw [e1, e2]
    rw [hleft, hright]
    have hR0 : 0 < R := by linarith
    have hRi : 0 < (R ^ (3:ℕ))⁻¹ := by positivity
    have hhalf : ((δ s / 2) ^ (3:ℕ))⁻¹ = 8 / δ s ^ 3 := by
      rw [div_pow]
      norm_num
    have h16 : 16 / (3 * δ s ^ 3) = 8 / δ s ^ 3 / 3 + 8 / δ s ^ 3 / 3 := by ring
    rw [hhalf]
    linarith
  calc ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 4
      ≤ ∑ t ∈ Finset.univ.erase s, 81 / 16 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u :=
        Finset.sum_le_sum hper
    _ = 81 / 16 * ∑ t ∈ Finset.univ.erase s, ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
        rw [Finset.mul_sum]
    _ = 81 / 16 * ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u := by
        rw [hsum]
    _ ≤ 81 / 16 * (16 / (3 * δ s ^ 3)) := by
        have := hUmono.trans hwindow
        gcongr
    _ = 27 / δ s ^ 3 := by field_simp; ring

/-- **Two-point lemma** (replaces Preissmann Lemme 6 at constant 36). -/
theorem two_point (h : Adm freq δ) {l m : ι} (hlm : l ≠ m) :
    ∑ k ∈ (Finset.univ.erase l).erase m,
        δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
      ≤ 36 * (δ l + δ m) / (δ l * δ m * (freq l - freq m) ^ 2) := by
  classical
  have hδl := h.pos l
  have hδm := h.pos m
  have hflm : (freq l - freq m) ≠ 0 := sub_ne_zero.2 fun hh => hlm (h.inj hh)
  have hC : 0 < (freq l - freq m) ^ 2 := pow_two_pos_of_ne_zero hflm
  have esq : ∀ x y : ℝ, (x - y) ^ 2 = (y - x) ^ 2 := fun x y => by ring
  have hsplit : ∀ k ∈ (Finset.univ.erase l).erase m,
      δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
        ≤ δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2)
          + δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by
    intro k hk
    have hkm : k ≠ m := Finset.ne_of_mem_erase hk
    have hkl : k ≠ l := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hkl' : (freq k - freq l) ≠ 0 := sub_ne_zero.2 fun hh => hkl (h.inj hh)
    have hkm' : (freq k - freq m) ≠ 0 := sub_ne_zero.2 fun hh => hkm (h.inj hh)
    have hA : 0 < (freq k - freq l) ^ 2 := pow_two_pos_of_ne_zero hkl'
    have hB : 0 < (freq k - freq m) ^ 2 := pow_two_pos_of_ne_zero hkm'
    have hδk := h.pos k
    have htri : |freq l - freq m| ≤ |freq k - freq l| + |freq k - freq m| := by
      calc |freq l - freq m| = |(freq l - freq k) + (freq k - freq m)| := by ring_nf
        _ ≤ |freq l - freq k| + |freq k - freq m| := abs_add_le _ _
        _ = |freq k - freq l| + |freq k - freq m| := by rw [abs_sub_comm (freq l) (freq k)]
    have habs : 0 ≤ |freq l - freq m| := abs_nonneg _
    rcases le_total (|freq l - freq m| / 2) (|freq k - freq m|) with hP | hP
    · -- k far from m: keep the l-factor, crush the m-factor
      have hBC : (freq l - freq m) ^ 2 / 4 ≤ (freq k - freq m) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hP 2
        rw [div_pow, sq_abs, sq_abs] at this
        linarith
      have key : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
          ≤ δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by
        have h1 : (1:ℝ) / (freq k - freq m) ^ 2 ≤ 4 / (freq l - freq m) ^ 2 := by
          rw [div_le_div_iff₀ hB hC]
          linarith
        have e : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
            = (δ k / (freq l - freq k) ^ 2) * (1 / (freq k - freq m) ^ 2) := by
          rw [esq (freq k) (freq l), div_mul_eq_div_div, div_eq_mul_one_div]
        rw [e]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hnn2 : 0 ≤ δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by positivity
      linarith
    · -- k far from l
      have hAC : (freq l - freq m) ^ 2 / 4 ≤ (freq k - freq l) ^ 2 := by
        have h2 : |freq l - freq m| / 2 ≤ |freq k - freq l| := by linarith
        have := pow_le_pow_left₀ (by positivity) h2 2
        rw [div_pow, sq_abs, sq_abs] at this
        linarith
      have key : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
          ≤ δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by
        have h1 : (1:ℝ) / (freq k - freq l) ^ 2 ≤ 4 / (freq l - freq m) ^ 2 := by
          rw [div_le_div_iff₀ hA hC]
          linarith
        have e : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
            = (δ k / (freq m - freq k) ^ 2) * (1 / (freq k - freq l) ^ 2) := by
          rw [mul_comm ((freq k - freq l) ^ 2) ((freq k - freq m) ^ 2),
            esq (freq k) (freq m), div_mul_eq_div_div, div_eq_mul_one_div]
        rw [e]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hnn2 : 0 ≤ δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by positivity
      linarith
  calc ∑ k ∈ (Finset.univ.erase l).erase m,
        δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
      ≤ ∑ k ∈ (Finset.univ.erase l).erase m,
          (δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2)
            + δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2)) :=
        Finset.sum_le_sum hsplit
    _ = (∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq l - freq k) ^ 2)
          * (4 / (freq l - freq m) ^ 2)
        + (∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq m - freq k) ^ 2)
          * (4 / (freq l - freq m) ^ 2) := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    _ ≤ (9 / δ l) * (4 / (freq l - freq m) ^ 2) + (9 / δ m) * (4 / (freq l - freq m) ^ 2) := by
        have hsl : ∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq l - freq k) ^ 2
            ≤ 9 / δ l := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
            (fun k hk => Finset.mem_of_mem_erase hk) ?_) (h.spacing_sq l)
          exact fun k _ _ => div_nonneg (h.pos k).le (sq_nonneg _)
        have hsm : ∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq m - freq k) ^ 2
            ≤ 9 / δ m := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
            (fun k hk => Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hk, Finset.mem_univ k⟩) ?_)
            (h.spacing_sq m)
          exact fun k _ _ => div_nonneg (h.pos k).le (sq_nonneg _)
        gcongr
    _ = 36 * (δ l + δ m) / (δ l * δ m * (freq l - freq m) ^ 2) := by
        field_simp
        ring


end Adm
end MV
end Zeta23
end
end

-- ===== Zeta23.MV.Quadratic =====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 1 — the quadratic-form bound `U ≤ 73 V` (arXiv:2203.14950 Thm 1.2 shape)

`U := Σ_{m≠n} δ_m^{3/2} δ_n^{1/2} t_m t_n/(freq m − freq n)²  ≤  73 Σ t_n² ` for nonneg `t`:
Cauchy–Schwarz `U² ≤ V·W`; `W = S + T` (diagonal/off-diagonal of the expanded square);
`S ≤ 27V` (σ=4 spacing); `T ≤ 72U` (two-point lemma); the quadratic inequality gives `U ≤ 73V`.
-/

noncomputable section
open Real Finset
open scoped BigOperators

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq δ : ι → ℝ}

/-- The quadratic form `U = Σ_{m≠n} δ_m^{3/2} δ_n^{1/2} t_m t_n/(freq m − freq n)²`. -/
def Uform (freq δ : ι → ℝ) (t : ι → ℝ) : ℝ :=
  ∑ m, ∑ n ∈ Finset.univ.erase m,
    δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * t m * t n / (freq m - freq n) ^ 2

/-- Swap the two layers of an `erase`-nested double sum. -/
lemma sum_erase_comm {M : Type*} [AddCommMonoid M] (F : ι → ι → M) :
    ∑ m, ∑ n ∈ Finset.univ.erase m, F m n = ∑ n, ∑ m ∈ Finset.univ.erase n, F m n := by
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun n => Finset.univ.erase n)]
  intro n m
  simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Swap the inner two layers of the distinct-triple sum (outer index `m` fixed). -/
lemma sum_erase_erase_comm {M : Type*} [AddCommMonoid M] (m : ι) (G : ι → ι → M) :
    ∑ n ∈ Finset.univ.erase m, ∑ l ∈ (Finset.univ.erase n).erase m, G n l
      = ∑ l ∈ Finset.univ.erase m, ∑ n ∈ (Finset.univ.erase l).erase m, G n l := by
  rw [Finset.sum_comm' (t' := Finset.univ.erase m)
    (s' := fun l => (Finset.univ.erase l).erase m)]
  intro n l
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, Ne.symm h3⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h3, Ne.symm h2⟩

/-- **Step 1**: `U ≤ 73 Σ t²` for admissible `(freq, δ)` and nonneg `t`. -/
theorem Uform_le (h : Adm freq δ) (t : ι → ℝ) (ht : ∀ r, 0 ≤ t r) :
    Uform freq δ t ≤ 73 * ∑ n, t n ^ 2 := by
  classical
  set V : ℝ := ∑ n, t n ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun n _ => sq_nonneg _
  set f : ι → ι → ℝ := fun m n => δ m * Real.sqrt (δ m) * t m / (freq m - freq n) ^ 2 with hf
  have hf0 : ∀ m n, 0 ≤ f m n := by
    intro m n
    have := (h.pos m).le
    have := ht m
    rw [hf]
    positivity
  set B : ι → ℝ := fun n => ∑ m ∈ Finset.univ.erase n, f m n with hB
  have hU0 : 0 ≤ Uform freq δ t := by
    apply Finset.sum_nonneg
    intro m _
    apply Finset.sum_nonneg
    intro n _
    have h1 := (h.pos m).le
    have h2 := (h.pos n).le
    have h3 := ht m
    have h4 := ht n
    positivity
  have hUeq : Uform freq δ t = ∑ n, t n * (Real.sqrt (δ n) * B n) := by
    rw [Uform, sum_erase_comm (fun m n => δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * t m * t n
      / (freq m - freq n) ^ 2)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hB, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hf]
    ring
  set W : ℝ := ∑ n, δ n * B n ^ 2 with hW
  have hCS : Uform freq δ t ^ 2 ≤ V * W := by
    rw [hUeq]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ t (fun n => Real.sqrt (δ n) * B n)
    calc (∑ n, t n * (Real.sqrt (δ n) * B n)) ^ 2
        ≤ (∑ n, t n ^ 2) * ∑ n, (Real.sqrt (δ n) * B n) ^ 2 := hcs
      _ = V * W := by
          rw [hV, hW]
          congr 1
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [mul_pow, Real.sq_sqrt (h.pos n).le]
  -- expand W = S + T
  have hWeq : W = (∑ n, ∑ m ∈ Finset.univ.erase n, δ n * (f m n * f m n))
      + ∑ n, ∑ m ∈ Finset.univ.erase n, ∑ l ∈ (Finset.univ.erase n).erase m,
          δ n * (f m n * f l n) := by
    rw [hW, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hB, sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mul_sum, ← Finset.add_sum_erase _ (fun l => δ n * (f m n * f l n)) hm]
  -- S ≤ 27 V
  have hS : (∑ n, ∑ m ∈ Finset.univ.erase n, δ n * (f m n * f m n)) ≤ 27 * V := by
    rw [← sum_erase_comm (fun m n => δ n * (f m n * f m n))]
    have hper : ∀ m ∈ (Finset.univ : Finset ι),
        ∑ n ∈ Finset.univ.erase m, δ n * (f m n * f m n) ≤ 27 * t m ^ 2 := by
      intro m _
      have hδm := h.pos m
      have hss : Real.sqrt (δ m) * Real.sqrt (δ m) = δ m := Real.mul_self_sqrt hδm.le
      have e2 : ∀ n, δ n * (f m n * f m n)
          = (δ m ^ 3 * t m ^ 2) * (δ n / (freq m - freq n) ^ 4) := by
        intro n
        rw [hf]
        have e3 : ((freq m - freq n) ^ 2) * ((freq m - freq n) ^ 2)
            = (freq m - freq n) ^ 4 := by ring
        field_simp
        rw [Real.sq_sqrt hδm.le]
      calc ∑ n ∈ Finset.univ.erase m, δ n * (f m n * f m n)
          = (δ m ^ 3 * t m ^ 2) * ∑ n ∈ Finset.univ.erase m, δ n / (freq m - freq n) ^ 4 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun n _ => e2 n
        _ ≤ (δ m ^ 3 * t m ^ 2) * (27 / δ m ^ 3) := by
            have hnn : 0 ≤ δ m ^ 3 * t m ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left (h.spacing_four m) hnn
        _ = 27 * t m ^ 2 := by field_simp
    calc ∑ m, ∑ n ∈ Finset.univ.erase m, δ n * (f m n * f m n)
        ≤ ∑ m, 27 * t m ^ 2 := Finset.sum_le_sum hper
      _ = 27 * V := by rw [hV, Finset.mul_sum]
  -- T ≤ 72 U
  have hT : (∑ n, ∑ m ∈ Finset.univ.erase n, ∑ l ∈ (Finset.univ.erase n).erase m,
        δ n * (f m n * f l n)) ≤ 72 * Uform freq δ t := by
    rw [← sum_erase_comm (fun m n => ∑ l ∈ (Finset.univ.erase n).erase m, δ n * (f m n * f l n))]
    have hswap : ∀ m : ι, ∑ n ∈ Finset.univ.erase m, ∑ l ∈ (Finset.univ.erase n).erase m,
        δ n * (f m n * f l n)
        = ∑ l ∈ Finset.univ.erase m, ∑ n ∈ (Finset.univ.erase l).erase m,
            δ n * (f m n * f l n) :=
      fun m => sum_erase_erase_comm m (fun n l => δ n * (f m n * f l n))
    calc ∑ m, ∑ n ∈ Finset.univ.erase m, ∑ l ∈ (Finset.univ.erase n).erase m,
          δ n * (f m n * f l n)
        = ∑ m, ∑ l ∈ Finset.univ.erase m, ∑ n ∈ (Finset.univ.erase l).erase m,
            δ n * (f m n * f l n) := Finset.sum_congr rfl fun m _ => hswap m
      _ ≤ ∑ m, ∑ l ∈ Finset.univ.erase m,
            (δ m * Real.sqrt (δ m) * t m) * (δ l * Real.sqrt (δ l) * t l)
              * (36 * (δ l + δ m) / (δ l * δ m * (freq l - freq m) ^ 2)) := by
          refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun l hl => ?_
          have hlm : l ≠ m := Finset.ne_of_mem_erase hl
          have hc1 : 0 ≤ δ m * Real.sqrt (δ m) * t m := by
            have := (h.pos m).le; have := ht m; positivity
          have hc2 : 0 ≤ δ l * Real.sqrt (δ l) * t l := by
            have := (h.pos l).le; have := ht l; positivity
          have hexp : ∑ n ∈ (Finset.univ.erase l).erase m, δ n * (f m n * f l n)
              = (δ m * Real.sqrt (δ m) * t m) * (δ l * Real.sqrt (δ l) * t l)
                * ∑ n ∈ (Finset.univ.erase l).erase m,
                    δ n / ((freq n - freq l) ^ 2 * (freq n - freq m) ^ 2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n hn => ?_
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            have hnl : n ≠ l := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hn)
            have h1 : freq n - freq m ≠ 0 := sub_ne_zero.2 fun hh => hnm (h.inj hh)
            have h2 : freq n - freq l ≠ 0 := sub_ne_zero.2 fun hh => hnl (h.inj hh)
            simp only [hf]
            rw [show (freq m - freq n) ^ 2 = (freq n - freq m) ^ 2 by ring,
              show (freq l - freq n) ^ 2 = (freq n - freq l) ^ 2 by ring]
            field_simp
          rw [hexp]
          exact mul_le_mul_of_nonneg_left (h.two_point hlm) (mul_nonneg hc1 hc2)
      _ = ∑ m, ∑ l ∈ Finset.univ.erase m, 36 *
            (δ m * Real.sqrt (δ m) * Real.sqrt (δ l) * t m * t l / (freq m - freq l) ^ 2
              + δ l * Real.sqrt (δ l) * Real.sqrt (δ m) * t l * t m / (freq m - freq l) ^ 2) := by
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l hl => ?_
          have hlm : l ≠ m := Finset.ne_of_mem_erase hl
          have hδl := h.pos l
          have hδm := h.pos m
          have hsl : Real.sqrt (δ l) * Real.sqrt (δ l) = δ l := Real.mul_self_sqrt hδl.le
          have hsm : Real.sqrt (δ m) * Real.sqrt (δ m) = δ m := Real.mul_self_sqrt hδm.le
          have hX : freq l - freq m ≠ 0 := sub_ne_zero.2 fun hh => hlm (h.inj hh)
          have hfe : (freq m - freq l) ^ 2 = (freq l - freq m) ^ 2 := by ring
          rw [hfe]
          field_simp
          ring
      _ = 36 * ((∑ m, ∑ l ∈ Finset.univ.erase m,
              δ m * Real.sqrt (δ m) * Real.sqrt (δ l) * t m * t l / (freq m - freq l) ^ 2)
            + ∑ m, ∑ l ∈ Finset.univ.erase m,
              δ l * Real.sqrt (δ l) * Real.sqrt (δ m) * t l * t m / (freq m - freq l) ^ 2) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      _ = 72 * Uform freq δ t := by
          have hsecond : (∑ m, ∑ l ∈ Finset.univ.erase m,
              δ l * Real.sqrt (δ l) * Real.sqrt (δ m) * t l * t m / (freq m - freq l) ^ 2)
              = Uform freq δ t := by
            rw [sum_erase_comm (fun m l => δ l * Real.sqrt (δ l) * Real.sqrt (δ m) * t l * t m
              / (freq m - freq l) ^ 2)]
            rw [Uform]
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
            rw [show (freq m - freq l) ^ 2 = (freq l - freq m) ^ 2 by ring]
          rw [hsecond, Uform]
          ring
  -- assemble the quadratic inequality
  have hq : Uform freq δ t ^ 2 ≤ V * (27 * V + 72 * Uform freq δ t) := by
    calc Uform freq δ t ^ 2 ≤ V * W := hCS
      _ = V * ((∑ n, ∑ m ∈ Finset.univ.erase n, δ n * (f m n * f m n))
          + ∑ n, ∑ m ∈ Finset.univ.erase n, ∑ l ∈ (Finset.univ.erase n).erase m,
              δ n * (f m n * f l n)) := by rw [hWeq]
      _ ≤ V * (27 * V + 72 * Uform freq δ t) := by
          apply mul_le_mul_of_nonneg_left _ hV0
          exact add_le_add hS hT
  nlinarith [hU0, hV0, sq_nonneg (Uform freq δ t - 73 * V), sq_nonneg V,
    mul_nonneg hU0 hV0, mul_nonneg hV0 hV0]

end MV
end Zeta23
end
end

-- ===== Zeta23.MV.EigenIdentity =====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The Preissmann–Lévêque eigen-identity (arXiv:2203.14950 Lemma 2.1)

For real `c_r > 0`, injective real `freq`, complex `u` and real `μ` with the eigen-relation
`Σ_{n≠m} c_m c_n u_n/(freq m − freq n) = iμ u_m` for every `m`, we prove, for every `m`,

  `μ² |u_m|² = Σ_{n≠m} c_m² c_n² |u_n|²/(freq m − freq n)²
               + 2 Σ_{n≠m} c_m³ c_n Re(u_m ū_n)/(freq m − freq n)²`.

Proof (pure finite algebra): expand `|iμ u_m|²` as a double sum over `(n,p)`; the diagonal
`p = n` is the first term; off the diagonal use the partial fraction
`1/((λm−λn)(λm−λp)) = 1/((λm−λn)(λn−λp)) − 1/((λm−λp)(λn−λp))` to write the summand as
`G(n,p) + G(p,n)`, so the off-diagonal part is `2 Σ_n Σ_{p≠n,m} G(n,p)`; the inner sum is
`Re(u_n · W_n)` with `W_n = Σ_{p≠n,m} c_p ū_p/(λn−λp)`, and the conjugate eigen-relation at `n`
gives `W_n = −iμ ū_n/c_n − c_m ū_m/(λn−λm)`; the `−iμ|u_n|²/c_n` piece is purely imaginary and
dies under `Re` — the Montgomery–Vaughan cancellation — leaving the second term.
-/

noncomputable section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq : ι → ℝ}

/-- `‖z‖² = Re(z z̄)`. -/
private lemma norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- `Re(u_n ū_p)` is symmetric in `(n,p)`. -/
private lemma re_mul_conj_comm (a b : ℂ) : (a * conj b).re = (b * conj a).re := by
  simp [Complex.mul_re]; ring

/-- **Preissmann–Lévêque eigen-identity** (arXiv:2203.14950 Lemma 2.1). -/
theorem eigen_identity' (hinj : Function.Injective freq) (c : ι → ℝ) (hc : ∀ r, 0 < c r)
    (u : ι → ℂ) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
        ((c m * c n / (freq m - freq n) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m)
    (m : ι) :
    μ ^ 2 * ‖u m‖ ^ 2 =
      (∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2)
      + 2 * ∑ n ∈ Finset.univ.erase m,
          c m ^ 3 * c n * (u m * conj (u n)).re / (freq m - freq n) ^ 2 := by
  classical
  set S : Finset ι := Finset.univ.erase m with hSdef
  have hmemS : ∀ {n : ι}, n ∈ S → n ≠ m := fun h => (Finset.mem_erase.mp h).1
  have hfr : ∀ {n p : ι}, n ≠ p → freq n - freq p ≠ 0 :=
    fun h => sub_ne_zero.mpr (fun e => h (hinj e))
  -- real coefficients a_n := c_m c_n/(λ_m − λ_n) and the real numbers R n p := Re(u_n ū_p)
  set a : ι → ℝ := fun n => c m * c n / (freq m - freq n) with hadef
  set R : ι → ι → ℝ := fun n p => (u n * conj (u p)).re with hRdef
  have hRsymm : ∀ n p, R n p = R p n := fun n p => re_mul_conj_comm _ _
  have hRdiag : ∀ n, R n n = ‖u n‖ ^ 2 := fun n => (norm_sq_eq_re_mul_conj _).symm
  /- Step A: μ²|u_m|² = Σ_n Σ_p a_n a_p R(n,p). -/
  have hA : μ ^ 2 * ‖u m‖ ^ 2 = ∑ n ∈ S, ∑ p ∈ S, a n * a p * R n p := by
    have h1 : μ ^ 2 * ‖u m‖ ^ 2 = ‖(μ : ℂ) * Complex.I * u m‖ ^ 2 := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, mul_pow,
        Real.norm_eq_abs, sq_abs]
    rw [h1, ← heig m, norm_sq_eq_re_mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    have : ((a n : ℝ) : ℂ) * u n * (((a p : ℝ) : ℂ) * conj (u p))
        = ((a n * a p : ℝ) : ℂ) * (u n * conj (u p)) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  /- Step B: split off the diagonal. -/
  have hB : ∑ n ∈ S, ∑ p ∈ S, a n * a p * R n p
      = (∑ n ∈ S, a n * a n * R n n) + ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Finset.add_sum_erase S _ hn]
  have hdiag : ∑ n ∈ S, a n * a n * R n n
      = ∑ n ∈ S, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have h1 := hfr (hmemS hn).symm
    rw [hRdiag]; simp only [hadef]; field_simp
  /- Step C: the off-diagonal part. G(n,p) := c_m² c_n c_p R(n,p)/((λm−λn)(λn−λp)). -/
  set G : ι → ι → ℝ := fun n p =>
    c m ^ 2 * c n * c p * R n p / ((freq m - freq n) * (freq n - freq p)) with hGdef
  have hF : ∀ n ∈ S, ∀ p ∈ S.erase n, a n * a p * R n p = G n p + G p n := by
    intro n hn p hp
    have hpn : p ≠ n := (Finset.mem_erase.mp hp).1
    have hpS : p ∈ S := (Finset.mem_erase.mp hp).2
    have h1 := hfr (hmemS hn).symm   -- freq m - freq n ≠ 0
    have h2 := hfr (hmemS hpS).symm  -- freq m - freq p ≠ 0
    have h3 := hfr hpn.symm          -- freq n - freq p ≠ 0
    have h4 := hfr hpn               -- freq p - freq n ≠ 0
    simp only [hadef, hGdef]
    rw [hRsymm p n]
    field_simp
    ring
  have hOff : ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p
      = 2 * ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
    have hswap : ∑ n ∈ S, ∑ p ∈ S.erase n, G p n = ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
      refine Finset.sum_comm' ?_
      intro n p
      simp only [Finset.mem_erase]
      tauto
    calc ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p
        = ∑ n ∈ S, ∑ p ∈ S.erase n, (G n p + G p n) := by
          refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun p hp => hF n hn p hp
      _ = (∑ n ∈ S, ∑ p ∈ S.erase n, G n p) + ∑ n ∈ S, ∑ p ∈ S.erase n, G p n := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => Finset.sum_add_distrib
      _ = 2 * ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by rw [hswap]; ring
  /- Step C2–C4: the inner sum, via the conjugate eigen-relation at n. -/
  have hInner : ∀ n ∈ S, ∑ p ∈ S.erase n, G n p
      = c m ^ 3 * c n * R m n / (freq m - freq n) ^ 2 := by
    intro n hn
    have hnm : n ≠ m := hmemS hn
    have h1 : freq m - freq n ≠ 0 := hfr hnm.symm
    have h1' : freq n - freq m ≠ 0 := hfr hnm
    have hcn : (c n : ℂ) ≠ 0 := by exact_mod_cast (hc n).ne'
    -- W_n := Σ_{p ∈ S.erase n} (c_p/(λn−λp)) ū_p
    set W : ℂ := ∑ p ∈ S.erase n, ((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p) with hWdef
    -- (i) Σ_p G n p = (c_m² c_n/(λm−λn)) · Re(u_n W)
    have hi : ∑ p ∈ S.erase n, G n p = c m ^ 2 * c n / (freq m - freq n) * (u n * W).re := by
      rw [hWdef, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpn : p ≠ n := (Finset.mem_erase.mp hp).1
      have h3 : freq n - freq p ≠ 0 := hfr hpn.symm
      have : u n * (((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p))
          = ((c p / (freq n - freq p) : ℝ) : ℂ) * (u n * conj (u p)) := by ring
      rw [this, Complex.re_ofReal_mul]
      simp only [hGdef, hRdef]
      field_simp
    -- (ii) the conjugate eigen-relation at n, with the p = m term split off:
    --      c_n · (c_m/(λn−λm) ū_m + W) = −iμ ū_n
    have hii : (c n : ℂ) * ((((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m) + W)
        = -((μ : ℂ) * Complex.I * conj (u n)) := by
      have hconj := congrArg conj (heig n)
      rw [map_sum] at hconj
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hconj
      -- split p = m off the sum over univ.erase n
      have hmS : m ∈ Finset.univ.erase n := Finset.mem_erase.mpr ⟨hnm.symm, Finset.mem_univ _⟩
      have hsplit := Finset.add_sum_erase (Finset.univ.erase n)
        (fun p => ((c n * c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)) hmS
      have hSS : (Finset.univ.erase n).erase m = S.erase n := by
        rw [hSdef, Finset.erase_right_comm]
      rw [hSS] at hsplit
      rw [← hsplit] at hconj
      -- factor c n out
      have hfac : ∀ p, ((c n * c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)
          = (c n : ℂ) * (((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)) := by
        intro p; push_cast; ring
      simp only [hfac, ← Finset.mul_sum] at hconj
      rw [hWdef]
      linear_combination hconj
    -- (iii) solve for W and take Re(u_n W): the −iμ|u_n|²/c_n piece is purely imaginary
    have hiii : (u n * W).re = -(c m / (freq n - freq m)) * R n m := by
      have hW : W = -((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ)
          - (((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m) := by
        field_simp
        linear_combination hii
      have hkill : (u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))).re = 0 := by
        have hz : u n * conj (u n) = ((‖u n‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have e : u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))
            = -((μ : ℂ) / (c n : ℂ)) * (u n * conj (u n)) * Complex.I := by
          field_simp
        have : u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))
            = ((-(μ / c n) * ‖u n‖ ^ 2 : ℝ) : ℂ) * Complex.I := by
          rw [e, hz]; push_cast; ring
        rw [this, Complex.re_ofReal_mul]; simp
      rw [hW, mul_sub, Complex.sub_re, hkill, zero_sub]
      have : u n * ((((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m))
          = (((c m / (freq n - freq m)) : ℝ) : ℂ) * (u n * conj (u m)) := by ring
      rw [this, Complex.re_ofReal_mul]
      simp only [hRdef]; ring
    rw [hi, hiii, hRsymm n m]
    field_simp
    ring
  -- assemble
  rw [hA, hB, hdiag, hOff, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hInner n hn]

end MV
end Zeta23

end
end

-- ===== Zeta23.MV.Eigen =====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV steps 2–3 — the Preissmann–Lévêque eigen-identity and the eigenvalue bound

* `eigen_identity` (arXiv:2203.14950 Lemma 2.1): pure Finset algebra
  over ℂ + partial fractions + the conjugate eigen-relation; the `−iμ` cross piece dies under
  `Re` — the cancellation at the heart of Montgomery–Vaughan.
* `eigen_bound`: with `c = √δ`, summing the identity over `m` for a unit
  eigenvector and inserting `spacing_sq` (≤ 9) and `Uform_le` (≤ 73):
  `μ² ≤ 9 + 2·73 = 155 ≤ 13²`.
-/

noncomputable section
open Real Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq δ : ι → ℝ}

/-- **Step 3, eigenvalue bound**: every eigenvalue of the normalized matrix
(`c = √δ`) with a unit eigenvector has `|μ| ≤ 13`. -/
theorem eigen_bound (h : Adm freq δ) (u : ι → ℂ) (hu : ∑ n, ‖u n‖ ^ 2 = 1) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
        ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * u n
          = (μ : ℂ) * Complex.I * u m) :
    |μ| ≤ 13 := by
  classical
  set c : ι → ℝ := fun r => Real.sqrt (δ r) with hc
  have hcpos : ∀ r, 0 < c r := fun r => Real.sqrt_pos.2 (h.pos r)
  have hid := eigen_identity' h.inj c hcpos u μ heig
  have hsumid : μ ^ 2
      = (∑ m, ∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2)
        + 2 * ∑ m, ∑ n ∈ Finset.univ.erase m,
            c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2 := by
    calc μ ^ 2 = μ ^ 2 * ∑ m, ‖u m‖ ^ 2 := by rw [hu, mul_one]
      _ = ∑ m, μ ^ 2 * ‖u m‖ ^ 2 := Finset.mul_sum _ _ _
      _ = ∑ m, ((∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2)
            + 2 * ∑ n ∈ Finset.univ.erase m,
                c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2) :=
          Finset.sum_congr rfl fun m _ => hid m
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hS : (∑ m, ∑ n ∈ Finset.univ.erase m,
      (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2) ≤ 9 := by
    have e1 : ∀ m n, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2
        = (δ n * ‖u n‖ ^ 2) * (δ m / (freq n - freq m) ^ 2) := by
      intro m n
      rw [hc]
      simp only [mul_pow, Real.sq_sqrt (h.pos m).le, Real.sq_sqrt (h.pos n).le,
        show (freq m - freq n) ^ 2 = (freq n - freq m) ^ 2 by ring]
      ring
    calc ∑ m, ∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2
        = ∑ m, ∑ n ∈ Finset.univ.erase m, (δ n * ‖u n‖ ^ 2) * (δ m / (freq n - freq m) ^ 2) :=
          Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => e1 m n
      _ = ∑ n, ∑ m ∈ Finset.univ.erase n, (δ n * ‖u n‖ ^ 2) * (δ m / (freq n - freq m) ^ 2) :=
          sum_erase_comm _
      _ = ∑ n, (δ n * ‖u n‖ ^ 2) * ∑ m ∈ Finset.univ.erase n, δ m / (freq n - freq m) ^ 2 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ n, (δ n * ‖u n‖ ^ 2) * (9 / δ n) := by
          refine Finset.sum_le_sum fun n _ => ?_
          refine mul_le_mul_of_nonneg_left (h.spacing_sq n) ?_
          have := (h.pos n).le
          positivity
      _ = ∑ n, 9 * ‖u n‖ ^ 2 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          have hδn := (h.pos n).ne'
          field_simp
      _ = 9 := by rw [← Finset.mul_sum, hu, mul_one]
  have hT : |∑ m, ∑ n ∈ Finset.univ.erase m,
      c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2| ≤ 73 := by
    have hper : ∀ m n : ι, |c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re
          / (freq m - freq n) ^ 2|
        ≤ δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * ‖u m‖ * ‖u n‖ / (freq m - freq n) ^ 2 := by
      intro m n
      have hre : |(u m * (starRingEnd ℂ) (u n)).re| ≤ ‖u m‖ * ‖u n‖ := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, RCLike.norm_conj]
      have hcube : c m ^ 3 = δ m * Real.sqrt (δ m) := by
        rw [hc]
        calc Real.sqrt (δ m) ^ 3 = Real.sqrt (δ m) ^ 2 * Real.sqrt (δ m) := by ring
          _ = δ m * Real.sqrt (δ m) := by rw [Real.sq_sqrt (h.pos m).le]
      rw [abs_div, abs_of_nonneg (sq_nonneg (freq m - freq n)), abs_mul, hcube]
      have hnn : (0:ℝ) ≤ δ m * Real.sqrt (δ m) * Real.sqrt (δ n) := by
        have := (h.pos m).le
        have := (h.pos n).le
        positivity
      have h1 : |δ m * Real.sqrt (δ m) * (c n)| = δ m * Real.sqrt (δ m) * Real.sqrt (δ n) := by
        rw [hc, abs_of_nonneg hnn]
      rw [h1]
      calc δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * |(u m * (starRingEnd ℂ) (u n)).re|
            / (freq m - freq n) ^ 2
          ≤ δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * (‖u m‖ * ‖u n‖)
              / (freq m - freq n) ^ 2 := by gcongr
        _ = δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * ‖u m‖ * ‖u n‖
              / (freq m - freq n) ^ 2 := by ring
    calc |∑ m, ∑ n ∈ Finset.univ.erase m,
          c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2|
        ≤ ∑ m, |∑ n ∈ Finset.univ.erase m,
            c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m, ∑ n ∈ Finset.univ.erase m,
            |c m ^ 3 * c n * (u m * (starRingEnd ℂ) (u n)).re / (freq m - freq n) ^ 2| :=
          Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m, ∑ n ∈ Finset.univ.erase m,
            δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * ‖u m‖ * ‖u n‖ / (freq m - freq n) ^ 2 :=
          Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => hper m n
      _ = Uform freq δ (fun r => ‖u r‖) := rfl
      _ ≤ 73 * ∑ n, ‖u n‖ ^ 2 := Uform_le h _ fun r => norm_nonneg _
      _ = 73 := by rw [hu, mul_one]
  have hmain : μ ^ 2 ≤ 155 := by
    have h2 := abs_le.1 hT
    linarith [hS, h2.1, h2.2]
  nlinarith [abs_nonneg μ, sq_abs μ]

end MV
end Zeta23
end
end

-- ===== Zeta23.Defs =====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs.lean — fixed data of the paper.

Reference text: the paper "More than two thirds of the zeros of the Riemann zeta function lie on
the critical line". Bracketed labels [eq:foo] below are the paper's own labels.

Design (ζ-free abstract layer): nothing in this file mentions
riemannZeta. The zeros enter only through the abstract structure ZeroConfig
("every locally finite multiset of points in the strip 0<β<1 that is invariant under ρ ↦ 1−ρ̄",
paper end of §4). Only Zeta23/Statement.lean instantiates ZeroConfig from Mathlib's ζ.
-/

open scoped BigOperators ArithmeticFunction
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

/-! ## 0. Fourier convention dictionary  [Notation], [subsec:weil]

Paper: "Fourier transforms are f̂(τ) := ∫_ℝ f(u) e^{iτu} du, so that ∫ f ḡ = (1/2π) ∫ f̂ conj(ĝ)
and (f∗g)^ = f̂ ĝ."  and  "For f ∈ C_c²(ℝ) put h_f(z) := f̂(z) = ∫ f(u) e^{izu} du, an entire
function".  Mathlib's Real.fourierIntegral 𝓕 is ∫ f(v) e^{−2πi v ξ} dv, so for real τ:
    paperFT f τ = 𝓕 f (−τ / (2π)).
All paper-side statements use paperFT; conversion to 𝓕 happens only inside proofs. -/

/-! ## 1. Scalars depending on T only  [Notation], [eq:RvM], [eq:Fdef] -/

/-! ## 2. The densities μ, Π_X, P_X, ν_X  [eq:mudef]–[eq:nudef]

Paper, verbatim: "Define, for τ ∈ ℝ and X = e^L > 1, s := 1/2 + iτ,
  μ(τ)   := (1/2π) Re Γ'/Γ(1/4 + iτ/2) − (log π)/(2π),                      [eq:mudef]
  Π_X(τ) := 1/(2π(1/4+τ²)) + (1/π) Re (X^s − 1)/s,                           [eq:Pidef]
  P_X(τ) := −(1/π) Σ_{n≤X} Λ(n)/√n · cos(τ log n),                           [eq:Pdef]
  ν_X    := μ + Π_X + P_X."                                                   [eq:nudef]
-/

/-! ## 3. Abstract zero configurations  [Results], [subsec:weil], §4 closing paragraph -/


/-! ## 4. The test family  [subsec:family] -/

namespace Params

variable (P : Params) (T : ℝ)

/-! ### The prime-side matrix (second expression in [eq:Gdef]) -/

end Params

/-! ### The zero-side matrices  [eq:Gdef] first expression, [eq:AE], §4 Block structure -/


end Zeta23
end
end

-- ===== Zeta23.Hypotheses =====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Hypotheses.lean — the hypothesis ("axiom") boundary.

Canonical text: the paper.

PRINCIPLE: the fields of PaperInputs are PUBLISHED, CLASSICAL inputs,
stated in the paper's own form with the paper's equation labels. Everything the paper itself derives
(lem:poisson, prop:block, prop:tail, [eq:PiPfacts], [eq:Bdef], prop:trace, thm:traces, §6, taper facts
[eq:phinorms]–[eq:psiints], …) is a proof obligation and must NOT be added here. There are NO Lean
axiom declarations anywhere in this project: hypotheses are fields of the Prop-valued structure
PaperInputs, which every headline theorem takes as an explicit argument, so #print axioms stays at
{propext, Classical.choice, Quot.sound} and the trust boundary is exactly this file.

Every field below: docstring = paper label + verbatim paper statement + literature source + any
deviation in shape (∃-constant form unless the constant is load-bearing).
-/

open scoped BigOperators ArithmeticFunction ComplexConjugate ContDiff
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

/-! ## H-EF — Weil's explicit formula in the paper's spectral form  [prop:EF], [eq:EF], [eq:Wdef] -/

/-! ## H-RvM — Riemann–von Mangoldt + local zero count  [eq:RvM], [prop:tail] first line -/

/-! ## H-cheb — Chebyshev–Mertens  [lem:cheb], [eq:cheb1], [eq:cheb2] -/

/-! ## H-MV — Montgomery–Vaughan weighted Hilbert inequality  [lem:MV] -/

/-! ## H-Γ — Stirling-type facts for μ  [eq:mufacts], [eq:muints] -/

/-! ## The bundle -/

end Zeta23
end
end

-- ===== Zeta23.MV =====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/MV.lean — the Montgomery–Vaughan weighted Hilbert inequality: literature (diagonal, y = x)
form ⇒ the bilinear (x, z) form H-MV of Zeta23/Hypotheses.lean.

Purpose (trust reduction): Zeta23.MVHilbert C — what [prop:PP]/[prop:cross] consume —
is the BILINEAR inequality |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ C (Σ|x_r|²/δ_r)^{1/2} (Σ|z_r|²/δ_r)^{1/2}.
The published theorem is the case z = x.  The paper, [lem:MV] and its proof,
verbatim: "Lemma (Montgomery–Vaughan). Let λ_1,…,λ_R be distinct real numbers and
δ_r := min_{s≠r}|λ_r−λ_s|. Then for all complex x_r, z_r,
  |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ (3π/2)(Σ_r |x_r|²/δ_r)^{1/2}(Σ_r |z_r|²/δ_r)^{1/2}.
Proof. For z = x this is the weighted ("generalised") Hilbert inequality of Montgomery and Vaughan
[MV74, Theorem 2]; see also [Mon94, Chapter 7]. Any absolute constant in place of 3π/2 would
suffice below. In general, let H be the Hermitian matrix with entries i/(λ_r−λ_s) off the
diagonal and 0 on it, and Δ := diag(δ_r^{1/2}). The case z = x says |y*(ΔHΔ)y| ≤ (3π/2)‖y‖₂² for
all y, i.e. ‖ΔHΔ‖ ≤ 3π/2 since ΔHΔ is Hermitian; hence
|x*Hz| = |(Δ⁻¹x)*(ΔHΔ)(Δ⁻¹z)| ≤ (3π/2)‖Δ⁻¹x‖₂‖Δ⁻¹z‖₂."

Literature statement transcribed (H. L. Montgomery and R. C. Vaughan, "Hilbert's inequality",
J. London Math. Soc. (2) 8 (1974), 73–82, Theorem 2 = the "generalised" weighted form, their
(1.8)): if λ_1,…,λ_R are distinct reals, δ_r := min_{s≠r}|λ_r − λ_s|, then for all complex x_r,
  |Σ_{r≠s} x_r x̄_s / (λ_r − λ_s)| ≤ (3π/2) Σ_r |x_r|²/δ_r.
(The constant 3π/2 was later improved — Preissmann 1984 — but the paper says any absolute
constant suffices, and the headline result only needs ∃ C, so C is kept abstract: MVDiag C.)
As in Zeta23.MVHilbert we allow any admissible δ (δ_r > 0, δ_r ≤ |λ_r − λ_s| for s ≠ r); the right
side is antitone in δ, so this is equivalent to the min-gap δ of the literature.

We derive the bilinear form with constant 2C (not C) by POLARIZATION of the sesquilinear form plus
the scaling x ↦ t x, z ↦ z/t — an elementary route that avoids operator norms; the factor 2 is
immaterial (∃ C).  Result: Zeta23.MVHilbert_of_diag : 0 ≤ C → MVDiag C → MVHilbert (2 * C), and
Zeta23.exists_MVHilbert_of_diag for the ∃-forms used by PaperInputs.MV.
-/

noncomputable section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23

/-- **MV74 Theorem 2 (weighted Hilbert inequality), literature = diagonal form**, with an
abstract absolute constant C (MV74: C = 3π/2): for distinct real frequencies λ_r and admissible
gaps δ_r (0 < δ_r ≤ |λ_r − λ_s| for all s ≠ r), and all complex x_r,
  |Σ_{r≠s} x_r x̄_s/(λ_r − λ_s)| ≤ C · Σ_r |x_r|²/δ_r.
Same binder shape as Zeta23.MVHilbert with z := x. -/
def MVDiag (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ) (x : ι → ℂ),
    Function.Injective freq → (∀ r, 0 < δ r) → (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ C * ∑ r, ‖x r‖ ^ 2 / δ r


end Zeta23
end
end

-- ===== Zeta23.LinAlg.PosIndex =====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were produced first, as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper —
like all Lean code in this repository, written by Claude, under the direction of the paper's authors — and are
incorporated here unchanged; they have no upstream outside this project (see README § Provenance and attribution).
-/

/-!
# Positive index of a Hermitian matrix

For a Hermitian matrix `A` over `𝕜 = ℝ` or `ℂ`, the *positive index*
`n₊(A)` is the number of strictly positive eigenvalues. By Sylvester's law
of inertia this equals the maximal dimension of a subspace on which the
Hermitian form `x ↦ xᴴ A x` is positive definite.

This file defines `posIndex` via the eigenvalue count, together with the
real-valued trace `rtrace` and squared Frobenius norm `frobSq` needed for
the rank–trace inequality (paper §3, `lem:ranktrace`).
-/

end

-- ===== Zeta23.LinAlg.HermitianPosPart =====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were produced first, as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper —
like all Lean code in this repository, written by Claude, under the direction of the paper's authors — and are
incorporated here unchanged; they have no upstream outside this project (see README § Provenance and attribution).
-/

/-!
# Positive and negative parts of a Hermitian matrix

For a Hermitian matrix `Q` with spectral decomposition `Q = U diag(λ) Uᴴ`,
define `Q₊ := U diag(λ⁺) Uᴴ` and `Q₋ := U diag(λ⁻) Uᴴ` where
`λ⁺ = max(λ,0)`, `λ⁻ = max(−λ,0)`.

Then `Q = Q₊ − Q₋`, both are PSD, `Q₊ Q₋ = 0`, and `rank Q₊ = n₊(Q)`.

This is equivalent to the CFC `Q⁺`/`Q⁻` via `Matrix.IsHermitian.cfc_eq`, but
the direct spectral construction keeps the eigenvalue bookkeeping explicit,
which is what the rank–trace proof needs.
-/

noncomputable section

open Matrix Finset Unitary
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Apply a real function to a Hermitian matrix via its spectral decomposition:
`specMap hA f := U diag(f ∘ λ) Uᴴ`. (This is `Matrix.IsHermitian.cfc`, reproduced
here to keep imports light and bookkeeping explicit.) -/
def specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix n n 𝕜 :=
  conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
    (diagonal (fun i => (f (hA.eigenvalues i) : 𝕜)))

lemma specMap_id {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    specMap hA id = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rfl


end RHLinalg
end
end

-- ===== Zeta23.MV.Duality =====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 4 — spectral reduction: `eigen_bound` ⇒ `MVDiag 13` ⇒ `∃ C, MVHilbert C`

With `k_{rs} := √δ_r √δ_s/(λ_r − λ_s)` (0 on the diagonal; real antisymmetric) the matrix
`M := i·K` is Hermitian.  Every eigen-pair `(ν, v)` of `M` (unit `v`, from Mathlib's
`Matrix.IsHermitian.eigenvectorBasis`) satisfies the eigen-relation of `eigen_bound` with `μ := −ν`,
so `|ν| ≤ 13` for all eigenvalues (step 3).  Expanding in the eigenbasis
(`y* M y = Σ_i ν_i |(U*y)_i|²`, `Σ_i |(U*y)_i|² = Σ_i |y_i|²`) gives `|y* M y| ≤ 13 ‖y‖²`;
substituting `y_r := x_r/√δ_r` lands exactly on `MVDiag 13` (the literature / diagonal form of the
Montgomery–Vaughan weighted Hilbert inequality, Zeta23/MV.lean), and polarization
`exists_MVHilbert_of_diag` yields the bilinear H-MV of `Hypotheses.lean`.
-/

noncomputable section

open Finset Complex Matrix Unitary
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV

/-- The conclusion of step 3 (`Zeta23.MV.eigen_bound`, Eigen.lean) as a `Prop` with a general
constant: every solution of the normalized eigen-relation with a unit vector has `|μ| ≤ C`. -/
def EigenBound (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ), Adm freq δ →
    ∀ (u : ι → ℂ), ∑ n, ‖u n‖ ^ 2 = 1 → ∀ (μ : ℝ),
      (∀ m, ∑ n ∈ Finset.univ.erase m,
        ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * u n
          = (μ : ℂ) * Complex.I * u m) → |μ| ≤ C

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The normalized kernel `k_{rs} = √δ_r √δ_s/(freq r − freq s)`, `0` on the diagonal. -/
def kfun (freq δ : ι → ℝ) (r s : ι) : ℝ :=
  if r = s then 0 else Real.sqrt (δ r) * Real.sqrt (δ s) / (freq r - freq s)

omit [Fintype ι] in
lemma kfun_antisymm (freq δ : ι → ℝ) (r s : ι) : kfun freq δ s r = -kfun freq δ r s := by
  unfold kfun
  by_cases h : r = s
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, ← neg_div_neg_eq, neg_sub]; ring

/-- `M := i·K`, a Hermitian complex matrix. -/
def Mmat (freq δ : ι → ℝ) : Matrix ι ι ℂ := fun r s => (kfun freq δ r s : ℂ) * Complex.I

omit [Fintype ι] in
lemma Mmat_isHermitian (freq δ : ι → ℝ) : (Mmat freq δ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun r s => ?_
  simp only [Mmat, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    kfun_antisymm freq δ r s]
  push_cast
  ring

omit [DecidableEq ι] in
/-- `star v ⬝ᵥ v = Σ ‖v_i‖²` (as a complex number). -/
lemma star_dotProduct_self (v : ι → ℂ) : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

/-- Spectral expansion of the Hermitian form, complex-valued:
`x* A x = Σ_i ν_i ‖(U* x)_i‖²` with `U` the eigenvector unitary. -/
lemma star_dotProduct_mulVec_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    star x ⬝ᵥ (A *ᵥ x)
      = ((∑ i, hA.eigenvalues i *
          ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  conv_lhs => rw [← RHLinalg.specMap_id hA]
  unfold RHLinalg.specMap
  rw [conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) U, hsc, ← hc_def]
  simp only [id, dotProduct, mulVec_diagonal, Pi.star_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.conj_mul', mul_left_comm]
  rfl

/-- `Σ ‖(U* x)_i‖² = Σ ‖x_i‖²` for the eigenvector unitary `U`. -/
lemma sum_norm_sq_unitary {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  have h : star c ⬝ᵥ c = star x ⬝ᵥ x := by
    have hU : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
    rw [← hsc, hc_def, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  rw [star_dotProduct_self, star_dotProduct_self] at h
  exact_mod_cast h

/-- Every eigenvalue of `M = iK` has absolute value `≤ C` (step 3 + Mathlib eigenbasis). -/
lemma abs_eigenvalue_le {C : ℝ} (hb : EigenBound C) {freq δ : ι → ℝ} (h : Adm freq δ) (j : ι) :
    |(Mmat_isHermitian freq δ).eigenvalues j| ≤ C := by
  set hM := Mmat_isHermitian freq δ
  set ν : ℝ := hM.eigenvalues j
  set v : ι → ℂ := ⇑(hM.eigenvectorBasis j) with hvdef
  have hv : Mmat freq δ *ᵥ v = ν • v := hM.mulVec_eigenvectorBasis j
  have hunit : ∑ n, ‖v n‖ ^ 2 = 1 := by
    have h1 : ‖hM.eigenvectorBasis j‖ = 1 := hM.eigenvectorBasis.orthonormal.1 j
    rw [← EuclideanSpace.norm_sq_eq, h1, one_pow]
  -- the eigen-relation in `eigen_bound`'s shape, with μ := −ν
  have heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
      ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * v n
        = ((-ν : ℝ) : ℂ) * Complex.I * v m := by
    intro m
    have hm := congrFun hv m
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] at hm
    -- Σ_s (k m s) I v s = ν v m ; drop the diagonal term (k m m = 0)
    have hsplit : ∑ s, Mmat freq δ m s * v s
        = ∑ s ∈ Finset.univ.erase m, (kfun freq δ m s : ℂ) * Complex.I * v s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
      simp [Mmat, kfun]
    rw [hsplit] at hm
    have hk : ∀ s ∈ Finset.univ.erase m, (kfun freq δ m s : ℂ) * Complex.I * v s
        = Complex.I * (((Real.sqrt (δ m) * Real.sqrt (δ s) / (freq m - freq s) : ℝ) : ℂ) * v s) := by
      intro s hs
      have hsm : m ≠ s := fun e => (Finset.mem_erase.mp hs).1 e.symm
      simp only [kfun, if_neg hsm]; ring
    rw [Finset.sum_congr rfl hk, ← Finset.mul_sum] at hm
    -- I * X = ν v_m  ⇒  X = (−ν) I v_m
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    calc ∑ n ∈ Finset.univ.erase m,
          ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * v n
        = -Complex.I * (Complex.I * ∑ n ∈ Finset.univ.erase m,
            ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * v n) := by
          rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
      _ = -Complex.I * ((ν : ℂ) * v m) := by rw [hm]
      _ = ((-ν : ℝ) : ℂ) * Complex.I * v m := by push_cast; ring
  have := hb ι freq δ h v hunit (-ν) heig
  simpa using this

/-- The Hermitian form of `M` is bounded by `C ‖y‖²`. -/
lemma norm_form_le {C : ℝ} (hb : EigenBound C) {freq δ : ι → ℝ} (h : Adm freq δ) (y : ι → ℂ) :
    ‖star y ⬝ᵥ (Mmat freq δ *ᵥ y)‖ ≤ C * ∑ i, ‖y i‖ ^ 2 := by
  set hM := Mmat_isHermitian freq δ
  rw [star_dotProduct_mulVec_eq hM, Complex.norm_real, Real.norm_eq_abs, ← sum_norm_sq_unitary hM y,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow, sq_abs]
  exact mul_le_mul_of_nonneg_right (abs_eigenvalue_le hb h i) (sq_nonneg _)

/-- **Spectral reduction**: an eigenvalue bound `EigenBound C` gives `MVDiag C` — the
Montgomery–Vaughan weighted Hilbert inequality (diagonal / literature form, Zeta23/MV.lean). -/
theorem mvDiag_of_eigenBound {C : ℝ} (hb : EigenBound C) : MVDiag C := by
  intro ι _ _ freq δ x hinj hpos hadm
  have h : Adm freq δ := ⟨hinj, hpos, hadm⟩
  -- y_r := x_r / √δ_r
  set y : ι → ℂ := fun r => x r / (Real.sqrt (δ r) : ℂ) with hydef
  have hsq : ∀ r, (Real.sqrt (δ r) : ℂ) ≠ 0 := fun r => by
    exact_mod_cast (Real.sqrt_pos.mpr (hpos r)).ne'
  have hxy : ∀ r, x r = (Real.sqrt (δ r) : ℂ) * y r := fun r => by
    simp only [hydef]; field_simp [hsq r]
  -- Σ ‖y_r‖² = Σ ‖x_r‖²/δ_r
  have hnorm : ∑ r, ‖y r‖ ^ 2 = ∑ r, ‖x r‖ ^ 2 / δ r := by
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hydef, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (hpos r).le]
  -- the double sum is rewritten termwise:
  -- Σ_{r,s} [r≠s] x_r x̄_s/(λ_r−λ_s) = Σ_r Σ_s y_r conj(y_s) k_{rs}
  have hterm : ∀ r s, (if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ))
      = y r * conj (y s) * (kfun freq δ r s : ℂ) := by
    intro r s
    by_cases hrs : r = s
    · simp [hrs, kfun]
    · rw [if_neg hrs]
      simp only [kfun, if_neg hrs, hxy r, hxy s, map_mul, Complex.conj_ofReal]
      have hf : ((freq r - freq s : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr (fun e => hrs (hinj e))
      push_cast
      field_simp
  have hsum : (∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ))
      = conj (star y ⬝ᵥ (Mmat freq δ *ᵥ y)) * Complex.I := by
    simp only [hterm, dotProduct, Matrix.mulVec, Mmat, Pi.star_apply, Complex.star_def, map_sum,
      map_mul, Complex.conj_conj, Complex.conj_ofReal, Complex.conj_I, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (y r * conj (y s) * (kfun freq δ r s : ℂ)) * this
  rw [hsum, norm_mul, Complex.norm_I, mul_one, Complex.norm_conj, ← hnorm]
  exact norm_form_le hb h y

end MV
end Zeta23

end
end

-- ===== Zeta23.MV.Final =====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The Montgomery–Vaughan weighted Hilbert inequality

`eigen_bound` (`Zeta23/MV/Eigen.lean`) is exactly `EigenBound 13`; the spectral reduction of
`Duality.lean` turns it into `MVDiag 13` and, via polarization (`Zeta23/MV.lean`), into the
bilinear `∃ C > 0, MVHilbert C` of `Hypotheses.lean` (C = 26) — discharging `PaperInputs.MV`.
-/

noncomputable section

namespace Zeta23
namespace MV

theorem eigenBound_thirteen : EigenBound 13 :=
  fun _ι _ _ _freq _δ h u hu μ heig => eigen_bound h u hu μ heig

/-- **`MVDiag 13`** — the weighted Hilbert inequality, literature (diagonal) form. -/
theorem mvDiag_thirteen : MVDiag 13 := mvDiag_of_eigenBound eigenBound_thirteen

end MV
end Zeta23

end
end

-- ===== LeanClassics.DensityMV =====
section
/-!
# Mean value of a Dirichlet polynomial on an interval (Montgomery–Vaughan form)

`integral_norm_sq_sum_le`: for distinct real frequencies `λ_r` with `δ_r ≤ |λ_r − λ_s|` (`s ≠ r`),
`∫_a^b |∑ x_r e^{iλ_r t}|² dt ≤ (b − a) ∑ |x_r|² + 26 ∑ |x_r|²/δ_r`.

`integral_norm_sq_dirichlet_le`: for `σ ≥ 1/2` and `N ≥ 1`,
`∫_a^b |∑_{n<N} (n+1)^{−σ−it}|² dt ≤ (b − a) ∑_{n<N} (n+1)^{−2σ} + 52 N`.

Proof. Expanding `|∑|²` leaves the diagonal `(b − a) ∑ |x_r|²` and the off-diagonal
`∑_{r≠s} x_r x̄_s (e^{ic b} − e^{ic a})/(ic)`, `c = λ_r − λ_s`. With `y_r(u) = x_r e^{iλ_r u}`,
`x_r x̄_s e^{icu} = y_r(u) ȳ_s(u)`, so the off-diagonal is `(B(b) − B(a))/i` with
`B(u) = ∑_{r≠s} y_r(u) ȳ_s(u)/(λ_r − λ_s)`. The Montgomery–Vaughan Hilbert inequality, as proved in
zeta23 (`Zeta23.MV.mvDiag_thirteen`: `|B(u)| ≤ 13 ∑ |y_r(u)|²/δ_r`), bounds each `B`. For the
Dirichlet polynomial, `λ_n = −log(n + 1)` and `δ_n = 1/(n + 2)` (from `log y ≥ 1 − 1/y`), and
`(n + 1)^{−2σ}(n + 2) ≤ 2`.
-/

open Complex Real Set Filter

noncomputable section

namespace LeanClassics.Density

open LeanClassics.ZetaMeanSquare

/-- `|∑ x_r e^{iλ_r t}|²` expanded, over any finite index type. -/
lemma sq_norm_sum' {ι : Type} [Fintype ι] (x : ι → ℂ) (lam : ι → ℝ) (t : ℝ) :
    ((‖∑ r, x r * cexp ((lam r : ℂ) * t * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m, ∑ n, x m * (starRingEnd ℂ) (x n) * cexp (((lam m - lam n : ℝ) : ℂ) * t * I) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, ← exp_mul_conj]; ring

lemma log_sep {r s : ℕ} (h : r ≠ s) :
    1 / ((r : ℝ) + 2) ≤ |-Real.log ((r : ℝ) + 1) - -Real.log ((s : ℝ) + 1)| := by
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  rcases Nat.lt_or_gt_of_ne h with hrs | hrs
  · -- s ≥ r + 1
    have hs : (r : ℝ) + 2 ≤ (s : ℝ) + 1 := by
      have : (r : ℝ) + 1 ≤ s := by exact_mod_cast hrs
      linarith
    have h1 : Real.log ((r : ℝ) + 2) ≤ Real.log ((s : ℝ) + 1) := Real.log_le_log (by positivity) hs
    have h2 := Real.one_sub_inv_le_log_of_pos (x := ((r : ℝ) + 2) / ((r : ℝ) + 1)) (by positivity)
    rw [Real.log_div (by positivity) hr1.ne', inv_div] at h2
    have h3 : 1 - ((r : ℝ) + 1) / ((r : ℝ) + 2) = 1 / ((r : ℝ) + 2) := by field_simp; ring
    rw [h3] at h2
    have hp : 0 < 1 / ((r : ℝ) + 2) := by positivity
    rw [abs_of_nonneg (by linarith)]
    linarith
  · -- s + 1 ≤ r
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hs : (s : ℝ) + 1 ≤ r := by exact_mod_cast hrs
    have h1 : Real.log ((s : ℝ) + 1) ≤ Real.log (r : ℝ) := Real.log_le_log (by positivity) hs
    have h2 := Real.one_sub_inv_le_log_of_pos (x := ((r : ℝ) + 1) / (r : ℝ)) (by positivity)
    rw [Real.log_div hr1.ne' hr0.ne', inv_div] at h2
    have h3 : 1 - (r : ℝ) / ((r : ℝ) + 1) = 1 / ((r : ℝ) + 1) := by field_simp; ring
    rw [h3] at h2
    have h4 : 1 / ((r : ℝ) + 2) ≤ 1 / ((r : ℝ) + 1) :=
      one_div_le_one_div_of_le hr1 (by linarith)
    have hp : 0 < 1 / ((r : ℝ) + 1) := by positivity
    rw [abs_of_nonpos (by linarith)]
    linarith

end LeanClassics.Density
end
end

-- ===== LeanClassics.NymanPlancherel =====
section
/-
Plancherel's identity for integrable square-integrable functions on ℝ, and its Mellin form on the
line Re s = 1/2:

* `integral_norm_sq_fourier`: if `f ∈ L¹ ∩ L²(ℝ)` then `∫ |𝓕 f(ξ)|² dξ = ∫ |f(x)|² dx`, with `𝓕 f`
  Mathlib's pointwise Fourier integral `∫ e^{−2πixξ} f(x) dx`.
* `integral_norm_sq_mellin`: if `g` is measurable and bounded on `(0, 1]`, then
  `∫₀¹ |g(x)|² dx = ∫ |∫₀¹ g(x) x^{s(ξ) − 1} dx|² dξ`, `s(ξ) = 1/2 + 2πiξ`.

Proof. Mathlib defines the L² Fourier transform abstractly (`Lp.fourierTransformₗᵢ`, a linear isometry
extending the Schwartz-space transform). Tested against a smooth compactly supported `g`, it agrees
with the pointwise transform: as tempered distributions `𝓕 F = 𝓕 (F as a distribution)`
(`Lp.fourier_toTemperedDistribution_eq`), and `∫ 𝓕g · f = ∫ g · 𝓕f` for integrable `f` (Fubini,
`VectorFourier.integral_fourierIntegral_smul_eq_flip`). Locally integrable functions with equal
integrals against every such `g` agree almost everywhere (`ae_eq_of_integral_contDiff_smul_eq`), and
the isometry gives the identity. The Mellin form substitutes `x = e^{−u}` (`mellin_eq_fourier`).
-/

open MeasureTheory FourierTransform Complex Set
open scoped ContDiff

noncomputable section

namespace LeanClassics.Nyman.Plancherel

lemma norm_sq_Lp_eq (F : Lp ℂ 2 (volume : Measure ℝ)) : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def, ← integral_re (L2.integrable_inner F F)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- **Plancherel for `L¹ ∩ L²`.** -/
theorem integral_norm_sq_fourier {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  set F : Lp ℂ 2 (volume : Measure ℝ) := hf2.toLp f with hF
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf1
  have hae : (𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume] 𝓕 f := by
    refine ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp _).locallyIntegrable (by norm_num)) hcont.locallyIntegrable ?_
    intro g hg hgs
    have hgc : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := ofRealCLM.contDiff.comp hg
    have hgcs : HasCompactSupport (fun x => (g x : ℂ)) := hgs.comp_left Complex.ofReal_zero
    set G : SchwartzMap ℝ ℂ := hgcs.toSchwartzMap hgc with hG
    have hGx : ∀ x, G x = (g x : ℂ) := fun x => rfl
    have h1 : ∫ x, g x • (𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) x =
        Lp.toTemperedDistribution (𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) G := by
      rw [Lp.toTemperedDistribution_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hGx, Complex.real_smul, smul_eq_mul]
    rw [h1, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
      Lp.toTemperedDistribution_apply (μ := volume)]
    have h2 : ∫ x, (𝓕 G) x • F x = ∫ x, (𝓕 (G : ℝ → ℂ)) x • f x := by
      refine integral_congr_ae ?_
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hF, hx]; rfl
    rw [h2]
    have h3 := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner (G.integrable (μ := volume)) hf1
    have h4 : ∫ x, (𝓕 (G : ℝ → ℂ)) x • f x = ∫ x, G x • 𝓕 f x := by
      have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
        ext; simp
      simp only [smul_eq_mul, hflip] at h3 ⊢; exact h3
    rw [h4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hGx, Complex.real_smul, smul_eq_mul]
  have hnorm : ‖(𝓕 F : Lp ℂ 2 (volume : Measure ℝ))‖ = ‖F‖ := Lp.norm_fourier_eq F
  have e1 := norm_sq_Lp_eq (𝓕 F)
  have e2 := norm_sq_Lp_eq F
  have e3 : ∫ x, ‖(𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) x‖ ^ 2 = ∫ ξ, ‖𝓕 f ξ‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx; rw [hx]
  have e4 : ∫ x, ‖F x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp] with x hx; rw [hF, hx]
  rw [← e3, ← e1, hnorm, e2, e4]

/-- `s(ξ) = 1/2 + 2πiξ`. -/
abbrev sLine (ξ : ℝ) : ℂ := 1 / 2 + 2 * Real.pi * ξ * I

/-- **Plancherel in Mellin form.** For `g` measurable and bounded on `(0, 1]`,
`∫₀¹ |g|² = ∫ |∫₀¹ g(x) x^{s(ξ) − 1} dx|² dξ` with `s(ξ) = 1/2 + 2πiξ`. -/
theorem integral_norm_sq_mellin {g : ℝ → ℂ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x ∈ Ioc (0 : ℝ) 1, ‖g x‖ ≤ B) :
    ∫ x in Ioc (0 : ℝ) 1, ‖g x‖ ^ 2 =
      ∫ ξ : ℝ, ‖∫ x in Ioc (0 : ℝ) 1, g x * (x : ℂ) ^ (sLine ξ - 1)‖ ^ 2 := by
  set gt : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator g with hgt
  have hgtm : Measurable gt := hg.indicator measurableSet_Ioc
  have hB0 : 0 ≤ B := by
    have := hB 1 ⟨one_pos, le_rfl⟩; exact (norm_nonneg _).trans this
  have hgtb : ∀ x, ‖gt x‖ ≤ B := fun x => by
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · simp only [hgt, indicator_of_mem hx]; exact hB x hx
    · simp only [hgt, indicator_of_notMem hx, norm_zero]; exact hB0
  set φ : ℝ → ℂ := fun u => Real.exp (-(1 / 2) * u) • gt (Real.exp (-u)) with hφ
  have hφm : Measurable φ :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).smul
      (hgtm.comp (Real.measurable_exp.comp measurable_neg))
  have hφ0 : ∀ u, u < 0 → φ u = 0 := fun u hu => by
    have : Real.exp (-u) ∉ Ioc (0 : ℝ) 1 := fun h => by
      have := h.2; rw [Real.exp_le_one_iff] at this; linarith
    simp [hφ, hgt, indicator_of_notMem this]
  set E : ℝ → ℝ := (Ici (0 : ℝ)).indicator fun u => Real.exp (-(1 / 2) * u) with hE
  have hEint : Integrable E :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2))).integrable_indicator
      measurableSet_Ici
  have hφb : ∀ u, ‖φ u‖ ≤ B * E u := fun u => by
    rcases lt_or_ge u 0 with hu | hu
    · rw [hφ0 u hu, norm_zero]
      exact mul_nonneg hB0 (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
    · simp only [hφ, hE, indicator_of_mem (show u ∈ Ici (0:ℝ) from hu), norm_smul,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [mul_comm B]
      exact mul_le_mul_of_nonneg_left (hgtb _) (Real.exp_pos _).le
  have hφ1 : Integrable φ :=
    (hEint.const_mul B).mono' hφm.aestronglyMeasurable (Filter.Eventually.of_forall hφb)
  have hφ2 : MemLp φ 2 := by
    refine (memLp_two_iff_integrable_sq_norm hφm.aestronglyMeasurable).mpr ?_
    refine ((hEint.const_mul (B ^ 2))).mono' (hφm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hEu : E u ≤ 1 := by
      simp only [hE]
      by_cases hu : u ∈ Ici (0 : ℝ)
      · rw [indicator_of_mem hu, Real.exp_le_one_iff]
        have : (0 : ℝ) ≤ u := hu
        linarith
      · rw [indicator_of_notMem hu]; norm_num
    have hE0 : 0 ≤ E u := indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
    calc ‖φ u‖ ^ 2 ≤ (B * E u) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hφb u) 2
      _ = B ^ 2 * (E u * E u) := by ring
      _ ≤ B ^ 2 * (E u * 1) := by gcongr
      _ = B ^ 2 * E u := by ring
  have hP := integral_norm_sq_fourier hφ1 hφ2
  -- the Fourier side
  have hF : ∀ ξ : ℝ, 𝓕 φ ξ = ∫ x in Ioc (0 : ℝ) 1, g x * (x : ℂ) ^ (sLine ξ - 1) := by
    intro ξ
    have h := mellin_eq_fourier gt (s := sLine ξ)
    have hre : (sLine ξ).re = 1 / 2 := by simp [sLine]
    have him : (sLine ξ).im / (2 * Real.pi) = ξ := by
      simp [sLine]
    rw [hre, him] at h
    rw [show φ = fun u : ℝ => Real.exp (-(1 / 2) * u) • gt (Real.exp (-u)) from rfl, ← h, mellin,
      ← Ioi_inter_Iic, ← setIntegral_indicator measurableSet_Iic]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    by_cases h1 : x ∈ Iic (1 : ℝ)
    · have hx' : x ∈ Ioc (0 : ℝ) 1 := ⟨hx, h1⟩
      simp only [indicator_of_mem h1, hgt, indicator_of_mem hx', smul_eq_mul]; ring
    · have hx' : x ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
      simp [indicator_of_notMem h1, hgt, indicator_of_notMem hx']
  -- the L² side
  have hL : ∫ u, ‖φ u‖ ^ 2 = ∫ x in Ioc (0 : ℝ) 1, ‖g x‖ ^ 2 := by
    set h : ℝ → ℂ := fun x => ((‖gt x‖ ^ 2 : ℝ) : ℂ) with hh
    have hm := mellin_eq_fourier h (s := 1)
    simp only [Complex.one_re, Complex.one_im, zero_div] at hm
    have hlhs : mellin h 1 = ∫ x in Ioc (0 : ℝ) 1, (((‖g x‖ ^ 2 : ℝ)) : ℂ) := by
      rw [mellin, show Ioc (0 : ℝ) 1 = Ioi 0 ∩ Iic 1 from (Ioi_inter_Iic).symm,
        ← setIntegral_indicator measurableSet_Iic]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      by_cases h1 : x ∈ Iic (1 : ℝ)
      · have hx' : x ∈ Ioc (0 : ℝ) 1 := ⟨hx, h1⟩
        simp [hh, hgt, indicator_of_mem h1, indicator_of_mem hx']
      · have hx' : x ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
        simp [hh, hgt, indicator_of_notMem h1, indicator_of_notMem hx']
    have hrhs : 𝓕 (fun u : ℝ => Real.exp (-1 * u) • h (Real.exp (-u))) 0 =
        ∫ u, (((‖φ u‖ ^ 2 : ℝ)) : ℂ) := by
      rw [Real.fourier_real_eq]
      congr 1; ext u
      simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul, hh, hφ, norm_smul,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [Complex.real_smul]
      push_cast
      rw [mul_pow, ← Complex.exp_nat_mul]
      push_cast; ring_nf
    rw [hlhs, hrhs, integral_complex_ofReal, integral_complex_ofReal] at hm
    exact_mod_cast hm.symm
  rw [← hL, ← hP]
  congr 1; ext ξ; rw [hF]

end LeanClassics.Nyman.Plancherel
end
end

-- ===== Zeta23.FromPNTPlus.Auxiliary =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Auxiliary.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none besides this header (upstream has no blueprint annotations
or intra-project imports in this file).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

/-!
### Auxiliary lemmas
-/


lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

end

-- ===== Zeta23.FromPNTPlus.Sobolev =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Sobolev.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none besides this header.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}






end

-- ===== Zeta23.FromPNTPlus.Fourier =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Fourier.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: redirected the intra-project import to Zeta23.FromPNTPlus.Sobolev.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Adjusted for Lean v4.33.0-rc2 / Mathlib 51e6992efd06: `Circle.norm_coe` supplied explicitly to two `simp` calls.
Modified 2026 by Anthropic PBC.
-/

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩


end

-- ===== Zeta23.FromPNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 10e1218932db7e2432aa5881d750acb819e91f19, file
PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint
tooling (import Architect, blueprint_comment blocks, @[blueprint ...] attributes),
redirected intra-project imports to Zeta23.FromPNTPlus.*.  Mathematical content unchanged.
Modified 2026 by Anthropic PBC.
-/

open Filter Real

end

-- ===== Zeta23.FromPNTPlus.Rectangle =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Rectangle.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
@[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}


end

-- ===== Zeta23.FromPNTPlus.ResidueCalcOnRectangles =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes) and redirected intra-project
imports to Zeta23.FromPNTPlus.*.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

/- An UpperUIntegral is the integral of a function over a |\_| shape. -/
/- A LowerUIntegral is the integral of a function over a |-| shape. -/
/-- A function is `HolomorphicOn` a set if it is complex
  differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)
-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.
-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.
-- Non-constancy of horizontal paths `x ↦ x + h * I`.
-- Non-constancy of vertical paths `y ↦ r + y * I`.
-- Helper for horizontal integral congruence on codiscrete set
-- Helper for vertical integral congruence on codiscrete set
-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.
-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.
-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.
-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.
end

-- ===== Zeta23.FromPNTPlus.EulerMaclaurin =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/EulerMaclaurin.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none (verbatim copy).
New in the v4.32.2 port set: upstream split this file's content (the first-order
Euler–Maclaurin section: B1 ... sum_eq_integral_add_integral_deriv) out of
PrimeNumberTheoremAnd/Mertens.lean, where our original v4.29.0 port carried it
inside Zeta23/FromPNTPlus/Mertens.lean; that file now imports this one instead.
Added when the project moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/


/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/


open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The 1st Bernoulli function. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp)
    (RCLike.continuous_ofReal.comp_aestronglyMeasurable aestronglyMeasurable_B1) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring
end

-- ===== Zeta23.FromPNTPlus.ZetaBounds =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaBounds.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes), redirected intra-project
imports to Zeta23.FromPNTPlus.*, and added a (name := ...) tag to the local notation.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/


open Complex Topology Filter Interval Set Asymptotics

lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]


-- Main theorem: if functions agree on a punctured set, their derivatives agree there too
/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach
/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/

lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : riemannZeta0 N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring

-- move near `Real.differentiableAt_rpow_const_of_ne`
lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])

lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]

lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring

lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]

lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])

lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf

lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf

lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩

lemma Finset.Ioc_eq_Ico (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith

lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]

lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop

lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3

lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr s_re_gt
  simp_rw [Finset.Ioc_eq_Ico]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]

lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr'
      (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      exact ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩
    · exact ZetaSum_aux3 s_re_gt
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply cpow_tendsto s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| cpow_inv_tendsto (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (integrableOn_of_Zeta0_fun N_pos <| by positivity) tendsto_natCast_atTop_atTop

lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)

open MeasureTheory in
lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have y_gt : y ≥ x₀ := by linarith
    have := hx₀ y y_gt
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1

open MeasureTheory in
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply Integrable.bdd_mul (c := c) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := integrable_log_over_pow (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real]; simp

open MeasureTheory in
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_setOf_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert! integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert! integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert! integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]; ext x; ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3 _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    exact h_bound1
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert! integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [h_bound1, self_mem_ae_restrict measSetIoi1] with x _ one_lt_x
    intro z hz
    convert! HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    convert! HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · convert! HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f]; ring_nf

noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))

lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert! hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]

lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero

lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (riemannZeta0 N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1
    · ring_nf
    · exact HasDerivAt_cpow_over_var N (by rw [sub_ne_zero]; exact s_ne_one.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert! HasDerivAt_neg_cpow_over2 Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| hasDerivAt_Zeta0Integral Npos reS_pos using 1

lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (riemannZeta0 N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`
lemma HolomorphicOn_riemannZeta :
    HolomorphicOn riemannZeta {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_setOf_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt

lemma isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  use (2 : ℂ)
  constructor
  · simp
  intro w hw; simp only [ne_eq, mem_setOf_eq] at hw
  by_cases w_im : w.im = 0
  · apply JoinedIn.trans (y := 1 + I)
    · let f : ℝ → ℂ := fun t ↦ (1 + I) * t + 2 * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, one_re,
        I_re, add_zero, ofReal_re, one_mul, add_im, one_im, I_im, zero_add, ofReal_im, mul_zero,
        sub_zero, re_ofNat, sub_re, im_ofNat, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      refine ⟨?_, by linarith⟩
      intro h
      rw [Complex.ext_iff] at h; simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · let f : ℝ → ℂ := fun t ↦ w * t + (1 + I) * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re,
        ofReal_re, ofReal_im, mul_zero, sub_zero, one_re, I_re, add_zero, sub_re, one_mul, add_im,
        one_im, I_im, zero_add, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      simp only [mem_setOf_eq]
      constructor
      · intro h
        refine hw.1 ?_
        rw [Complex.ext_iff] at h
        have : x = 1 := by linarith [(by apply And.right; simpa [w_im] using h : 1 - x = 0)]
        rw [Complex.ext_iff, one_re, one_im]; exact ⟨by simpa [this, w_im] using h, w_im⟩
      · by_cases hxx : x = 0
        · simp only [hxx]; linarith
        · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
          have : 0 ≤ 1 - x := by linarith
          have := hw.2
          positivity
  · let f : ℝ → ℂ := fun t ↦ w * t + 2 * (1 - t)
    have cont : Continuous f := by continuity
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero, re_ofNat, sub_re, one_re, im_ofNat, sub_im, one_im, sub_self,
      f]
    intro x hx; simp only [mem_Icc] at hx
    constructor
    · intro h
      rw [Complex.ext_iff] at h;
      simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · by_cases hxx : x = 0
      · simp only [hxx]; linarith
      · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
        have : 0 ≤ 1 - x := by linarith
        have := hw.2
        positivity

lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    riemannZeta0 N s = riemannZeta s := by
  let f := riemannZeta
  let g := riemannZeta0 N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, setOf_subset_setOf, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (HolomorphicOn_riemannZeta0 N_pos).analyticOnNhd isOpen_aux
  have preconU : IsPreconnected U := by
    apply IsConnected.isPreconnected
    apply (IsOpen.isConnected_iff_isPathConnected isOpen_aux).mpr isPathConnected_aux
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [setOf_subset_setOf, imp_self, forall_const, mem_setOf_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

-- **End collaboration 6/20/25**

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

-- **End collaboration**

open ArithmeticFunction (vonMangoldt)
--TODO generalize to any LSeries with nonnegative coefficients
end

-- ===== LeanClassics.RealZeros =====
section
/-
ζ has no zeros on the real segment (0, 1): in fact Re ζ(σ) ≤ 1 − 1/(1 − σ) < 0 there.

From the Euler–Maclaurin form (`riemannZeta0` with N = 1, PrimeNumberTheoremAnd as vendored in zeta23):
  ζ(s) = 1 − 1/(1 − s) − 1/2 + s ∫_1^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx   (Re s > 0, s ≠ 1),
and |⌊x⌋ + 1/2 − x| ≤ 1/2 bounds the last term by σ · (1/2) · (1/σ) = 1/2 at s = σ.
-/

open Complex MeasureTheory Set

namespace LeanClassics.RealZeros

lemma frac_bound (x : ℝ) : ‖((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ))‖ ≤ 1 / 2 := by
  have e : ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) = (((⌊x⌋ : ℝ) + 1 / 2 - x : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  constructor <;> linarith

end LeanClassics.RealZeros
end

-- ===== LeanClassics.DensityTail =====
section
/-!
# Mean square of the Euler–Maclaurin remainder of `ζ` on a vertical line

`integral_norm_sq_tail_le`: for `σ ≥ 1/2`, real `N > 0` and any `a ≤ b`,
`∫_a^b |∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−(σ+it)−1} dx|² dt ≤ (π/2) N^{−2σ}`; the integrand `tailFn`
is integrable over the whole line (`integrable_norm_sq_tailFn`).

Proof. Substituting `x = N/w`, the inner integral is `N^{−s}` times the Mellin transform on `(0, 1]`
of `g(w) = (⌊N/w⌋ + 1/2 − N/w) w^{σ − 1/2}` (for `w < 1`; `0` at `w = 1`) at `1/2 + it`
(`mellin_comp_inv`, `mellin_comp_mul_left`). `|g| ≤ 1/2` on `(0, 1]`, so Plancherel in Mellin form
(`Nyman.Plancherel.integral_norm_sq_mellin`) bounds the integral over the whole line by
`2π N^{−2σ} ∫_0^1 |g|² ≤ (π/2) N^{−2σ}`.
-/

open Complex Real Set MeasureTheory Filter

noncomputable section

namespace LeanClassics.Density

open LeanClassics.Nyman.Plancherel

/-- `(⌊x⌋ + 1/2 − x)` cut off to `x > N`. -/
def psiN (N : ℝ) : ℝ → ℂ := (Ioi N).indicator fun x => ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ))

lemma measurable_psiN (N : ℝ) : Measurable (psiN N) := by
  refine Measurable.indicator ?_ measurableSet_Ioi
  have h1 : Measurable fun x : ℝ => ((⌊x⌋ : ℤ) : ℂ) :=
    (measurable_of_countable fun n : ℤ => (n : ℂ)).comp Int.measurable_floor
  exact (h1.add measurable_const).sub Complex.measurable_ofReal

lemma norm_psiN_le (N x : ℝ) : ‖psiN N x‖ ≤ 1 / 2 := by
  unfold psiN
  by_cases hx : x ∈ Ioi N
  · rw [indicator_of_mem hx]; exact LeanClassics.RealZeros.frac_bound x
  · rw [indicator_of_notMem hx, norm_zero]; norm_num

lemma tail_eq_mellin {N : ℝ} (hN : 0 < N) (s : ℂ) :
    ∫ x in Ioi N, ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ (s + 1) = mellin (psiN N) (-s) := by
  rw [mellin, psiN]
  have e : ∀ x : ℝ, (x : ℂ) ^ (-s - 1) • (Ioi N).indicator
      (fun x => ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ))) x =
      (Ioi N).indicator (fun x => ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ (s + 1)) x := by
    intro x
    by_cases hx : x ∈ Ioi N
    · rw [indicator_of_mem hx, indicator_of_mem hx, smul_eq_mul,
        show -s - 1 = -(s + 1) by ring, cpow_neg]
      ring
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]
  simp_rw [e]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hN.le]

/-- The function whose Mellin transform on `(0, 1]` gives the tail. -/
def gTail (N σ : ℝ) (w : ℝ) : ℂ := psiN N (N * w⁻¹) * (w : ℂ) ^ ((σ - 1 / 2 : ℝ) : ℂ)

lemma measurable_gTail (N σ : ℝ) : Measurable (gTail N σ) := by
  unfold gTail
  refine ((measurable_psiN N).comp (measurable_const.mul measurable_inv)).mul ?_
  exact Complex.measurable_ofReal.pow_const _

lemma norm_gTail_le {N σ : ℝ} (hσ : 1 / 2 ≤ σ) {w : ℝ} (hw : w ∈ Ioc (0 : ℝ) 1) :
    ‖gTail N σ w‖ ≤ 1 / 2 := by
  unfold gTail
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw.1, Complex.ofReal_re]
  have h1 : w ^ (σ - 1 / 2) ≤ 1 := Real.rpow_le_one hw.1.le hw.2 (by linarith)
  have h2 := norm_psiN_le N (N * w⁻¹)
  calc ‖psiN N (N * w⁻¹)‖ * w ^ (σ - 1 / 2) ≤ 1 / 2 * 1 :=
        mul_le_mul h2 h1 (Real.rpow_nonneg hw.1.le _) (by norm_num)
    _ = 1 / 2 := by ring

/-- The tail at `σ + 2πiξ` is `N^{−s}` times the Mellin transform of `gTail` at `sLine ξ`. -/
lemma tail_eq {N : ℝ} (hN : 0 < N) (σ ξ : ℝ) :
    ∫ x in Ioi N, ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ (((σ : ℂ) + 2 * π * ξ * I) + 1) =
      (N : ℂ) ^ (-((σ : ℂ) + 2 * π * ξ * I)) *
        ∫ w in Ioc (0 : ℝ) 1, gTail N σ w * (w : ℂ) ^ (sLine ξ - 1) := by
  set s : ℂ := (σ : ℂ) + 2 * π * ξ * I with hs
  set k : ℝ → ℂ := fun w => psiN N (N * w⁻¹) with hk
  rw [tail_eq_mellin hN, ← mellin_comp_inv]
  have hfun : (fun t : ℝ => psiN N t⁻¹) = fun t => k (N * t) := by
    funext t
    simp only [hk]
    congr 1
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · field_simp
  rw [hfun, mellin_comp_mul_left k s hN, smul_eq_mul]
  congr 1
  rw [mellin]
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun w hw => hw.1
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub ?_]
  · refine setIntegral_congr_fun measurableSet_Ioc fun w hw => ?_
    simp only [hk, gTail, smul_eq_mul]
    have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast hw.1.ne'
    rw [mul_assoc, ← cpow_add _ _ hw0]
    rw [mul_comm]
    congr 2
    simp only [hs, sLine]; push_cast; ring
  · intro w hw
    have hw1 : 1 < w := by
      rcases hw with ⟨h0, h1⟩
      simp only [mem_Ioc, not_and, not_le] at h1
      exact h1 h0
    have hw0 : 0 < w := lt_trans one_pos hw1
    have : N * w⁻¹ ∉ Ioi N := by
      simp only [mem_Ioi, not_lt]
      rw [← div_eq_mul_inv, div_le_iff₀ hw0]
      nlinarith
    simp only [hk, psiN, indicator_of_notMem this, smul_zero]

/-- The Mellin side, `ξ ↦ |∫_0^1 g(w) w^{sLine ξ − 1} dw|²`, is integrable, with integral
`∫_0^1 |g|² ≤ 1/4`. -/
lemma mellin_side {N σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    Integrable (fun ξ : ℝ => ‖∫ w in Ioc (0 : ℝ) 1, gTail N σ w * (w : ℂ) ^ (sLine ξ - 1)‖ ^ 2) ∧
    ∫ ξ : ℝ, ‖∫ w in Ioc (0 : ℝ) 1, gTail N σ w * (w : ℂ) ^ (sLine ξ - 1)‖ ^ 2 ≤ 1 / 4 := by
  have hB : ∀ w ∈ Ioc (0 : ℝ) 1, ‖gTail N σ w‖ ≤ 1 / 2 := fun w hw => norm_gTail_le hσ hw
  have hP := integral_norm_sq_mellin (measurable_gTail N σ) hB
  have hgi : IntegrableOn (fun w => ‖gTail N σ w‖ ^ 2) (Ioc (0 : ℝ) 1) := by
    refine Measure.integrableOn_of_bounded (M := 1 / 4) (by simp)
      ((measurable_gTail N σ).norm.pow_const 2).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun w hw => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hB w hw
    nlinarith [norm_nonneg (gTail N σ w)]
  have hle : ∫ w in Ioc (0 : ℝ) 1, ‖gTail N σ w‖ ^ 2 ≤ 1 / 4 := by
    calc ∫ w in Ioc (0 : ℝ) 1, ‖gTail N σ w‖ ^ 2 ≤ ∫ _w in Ioc (0 : ℝ) 1, (1 / 4 : ℝ) := by
          refine setIntegral_mono_on hgi (integrableOn_const (by simp)) measurableSet_Ioc
            fun w hw => ?_
          have := hB w hw
          nlinarith [norm_nonneg (gTail N σ w)]
      _ = 1 / 4 := by simp
  refine ⟨?_, hP ▸ hle⟩
  by_contra hni
  rw [integral_undef hni] at hP
  -- then `∫_0^1 |g|² = 0`, so `g = 0` a.e. on `(0, 1]` and the Mellin side vanishes identically
  have hz : (fun w => ‖gTail N σ w‖ ^ 2) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun w => by positivity) hgi).mp hP
  apply hni
  have h0 : ∀ ξ : ℝ, ∫ w in Ioc (0 : ℝ) 1, gTail N σ w * (w : ℂ) ^ (sLine ξ - 1) = 0 := by
    intro ξ
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hz] with w hw
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      norm_eq_zero] at hw
    simp [hw]
  simp_rw [h0]
  simp

/-- The tail on `Re s = σ`, as a function of `t`. -/
def tailFn (N σ t : ℝ) : ℂ :=
  ∫ x in Ioi N, ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ (((σ : ℂ) + t * I) + 1)

lemma norm_sq_tailFn_eq {σ N : ℝ} (hN : 0 < N) (t : ℝ) :
    ‖tailFn N σ t‖ ^ 2 = N ^ (-(2 * σ)) *
      ‖∫ w in Ioc (0 : ℝ) 1, gTail N σ w * (w : ℂ) ^ (sLine (t / (2 * π)) - 1)‖ ^ 2 := by
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have ht : (t : ℂ) = 2 * π * ((t / (2 * π) : ℝ) : ℂ) := by
    push_cast; field_simp
  have hre : ∀ u : ℝ, (-((σ : ℂ) + 2 * π * (u : ℂ) * I)).re = -σ := fun u => by simp
  rw [tailFn, ht, tail_eq hN, norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos hN, hre]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  congr 1
  push_cast; ring

lemma integrable_norm_sq_tailFn {σ : ℝ} (hσ : 1 / 2 ≤ σ) {N : ℝ} (hN : 0 < N) :
    Integrable fun t => ‖tailFn N σ t‖ ^ 2 := by
  obtain ⟨hint, -⟩ := mellin_side (N := N) hσ
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  simp_rw [norm_sq_tailFn_eq hN]
  exact (hint.comp_div hpi).const_mul _

/-- **Mean square of the Euler–Maclaurin remainder.** -/
theorem integral_norm_sq_tail_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) {N : ℝ} (hN : 0 < N) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ t in a..b, ‖tailFn N σ t‖ ^ 2 ≤ π / 2 * N ^ (-(2 * σ)) := by
  obtain ⟨hint, hval⟩ := mellin_side (N := N) hσ
  set M : ℝ → ℝ := fun ξ => ‖∫ w in Ioc (0 : ℝ) 1, gTail N σ w * (w : ℂ) ^ (sLine ξ - 1)‖ ^ 2
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  simp_rw [norm_sq_tailFn_eq hN]
  have hint' : Integrable fun t : ℝ => N ^ (-(2 * σ)) * M (t / (2 * π)) :=
    (hint.comp_div hpi).const_mul _
  have hnn : ∀ t, 0 ≤ N ^ (-(2 * σ)) * M (t / (2 * π)) := fun t => by positivity
  rw [intervalIntegral.integral_of_le hab]
  calc ∫ t in Ioc a b, N ^ (-(2 * σ)) * M (t / (2 * π))
      ≤ ∫ t, N ^ (-(2 * σ)) * M (t / (2 * π)) :=
        setIntegral_le_integral hint' (Eventually.of_forall hnn)
    _ = N ^ (-(2 * σ)) * (|2 * π| * ∫ ξ, M ξ) := by
        rw [integral_const_mul, Measure.integral_comp_div (fun ξ => M ξ) (2 * π), smul_eq_mul]
    _ ≤ N ^ (-(2 * σ)) * (|2 * π| * (1 / 4)) := by gcongr
    _ = π / 2 * N ^ (-(2 * σ)) := by
        rw [abs_of_pos (by positivity)]; ring

end LeanClassics.Density
end
end

-- ===== LeanClassics.DensityMeanSquare =====
section
/-!
# Mean square of `ζ` on `Re s = σ > 1/2`: `∫_1^X |ζ(σ + it)|² dt ≪ X`, uniformly in `σ`

`integral_norm_sq_zeta_le`: for `1/2 < σ₁ ≤ σ₂` there is `C` with
`∫_1^X |ζ(σ + it)|² dt ≤ C X` for all `σ ∈ [σ₁, σ₂]` and `X ≥ 1` (Hardy–Littlewood's upper bound;
the asymptotic `∼ ζ(2σ) X` is not proved here).

Proof. With `N = ⌈X⌉`, PNT+'s Euler–Maclaurin form (`Zeta0EqZeta`, vendored in zeta23) writes
`ζ(s) = ∑_{n<N} (n+1)^{−s} − N^{1−s}/(1 − s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx`.
The Dirichlet polynomial has mean square `≤ X ∑ (n+1)^{−2σ₁} + 52 N` (`DensityMV`,
Montgomery–Vaughan),
`|N^{1−s}/(1 − s)|² ≤ N/t²` integrates to `≤ N`, `|N^{−s}/2|² ≤ 1/4`, and the remainder has mean
square `≤ (σ₂² + X²) (π/2) N^{−2σ} ≤ (π/2)(σ₂² + X)` (`DensityTail`, Plancherel). Then
`|a + b + c + d|² ≤ 4(|a|² + |b|² + |c|² + |d|²)`.
-/

open Complex Real Set MeasureTheory Filter

noncomputable section

namespace LeanClassics.Density

lemma line_ne_one {σ t : ℝ} (ht : t ≠ 0) : (σ : ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact ht this

lemma continuousOn_norm_sq_zeta_line (σ : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) (Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := (lt_of_lt_of_le ha ht.1).ne'
  have h1 : ContinuousAt (fun t : ℝ => (σ : ℂ) + t * I) t := by fun_prop
  have h2 : ContinuousAt riemannZeta ((σ : ℂ) + t * I) :=
    (differentiableAt_riemannZeta (line_ne_one ht0)).continuousAt
  exact ((ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + t * I) h2 h1).norm.pow
    2).continuousWithinAt

lemma zeta_split {σ t : ℝ} (hσ : 0 < σ) (ht : t ≠ 0) {N : ℕ} (hN : 0 < N) :
    riemannZeta ((σ : ℂ) + t * I) =
      (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I))
      + (-((N : ℂ) ^ (1 - ((σ : ℂ) + t * I)))) / (1 - ((σ : ℂ) + t * I))
      + (-((N : ℂ) ^ (-((σ : ℂ) + t * I)))) / 2
      + ((σ : ℂ) + t * I) * tailFn N σ t := by
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hre : 0 < s.re := by simpa [hs] using hσ
  have hs0 : s ≠ 0 := fun h => by rw [h] at hre; simp at hre
  rw [← Zeta0EqZeta hN hre (line_ne_one ht), riemannZeta0, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_cpow hs0, div_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rfl

lemma continuous_dirichlet (σ : ℝ) (N : ℕ) :
    Continuous fun t : ℝ => ‖∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I)‖ ^ 2 := by
  have e : (fun t : ℝ => ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I)) =
      fun t : ℝ => ∑ n ∈ Finset.range N, ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) *
        cexp (((-Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * t * I) := by
    funext t
    exact Finset.sum_congr rfl fun n _ => ZetaMeanSquare.term_eq n σ t
  have hc : Continuous fun t : ℝ =>
      ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I) := by
    rw [e]; exact continuous_finsetSum _ fun n _ => ZetaMeanSquare.continuous_term _ _
  exact hc.norm.pow 2

end LeanClassics.Density
end
end

-- ===== LeanClassics.ZetaSecondMoment =====
section
/-!
# Hardy–Littlewood: `∫₀ᵀ |ζ(1/2 + it)|² dt ∼ T log T`

`integral_norm_sq_zeta_half_sub_le`: there is `C` with
`|∫_1^X |ζ(1/2 + it)|² dt − X log X| ≤ C X √(log X)` for every `X ≥ 3`.

`integral_zero_norm_sq_zeta_half_sub_le`: the same bound for `∫_0^X`.

`integral_norm_sq_zeta_half_isEquivalent`: `∫_0^T |ζ(1/2 + it)|² dt ∼ T log T` as `T → ∞`
(Hardy and Littlewood, 1918; Titchmarsh §7.3).

Only the main term is proved. The error `O(X √(log X))` is weaker than the classical
`T log(T/2π) + (2γ − 1)T + O(T^{1/2} log T)` (Ingham, Titchmarsh §7.4), which is not proved here.

Proof. On `Re s = 1/2`, with `N = ⌈X⌉`, the Euler–Maclaurin split used for `σ > 1/2`
(`Density.zeta_split`) writes `ζ(s) = A(t) + E(t)`, `A(t) = ∑_{n<N} (n+1)^{−s}`. The Montgomery–Vaughan
mean value theorem, now with both signs (`abs_integral_norm_sq_sum_sub_le`), gives
`|∫_1^X |A|² − (X − 1) H_N| ≤ 52 N`, `H_N = ∑_{n<N} 1/(n+1) = log X + O(1)`; so
`∫_1^X |A|² = X log X + O(X)`. The three remaining terms have mean square `O(X)` as in
`Density.integral_norm_sq_zeta_le` (`integral_norm_sq_E_le`). Then
`(1 − η)|a|² − (1 + 1/η)|e|² ≤ |a + e|² ≤ (1 + η)|a|² + (1 + 1/η)|e|²` with `η = 1/√(log X)`.
-/

open Complex Real Set MeasureTheory Filter Asymptotics

noncomputable section

namespace LeanClassics.ZetaSecondMoment

open LeanClassics.Density LeanClassics.ZetaMeanSquare

/-- **Mean value theorem with the Montgomery–Vaughan error, both signs**, on an interval `[a, b]`:
`|∫_a^b |∑ x_r e^{iλ_r t}|² dt − (b − a) ∑ |x_r|²| ≤ 26 ∑ |x_r|²/δ_r`. -/
theorem abs_integral_norm_sq_sum_sub_le {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → ℂ)
    {freq δ : ι → ℝ} (hinj : Function.Injective freq) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) {a b : ℝ} :
    |(∫ t in a..b, ‖∑ r, x r * cexp ((freq r : ℂ) * t * I)‖ ^ 2) - (b - a) * ∑ r, ‖x r‖ ^ 2| ≤
      26 * ∑ r, ‖x r‖ ^ 2 / δ r := by
  set X := ∫ t in a..b, ‖∑ r, x r * cexp ((freq r : ℂ) * t * I)‖ ^ 2
  have hX : (X : ℂ) = ∑ m, ∑ n, x m * (starRingEnd ℂ) (x n) *
      ∫ t in a..b, cexp (((freq m - freq n : ℝ) : ℂ) * t * I) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [sq_norm_sum']
    rw [intervalIntegral.integral_finsetSum fun m _ => ?_]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_finsetSum fun n _ => ?_]
      · refine Finset.sum_congr rfl fun n _ => ?_
        exact intervalIntegral.integral_const_mul _ _
      · exact (continuous_term _ _).intervalIntegrable _ _
    · exact (continuous_finsetSum _ fun n _ => continuous_term _ _).intervalIntegrable _ _
  set y : ℝ → ι → ℂ := fun u r => x r * cexp ((freq r : ℂ) * u * I) with hy
  set B : ℝ → ℂ := fun u => ∑ r, ∑ s, if r = s then (0 : ℂ) else
    y u r * (starRingEnd ℂ) (y u s) / ((freq r - freq s : ℝ) : ℂ) with hB
  have hyn : ∀ u r, ‖y u r‖ = ‖x r‖ := fun u r => by
    simp only [hy, norm_mul, norm_cexp_mul, mul_one]
  have hBle : ∀ u, ‖B u‖ ≤ 13 * ∑ r, ‖x r‖ ^ 2 / δ r := fun u => by
    have := Zeta23.MV.mvDiag_thirteen ι freq δ (y u) hinj hδ hsep
    simpa [hB, hyn] using this
  have hyy : ∀ u m n, y u m * (starRingEnd ℂ) (y u n) =
      x m * (starRingEnd ℂ) (x n) * cexp (((freq m - freq n : ℝ) : ℂ) * u * I) := by
    intro u m n
    simp only [hy, map_mul]
    rw [← exp_mul_conj]; ring
  have hoff : ∀ m n, m ≠ n → x m * (starRingEnd ℂ) (x n) *
      ∫ t in a..b, cexp (((freq m - freq n : ℝ) : ℂ) * t * I) =
      (y b m * (starRingEnd ℂ) (y b n) / ((freq m - freq n : ℝ) : ℂ) -
        y a m * (starRingEnd ℂ) (y a n) / ((freq m - freq n : ℝ) : ℂ)) * (-I) := by
    intro m n hmn
    have hc : ((freq m - freq n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr fun e => hmn (hinj e)
    have hcI : ((freq m - freq n : ℝ) : ℂ) * I ≠ 0 := mul_ne_zero hc I_ne_zero
    have e : (fun t : ℝ => cexp (((freq m - freq n : ℝ) : ℂ) * t * I)) =
        fun t : ℝ => cexp (((freq m - freq n : ℝ) : ℂ) * I * t) := by
      funext t; ring_nf
    rw [e, integral_exp_mul_complex hcI, hyy, hyy]
    field_simp
    ring_nf
    rw [I_sq]; ring
  have hdiag : ((b - a) * ∑ r, ‖x r‖ ^ 2 : ℝ) = ∑ m, ∑ n,
      (if m = n then x m * (starRingEnd ℂ) (x n) *
        ∫ t in a..b, cexp (((freq m - freq n : ℝ) : ℂ) * t * I) else 0) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, sub_self, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, mul_one, Complex.real_smul]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hsplit : (X : ℂ) - ((b - a) * ∑ r, ‖x r‖ ^ 2 : ℝ) = (B b - B a) * (-I) := by
    rw [hX, hdiag, ← Finset.sum_sub_distrib, hB]
    simp only
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with h
    · simp
    · rw [sub_zero, hoff m n h]
  have hnorm : ‖(X : ℂ) - ((b - a) * ∑ r, ‖x r‖ ^ 2 : ℝ)‖ ≤ 26 * ∑ r, ‖x r‖ ^ 2 / δ r := by
    rw [hsplit, norm_mul, norm_neg, Complex.norm_I, mul_one]
    calc ‖B b - B a‖ ≤ ‖B b‖ + ‖B a‖ := norm_sub_le _ _
      _ ≤ 13 * ∑ r, ‖x r‖ ^ 2 / δ r + 13 * ∑ r, ‖x r‖ ^ 2 / δ r := add_le_add (hBle b) (hBle a)
      _ = 26 * ∑ r, ‖x r‖ ^ 2 / δ r := by ring
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hnorm
  exact hnorm

/-- **Mean square of `∑_{n<N} (n + 1)^{−s}` on `Re s = σ ≥ 1/2`, both signs**, on any interval. -/
theorem abs_integral_norm_sq_dirichlet_sub_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (N : ℕ) (a b : ℝ) :
    |(∫ t in a..b, ‖∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I)‖ ^ 2) -
      (b - a) * ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-(2 * σ))| ≤ 52 * N := by
  set x : Fin N → ℂ := fun i => (((((i : ℕ) : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)
  set freq : Fin N → ℝ := fun i => -Real.log (((i : ℕ) : ℝ) + 1)
  set δ : Fin N → ℝ := fun i => 1 / (((i : ℕ) : ℝ) + 2)
  have hinj : Function.Injective freq := by
    intro i j hij
    simp only [freq, neg_inj] at hij
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity : (0:ℝ) < ((i : ℕ) : ℝ) + 1))
      (Set.mem_Ioi.mpr (by positivity : (0:ℝ) < ((j : ℕ) : ℝ) + 1)) hij
    exact Fin.ext (by exact_mod_cast (add_right_cancel this))
  have hδ : ∀ r, 0 < δ r := fun r => by positivity
  have hsep : ∀ r s, r ≠ s → δ r ≤ |freq r - freq s| := fun r s h =>
    log_sep (fun e => h (Fin.ext e))
  have hmv := abs_integral_norm_sq_sum_sub_le x hinj hδ hsep (a := a) (b := b)
  have hfun : ∀ t : ℝ, ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I) =
      ∑ r, x r * cexp ((freq r : ℂ) * t * I) := fun t => by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [term_eq]
  have hxn : ∀ r : Fin N, ‖x r‖ ^ 2 = (((r : ℕ) : ℝ) + 1) ^ (-(2 * σ)) := fun r => by
    simp only [x, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  have hdiag : ∑ r, ‖x r‖ ^ 2 = ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-(2 * σ)) := by
    simp_rw [hxn]
    exact Fin.sum_univ_eq_sum_range (fun n => ((n : ℝ) + 1) ^ (-(2 * σ))) N
  have hoff : ∑ r, ‖x r‖ ^ 2 / δ r ≤ 2 * N := by
    calc ∑ r, ‖x r‖ ^ 2 / δ r ≤ ∑ _r : Fin N, (2 : ℝ) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [hxn]
          have hr1 : (1 : ℝ) ≤ ((r : ℕ) : ℝ) + 1 := by
            linarith [(Nat.cast_nonneg (r : ℕ) : (0:ℝ) ≤ _)]
          have hp : (((r : ℕ) : ℝ) + 1) ^ (-(2 * σ)) ≤ (((r : ℕ) : ℝ) + 1) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
          rw [Real.rpow_neg_one] at hp
          simp only [δ, div_div_eq_mul_div, div_one]
          calc (((r : ℕ) : ℝ) + 1) ^ (-(2 * σ)) * (((r : ℕ) : ℝ) + 2)
              ≤ (((r : ℕ) : ℝ) + 1)⁻¹ * (((r : ℕ) : ℝ) + 2) := by gcongr
            _ ≤ 2 := by
              rw [inv_mul_le_iff₀ (by linarith)]; linarith
      _ = 2 * N := by simp [mul_comm]
  have hint : ∫ t in a..b, ‖∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I)‖ ^ 2
      = ∫ t in a..b, ‖∑ r, x r * cexp ((freq r : ℂ) * t * I)‖ ^ 2 := by
    simp_rw [hfun]
  rw [hint, ← hdiag]
  linarith

/-- On `Re s = 1/2` the diagonal is the harmonic number: `∑_{n<N} (n + 1)^{−1} = H_N`. -/
lemma sum_rpow_half_eq_harmonic (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-(2 * (1 / 2 : ℝ))) = (harmonic N : ℝ) := by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]

/-- `|∫_1^X |∑_{n<N} (n+1)^{−1/2−it}|² dt − X log X| ≤ 106 X` for `N = ⌈X⌉`, `X ≥ 1`. -/
theorem abs_integral_dirichlet_half_sub_le {X : ℝ} (hX : 1 ≤ X) :
    |(∫ t in (1 : ℝ)..X,
        ‖∑ n ∈ Finset.range ⌈X⌉₊, 1 / ((n : ℂ) + 1) ^ (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2) -
      X * Real.log X| ≤ 106 * X := by
  set N : ℕ := ⌈X⌉₊ with hNdef
  have hXN : X ≤ N := Nat.le_ceil X
  have hNX : (N : ℝ) ≤ X + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hX0 : 0 < X := by linarith
  have hmv := abs_integral_norm_sq_dirichlet_sub_le (σ := 1 / 2) le_rfl N 1 X
  rw [sum_rpow_half_eq_harmonic] at hmv
  -- `log X ≤ H_N ≤ log X + 2`
  have hH1 : Real.log X ≤ (harmonic N : ℝ) := by
    have h := log_add_one_le_harmonic N
    have : Real.log X ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_le_log hX0 (by push_cast; linarith)
    linarith
  have hH2 : (harmonic N : ℝ) ≤ Real.log X + 2 := by
    have h := harmonic_le_one_add_log N
    have hN2 : (N : ℝ) ≤ 2 * X := by linarith
    have : Real.log N ≤ Real.log X + 1 := by
      calc Real.log N ≤ Real.log (2 * X) := Real.log_le_log (by linarith) hN2
        _ = Real.log 2 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
        _ ≤ Real.log X + 1 := by
          have := Real.log_two_lt_d9; linarith
    linarith
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlogX : Real.log X ≤ X := by
    have := Real.log_le_sub_one_of_pos hX0; linarith
  rw [abs_le] at hmv ⊢
  constructor
  · nlinarith
  · nlinarith

/-- The Euler–Maclaurin remainder on `Re s = 1/2`: `ζ(1/2 + it)` minus the Dirichlet polynomial. -/
def E (X t : ℝ) : ℂ :=
  riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I) -
    ∑ n ∈ Finset.range ⌈X⌉₊, 1 / ((n : ℂ) + 1) ^ (((1 / 2 : ℝ) : ℂ) + t * I)

/-- `|a + b + c|² ≤ 3(|a|² + |b|² + |c|²)`. -/
lemma norm_add3_sq_le (a b c : ℂ) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_add₃_le
  have h0 : 0 ≤ ‖a + b + c‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖b‖ - ‖c‖),
    norm_nonneg a, norm_nonneg b, norm_nonneg c]

/-- **The remainder has mean square `O(X)`**: `∫_1^X |E(X, t)|² dt ≤ 3(3 + π) X` for `X ≥ 1`. -/
theorem integral_norm_sq_E_le {X : ℝ} (hX : 1 ≤ X) :
    ∫ t in (1 : ℝ)..X, ‖E X t‖ ^ 2 ≤ 3 * (3 + π) * X := by
  set σ : ℝ := 1 / 2 with hσdef
  have hσ0 : 0 < σ := by norm_num [hσdef]
  have hσh : 1 / 2 ≤ σ := le_rfl
  set N : ℕ := ⌈X⌉₊ with hNdef
  have hXN : X ≤ N := Nat.le_ceil X
  have hNX : (N : ℝ) ≤ X + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hN1 : (1 : ℝ) ≤ N := le_trans hX hXN
  have hN : 0 < N := by exact_mod_cast (lt_of_lt_of_le one_pos hN1)
  have hNr : (0 : ℝ) < N := by linarith
  -- the pointwise bound on `[1, X]`
  have hpt : ∀ t ∈ Icc (1 : ℝ) X, ‖E X t‖ ^ 2 ≤
      3 * ((N : ℝ) * (t ^ (-2 : ℝ))) + 1 + 3 * (σ ^ 2 + X ^ 2) * ‖tailFn N σ t‖ ^ 2 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
    set s : ℂ := (σ : ℂ) + t * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hEeq : E X t = (-((N : ℂ) ^ (1 - s))) / (1 - s) + (-((N : ℂ) ^ (-s))) / 2 +
        s * tailFn N σ t := by
      rw [E, ← hNdef, zeta_split hσ0 ht0.ne' hN]
      ring
    rw [hEeq]
    refine (norm_add3_sq_le _ _ _).trans ?_
    have hB : ‖(-((N : ℂ) ^ (1 - s))) / (1 - s)‖ ^ 2 ≤ (N : ℝ) * t ^ (-2 : ℝ) := by
      rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hN]
      have h1s : t ≤ ‖1 - s‖ := by
        have := Complex.abs_im_le_norm (1 - s)
        simp [hs] at this
        rwa [abs_of_pos ht0] at this
      have hre1 : (1 - s).re = 1 - σ := by simp [hs]
      rw [hre1, div_pow, Real.rpow_neg ht0.le, Real.rpow_two]
      have hpow : ((N : ℝ) ^ (1 - σ)) ^ 2 ≤ N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
        calc (N : ℝ) ^ ((1 - σ) * ((2 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; norm_num [hσdef])
          _ = N := Real.rpow_one _
      rw [div_eq_mul_inv]
      gcongr
    have hC : ‖(-((N : ℂ) ^ (-s))) / 2‖ ^ 2 ≤ 1 / 4 := by
      rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hN]
      have : (N : ℝ) ^ (-s).re ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos hN1
        simp [hs]; linarith
      have h0 : 0 ≤ (N : ℝ) ^ (-s).re := Real.rpow_nonneg hNr.le _
      rw [show ‖(2 : ℂ)‖ = 2 by simp, div_pow]
      nlinarith
    have hD : ‖s * tailFn N σ t‖ ^ 2 ≤ (σ ^ 2 + X ^ 2) * ‖tailFn N σ t‖ ^ 2 := by
      rw [norm_mul, mul_pow]
      gcongr
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hsre]
      simp only [hs, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
      have h2 : t * t ≤ X ^ 2 := by nlinarith [ht.2]
      nlinarith
    have hsum := add_le_add (add_le_add hB hC) hD
    nlinarith [hsum]
  -- integrability
  have hiB : IntervalIntegrable (fun t : ℝ => 3 * ((N : ℝ) * (t ^ (-2 : ℝ)))) volume 1 X := by
    refine (ContinuousOn.intervalIntegrable ?_)
    rw [uIcc_of_le hX]
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul continuousOn_const ?_)
    exact fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl
      (lt_of_lt_of_le one_pos ht.1).ne')).continuousWithinAt
  have hiD : IntervalIntegrable (fun t => 3 * (σ ^ 2 + X ^ 2) * ‖tailFn N σ t‖ ^ 2) volume 1 X :=
    ((integrable_norm_sq_tailFn hσh hNr).const_mul _).intervalIntegrable
  have hiE : IntervalIntegrable (fun t : ℝ => ‖E X t‖ ^ 2) volume 1 X := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hX]
    intro t ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht.1).ne'
    have h1 : ContinuousAt (fun t : ℝ => (σ : ℂ) + t * I) t := by fun_prop
    have h2 : ContinuousAt riemannZeta ((σ : ℂ) + t * I) :=
      (differentiableAt_riemannZeta (line_ne_one ht0)).continuousAt
    have hz := ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + t * I) h2 h1
    have hA : Continuous fun t : ℝ =>
        ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I) := by
      have e : (fun t : ℝ => ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I)) =
          fun t : ℝ => ∑ n ∈ Finset.range N, ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) *
            cexp (((-Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * t * I) := by
        funext t
        exact Finset.sum_congr rfl fun n _ => ZetaMeanSquare.term_eq n σ t
      rw [e]; exact continuous_finsetSum _ fun n _ => ZetaMeanSquare.continuous_term _ _
    exact ((hz.sub hA.continuousAt).norm.pow 2).continuousWithinAt
  have hmono := intervalIntegral.integral_mono_on hX hiE
    ((hiB.add intervalIntegrable_const).add hiD) hpt
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add (hiB.add intervalIntegrable_const) hiD,
    intervalIntegral.integral_add hiB intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  have IB : ∫ t in (1 : ℝ)..X, t ^ (-2 : ℝ) ≤ 1 := by
    rw [integral_rpow (Or.inr ⟨by norm_num, by
      rw [uIcc_of_le hX]; exact fun h => by linarith [h.1]⟩)]
    norm_num
    have : 0 < X ^ (-1 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    linarith
  have ID := integral_norm_sq_tail_le hσh hNr hX
  have hNinv : (N : ℝ) ^ (-(2 * σ)) = (N : ℝ)⁻¹ := by
    rw [show -(2 * σ) = -1 by norm_num [hσdef], Real.rpow_neg_one]
  rw [hNinv] at ID
  have hπ : 0 < π := Real.pi_pos
  have hIDp : 0 ≤ ∫ t in (1 : ℝ)..X, ‖tailFn N σ t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hX fun t _ => by positivity
  -- `(σ² + X²)/N ≤ 1/4 + X`
  have hND : (σ ^ 2 + X ^ 2) * (π / 2 * (N : ℝ)⁻¹) ≤ π / 2 * (1 / 4 + X) := by
    have h1 : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
    have h2 : X ^ 2 * (N : ℝ)⁻¹ ≤ X := by
      rw [← div_eq_mul_inv, div_le_iff₀ hNr]; nlinarith
    have h0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
    have hs2 : σ ^ 2 = 1 / 4 := by norm_num [hσdef]
    rw [hs2]
    nlinarith
  have hD2 : 3 * (σ ^ 2 + X ^ 2) * ∫ t in (1 : ℝ)..X, ‖tailFn N σ t‖ ^ 2 ≤
      3 * (π / 2 * (1 / 4 + X)) := by
    calc 3 * (σ ^ 2 + X ^ 2) * ∫ t in (1 : ℝ)..X, ‖tailFn N σ t‖ ^ 2
        = 3 * ((σ ^ 2 + X ^ 2) * ∫ t in (1 : ℝ)..X, ‖tailFn N σ t‖ ^ 2) := by ring
      _ ≤ 3 * ((σ ^ 2 + X ^ 2) * (π / 2 * (N : ℝ)⁻¹)) := by gcongr
      _ ≤ 3 * (π / 2 * (1 / 4 + X)) := by gcongr
  simp only [smul_eq_mul, mul_one]
  have h3 : (N : ℝ) * ∫ t in (1 : ℝ)..X, t ^ (-2 : ℝ) ≤ N := mul_le_of_le_one_right hNr.le IB
  have h4 : π / 2 * (1 / 4) ≤ π / 2 * X := by nlinarith
  refine le_trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h3 (by norm_num)) le_rfl) hD2) ?_
  nlinarith

/-- `(1 − η)|a|² − (1 + 1/η)|e|² ≤ |a + e|² ≤ (1 + η)|a|² + (1 + 1/η)|e|²` for `η > 0`. -/
lemma norm_add_sq_bounds (a e : ℂ) {η : ℝ} (hη : 0 < η) :
    (1 - η) * ‖a‖ ^ 2 - (1 + 1 / η) * ‖e‖ ^ 2 ≤ ‖a + e‖ ^ 2 ∧
      ‖a + e‖ ^ 2 ≤ (1 + η) * ‖a‖ ^ 2 + (1 + 1 / η) * ‖e‖ ^ 2 := by
  -- `2uv ≤ ηu² + v²/η`
  have key : ∀ u v : ℝ, 2 * u * v ≤ η * u ^ 2 + 1 / η * v ^ 2 := fun u v => by
    have h := sq_nonneg (η * u - v)
    have : η * u ^ 2 + 1 / η * v ^ 2 - 2 * u * v = (η * u - v) ^ 2 / η := by
      field_simp; ring
    have : 0 ≤ (η * u - v) ^ 2 / η := div_nonneg h hη.le
    linarith
  set u := ‖a‖; set v := ‖e‖; set w := ‖a + e‖
  have hu : 0 ≤ u := norm_nonneg _
  have hv : 0 ≤ v := norm_nonneg _
  have hw : 0 ≤ w := norm_nonneg _
  have h1 : w ≤ u + v := norm_add_le a e
  have h2 : u ≤ w + v := by
    have := norm_sub_le (a + e) e
    simp only [add_sub_cancel_right] at this
    exact this
  have hiη : 0 < 1 / η := by positivity
  constructor
  · -- `u² ≤ (1 + η) w² + (1 + 1/η) v²`, and `1/(1 + η) ≥ 1 − η`
    have hk := key w v
    have hu2 : u ^ 2 ≤ (1 + η) * w ^ 2 + (1 + 1 / η) * v ^ 2 := by nlinarith
    have hηu : 0 ≤ η ^ 2 * u ^ 2 := by positivity
    have hηv : 0 ≤ η * (1 + 1 / η) * v ^ 2 := by positivity
    nlinarith
  · have hk := key u v
    have : w ^ 2 ≤ (u + v) ^ 2 := pow_le_pow_left₀ hw h1 2
    nlinarith

/-- **Hardy–Littlewood's second moment**, with error `O(X √(log X))`: there is `C` with
`|∫_1^X |ζ(1/2 + it)|² dt − X log X| ≤ C X √(log X)` for every `X ≥ 3`. -/
theorem integral_norm_sq_zeta_half_sub_le :
    ∃ C : ℝ, ∀ X : ℝ, 3 ≤ X →
      |(∫ t in (1 : ℝ)..X, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) - X * Real.log X| ≤
        C * X * Real.sqrt (Real.log X) := by
  set K : ℝ := 3 * (3 + π) with hK
  refine ⟨213 + 2 * K, fun X hX3 => ?_⟩
  have hX : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  set L := Real.log X with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  set q := Real.sqrt L with hq
  have hq1 : 1 ≤ q := by rw [hq]; exact Real.one_le_sqrt.mpr hL1
  have hqq : q * q = L := Real.mul_self_sqrt (by linarith)
  set η := 1 / q with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by rw [hη, div_le_one (by linarith)]; exact hq1
  have hiη : 1 / η = q := by rw [hη, one_div_one_div]
  have hηL : η * L = q := by rw [hη, ← hqq]; field_simp
  set A : ℝ → ℂ := fun t =>
    ∑ n ∈ Finset.range ⌈X⌉₊, 1 / ((n : ℂ) + 1) ^ (((1 / 2 : ℝ) : ℂ) + t * I) with hA
  have hcast : ∀ t : ℝ, (1 / 2 : ℂ) + t * I = ((1 / 2 : ℝ) : ℂ) + t * I := fun t => by
    push_cast; ring
  have hsplit : ∀ t : ℝ, riemannZeta (1 / 2 + t * I) = A t + E X t := fun t => by
    rw [E, hcast]; ring
  -- integrability
  have hcA : Continuous fun t : ℝ => ‖A t‖ ^ 2 := continuous_dirichlet (1 / 2) _
  have hiA : IntervalIntegrable (fun t : ℝ => ‖A t‖ ^ 2) volume 1 X := hcA.intervalIntegrable _ _
  have hiZ : IntervalIntegrable (fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) volume 1 X := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hX]
    have := continuousOn_norm_sq_zeta_line (1 / 2) (a := 1) (b := X) one_pos
    refine this.congr fun t _ => ?_
    simp only [hcast]
  have hiE : IntervalIntegrable (fun t : ℝ => ‖E X t‖ ^ 2) volume 1 X := by
    have : (fun t : ℝ => ‖E X t‖ ^ 2) =
        fun t : ℝ => ‖riemannZeta (1 / 2 + t * I) - A t‖ ^ 2 := by
      funext t; rw [hsplit]; ring_nf
    rw [this]
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hX]
    intro t ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht.1).ne'
    have h1 : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + t * I) t := by fun_prop
    have h2 : ContinuousAt riemannZeta ((1 / 2 : ℂ) + t * I) := by
      rw [hcast]; exact (differentiableAt_riemannZeta (line_ne_one ht0)).continuousAt
    have hz := ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (1 / 2 : ℂ) + t * I) h2 h1
    have hAc : Continuous A := by
      have e : A = fun t : ℝ => ∑ n ∈ Finset.range ⌈X⌉₊,
          (((((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            cexp (((-Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * t * I)) := by
        funext t
        exact Finset.sum_congr rfl fun n _ => ZetaMeanSquare.term_eq n (1 / 2) t
      rw [e]; exact continuous_finsetSum _ fun n _ => ZetaMeanSquare.continuous_term _ _
    exact ((hz.sub hAc.continuousAt).norm.pow 2).continuousWithinAt
  -- the two pointwise bounds, integrated
  have hup : ∫ t in (1 : ℝ)..X, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 ≤
      (1 + η) * (∫ t in (1 : ℝ)..X, ‖A t‖ ^ 2) + (1 + 1 / η) * ∫ t in (1 : ℝ)..X, ‖E X t‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hiA.const_mul _) (hiE.const_mul _)]
    refine intervalIntegral.integral_mono_on hX hiZ ((hiA.const_mul _).add (hiE.const_mul _))
      fun t _ => ?_
    rw [hsplit]; exact (norm_add_sq_bounds (A t) (E X t) hη0).2
  have hlo : (1 - η) * (∫ t in (1 : ℝ)..X, ‖A t‖ ^ 2) -
      (1 + 1 / η) * (∫ t in (1 : ℝ)..X, ‖E X t‖ ^ 2) ≤
      ∫ t in (1 : ℝ)..X, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hiA.const_mul _) (hiE.const_mul _)]
    refine intervalIntegral.integral_mono_on hX ((hiA.const_mul _).sub (hiE.const_mul _)) hiZ
      fun t _ => ?_
    rw [hsplit]; exact (norm_add_sq_bounds (A t) (E X t) hη0).1
  have hIA := abs_integral_dirichlet_half_sub_le hX
  have hIE := integral_norm_sq_E_le hX
  have hIE0 : 0 ≤ ∫ t in (1 : ℝ)..X, ‖E X t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hX fun t _ => by positivity
  rw [← hL, ← hK] at *
  rw [hiη] at hup hlo
  set IA := ∫ t in (1 : ℝ)..X, ‖A t‖ ^ 2
  set IE := ∫ t in (1 : ℝ)..X, ‖E X t‖ ^ 2
  set I := ∫ t in (1 : ℝ)..X, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2
  rw [abs_le] at hIA ⊢
  have hK0 : 0 < K := by rw [hK]; have := Real.pi_pos; positivity
  -- `η · IA ≤ η (X L + 106 X) ≤ X q + 106 X`
  have hηIA : η * IA ≤ X * q + 106 * X := by
    have : η * IA ≤ η * (X * L + 106 * X) := by
      apply mul_le_mul_of_nonneg_left _ hη0.le; linarith [hIA.2]
    have h2 : η * (X * L + 106 * X) = X * (η * L) + η * (106 * X) := by ring
    rw [hηL] at h2
    have h3 : η * (106 * X) ≤ 106 * X := by nlinarith
    linarith
  have hηIA' : -(X * q + 106 * X) ≤ η * IA := by
    have : -(106 * X) ≤ η * IA := by
      have hIA0 : -(106 * X) ≤ IA := by
        have : 0 ≤ X * L := by positivity
        linarith [hIA.1]
      rcases le_or_gt 0 IA with h | h
      · have : 0 ≤ η * IA := mul_nonneg hη0.le h
        linarith
      · nlinarith
    have : 0 ≤ X * q := by positivity
    linarith
  have hEq : (1 + q) * IE ≤ (1 + q) * (K * X) := by
    apply mul_le_mul_of_nonneg_left hIE; linarith
  have hXq : X ≤ X * q := by nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- `t ↦ |ζ(1/2 + it)|²` is integrable on every interval (`1/2 + it ≠ 1`). -/
lemma intervalIntegrable_norm_sq_zeta_half (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) volume a b := by
  refine Continuous.intervalIntegrable ?_ _ _
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hne : (1 / 2 : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h1 : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + t * I) t := by fun_prop
  have h2 : ContinuousAt riemannZeta ((1 / 2 : ℂ) + t * I) :=
    (differentiableAt_riemannZeta hne).continuousAt
  exact (ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (1 / 2 : ℂ) + t * I) h2 h1).norm.pow 2

/-- **Hardy–Littlewood's second moment from `0`**: there is `C` with
`|∫_0^X |ζ(1/2 + it)|² dt − X log X| ≤ C X √(log X)` for every `X ≥ 3`. -/
theorem integral_zero_norm_sq_zeta_half_sub_le :
    ∃ C : ℝ, ∀ X : ℝ, 3 ≤ X →
      |(∫ t in (0 : ℝ)..X, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) - X * Real.log X| ≤
        C * X * Real.sqrt (Real.log X) := by
  obtain ⟨C, hC⟩ := integral_norm_sq_zeta_half_sub_le
  set c₀ := ∫ t in (0 : ℝ)..1, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2
  refine ⟨C + |c₀|, fun X hX3 => ?_⟩
  have hX0 : 0 < X := by linarith
  have hsplit : ∫ t in (0 : ℝ)..X, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 =
      c₀ + ∫ t in (1 : ℝ)..X, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_norm_sq_zeta_half 0 1)
      (intervalIntegrable_norm_sq_zeta_half 1 X)).symm
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have hq1 : 1 ≤ Real.sqrt (Real.log X) := Real.one_le_sqrt.mpr hL1
  have h1 : 1 ≤ X * Real.sqrt (Real.log X) := by nlinarith
  have hc : |c₀| ≤ |c₀| * X * Real.sqrt (Real.log X) := by
    have := mul_le_mul_of_nonneg_left h1 (abs_nonneg c₀)
    linarith [show |c₀| * X * Real.sqrt (Real.log X) = |c₀| * (X * Real.sqrt (Real.log X)) by ring]
  rw [hsplit]
  calc |c₀ + (∫ t in (1 : ℝ)..X, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) - X * Real.log X|
      = |c₀ + ((∫ t in (1 : ℝ)..X, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) - X * Real.log X)| := by
        rw [add_sub_assoc]
    _ ≤ |c₀| + |(∫ t in (1 : ℝ)..X, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) - X * Real.log X| :=
        abs_add_le _ _
    _ ≤ |c₀| * X * Real.sqrt (Real.log X) + C * X * Real.sqrt (Real.log X) :=
        add_le_add hc (hC X hX3)
    _ = (C + |c₀|) * X * Real.sqrt (Real.log X) := by ring

/-- **Hardy–Littlewood (1918): `∫_0^T |ζ(1/2 + it)|² dt ∼ T log T`.** -/
theorem integral_norm_sq_zeta_half_isEquivalent :
    (fun T : ℝ => ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) ~[atTop]
      fun T : ℝ => T * Real.log T := by
  obtain ⟨C, hC⟩ := integral_zero_norm_sq_zeta_half_sub_le
  refine IsLittleO.isEquivalent ?_
  refine isLittleO_iff.mpr fun c hc => ?_
  set M : ℝ := (|C| / c + 1) ^ 2
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop M] with X hX3 hXM
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  set L := Real.log X
  set q := Real.sqrt L
  have hqq : q * q = L := Real.mul_self_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqM : |C| / c + 1 ≤ q := by
    rw [show q = Real.sqrt L from rfl]
    calc |C| / c + 1 = Real.sqrt ((|C| / c + 1) ^ 2) := by
          rw [Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hXM
  have hCq : |C| ≤ c * q := by
    have : |C| / c ≤ q := by linarith
    rwa [div_le_iff₀ hc, mul_comm] at this
  have hb := hC X hX3
  have hgL : 0 ≤ X * L := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgL]
  simp only [Pi.sub_apply]
  calc |(∫ t in (0 : ℝ)..X, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) - X * L|
      ≤ C * X * q := hb
    _ ≤ |C| * X * q := by
        have : C ≤ |C| := le_abs_self C
        have : 0 ≤ X * q := by positivity
        nlinarith
    _ ≤ (c * q) * X * q := by
        have : 0 ≤ X * q := by positivity
        nlinarith
    _ = c * (X * L) := by rw [← hqq]; ring

end LeanClassics.ZetaSecondMoment
end
end

-- ===== ZetaMomentsFC.Main =====
/-
Hardy-Littlewood (1918) in formal-conjectures' wording (from ZetaMomentsFC/Main.lean).
`(1/T) ∫_0^T |ζ(1/2 + it)|² dt ∼ log T` as `T → ∞`: multiply
`LeanClassics.ZetaSecondMoment.integral_norm_sq_zeta_half_isEquivalent` (`∫_0^T |ζ(1/2 + it)|² dt ∼ T log T`)
by `1/T`. The definition `moment` is the one imported from formal-conjectures.
-/
section
open Complex Filter Real
open scoped Asymptotics Nat
open RiemannZetaMoments

namespace OMAPort_ZetaMoments

/-- `moment 1 T` is `1/T` times lean_classics' integral (same integrand up to `I * t = t * I`). -/
lemma moment_one_eq (T : ℝ) :
    moment 1 T = 1 / T * ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 := by
  simp only [moment, mul_one]
  congr 2
  funext t
  rw [mul_comm I]

end OMAPort_ZetaMoments

/-- Hardy and Littlewood: `moment 1 T ∼ log T` (original theorem `RiemannZetaMoments.moment_isEquiv₁`). -/
theorem OMA.solution : type_of% @RiemannZetaMoments.moment_isEquiv₁ := by
  have h := (Asymptotics.IsEquivalent.refl (u := fun T : ℝ => 1 / T) (l := atTop)).mul
    LeanClassics.ZetaSecondMoment.integral_norm_sq_zeta_half_isEquivalent
  have hl : (fun T : ℝ => 1 / T) * (fun T : ℝ => T * Real.log T) =ᶠ[atTop] fun T ↦ T.log := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simp only [Pi.mul_apply]
    field_simp
  have hm : (fun T : ℝ => 1 / T) * (fun T : ℝ => ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) =
      moment 1 := by
    funext T
    rw [OMAPort_ZetaMoments.moment_one_eq]
    rfl
  rw [← hm]
  exact h.congr_right hl

end
