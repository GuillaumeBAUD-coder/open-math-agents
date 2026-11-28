import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1.R4 of step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1
-- Credit: @mucoucah
-- CREDIT: OpenAI, openai/math, Quasipolynomial Bounds for Arithmetic Progressions (2026), commit 3344da5, lean/OAI/Combinatorics/Progressions/Estimates/UniformRelativePatchSource.lean (subquadratic_patch_descent, quantitative_density_of_patch_source), Apache-2.0 (source, not solver).
-- CREDIT: @YevhenDiachenko0, PR #36701 (reduction lower.R1.H2.R1.H1.R3): statements of H1 and H2 and the budget glue copied (source, not solver).
-- CREDIT: @mijuny, PR #36674 (reduction lower.R2.H1.R1.H2.R1.H1.R1): H3, the finite descent and the inversion to the uniform bound copied (source, not solver).
-- CREDIT: @NicholasWierenga, reduction lower.R1.H2.R1: the descent formulation.

/-!
# The uniform quasipolynomial bound from OpenAI's patch source and density step

Target: step H1 of reduction lower.R2.H1.R1.H2.R1, the bound
|S| ≤ C N exp (-c (log log N)^(1+η)) for k-progression-free S ⊆ [1, N], k ≥ 4. This is
QuantitativeDensityBound of the openai/math library.

This file splits it at the two deep inputs of the openai/math proof, so that a port of those
inputs closes this step directly:

* H1 (patch source): a sparse progression-free set inside its log-log budget has an amplified
  correlation with a polynomial patch (written out with Mathlib objects). In openai/math:
  SubquadraticPatchSource with exists_selected_density_drop.
* H2 (structured density step): such a correlation gives a progression with a larger density.
  In openai/math: scored_patch_density_step.
* H3 (terminal step at fixed density): the same statement as step lower.R1.H2.R1.H2, which is
  already proved on main.

The proof composes two existing reductions: H1 and H2 give the sparse affine density increment
(the glue of PR #36701), and that increment with H3 gives the uniform bound by finite descent
and inversion (the glue of PR #36674).
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R4

open Filter Real
open scoped Topology


/-- Source: a sparse progression-free set has an amplified correlation with a polynomial patch. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ (s : ℕ) (ν c B D p₀ C₁ : ℝ), 0 < ν ∧ ν < 1 ∧ 0 < c ∧ 0 ≤ B ∧ 0 ≤ D ∧
    ∀ (N : ℕ) (S : Finset ℕ) (p : ℝ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      p = max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) →
      p₀ ≤ p → p ^ (1 - ν / 2) + C₁ ≤ Real.log (Real.log (N : ℝ)) →
      ∃ (d M a q : ℕ) (U G : ℝ) (w : Fin d → ℕ)
        (P : (i : Fin d) → MvPolynomial (Unit ⊕ Fin i.val) ℝ)
        (Φ : (Fin d → ℝ) → ℝ) (L : NNReal),
        (∀ i, 1 ≤ w i ∧ w i ≤ s) ∧ Monotone w ∧
        (∀ i, P i ∈ MvPolynomial.restrictSupport ℝ
          {m | Finsupp.weight (Sum.elim (fun _ : Unit ↦ (1 : ℕ))
            (fun j : Fin i.val ↦ w ⟨j.val, lt_trans j.isLt i.isLt⟩)) m ≤ w i}) ∧
        (∀ x, 0 ≤ Φ x ∧ Φ x ≤ 1) ∧ (∀ x, Φ x ≠ 0 → ∀ i, |x i| ≤ 1 / 4) ∧
        LipschitzWith L Φ ∧
        0 < q ∧ (∀ n < M, a + q * n ∈ Finset.Icc 1 N) ∧ 1 ≤ U ∧
        Real.log (N : ℝ) - U ≤ Real.log (M : ℝ) ∧ (L : ℝ) + 1 ≤ Real.exp U ∧
        Real.log ((d : ℝ) + 1) ≤ B * Real.log (2 + p) ∧
        Real.log U ≤ D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) ∧
        0 < G ∧ c * p ^ ν ≤ Real.log G ∧
        Real.exp (-U) ≤ (∑ n ∈ Finset.range M,
          ((if a + q * n ∈ S then (1 : ℝ) else 0) - G * ((S.card : ℝ) / (N : ℝ))) *
            ∑' b : Fin d → ℤ, Φ (fun i ↦ (b i : ℝ) - MvPolynomial.aeval
              (Sum.elim (fun _ : Unit ↦ (n : ℝ))
                (fun j : Fin i.val ↦ (b ⟨j.val, lt_trans j.isLt i.isLt⟩ : ℝ))) (P i))) /
          (M : ℝ)

/-- Structured density step: a correlation with a patch gives a denser progression. -/
def H2 : Prop :=
  ∀ s : ℕ, ∃ L₀ : ℝ, ∀ (N : ℕ) (S : Finset ℕ) (p : ℝ) (d M a q : ℕ) (U R V G δ : ℝ)
      (w : Fin d → ℕ) (P : (i : Fin d) → MvPolynomial (Unit ⊕ Fin i.val) ℝ)
      (Φ : (Fin d → ℝ) → ℝ) (L : NNReal),
    (∀ i, 1 ≤ w i ∧ w i ≤ s) → Monotone w →
    (∀ i, P i ∈ MvPolynomial.restrictSupport ℝ
      {m | Finsupp.weight (Sum.elim (fun _ : Unit ↦ (1 : ℕ))
        (fun j : Fin i.val ↦ w ⟨j.val, lt_trans j.isLt i.isLt⟩)) m ≤ w i}) →
    (∀ x, 0 ≤ Φ x ∧ Φ x ≤ 1) → (∀ x, Φ x ≠ 0 → ∀ i, |x i| ≤ 1 / 4) →
    LipschitzWith L Φ →
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    p = max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) →
    0 < q → (∀ n < M, a + q * n ∈ Finset.Icc 1 N) → 1 ≤ U →
    Real.log (N : ℝ) - U ≤ Real.log (M : ℝ) → (L : ℝ) + 1 ≤ Real.exp U →
    Real.log ((d : ℝ) + 1) ≤ R → Real.log U ≤ V →
    L₀ + ((2 * s * s + 1 : ℕ) : ℝ) * R + V ≤ Real.log (Real.log (N : ℝ)) →
    0 < G → δ ≤ Real.log G → 2 ≤ p - δ →
    Real.exp (-U) ≤ (∑ n ∈ Finset.range M,
      ((if a + q * n ∈ S then (1 : ℝ) else 0) - G * ((S.card : ℝ) / (N : ℝ))) *
        ∑' b : Fin d → ℤ, Φ (fun i ↦ (b i : ℝ) - MvPolynomial.aeval
          (Sum.elim (fun _ : Unit ↦ (n : ℝ))
            (fun j : Fin i.val ↦ (b ⟨j.val, lt_trans j.isLt i.isLt⟩ : ℝ))) (P i))) /
      (M : ℝ) →
    ∃ a' q' M' : ℕ, 0 < q' ∧ 2 ≤ M' ∧
      (∀ i ∈ Finset.Icc 1 M', a' + (i - 1) * q' ∈ Finset.Icc 1 N) ∧
      Real.log (Real.log (N : ℝ)) - (L₀ + ((2 * s * s : ℕ) : ℝ) * R) ≤
        Real.log (Real.log (M' : ℝ)) ∧
      G * ((S.card : ℝ) / (N : ℝ)) <
        (((Finset.Icc 1 M').filter (fun i ↦ a' + (i - 1) * q' ∈ S)).card : ℝ) / (M' : ℝ) ∧
      max 2 (Real.log (2 * (M' : ℝ) /
        (((Finset.Icc 1 M').filter (fun i ↦ a' + (i - 1) * q' ∈ S)).card : ℝ))) ≤ p - δ

/-- Fixed positive density forces a progression once the interval is long enough. -/
def H3 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ T : ℝ, ∃ Q : ℝ, ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
    max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) ≤ T →
      Real.log (Real.log (N : ℝ)) < Q

/-- Concavity of x ↦ x^β for 0 ≤ β ≤ 1, in tangent-line form at p. -/
lemma concave_drop {p δ β : ℝ} (hp : 0 < p) (_hδ0 : 0 ≤ δ) (hδp : δ ≤ p) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) : (p - δ) ^ β ≤ p ^ β - β * p ^ (β - 1) * δ := by
  have hs : -1 ≤ -δ / p := by
    rw [neg_div, neg_le_neg_iff, div_le_one hp]
    exact hδp
  have h := rpow_one_add_le_one_add_mul_self hs hβ0 hβ1
  have h1 : 0 ≤ 1 + -δ / p := by linarith
  have e1 : p - δ = p * (1 + -δ / p) := by
    field_simp
    ring
  have e2 : p ^ (β - 1) = p ^ β / p := Real.rpow_sub_one hp.ne' β
  have hpβ : 0 ≤ p ^ β := Real.rpow_nonneg hp.le β
  calc (p - δ) ^ β = p ^ β * (1 + -δ / p) ^ β := by rw [e1, Real.mul_rpow hp.le h1]
    _ ≤ p ^ β * (1 + β * (-δ / p)) := mul_le_mul_of_nonneg_left h hpβ
    _ = p ^ β - β * p ^ (β - 1) * δ := by
      rw [e2]
      field_simp
      ring

/-- A power bound for log (2 + p). -/
lemma log_two_add_le {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    Real.log (2 + p) ≤ 2 ^ ε / ε * p ^ ε := by
  have h := Real.log_le_rpow_div (show (0 : ℝ) ≤ 2 + p by linarith) hε
  have h2 : (2 + p) ^ ε ≤ (2 * p) ^ ε := Real.rpow_le_rpow (by linarith) (by linarith) hε.le
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h2
  calc Real.log (2 + p) ≤ (2 + p) ^ ε / ε := h
    _ ≤ (2 ^ ε * p ^ ε) / ε := div_le_div_of_nonneg_right h2 hε.le
    _ = 2 ^ ε / ε * p ^ ε := by ring

/-- Logarithmic resources are eventually dominated by a larger power. -/
lemma ev_budget (K₁ K₂ K₃ K₄ a γ : ℝ) (h1 : 0 ≤ K₁) (h2 : 0 ≤ K₂) (h4 : 0 < K₄) (ha : 0 ≤ a)
    (haγ : a < γ) :
    ∀ᶠ p : ℝ in atTop,
      K₁ * Real.log (2 + p) + K₂ * p ^ a * Real.log (2 + p) + K₃ ≤ K₄ * p ^ γ := by
  have hε0 : 0 < (γ - a) / 2 := by linarith
  have hA0 : 0 ≤ 2 ^ ((γ - a) / 2) / ((γ - a) / 2) := by positivity
  have hev : ∀ᶠ p : ℝ in atTop,
      ((K₁ + K₂) * (2 ^ ((γ - a) / 2) / ((γ - a) / 2)) + |K₃|) / K₄ ≤ p ^ ((γ - a) / 2) :=
    (tendsto_rpow_atTop hε0).eventually_ge_atTop _
  filter_upwards [hev, eventually_ge_atTop (2 : ℝ)] with p hpε hp2
  set ε : ℝ := (γ - a) / 2 with hε
  set A : ℝ := 2 ^ ε / ε with hA
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hlog : Real.log (2 + p) ≤ A * p ^ ε := log_two_add_le hp2 hε0
  have hpa : 0 ≤ p ^ a := Real.rpow_nonneg hp0.le a
  have e1 : p ^ a * p ^ ε = p ^ (a + ε) := (Real.rpow_add hp0 a ε).symm
  have hq1 : p ^ ε ≤ p ^ (a + ε) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hq0 : 1 ≤ p ^ (a + ε) := Real.one_le_rpow hp1 (by linarith)
  have e2 : p ^ γ = p ^ (a + ε) * p ^ ε := by
    rw [← Real.rpow_add hp0]
    congr 1
    rw [hε]
    ring
  have t1 : K₁ * Real.log (2 + p) ≤ K₁ * A * p ^ (a + ε) := by
    calc K₁ * Real.log (2 + p) ≤ K₁ * (A * p ^ ε) := mul_le_mul_of_nonneg_left hlog h1
      _ ≤ K₁ * (A * p ^ (a + ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq1 hA0) h1
      _ = K₁ * A * p ^ (a + ε) := by ring
  have t2 : K₂ * p ^ a * Real.log (2 + p) ≤ K₂ * A * p ^ (a + ε) := by
    calc K₂ * p ^ a * Real.log (2 + p) ≤ K₂ * p ^ a * (A * p ^ ε) :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg h2 hpa)
      _ = K₂ * A * (p ^ a * p ^ ε) := by ring
      _ = K₂ * A * p ^ (a + ε) := by rw [e1]
  have t3 : K₃ ≤ |K₃| * p ^ (a + ε) := by
    calc K₃ ≤ |K₃| := le_abs_self K₃
      _ = |K₃| * 1 := (mul_one _).symm
      _ ≤ |K₃| * p ^ (a + ε) := mul_le_mul_of_nonneg_left hq0 (abs_nonneg _)
  have t4 : (K₁ + K₂) * A + |K₃| ≤ K₄ * p ^ ε := by
    rw [div_le_iff₀ h4] at hpε
    linarith
  have hq : 0 ≤ p ^ (a + ε) := by linarith
  have e3 : ((K₁ + K₂) * A + |K₃|) * p ^ (a + ε) =
      K₁ * A * p ^ (a + ε) + K₂ * A * p ^ (a + ε) + |K₃| * p ^ (a + ε) := by ring
  calc K₁ * Real.log (2 + p) + K₂ * p ^ a * Real.log (2 + p) + K₃
      ≤ ((K₁ + K₂) * A + |K₃|) * p ^ (a + ε) := by linarith
    _ ≤ K₄ * p ^ ε * p ^ (a + ε) := mul_le_mul_of_nonneg_right t4 hq
    _ = K₄ * p ^ γ := by rw [e2]; ring


/-- The sparse affine density increment of reduction lower.R1.H2.R1 (its step H1), obtained
from the patch source H1 and the structured density step H2. Glue copied from PR #36701
(@YevhenDiachenko0), which ports openai/math subquadratic_patch_descent. -/
theorem descent_of_source (h1 : H1) (h2 : H2) :
  ∀ k : ℕ, 4 ≤ k →
    ∃ (β C T R₀ : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ (N : ℕ) (S : Finset ℕ),
        2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
          (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
        T < p → C * p ^ β + R ≤ Real.log (Real.log (N : ℝ)) →
          ∃ (a q M : ℕ), 0 < q ∧ 2 ≤ M ∧
            (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
            let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
            let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
            0 < U.card ∧ p' + 1 ≤ p ∧ C * p' ^ β + R ≤ Real.log (Real.log (M : ℝ)) := by
  intro k hk
  obtain ⟨s, ν, c, B, D, p₀, C₁, hν, hν1, hc, hB, hD, hsrc⟩ := h1 k hk
  obtain ⟨L₀, hstep⟩ := h2 s
  set β : ℝ := 1 - ν / 2 with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; linarith
  have hβ1 : β < 1 := by rw [hβdef]; linarith
  have hβq : 1 / 4 < β := by rw [hβdef]; linarith
  have hK1 : (0 : ℝ) ≤ ((2 * s * s + 1 : ℕ) : ℝ) * B := by positivity
  have hK1' : (0 : ℝ) ≤ ((2 * s * s : ℕ) : ℝ) * B := by positivity
  have hE2 := ev_budget (((2 * s * s + 1 : ℕ) : ℝ) * B) D L₀ 1 (1 / 4) β hK1 hD one_pos
    (by norm_num) hβq
  have hE4 := ev_budget (((2 * s * s : ℕ) : ℝ) * B) 0 L₀ (β * c) 0 (ν / 2) hK1' le_rfl
    (mul_pos hβ0 hc) le_rfl (by linarith)
  have hE3a : ∀ᶠ p : ℝ in atTop, 1 ≤ c * p ^ ν := by
    filter_upwards [(tendsto_rpow_atTop hν).eventually_ge_atTop (1 / c)] with p hp
    rw [div_le_iff₀ hc] at hp
    linarith
  have hE3b : ∀ᶠ p : ℝ in atTop, c * p ^ ν + 2 ≤ p := by
    filter_upwards [(tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - ν)).eventually_ge_atTop
      (2 * c), eventually_ge_atTop (4 : ℝ)] with p hp1 hp4
    have hp0 : 0 < p := by linarith
    have e : p ^ ν * p ^ (1 - ν) = p := by
      rw [← Real.rpow_add hp0, show ν + (1 - ν) = 1 by ring, Real.rpow_one]
    have hpν : 0 ≤ p ^ ν := Real.rpow_nonneg hp0.le ν
    have h2c : c * p ^ ν * 2 ≤ p := by
      calc c * p ^ ν * 2 = p ^ ν * (2 * c) := by ring
        _ ≤ p ^ ν * p ^ (1 - ν) := mul_le_mul_of_nonneg_left hp1 hpν
        _ = p := e
    linarith
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop p₀).and (hE2.and (hE4.and (hE3a.and hE3b))))
  refine ⟨β, 1, max T₀ 2, max C₁ 0, hβ0, hβ1, one_pos, ?_⟩
  intro R hR N S hN hS hcard hfree p hTp hinv
  have hpT : T₀ ≤ p := le_trans (le_max_left _ _) hTp.le
  obtain ⟨hp₀, hb2, hb4, hc1, hc2⟩ := hT₀ p hpT
  have hp2 : (2 : ℝ) ≤ p := le_max_left _ _
  have hp0 : 0 < p := by linarith
  have hRC : C₁ ≤ R := le_trans (le_max_left _ _) hR
  have hR0 : 0 ≤ R := le_trans (le_max_right _ _) hR
  have hinv' : p ^ β + R ≤ Real.log (Real.log (N : ℝ)) := by linarith
  obtain ⟨d, M, a, q, U, G, w, P, Φ, L, hw, hmono, hP, hΦ, hsupp, hlip, hq, hprog, hU, hM, hL,
    hd, hUV, hG, hGc, hcorr⟩ := hsrc N S p hN hS hcard hfree rfl hp₀ (by linarith)
  have e5 : ((2 * s * s + 1 : ℕ) : ℝ) * (B * Real.log (2 + p)) =
      ((2 * s * s + 1 : ℕ) : ℝ) * B * Real.log (2 + p) := by ring
  have hsize : L₀ + ((2 * s * s + 1 : ℕ) : ℝ) * (B * Real.log (2 + p)) +
      D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) ≤ Real.log (Real.log (N : ℝ)) := by
    linarith
  obtain ⟨a', q', M', hq', hM', hprog', hll, hdens, hp'⟩ :=
    hstep N S p d M a q U (B * Real.log (2 + p)) (D * p ^ (1 / 4 : ℝ) * Real.log (2 + p)) G
      (c * p ^ ν) w P Φ L hw hmono hP hΦ hsupp hlip hN hS hcard rfl hq hprog hU hM hL hd hUV
      hsize hG hGc (by linarith) hcorr
  refine ⟨a', q', M', hq', hM', hprog', ?_⟩
  intro U' p'
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hScard : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcard
  have hα : 0 < (S.card : ℝ) / (N : ℝ) := div_pos hScard hNpos
  have hGα : 0 < G * ((S.card : ℝ) / (N : ℝ)) := mul_pos hG hα
  have hdens' : G * ((S.card : ℝ) / (N : ℝ)) < (U'.card : ℝ) / (M' : ℝ) := hdens
  have hM'pos : (0 : ℝ) < (M' : ℝ) := by
    have : (2 : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hM'
    linarith
  have hpos : 0 < U'.card := by
    have h0 : 0 < (U'.card : ℝ) / (M' : ℝ) := lt_trans hGα hdens'
    have h0' : (0 : ℝ) < (U'.card : ℝ) := by
      by_contra hcon
      push Not at hcon
      have : (U'.card : ℝ) / (M' : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcon hM'pos.le
      linarith
    exact_mod_cast h0'
  have hp'le : p' ≤ p - c * p ^ ν := hp'
  have hp'2 : (2 : ℝ) ≤ p' := le_max_left _ _
  refine ⟨hpos, by linarith, ?_⟩
  have hδ0 : 0 ≤ c * p ^ ν := by
    have := Real.rpow_nonneg hp0.le ν
    positivity
  have hconc := concave_drop hp0 hδ0 (by linarith) hβ0.le hβ1.le
  have hmono' : p' ^ β ≤ (p - c * p ^ ν) ^ β := Real.rpow_le_rpow (by linarith) hp'le hβ0.le
  have hexp : p ^ (β - 1) * (c * p ^ ν) = c * p ^ (ν / 2) := by
    rw [mul_left_comm, ← Real.rpow_add hp0]
    congr 2
    rw [hβdef]
    ring
  have e3 : β * p ^ (β - 1) * (c * p ^ ν) = β * c * p ^ (ν / 2) := by
    rw [mul_assoc, hexp]
    ring
  have e4 : ((2 * s * s : ℕ) : ℝ) * (B * Real.log (2 + p)) =
      ((2 * s * s : ℕ) : ℝ) * B * Real.log (2 + p) := by ring
  have e6 : (0 : ℝ) * p ^ (0 : ℝ) * Real.log (2 + p) = 0 := by ring
  linarith

lemma eliminate_descent {X : Type} (p : X → ℝ) (P : X → Prop)
    (hp : ∀ x, 0 ≤ p x)
    (decrease : ∀ x, P x → ∃ y, P y ∧ p y + 1 ≤ p x) :
    ∀ x, ¬ P x := by
  suffices H : ∀ n : ℕ, ∀ x, P x → ⌊p x⌋₊ = n → False from
    fun x hx ↦ H _ x hx rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hx he
    obtain ⟨y, hy, hdrop⟩ := decrease x hx
    have hlt : ⌊p y⌋₊ < ⌊p x⌋₊ := (Nat.floor_lt (hp y)).mpr (by
      linarith [Nat.lt_floor_add_one (p x)])
    exact ih _ (by simpa only [he] using hlt) y hy rfl

lemma progression_preimage_free {k a q M : ℕ} {S : Finset ℕ}
    (hk : 4 ≤ k) (hq : 0 < q)
    (hfree : ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k, b + i * d ∈ S) :
    ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k,
      b + i * d ∈ (Finset.Icc 1 M).filter (fun j ↦ a + (j - 1) * q ∈ S) := by
  rintro ⟨b, d, hd, hAP⟩
  have hbase : b ∈ Finset.Icc 1 M := by
    simpa only [zero_mul, add_zero] using (Finset.mem_filter.mp (hAP 0 (by omega))).1
  have hb : 1 ≤ b := (Finset.mem_Icc.mp hbase).1
  refine hfree ⟨a + (b - 1) * q, d * q, Nat.mul_pos hd hq, fun i hi ↦ ?_⟩
  have hmem := (Finset.mem_filter.mp (hAP i hi)).2
  have he : b + i * d - 1 = b - 1 + i * d := by omega
  rw [he] at hmem
  simpa only [add_mul, Nat.add_assoc, Nat.mul_assoc] using hmem


lemma no_budget (h1 : H1) (h2 : H2) (hterm : H3) {k : ℕ} (hk : 4 ≤ k) :
    ∃ (β C R : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        ¬ C * (max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))) ^ β + R ≤
          Real.log (Real.log (N : ℝ)) := by
  obtain ⟨β, C, T, R₀, hβ, hβ1, hC, hstep⟩ := descent_of_source h1 h2 k hk
  obtain ⟨Q, hstop⟩ := hterm k hk T
  let R := max R₀ Q
  refine ⟨β, C, R, hβ, hβ1, hC, ?_⟩
  let X := ℕ × Finset ℕ
  let p (x : X) := max 2 (Real.log (2 * (x.1 : ℝ) / (x.2.card : ℝ)))
  let admissible (x : X) :=
    2 ≤ x.1 ∧ x.2 ⊆ Finset.Icc 1 x.1 ∧ 0 < x.2.card ∧
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ x.2) ∧
      C * (p x) ^ β + R ≤ Real.log (Real.log (x.1 : ℝ))
  have hp (x : X) : 0 ≤ p x := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  have decrease (x : X) (hx : admissible x) :
      ∃ y, admissible y ∧ p y + 1 ≤ p x := by
    obtain ⟨hN, hS, hcard, hfree, hbudget⟩ := hx
    have hlarge : T < p x := by
      by_contra! hsmall
      have hlt := hstop x.1 x.2 hN hS hcard hfree hsmall
      have hnonneg := mul_nonneg hC.le (Real.rpow_nonneg (hp x) β)
      have hQR : Q ≤ R := le_max_right _ _
      linarith
    obtain ⟨a, q, M, hq, hM, _, hcard', hdrop, hbudget'⟩ :=
      hstep R (le_max_left _ _) x.1 x.2 hN hS hcard hfree hlarge hbudget
    let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ x.2)
    refine ⟨(M, U), ⟨hM, Finset.filter_subset _ _, hcard', ?_, hbudget'⟩, hdrop⟩
    exact progression_preimage_free hk hq hfree
  intro N S hN hS hcard hfree hbudget
  exact eliminate_descent p admissible hp decrease (N, S) ⟨hN, hS, hcard, hfree, hbudget⟩

lemma log_log_pos_of_ge_three {N : ℕ} (hN : 3 ≤ N) :
    0 < Real.log (Real.log (N : ℝ)) := by
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexpN : Real.exp 1 < (N : ℝ) := lt_of_lt_of_le he h3
  have hlog1 : 1 < Real.log (N : ℝ) := by
    have := Real.log_lt_log (Real.exp_pos 1) hexpN
    rwa [Real.log_exp] at this
  exact Real.log_pos hlog1

theorem main : H1 → H2 → H3 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H1 := by
  intro h1 h2 hterm k hk
  obtain ⟨β, C, R, hβ, hβ1, hC, hno⟩ := no_budget h1 h2 hterm hk
  let η : ℝ := (1 - β) / β
  have hη : 0 < η := div_pos (sub_pos.mpr hβ1) hβ
  have h1η_pos : 0 < 1 + η := by linarith
  have hmul : β * (1 + η) = 1 := by
    dsimp [η]
    field_simp [hβ.ne']
    ring
  let c : ℝ := (1 / (2 * C)) ^ (1 + η)
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) (1 + η)
  let L₀ : ℝ := max 1 (max (2 * R) (4 * C * (2 : ℝ) ^ β))
  have hL₀1 : 1 ≤ L₀ := le_max_left _ _
  have hL₀R : 2 * R ≤ L₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hL₀2 : 4 * C * (2 : ℝ) ^ β ≤ L₀ := (le_max_right _ _).trans (le_max_right _ _)
  let C' : ℝ := max 2 (Real.exp (c * L₀ ^ (1 + η)))
  have hC'2 : 2 ≤ C' := le_max_left _ _
  have hC'exp : Real.exp (c * L₀ ^ (1 + η)) ≤ C' := le_max_right _ _
  have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num) hC'2
  refine ⟨C', c, η, hC'pos, hc, hη, ?_⟩
  intro N S hN3 hS hfree
  by_cases hScard : S.card = 0
  · rw [hScard, Nat.cast_zero]
    positivity
  have hSpos : 0 < S.card := Nat.pos_of_ne_zero hScard
  have hSposR : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hSpos
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  let L : ℝ := Real.log (Real.log (N : ℝ))
  have hLpos : 0 < L := log_log_pos_of_ge_three hN3
  by_cases hsmall : L ≤ L₀
  · have hpow : L ^ (1 + η) ≤ L₀ ^ (1 + η) :=
      Real.rpow_le_rpow hLpos.le hsmall h1η_pos.le
    have hcmul : c * L ^ (1 + η) ≤ c * L₀ ^ (1 + η) :=
      mul_le_mul_of_nonneg_left hpow hc.le
    have hexp : Real.exp (-(c * L₀ ^ (1 + η))) ≤ Real.exp (-c * L ^ (1 + η)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hone : 1 ≤ C' * Real.exp (-c * L ^ (1 + η)) := by
      calc (1 : ℝ)
          = Real.exp (c * L₀ ^ (1 + η)) * Real.exp (-(c * L₀ ^ (1 + η))) := by
              rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        _ ≤ C' * Real.exp (-c * L ^ (1 + η)) :=
              mul_le_mul hC'exp hexp (Real.exp_pos _).le hC'pos.le
    have hcardN : (S.card : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast ((Finset.card_mono hS).trans_eq (Nat.card_Icc 1 N))
    calc (S.card : ℝ)
        ≤ (N : ℝ) * 1 := by linarith
      _ ≤ (N : ℝ) * (C' * Real.exp (-c * L ^ (1 + η))) :=
            mul_le_mul_of_nonneg_left hone hNposR.le
      _ = C' * (N : ℝ) * Real.exp (-c * L ^ (1 + η)) := by ring
  · have hsmall' : L₀ < L := lt_of_not_ge hsmall
    let q : ℝ := Real.log (2 * (N : ℝ) / (S.card : ℝ))
    let p : ℝ := max 2 q
    have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
    have hfail := hno N S (by omega) hS hSpos hfree
    have hgt : L < C * p ^ β + R := not_le.mp hfail
    have hhalf : L / 2 < C * p ^ β := by linarith
    have hdiv : L / (2 * C) < p ^ β := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have hp_gt2 : 2 < q := by
      by_contra! hq2
      have hp_eq2 : p = 2 := max_eq_left hq2
      rw [hp_eq2] at hhalf
      linarith
    have hp_eq : p = q := max_eq_right hp_gt2.le
    have hrpow : (L / (2 * C)) ^ (1 + η) < (p ^ β) ^ (1 + η) :=
      Real.rpow_lt_rpow (by positivity) hdiv h1η_pos
    have hlhs : (L / (2 * C)) ^ (1 + η) = c * L ^ (1 + η) := by
      have hrewrite : L / (2 * C) = (1 / (2 * C)) * L := by ring
      rw [hrewrite, Real.mul_rpow (by positivity) hLpos.le]
    have hrhs : (p ^ β) ^ (1 + η) = q := by
      rw [← Real.rpow_mul hp_pos.le, hmul, Real.rpow_one, hp_eq]
    rw [hlhs, hrhs] at hrpow
    have hratio_pos : 0 < 2 * (N : ℝ) / (S.card : ℝ) := by positivity
    have hexp_lt : Real.exp (c * L ^ (1 + η)) < 2 * (N : ℝ) / (S.card : ℝ) := by
      have h := Real.exp_lt_exp.mpr hrpow
      rwa [Real.exp_log hratio_pos] at h
    have hmul_lt : (S.card : ℝ) * Real.exp (c * L ^ (1 + η)) < 2 * (N : ℝ) := by
      linarith [(lt_div_iff₀ hSposR).mp hexp_lt]
    calc (S.card : ℝ)
        = ((S.card : ℝ) * Real.exp (c * L ^ (1 + η))) * Real.exp (-c * L ^ (1 + η)) := by
            rw [mul_assoc, ← Real.exp_add]
            have hcancel : c * L ^ (1 + η) + -c * L ^ (1 + η) = 0 := by ring
            rw [hcancel, Real.exp_zero, mul_one]
      _ ≤ (2 * (N : ℝ)) * Real.exp (-c * L ^ (1 + η)) :=
            mul_le_mul_of_nonneg_right hmul_lt.le (Real.exp_pos _).le
      _ ≤ (C' * (N : ℝ)) * Real.exp (-c * L ^ (1 + η)) := by
            gcongr
      _ = C' * (N : ℝ) * Real.exp (-c * L ^ (1 + η)) := by ring

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R4
