import FormalConjectures.ErdosProblems.«1221»

-- Credit: @ptc-prover-bot

/-!
# Erdős 1221, part i — a complete proof

Following Korsky (arXiv:2609.07196, CC BY 4.0), Sections 6–8. The argument is organised as a
reduction (namespace `OMA.R_Erdos1221_erdos_1221_parts_i_R1`: three hypotheses and `main`) together
with proofs of all three hypotheses, so the file proves the problem outright:
* H1: Halász's L¹ lower bound for planar discrepancy (complex Riesz product; constant 1/5120).
* H2: L¹ short-arc regularity from the one-sided span bound (Korsky Lemmas 6.1–6.3, Prop. 6.4).
* H3: from L¹ short-arc regularity to a planar point set with small L¹ discrepancy (Lemma 7.2).
-/

/-!
Reduction R1 of `Erdos1221.erdos_1221.parts.i`: `Λ_r - r → ∞`.

Following Korsky, *A Resolution of the de Bruijn–Erdős Consecutive-Gap Problem*
(arXiv:2609.07196, CC BY 4.0), Theorem 1.1 (first one-sided part), Sections 6–8. If a sequence has
`n M_n^{(r)} - r ≤ A` for all large `n`, with `A = c √(log r)`:
* H2 (Lemmas 6.1–6.3, Proposition 6.4): the `L¹` short-arc discrepancy is then at most `C₃ A` for
  `0 ≤ D ≤ S = √(Ar)/log²(r/A)`.
* H3 (Lemma 7.2, first half): such `L¹` regularity with bound `B ≤ ⌊S⌋/4` yields a point set in the
  unit square of at least `⌊S⌋/2` points whose anchored-box discrepancy has `L¹` norm at most `3B`.
* H1 (Halász 1981; the paper's Theorem 7.1): every `M ≥ 2` points of the unit square have anchored
  `L¹` discrepancy at least `c_H √(log M)`.
`main` is Section 8 with explicit asymptotics: for `c = c_H / (6(|C₃|+1))` these are incompatible
for large `r`, so every admissible sequence has `limsup n M_n ≥ r + c √(log r)`, hence so does `Λ_r`.
-/

namespace OMA.R_Erdos1221_erdos_1221_parts_i_R1

open Filter Erdos1221 MeasureTheory
open scoped ENNReal

/-- Halász's `L¹` lower bound for planar discrepancy (the paper's Theorem 7.1). -/
def H1 : Prop :=
  ∃ cH : ℝ, 0 < cH ∧ ∀ P : Finset (ℝ × ℝ), 2 ≤ P.card →
    (∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) →
    cH * Real.sqrt (Real.log P.card) ≤ ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |(((P.filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card : ℝ) - P.card * u * v)|

/-- `L¹` short-arc regularity from the one-sided bound `n M_n - r ≤ A` (the paper's Lemmas
6.1–6.3 and Proposition 6.4). -/
def H2 : Prop :=
  ∃ C₂ C₃ : ℝ, ∀ (r : ℕ) (A : ℝ), 1 ≤ A → C₂ * A ≤ r →
    ∀ a : ℕ → ℝ, Function.Injective (fun k ↦ Int.fract (a k)) →
    (∀ᶠ n : ℕ in atTop, (n : ℝ) * maxSpan a n r ≤ r + A) →
    ∀ᶠ n : ℕ in atTop, ∀ D : ℝ, 0 ≤ D → D ≤ Real.sqrt (A * r) / Real.log (r / A) ^ 2 →
      ∫ x in (0 : ℝ)..1, |(((Finset.range n).filter fun j => 0 < Int.fract (a j - x) ∧ Int.fract (a j - x) ≤ D / n).card : ℝ) - D| ≤ C₃ * A

/-- From `L¹` short-arc regularity to a planar point set with small `L¹` discrepancy (the paper's
Lemma 7.2, before Halász's theorem is applied). -/
def H3 : Prop :=
  ∀ a : ℕ → ℝ, Function.Injective (fun k ↦ Int.fract (a k)) → ∀ B S : ℝ, 1 ≤ B → 8 ≤ S →
    4 * B ≤ ⌊S⌋₊ →
    (∀ᶠ n : ℕ in atTop, ∀ D : ℝ, 0 ≤ D → D ≤ S →
      ∫ x in (0 : ℝ)..1, |(((Finset.range n).filter fun j => 0 < Int.fract (a j - x) ∧ Int.fract (a j - x) ≤ D / n).card : ℝ) - D| ≤ B) →
    ∃ P : Finset (ℝ × ℝ), (∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) ∧
      (⌊S⌋₊ : ℝ) / 2 ≤ P.card ∧
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |(((P.filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card : ℝ) - P.card * u * v)| ≤ 3 * B

lemma log_le_two_sqrt {y : ℝ} (hy : 0 ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h := Real.log_le_rpow_div hy (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  linarith

set_option maxHeartbeats 2000000 in
/-- All the size conditions of Section 8 hold for large `r`. -/
lemma eventually_conditions (c C₂ B₀ : ℝ) (hc : 0 < c) (hB₀ : 0 ≤ B₀) :
    ∀ᶠ r : ℕ in atTop,
      let A : ℝ := c * Real.sqrt (Real.log r)
      let S : ℝ := Real.sqrt (A * r) / Real.log (r / A) ^ 2
      1 ≤ A ∧ C₂ * A ≤ r ∧ 8 ≤ S ∧ 4 * (B₀ * A) ≤ ⌊S⌋₊ ∧
        Real.log r / 3 ≤ Real.log ((⌊S⌋₊ : ℝ) / 2) := by
  have hc0 := sq_nonneg (C₂ + 1)
  have t2 := sq_nonneg (1 / c)
  have t3 := sq_nonneg ((c + 1) * (|C₂| + 1) * 4)
  have t4 := sq_nonneg (4 * (B₀ + 1) * (c + 1) + 8)
  have t5 := sq_nonneg (c + 1)
  obtain ⟨Y, hY1, hY2, hY3, hY4, hY5⟩ : ∃ Y : ℝ, 10 ^ 6 ≤ Y ∧ (1 / c) ^ 2 ≤ Y ∧
      ((c + 1) * (|C₂| + 1) * 4) ^ 2 ≤ Y ∧ (4 * (B₀ + 1) * (c + 1) + 8) ^ 2 ≤ Y ∧
      (c + 1) ^ 2 ≤ Y :=
    ⟨10 ^ 6 + (1 / c) ^ 2 + ((c + 1) * (|C₂| + 1) * 4) ^ 2 + (4 * (B₀ + 1) * (c + 1) + 8) ^ 2
      + (c + 1) ^ 2, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hlog : Tendsto (fun r : ℕ => Real.log (r : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop Y, eventually_gt_atTop 0] with r hr hr0
  intro A S
  set y := Real.log (r : ℝ) with hy
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
  have hy0 : 0 ≤ y := by linarith
  have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
  have hsy : 1000 ≤ Real.sqrt y := by
    rw [show (1000 : ℝ) = Real.sqrt (1000 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  -- A ≥ 1
  have hcs : 1 / c ≤ Real.sqrt y := by
    rw [show 1 / c = Real.sqrt ((1 / c) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (hY2.trans hr)
  have hA : 1 ≤ A := by
    simp only [A]
    have := mul_le_mul_of_nonneg_left hcs hc.le
    rwa [mul_one_div_cancel hc.ne'] at this
  have hApos : 0 < A := by linarith
  -- A ≤ (c+1) √y and √y ≤ y
  have hAle : A ≤ (c + 1) * Real.sqrt y := by simp only [A]; nlinarith
  have hsyy : Real.sqrt y ≤ y := by nlinarith
  -- log A ≤ log y
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlogA : Real.log A ≤ 2 * Real.sqrt y := by
    have h1 : A ≤ (c + 1) * Real.sqrt y := hAle
    have h2 : Real.log A ≤ Real.log ((c + 1) * Real.sqrt y) := Real.log_le_log hApos h1
    have h3 : Real.log ((c + 1) * Real.sqrt y) ≤ 2 * Real.sqrt ((c + 1) * Real.sqrt y) :=
      log_le_two_sqrt (by positivity)
    have h4 : (c + 1) * Real.sqrt y ≤ y / (c + 1) ^ 2 * (c + 1) ^ 2 := by
      rw [div_mul_cancel₀ _ (by positivity)]
      have : (c + 1) ≤ Real.sqrt y := by
        rw [show c + 1 = Real.sqrt ((c + 1) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
        exact Real.sqrt_le_sqrt (hY5.trans hr)
      nlinarith
    have h5 : Real.sqrt ((c + 1) * Real.sqrt y) ≤ Real.sqrt y := Real.sqrt_le_sqrt (by
      rw [div_mul_cancel₀ _ (by positivity)] at h4; exact h4)
    linarith
  -- Λ = y - log A ∈ [y/2, y]
  have hΛ : Real.log (r / A) = y - Real.log A := by rw [Real.log_div hrpos.ne' hApos.ne']
  have hΛlo : y / 2 ≤ Real.log (r / A) := by rw [hΛ]; nlinarith
  have hΛhi : Real.log (r / A) ≤ y := by rw [hΛ]; linarith
  have hΛpos : 0 < Real.log (r / A) := by linarith
  have hAr : 0 < A * r := by positivity
  have hSpos : 0 < S := by simp only [S]; positivity
  -- log S ≥ y/2 - 4 √y
  have hlogS : y / 2 - 4 * Real.sqrt y ≤ Real.log S := by
    have e1 : Real.log S = Real.log (A * r) / 2 - 2 * Real.log (Real.log (r / A)) := by
      simp only [S]
      rw [Real.log_div (Real.sqrt_pos.mpr hAr).ne' (by positivity), Real.log_sqrt hAr.le,
        Real.log_pow]
      push_cast; ring
    have e2 : Real.log (A * r) = Real.log A + y := by rw [Real.log_mul hApos.ne' hrpos.ne']
    have e3 : Real.log (Real.log (r / A)) ≤ Real.log y := Real.log_le_log hΛpos hΛhi
    have e4 := log_le_two_sqrt hy0
    rw [e1, e2]; nlinarith
  -- S ≥ exp(...) is huge
  have hbig : y / 3 + 2 ≤ Real.log S := by nlinarith
  have hSge : Real.exp (y / 3 + 2) ≤ S := by
    have := Real.exp_le_exp.mpr hbig; rwa [Real.exp_log hSpos] at this
  have hexp1 : y / 3 + 3 ≤ Real.exp (y / 3 + 2) := by
    have := Real.add_one_le_exp (y / 3 + 2); linarith
  have hexp2 : 1 + (y / 3 + 2) + (y / 3 + 2) ^ 2 / 2 ≤ Real.exp (y / 3 + 2) :=
    Real.quadratic_le_exp_of_nonneg (by positivity)
  have hSy : y + 9 ≤ S := by nlinarith
  have hS8 : 8 ≤ S := by nlinarith
  have hflS : S - 1 ≤ (⌊S⌋₊ : ℝ) := by have := Nat.lt_floor_add_one S; linarith
  refine ⟨hA, ?_, hS8, ?_, ?_⟩
  · -- C₂ A ≤ r
    have h1 : y ≤ 2 * Real.sqrt (r : ℝ) := log_le_two_sqrt hrpos.le
    have h2 : Real.sqrt (r : ℝ) ^ 2 = r := Real.sq_sqrt hrpos.le
    have hsr : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
    have h3 : (c + 1) * (|C₂| + 1) * 4 ≤ Real.sqrt y := by
      rw [show (c + 1) * (|C₂| + 1) * 4 = Real.sqrt (((c + 1) * (|C₂| + 1) * 4) ^ 2) by
        rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (hY3.trans hr)
    have hC2abs : C₂ ≤ |C₂| := le_abs_self C₂
    rcases le_or_gt C₂ 0 with h | h
    · nlinarith
    · have hA2 : A ≤ (c + 1) * Real.sqrt y := hAle
      nlinarith [mul_le_mul_of_nonneg_left hA2 h.le, mul_nonneg hs0 hsr]
  · -- 4 B₀ A ≤ ⌊S⌋
    have h1 : 4 * (B₀ * A) ≤ 4 * (B₀ + 1) * (c + 1) * Real.sqrt y := by nlinarith
    have h2 : 4 * (B₀ + 1) * (c + 1) * Real.sqrt y + 8 ≤ y := by
      have : 4 * (B₀ + 1) * (c + 1) + 8 ≤ Real.sqrt y := by
        rw [show 4 * (B₀ + 1) * (c + 1) + 8 = Real.sqrt ((4 * (B₀ + 1) * (c + 1) + 8) ^ 2) by
          rw [Real.sqrt_sq (by positivity)]]
        exact Real.sqrt_le_sqrt (hY4.trans hr)
      nlinarith
    linarith
  · -- log(⌊S⌋/2) ≥ y/3
    have h1 : S / 4 ≤ (⌊S⌋₊ : ℝ) / 2 := by linarith
    have h2 : Real.log (S / 4) ≤ Real.log ((⌊S⌋₊ : ℝ) / 2) := Real.log_le_log (by positivity) h1
    have h3 : Real.log (S / 4) = Real.log S - Real.log 4 := Real.log_div hSpos.ne' (by norm_num)
    have h4 : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    linarith

theorem main : H1 → H2 → H3 → type_of% @Erdos1221.erdos_1221.parts.i := by
  rintro ⟨cH, hcH, hH1⟩ ⟨C₂, C₃, h2⟩ h3 K
  set B₀ : ℝ := |C₃| + 1 with hB₀
  have hB₀pos : 0 < B₀ := by positivity
  set c : ℝ := cH / (6 * B₀) with hc
  have hcpos : 0 < c := by positivity
  have hlog : Tendsto (fun r : ℕ => Real.log (r : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hK : ∀ᶠ r : ℕ in atTop, (K / c) ^ 2 + 1 ≤ Real.log r := hlog.eventually_ge_atTop _
  filter_upwards [eventually_conditions c C₂ B₀ hcpos hB₀pos.le, hK, eventually_gt_atTop 0]
    with r hc8 hKr hr0
  dsimp only at hc8
  obtain ⟨hA, hC2, hS8, hBS, hlogM⟩ := hc8
  set y := Real.log (r : ℝ) with hy
  set A : ℝ := c * Real.sqrt y with hAdef
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
  have hy0 : 0 ≤ y := by nlinarith [sq_nonneg (K / c)]
  -- every admissible sequence has limsup n M_n ≥ r + A
  have key : ∀ a : ℕ → ℝ, Function.Injective (fun k ↦ Int.fract (a k)) →
      ENNReal.ofReal (r + A) ≤
        limsup (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * maxSpan a n r)) atTop := by
    intro a ha
    by_contra hlt
    push Not at hlt
    have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) * maxSpan a n r ≤ r + A :=
      (eventually_lt_of_limsup_lt hlt).mono fun n h =>
        ((ENNReal.ofReal_lt_ofReal_iff'.mp h).1).le
    have hreg := h2 r A hA hC2 a ha hev
    have hreg' : ∀ᶠ n : ℕ in atTop, ∀ D : ℝ, 0 ≤ D →
        D ≤ Real.sqrt (A * r) / Real.log (r / A) ^ 2 →
        ∫ x in (0 : ℝ)..1, |(((Finset.range n).filter fun j => 0 < Int.fract (a j - x) ∧ Int.fract (a j - x) ≤ D / n).card : ℝ) - D| ≤ B₀ * A :=
      hreg.mono fun n hn D hD0 hDS => (hn D hD0 hDS).trans
        (mul_le_mul_of_nonneg_right (by simp only [hB₀]; linarith [le_abs_self C₃]) (by linarith))
    have hB1 : 1 ≤ B₀ := by rw [hB₀]; linarith [abs_nonneg C₃]
    have hB1A : 1 ≤ B₀ * A := by nlinarith
    have hfl4 : (4 : ℝ) ≤ (⌊Real.sqrt (A * r) / Real.log (r / A) ^ 2⌋₊ : ℝ) := by linarith
    obtain ⟨P, hP, hPcard, hPint⟩ := h3 a ha (B₀ * A) _ hB1A hS8 hBS hreg'
    have hS2 : (2 : ℝ) ≤ P.card := by linarith
    have hP2 : 2 ≤ P.card := by exact_mod_cast hS2
    have hH := hH1 P hP2 hP
    -- log |P| ≥ y/3
    have hlogP : y / 3 ≤ Real.log P.card := by
      have hpos : (0 : ℝ) < (⌊Real.sqrt (A * r) / Real.log (r / A) ^ 2⌋₊ : ℝ) / 2 := by linarith
      exact le_trans hlogM (Real.log_le_log hpos hPcard)
    have hsq3 : Real.sqrt (y / 3) ≤ Real.sqrt (Real.log P.card) := Real.sqrt_le_sqrt hlogP
    -- √(y/3) > √y / 2
    have hy3 : Real.sqrt y / 2 < Real.sqrt (y / 3) := by
      have hypos : 0 < y := by nlinarith [sq_nonneg (K / c)]
      have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hypos
      rw [show y / 3 = y * (1 / 3) by ring, Real.sqrt_mul hy0]
      have : (1 / 2 : ℝ) < Real.sqrt (1 / 3) := by
        rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      nlinarith
    -- contradiction: cH √(log |P|) ≤ 3 B₀ A = (cH/2) √y
    have h3B : 3 * (B₀ * A) = cH / 2 * Real.sqrt y := by
      simp only [hAdef, hc]; field_simp; ring
    nlinarith
  have hlam : ENNReal.ofReal (r + A) ≤ bigLambda r := le_iInf₂ fun a ha => key a ha
  refine lt_of_lt_of_le ?_ hlam
  rw [ENNReal.ofReal_lt_ofReal_iff (by
    have : 0 ≤ A := by positivity
    linarith)]
  -- K < A since √y > K / c
  have : K < A := by
    have h1 : (K / c) ^ 2 < y := by linarith
    have h2 : |K / c| < Real.sqrt y := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) h1
    have h3 : K / c < Real.sqrt y := lt_of_le_of_lt (le_abs_self _) h2
    have := mul_lt_mul_of_pos_left h3 hcpos
    rwa [mul_div_cancel₀ _ hcpos.ne'] at this
  linarith

end OMA.R_Erdos1221_erdos_1221_parts_i_R1


section StepH1

/-!
Proof of hypothesis `H1` of reduction R1 of `Erdos1221.erdos_1221.parts.i`: Halász's `L¹` lower
bound for planar discrepancy (Halász 1981; the paper's Theorem 7.1 in Korsky, arXiv:2609.07196),
with the explicit constant `c_H = 1/5120`.

Proof (Halász's complex Riesz product, run on a finite grid): take `n = ⌊log₂ N⌋ + 2`, so
`2N ≤ 2^n ≤ 4N`, and the grid of `2^(n+1) × 2^(n+1)` cells. The `L¹` norm dominates the sum of the
absolute cell integrals `d i j` of the discrepancy (`grid`). For each splitting `k` of `n` into the
two coordinates, the test function `f_k` is a sum of products of two Rademacher signs over the dyadic
blocks of that shape that contain no point, with sign chosen so that `⟨f_k, d⟩ ≥ N/(32·2^n)` (at
least half of the `2^n` blocks are empty) (`main_term`); for any test function constant on blocks
the pairing is at most `(5/4)·B·N·δx·δy` (`BD`, `KB'`). The Riesz product `Π_k (1 + i ρ f_k)` with
`ρ = 1/√(n+1)` has sup-norm at most `2`, and the imaginary part of its pairing with `d` is at least
`√(n+1)·N/(32·2^n) - (5/8)·N/2^n` (`riesz_expand`, `riesz_lower`). Hence `Σ|d| ≥ √(n+1)/5120`, and
`log N ≤ n + 1`.
-/

/-!
Halász's L¹ lower bound, part A: one-dimensional block sums, the block decomposition (BD)
and the key bound (KB). See `Halasz_blueprint.md`.
-/

open Finset

namespace Halasz

noncomputable def G (x y : ℝ) : ℝ := max (y - x) 0

noncomputable def hh (n : ℕ) : ℝ := 1 / 2 ^ (n + 1)

noncomputable def a (n i : ℕ) (x : ℝ) : ℝ := G x (((i : ℝ) + 1) * hh n) - G x ((i : ℝ) * hh n)

noncomputable def al (n i : ℕ) : ℝ := ((((i : ℝ) + 1) * hh n) ^ 2 - ((i : ℝ) * hh n) ^ 2) / 2

noncomputable def d (P : Finset (ℝ × ℝ)) (n i j : ℕ) : ℝ :=
  ∑ p ∈ P, a n i p.1 * a n j p.2 - (P.card : ℝ) * al n i * al n j

def blk (c i : ℕ) : ℕ := i / 2 ^ (c + 1)

noncomputable def rad (c i : ℕ) : ℝ := if (i / 2 ^ c) % 2 = 1 then 1 else -1

noncomputable def dl (n c : ℕ) : ℝ := 2 ^ c * hh n

noncomputable def Dl (x s δ : ℝ) : ℝ := G x (s + 2 * δ) - 2 * G x (s + δ) + G x s

noncomputable def K (P : Finset (ℝ × ℝ)) (n cx cy I J : ℕ) : ℝ :=
  ∑ p ∈ P, Dl p.1 (2 * I * dl n cx) (dl n cx) * Dl p.2 (2 * J * dl n cy) (dl n cy) -
    (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2

def Inv (cx cy : ℕ) (τ : ℕ → ℕ → ℂ) : Prop :=
  ∀ i i' j j', blk cx i = blk cx i' → blk cy j = blk cy j' → τ i j = τ i' j'

lemma rad_lo (c I t : ℕ) (ht : t < 2 ^ c) : rad c (I * 2 ^ (c + 1) + t) = -1 := by
  have hp : 0 < 2 ^ c := by positivity
  have e : (I * 2 ^ (c + 1) + t) / 2 ^ c = 2 * I := by
    rw [pow_succ, show I * (2 ^ c * 2) + t = t + (2 * I) * 2 ^ c by ring,
      Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ht, zero_add]
  unfold rad
  rw [e, Nat.mul_mod_right]
  simp

lemma rad_hi (c I t : ℕ) (ht : t < 2 ^ c) : rad c (I * 2 ^ (c + 1) + (2 ^ c + t)) = 1 := by
  have hp : 0 < 2 ^ c := by positivity
  have e : (I * 2 ^ (c + 1) + (2 ^ c + t)) / 2 ^ c = 2 * I + 1 := by
    rw [pow_succ, show I * (2 ^ c * 2) + (2 ^ c + t) = t + (2 * I + 1) * 2 ^ c by ring,
      Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ht, zero_add]
  unfold rad
  rw [e]
  simp [Nat.add_mod]

lemma T1 (F : ℝ → ℝ) (h : ℝ) (c I : ℕ) :
    ∑ t ∈ range (2 ^ (c + 1)), (F ((((I * 2 ^ (c + 1) + t : ℕ) : ℝ) + 1) * h) -
      F (((I * 2 ^ (c + 1) + t : ℕ) : ℝ) * h)) * rad c (I * 2 ^ (c + 1) + t) =
    F (((I * 2 ^ (c + 1) + 2 ^ c + 2 ^ c : ℕ) : ℝ) * h) -
      2 * F (((I * 2 ^ (c + 1) + 2 ^ c : ℕ) : ℝ) * h) + F (((I * 2 ^ (c + 1) : ℕ) : ℝ) * h) := by
  have e : range (2 ^ (c + 1)) = range (2 ^ c + 2 ^ c) := by rw [pow_succ, mul_two]
  rw [e, sum_range_add]
  have h1 : ∀ t ∈ range (2 ^ c), (F ((((I * 2 ^ (c + 1) + t : ℕ) : ℝ) + 1) * h) -
      F (((I * 2 ^ (c + 1) + t : ℕ) : ℝ) * h)) * rad c (I * 2 ^ (c + 1) + t) =
      -(F (((I * 2 ^ (c + 1) + (t + 1) : ℕ) : ℝ) * h) - F (((I * 2 ^ (c + 1) + t : ℕ) : ℝ) * h)) := by
    intro t ht
    rw [rad_lo c I t (mem_range.mp ht)]
    push_cast; ring_nf
  have h2 : ∀ t ∈ range (2 ^ c), (F ((((I * 2 ^ (c + 1) + (2 ^ c + t) : ℕ) : ℝ) + 1) * h) -
      F (((I * 2 ^ (c + 1) + (2 ^ c + t) : ℕ) : ℝ) * h)) * rad c (I * 2 ^ (c + 1) + (2 ^ c + t)) =
      (F (((I * 2 ^ (c + 1) + 2 ^ c + (t + 1) : ℕ) : ℝ) * h) -
        F (((I * 2 ^ (c + 1) + 2 ^ c + t : ℕ) : ℝ) * h)) := by
    intro t ht
    rw [rad_hi c I t (mem_range.mp ht)]
    push_cast; ring_nf
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_neg_distrib,
    sum_range_sub (fun t => F (((I * 2 ^ (c + 1) + t : ℕ) : ℝ) * h)),
    sum_range_sub (fun t => F (((I * 2 ^ (c + 1) + 2 ^ c + t : ℕ) : ℝ) * h))]
  simp only [add_zero]
  ring_nf

lemma cast_blk1 (n c I : ℕ) :
    ((I * 2 ^ (c + 1) + 2 ^ c + 2 ^ c : ℕ) : ℝ) * hh n = 2 * I * dl n c + 2 * dl n c := by
  unfold dl; push_cast; ring

lemma cast_blk2 (n c I : ℕ) :
    ((I * 2 ^ (c + 1) + 2 ^ c : ℕ) : ℝ) * hh n = 2 * I * dl n c + dl n c := by
  unfold dl; push_cast; ring

lemma cast_blk3 (n c I : ℕ) :
    ((I * 2 ^ (c + 1) : ℕ) : ℝ) * hh n = 2 * I * dl n c := by
  unfold dl; push_cast; ring

lemma blockA (n c I : ℕ) (x : ℝ) :
    ∑ t ∈ range (2 ^ (c + 1)), a n (I * 2 ^ (c + 1) + t) x * rad c (I * 2 ^ (c + 1) + t) =
      Dl x (2 * I * dl n c) (dl n c) := by
  unfold a
  rw [T1 (G x) (hh n) c I, cast_blk1, cast_blk2, cast_blk3]
  unfold Dl
  ring_nf

lemma blockAl (n c I : ℕ) :
    ∑ t ∈ range (2 ^ (c + 1)), al n (I * 2 ^ (c + 1) + t) * rad c (I * 2 ^ (c + 1) + t) =
      dl n c ^ 2 := by
  have e : ∀ t ∈ range (2 ^ (c + 1)), al n (I * 2 ^ (c + 1) + t) * rad c (I * 2 ^ (c + 1) + t) =
      ((fun y : ℝ => y ^ 2 / 2) ((((I * 2 ^ (c + 1) + t : ℕ) : ℝ) + 1) * hh n) -
        (fun y : ℝ => y ^ 2 / 2) (((I * 2 ^ (c + 1) + t : ℕ) : ℝ) * hh n)) *
        rad c (I * 2 ^ (c + 1) + t) := by
    intro t _
    unfold al
    ring
  rw [sum_congr rfl e, T1 (fun y : ℝ => y ^ 2 / 2) (hh n) c I, cast_blk1, cast_blk2, cast_blk3]
  ring

lemma D1 {x s δ : ℝ} (hx : x ≤ s) (hδ : 0 ≤ δ) : Dl x s δ = 0 := by
  unfold Dl G
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

lemma D2 {x s δ : ℝ} (hx : s + 2 * δ ≤ x) (hδ : 0 ≤ δ) : Dl x s δ = 0 := by
  unfold Dl G
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

lemma D3 (x s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : |Dl x s δ| ≤ δ := by
  rcases le_or_gt x s with h1 | h1
  · rw [D1 h1 hδ, abs_zero]; exact hδ
  rcases le_or_gt (s + 2 * δ) x with h2 | h2
  · rw [D2 h2 hδ, abs_zero]; exact hδ
  unfold Dl G
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ s + 2 * δ - x), max_eq_right (by linarith : s - x ≤ 0)]
  rcases le_total (s + δ - x) 0 with h3 | h3
  · rw [max_eq_right h3, abs_le]; constructor <;> linarith
  · rw [max_eq_left h3, abs_le]; constructor <;> linarith

lemma D4 (x : ℝ) {δ : ℝ} (hδ : 0 < δ) (A : ℕ) :
    ∑ I ∈ range A, |Dl x (2 * I * δ) δ| ≤ δ := by
  set S := (range A).filter (fun I : ℕ => 2 * I * δ < x ∧ x < 2 * I * δ + 2 * δ) with hS
  have hpt : ∀ I ∈ range A, |Dl x (2 * I * δ) δ| ≤
      if (2 * I * δ < x ∧ x < 2 * I * δ + 2 * δ) then δ else 0 := by
    intro I _
    split_ifs with hc
    · exact D3 _ _ hδ.le
    · rw [not_and_or, not_lt, not_lt] at hc
      rcases hc with hc | hc
      · rw [D1 hc hδ.le, abs_zero]
      · rw [D2 hc hδ.le, abs_zero]
  refine (sum_le_sum hpt).trans ?_
  rw [← sum_filter, sum_const, ← hS, nsmul_eq_mul]
  have hc : S.card ≤ 1 := by
    rw [card_le_one]
    intro I hI J hJ
    rw [hS, mem_filter] at hI hJ
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : (I : ℝ) + 1 ≤ J := by exact_mod_cast h
      nlinarith [hI.2.2, hJ.2.1]
    · have : (J : ℝ) + 1 ≤ I := by exact_mod_cast h
      nlinarith [hI.2.1, hJ.2.2]
  have : (S.card : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith

lemma sum_blocks {M : Type*} [AddCommMonoid M] (A ℓ : ℕ) (F : ℕ → M) :
    ∑ i ∈ range (A * ℓ), F i = ∑ I ∈ range A, ∑ t ∈ range ℓ, F (I * ℓ + t) := by
  induction A with
  | zero => simp
  | succ A ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

lemma blk_eq (c I t : ℕ) (ht : t < 2 ^ (c + 1)) : blk c (I * 2 ^ (c + 1) + t) = I := by
  unfold blk
  have hp : 0 < 2 ^ (c + 1) := by positivity
  rw [add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ht, zero_add]

lemma blockK (P : Finset (ℝ × ℝ)) (n cx cy I J : ℕ) :
    ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)),
      d P n (I * 2 ^ (cx + 1) + t) (J * 2 ^ (cy + 1) + u) * rad cx (I * 2 ^ (cx + 1) + t) *
        rad cy (J * 2 ^ (cy + 1) + u) = K P n cx cy I J := by
  have lhs : ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)),
      d P n (I * 2 ^ (cx + 1) + t) (J * 2 ^ (cy + 1) + u) * rad cx (I * 2 ^ (cx + 1) + t) *
        rad cy (J * 2 ^ (cy + 1) + u) =
      ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)), ∑ p ∈ P,
        (a n (I * 2 ^ (cx + 1) + t) p.1 * rad cx (I * 2 ^ (cx + 1) + t)) *
        (a n (J * 2 ^ (cy + 1) + u) p.2 * rad cy (J * 2 ^ (cy + 1) + u)) -
      (P.card : ℝ) * ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)),
        (al n (I * 2 ^ (cx + 1) + t) * rad cx (I * 2 ^ (cx + 1) + t)) *
        (al n (J * 2 ^ (cy + 1) + u) * rad cy (J * 2 ^ (cy + 1) + u)) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun u _ => ?_
    unfold d
    rw [sub_mul, sub_mul, sum_mul, sum_mul]
    congr 1
    · refine sum_congr rfl fun p _ => ?_
      ring
    · ring
  have rhs : K P n cx cy I J =
      ∑ p ∈ P, ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)),
        (a n (I * 2 ^ (cx + 1) + t) p.1 * rad cx (I * 2 ^ (cx + 1) + t)) *
        (a n (J * 2 ^ (cy + 1) + u) p.2 * rad cy (J * 2 ^ (cy + 1) + u)) -
      (P.card : ℝ) * ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)),
        (al n (I * 2 ^ (cx + 1) + t) * rad cx (I * 2 ^ (cx + 1) + t)) *
        (al n (J * 2 ^ (cy + 1) + u) * rad cy (J * 2 ^ (cy + 1) + u)) := by
    unfold K
    rw [← sum_mul_sum, blockAl, blockAl]
    congr 1
    · refine sum_congr rfl fun p _ => ?_
      rw [← sum_mul_sum, blockA, blockA]
    · ring
  rw [lhs, rhs]
  congr 1
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_comm]

lemma range_split (n c : ℕ) (hc : c ≤ n) :
    range (2 ^ (n + 1)) = range (2 ^ (n - c) * 2 ^ (c + 1)) := by
  rw [← pow_add, show n - c + (c + 1) = n + 1 by omega]

lemma BD (P : Finset (ℝ × ℝ)) (n cx cy : ℕ) (hcx : cx ≤ n) (hcy : cy ≤ n) (τ : ℕ → ℕ → ℂ)
    (hτ : Inv cx cy τ) :
    ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)),
      (d P n i j : ℂ) * τ i j * (rad cx i : ℂ) * (rad cy j : ℂ) =
    ∑ I ∈ range (2 ^ (n - cx)), ∑ J ∈ range (2 ^ (n - cy)),
      τ (I * 2 ^ (cx + 1)) (J * 2 ^ (cy + 1)) * (K P n cx cy I J : ℂ) := by
  have e1 : ∀ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)),
      (d P n i j : ℂ) * τ i j * (rad cx i : ℂ) * (rad cy j : ℂ) =
      ∑ J ∈ range (2 ^ (n - cy)), ∑ u ∈ range (2 ^ (cy + 1)),
      (d P n i (J * 2 ^ (cy + 1) + u) : ℂ) * τ i (J * 2 ^ (cy + 1) + u) * (rad cx i : ℂ) *
        (rad cy (J * 2 ^ (cy + 1) + u) : ℂ) := by
    intro i _
    rw [range_split n cy hcy, sum_blocks]
  rw [sum_congr rfl e1, range_split n cx hcx, sum_blocks]
  refine sum_congr rfl fun I _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun J _ => ?_
  rw [← blockK P n cx cy I J]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun t ht => ?_
  rw [mul_sum]
  refine sum_congr rfl fun u hu => ?_
  have hp1 : 0 < 2 ^ (cx + 1) := by positivity
  have hp2 : 0 < 2 ^ (cy + 1) := by positivity
  have : τ (I * 2 ^ (cx + 1) + t) (J * 2 ^ (cy + 1) + u) =
      τ (I * 2 ^ (cx + 1)) (J * 2 ^ (cy + 1)) := by
    apply hτ
    · rw [blk_eq _ _ _ (mem_range.mp ht), ← add_zero (I * 2 ^ (cx + 1)), blk_eq _ _ _ hp1]
    · rw [blk_eq _ _ _ (mem_range.mp hu), ← add_zero (J * 2 ^ (cy + 1)), blk_eq _ _ _ hp2]
  rw [this]
  ring

/-! ## Part B: the key bound and the main term -/

lemma idx_lt (n c I : ℕ) (hc : c ≤ n) (hI : I < 2 ^ (n - c)) : I * 2 ^ (c + 1) < 2 ^ (n + 1) := by
  have h1 : I * 2 ^ (c + 1) < 2 ^ (n - c) * 2 ^ (c + 1) :=
    Nat.mul_lt_mul_of_pos_right hI (by positivity)
  rwa [← pow_add, show n - c + (c + 1) = n + 1 by omega] at h1

lemma dl_pos (n c : ℕ) : 0 < dl n c := by unfold dl hh; positivity

lemma abs_K (P : Finset (ℝ × ℝ)) (n cx cy I J : ℕ) :
    |K P n cx cy I J| ≤ ∑ p ∈ P, |Dl p.1 (2 * I * dl n cx) (dl n cx)| *
      |Dl p.2 (2 * J * dl n cy) (dl n cy)| + (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2 := by
  unfold K
  refine (abs_sub _ _).trans (add_le_add ?_ (le_of_eq ?_))
  · refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine sum_congr rfl fun p _ => abs_mul _ _
  · rw [abs_of_nonneg (by positivity)]

lemma KB (P : Finset (ℝ × ℝ)) (n cx cy : ℕ) (hcx : cx ≤ n) (hcy : cy ≤ n) (τ : ℕ → ℕ → ℂ)
    (hτ : Inv cx cy τ) (B : ℝ)
    (hB : ∀ i < 2 ^ (n + 1), ∀ j < 2 ^ (n + 1), ‖τ i j‖ ≤ B) :
    ‖∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)),
      (d P n i j : ℂ) * τ i j * (rad cx i : ℂ) * (rad cy j : ℂ)‖ ≤
    B * ((P.card : ℝ) * dl n cx * dl n cy +
      (2 ^ (n - cx) : ℝ) * 2 ^ (n - cy) * (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2) := by
  rw [BD P n cx cy hcx hcy τ hτ]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by positivity) 0 (by positivity))
  have hx := dl_pos n cx
  have hy := dl_pos n cy
  calc ‖∑ I ∈ range (2 ^ (n - cx)), ∑ J ∈ range (2 ^ (n - cy)),
        τ (I * 2 ^ (cx + 1)) (J * 2 ^ (cy + 1)) * (K P n cx cy I J : ℂ)‖
      ≤ ∑ I ∈ range (2 ^ (n - cx)), ∑ J ∈ range (2 ^ (n - cy)),
        ‖τ (I * 2 ^ (cx + 1)) (J * 2 ^ (cy + 1)) * (K P n cx cy I J : ℂ)‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun I _ => norm_sum_le _ _)
    _ ≤ ∑ I ∈ range (2 ^ (n - cx)), ∑ J ∈ range (2 ^ (n - cy)),
        B * (∑ p ∈ P, |Dl p.1 (2 * I * dl n cx) (dl n cx)| *
          |Dl p.2 (2 * J * dl n cy) (dl n cy)| + (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2) := by
        refine sum_le_sum fun I hI => sum_le_sum fun J hJ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hB _ (idx_lt n cx I hcx (mem_range.mp hI)) _
          (idx_lt n cy J hcy (mem_range.mp hJ))) (abs_K P n cx cy I J) (abs_nonneg _) hB0
    _ = B * (∑ p ∈ P, (∑ I ∈ range (2 ^ (n - cx)), |Dl p.1 (2 * I * dl n cx) (dl n cx)|) *
          (∑ J ∈ range (2 ^ (n - cy)), |Dl p.2 (2 * J * dl n cy) (dl n cy)|) +
          (2 ^ (n - cx) : ℝ) * 2 ^ (n - cy) * (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2) := by
        have hpt : ∑ p ∈ P, (∑ I ∈ range (2 ^ (n - cx)), |Dl p.1 (2 * I * dl n cx) (dl n cx)|) *
            (∑ J ∈ range (2 ^ (n - cy)), |Dl p.2 (2 * J * dl n cy) (dl n cy)|) =
            ∑ I ∈ range (2 ^ (n - cx)), ∑ J ∈ range (2 ^ (n - cy)), ∑ p ∈ P,
              |Dl p.1 (2 * I * dl n cx) (dl n cx)| * |Dl p.2 (2 * J * dl n cy) (dl n cy)| := by
          simp_rw [sum_mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun I _ => ?_
          rw [sum_comm]
        rw [hpt]
        simp only [mul_add, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ B * (∑ p ∈ P, dl n cx * dl n cy +
          (2 ^ (n - cx) : ℝ) * 2 ^ (n - cy) * (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2) := by
        have hpt2 : ∑ p ∈ P, (∑ I ∈ range (2 ^ (n - cx)), |Dl p.1 (2 * I * dl n cx) (dl n cx)|) *
            (∑ J ∈ range (2 ^ (n - cy)), |Dl p.2 (2 * J * dl n cy) (dl n cy)|) ≤
            ∑ p ∈ P, dl n cx * dl n cy :=
          sum_le_sum fun p _ => mul_le_mul (D4 _ hx _) (D4 _ hy _)
            (sum_nonneg fun _ _ => abs_nonneg _) hx.le
        exact mul_le_mul_of_nonneg_left (add_le_add hpt2 le_rfl) hB0
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

lemma pow_dl (n c : ℕ) (hc : c ≤ n) : (2 : ℝ) ^ (n - c) * dl n c = 1 / 2 := by
  unfold dl hh
  rw [← mul_assoc, ← pow_add, show n - c + c = n by omega, pow_succ]
  field_simp

lemma KB' (P : Finset (ℝ × ℝ)) (n cx cy : ℕ) (hcx : cx ≤ n) (hcy : cy ≤ n) (τ : ℕ → ℕ → ℂ)
    (hτ : Inv cx cy τ) (B : ℝ)
    (hB : ∀ i < 2 ^ (n + 1), ∀ j < 2 ^ (n + 1), ‖τ i j‖ ≤ B) :
    ‖∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)),
      (d P n i j : ℂ) * τ i j * (rad cx i : ℂ) * (rad cy j : ℂ)‖ ≤
    B * (5 / 4) * (P.card : ℝ) * dl n cx * dl n cy := by
  refine (KB P n cx cy hcx hcy τ hτ B hB).trans (le_of_eq ?_)
  have e : (2 ^ (n - cx) : ℝ) * 2 ^ (n - cy) * (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2 =
      ((2 : ℝ) ^ (n - cx) * dl n cx) * ((2 : ℝ) ^ (n - cy) * dl n cy) * (P.card : ℝ) *
        dl n cx * dl n cy := by ring
  rw [e, pow_dl n cx hcx, pow_dl n cy hcy]
  ring

/-- The block `(I, J)` of shape `2^{-k} × 2^{-(n-k)}` contains a point of `P` in its interior. -/
def occ (P : Finset (ℝ × ℝ)) (n k I J : ℕ) : Prop :=
  ∃ p ∈ P, 2 * I * dl n (n - k) < p.1 ∧ p.1 < 2 * I * dl n (n - k) + 2 * dl n (n - k) ∧
    2 * J * dl n k < p.2 ∧ p.2 < 2 * J * dl n k + 2 * dl n k

open Classical in
noncomputable def sig (P : Finset (ℝ × ℝ)) (n k I J : ℕ) : ℂ := if occ P n k I J then 0 else -1

noncomputable def f (P : Finset (ℝ × ℝ)) (n k i j : ℕ) : ℂ :=
  sig P n k (blk (n - k) i) (blk k j) * (rad (n - k) i : ℂ) * (rad k j : ℂ)

lemma K_unocc (P : Finset (ℝ × ℝ)) (n k I J : ℕ) (h : ¬ occ P n k I J) :
    K P n (n - k) k I J = -((P.card : ℝ) * dl n (n - k) ^ 2 * dl n k ^ 2) := by
  unfold K
  have hx := (dl_pos n (n - k)).le
  have hy := (dl_pos n k).le
  rw [sum_eq_zero, zero_sub]
  intro p hp
  unfold occ at h
  push Not at h
  have h' := h p hp
  by_cases h1 : 2 * I * dl n (n - k) < p.1
  · by_cases h2 : p.1 < 2 * I * dl n (n - k) + 2 * dl n (n - k)
    · by_cases h3 : 2 * J * dl n k < p.2
      · have h4 := h' h1 h2 h3
        rw [D2 h4 hy, mul_zero]
      · rw [D1 (not_lt.mp h3) hy, mul_zero]
    · rw [D2 (not_lt.mp h2) hx, zero_mul]
  · rw [D1 (not_lt.mp h1) hx, zero_mul]

open Classical in
lemma card_occ (P : Finset (ℝ × ℝ)) (n k : ℕ) :
    ((range (2 ^ (n - (n - k))) ×ˢ range (2 ^ (n - k))).filter
      (fun x => occ P n k x.1 x.2)).card ≤ P.card := by
  have hx := dl_pos n (n - k)
  have hy := dl_pos n k
  refine (card_le_card ?_).trans (card_image_le (s := P)
    (f := fun p => (⌊p.1 / (2 * dl n (n - k))⌋₊, ⌊p.2 / (2 * dl n k)⌋₊)))
  intro x hx'
  rw [mem_filter] at hx'
  obtain ⟨p, hp, h1, h2, h3, h4⟩ := hx'.2
  rw [mem_image]
  refine ⟨p, hp, ?_⟩
  have e1 : ⌊p.1 / (2 * dl n (n - k))⌋₊ = x.1 := by
    rw [Nat.floor_eq_iff (by
      have : 0 ≤ 2 * (x.1 : ℝ) * dl n (n - k) := by positivity
      exact div_nonneg (by linarith) (by positivity))]
    rw [le_div_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
    constructor <;> nlinarith
  have e2 : ⌊p.2 / (2 * dl n k)⌋₊ = x.2 := by
    rw [Nat.floor_eq_iff (by
      have : 0 ≤ 2 * (x.2 : ℝ) * dl n k := by positivity
      exact div_nonneg (by linarith) (by positivity))]
    rw [le_div_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
    constructor <;> nlinarith
  simp only [e1, e2]

lemma dl_prod (n k : ℕ) (hk : k ≤ n) :
    dl n (n - k) * dl n k = 1 / (4 * 2 ^ n) := by
  unfold dl hh
  have e : (2 : ℝ) ^ (n - k) * (1 / 2 ^ (n + 1)) * (2 ^ k * (1 / 2 ^ (n + 1))) =
      2 ^ (n - k + k) / (2 ^ (n + 1)) ^ 2 := by rw [pow_add]; ring
  rw [e, show n - k + k = n by omega, pow_succ]
  field_simp
  ring

lemma inv_f (P : Finset (ℝ × ℝ)) (n k : ℕ) :
    Inv (n - k) k (fun i j => sig P n k (blk (n - k) i) (blk k j)) := by
  intro i i' j j' h1 h2
  simp only [h1, h2]

open Classical in
lemma main_term (P : Finset (ℝ × ℝ)) (n k : ℕ) (hk : k ≤ n)
    (hN : 2 * (P.card : ℝ) ≤ 2 ^ n) :
    (P.card : ℝ) / (32 * 2 ^ n) ≤
      (∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), (d P n i j : ℂ) * f P n k i j).re := by
  have e0 : ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), (d P n i j : ℂ) * f P n k i j =
      ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), (d P n i j : ℂ) *
        (fun i j => sig P n k (blk (n - k) i) (blk k j)) i j *
        (rad (n - k) i : ℂ) * (rad k j : ℂ) := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    unfold f; ring
  rw [e0, BD P n (n - k) k (Nat.sub_le n k) hk _ (inv_f P n k)]
  have hb1 : ∀ I : ℕ, blk (n - k) (I * 2 ^ (n - k + 1)) = I := fun I => by
    rw [← add_zero (I * 2 ^ (n - k + 1))]; exact blk_eq _ _ _ (by positivity)
  have hb2 : ∀ J : ℕ, blk k (J * 2 ^ (k + 1)) = J := fun J => by
    rw [← add_zero (J * 2 ^ (k + 1))]; exact blk_eq _ _ _ (by positivity)
  simp only [hb1, hb2]
  set c0 : ℝ := (P.card : ℝ) * dl n (n - k) ^ 2 * dl n k ^ 2 with hc0
  have e1 : ∀ I J : ℕ, (sig P n k I J * (K P n (n - k) k I J : ℂ)).re =
      if occ P n k I J then 0 else c0 := by
    intro I J
    unfold sig
    split_ifs with h
    · simp
    · rw [K_unocc P n k I J h, ← hc0]; simp
  simp only [Complex.re_sum, e1]
  rw [← sum_product' (f := fun I J => if occ P n k I J then (0 : ℝ) else c0), sum_ite,
    sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
  have hcard := card_filter_add_card_filter_not (s := range (2 ^ (n - (n - k))) ×ˢ
    range (2 ^ (n - k))) (fun x => occ P n k x.1 x.2)
  rw [card_product, card_range, card_range, ← pow_add,
    show n - (n - k) + (n - k) = n by omega] at hcard
  have hocc := card_occ P n k
  have hun : (2 : ℝ) ^ n - P.card ≤
      (((range (2 ^ (n - (n - k))) ×ˢ range (2 ^ (n - k))).filter
        (fun x => ¬ occ P n k x.1 x.2)).card : ℝ) := by
    have : (2 ^ n : ℕ) ≤ P.card + ((range (2 ^ (n - (n - k))) ×ˢ range (2 ^ (n - k))).filter
        (fun x => ¬ occ P n k x.1 x.2)).card := by omega
    have : ((2 ^ n : ℕ) : ℝ) ≤ P.card + (((range (2 ^ (n - (n - k))) ×ˢ range (2 ^ (n - k))).filter
        (fun x => ¬ occ P n k x.1 x.2)).card : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hc0' : c0 = (P.card : ℝ) * (1 / (4 * 2 ^ n)) ^ 2 := by
    rw [hc0, ← dl_prod n k hk]; ring
  have hX : (0 : ℝ) < 2 ^ n := by positivity
  have hN0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  calc (P.card : ℝ) / (32 * 2 ^ n) = (2 ^ n / 2) * ((P.card : ℝ) * (1 / (4 * 2 ^ n)) ^ 2) := by
        field_simp; ring
    _ ≤ (2 ^ n - P.card) * ((P.card : ℝ) * (1 / (4 * 2 ^ n)) ^ 2) := by
        gcongr; linarith
    _ ≤ _ := by rw [← hc0']; exact mul_le_mul_of_nonneg_right hun (by rw [hc0']; positivity)

/-! ## Part C: the Riesz product -/

open Classical in
noncomputable def fR (P : Finset (ℝ × ℝ)) (n k i j : ℕ) : ℝ :=
  (if occ P n k (blk (n - k) i) (blk k j) then 0 else -1) * rad (n - k) i * rad k j

lemma f_eq (P : Finset (ℝ × ℝ)) (n k i j : ℕ) : f P n k i j = (fR P n k i j : ℂ) := by
  unfold f sig fR
  split_ifs <;> push_cast <;> ring

lemma abs_rad (c i : ℕ) : |rad c i| = 1 := by
  unfold rad; split_ifs <;> simp

lemma norm_rad (c i : ℕ) : ‖(rad c i : ℂ)‖ = 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_rad]

lemma norm_sig (P : Finset (ℝ × ℝ)) (n k I J : ℕ) : ‖sig P n k I J‖ ≤ 1 := by
  unfold sig; split_ifs <;> simp

lemma abs_fR (P : Finset (ℝ × ℝ)) (n k i j : ℕ) : |fR P n k i j| ≤ 1 := by
  unfold fR
  rw [abs_mul, abs_mul, abs_rad, abs_rad]
  split_ifs <;> simp

noncomputable def R1 (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (k i j : ℕ) : ℂ :=
  1 + Complex.I * ((ρ : ℂ) * f P n k i j)

noncomputable def Pr (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (s m i j : ℕ) : ℂ :=
  ∏ k ∈ Ico s m, R1 P n ρ k i j

lemma norm_R1 (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (k i j : ℕ) :
    ‖R1 P n ρ k i j‖ ≤ 1 + ρ ^ 2 / 2 := by
  unfold R1
  rw [f_eq]
  have ht := abs_fR P n k i j
  set t := fR P n k i j
  have h2 : ‖(1 : ℂ) + Complex.I * ((ρ : ℂ) * (t : ℂ))‖ ^ 2 = 1 + (ρ * t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have ht2 : t ^ 2 ≤ 1 := by
    have := sq_abs t
    nlinarith [abs_nonneg t]
  have h3 : (ρ * t) ^ 2 ≤ ρ ^ 2 := by rw [mul_pow]; nlinarith [sq_nonneg ρ]
  nlinarith [norm_nonneg ((1 : ℂ) + Complex.I * ((ρ : ℂ) * (t : ℂ))), sq_nonneg ρ]

lemma pow_bound (ρ : ℝ) (n : ℕ) (h : ρ ^ 2 * (n + 1) ≤ 1) : (1 + ρ ^ 2 / 2) ^ (n + 1) ≤ 2 := by
  have h1 : 1 + ρ ^ 2 / 2 ≤ Real.exp (ρ ^ 2 / 2) := by linarith [Real.add_one_le_exp (ρ ^ 2 / 2)]
  have h2 := pow_le_pow_left₀ (by positivity) h1 (n + 1)
  rw [← Real.exp_nat_mul] at h2
  have h3 : Real.exp (((n + 1 : ℕ) : ℝ) * (ρ ^ 2 / 2)) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.mpr (by push_cast; nlinarith)
  have h4 : Real.exp (1 / 2) < 2 := by
    have := Real.exp_one_lt_d9
    have e : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  linarith

lemma norm_Pr (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (hρ : ρ ^ 2 * (n + 1) ≤ 1) (s m i j : ℕ)
    (hm : m ≤ n + 1) : ‖Pr P n ρ s m i j‖ ≤ 2 := by
  unfold Pr
  calc ‖∏ k ∈ Ico s m, R1 P n ρ k i j‖ ≤ ∏ k ∈ Ico s m, ‖R1 P n ρ k i j‖ :=
        Finset.norm_prod_le _ _
    _ ≤ ∏ k ∈ Ico s m, (1 + ρ ^ 2 / 2) :=
        prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_R1 _ _ _ _ _ _)
    _ = (1 + ρ ^ 2 / 2) ^ (m - s) := by rw [prod_const, Nat.card_Ico]
    _ ≤ (1 + ρ ^ 2 / 2) ^ (n + 1) :=
        pow_le_pow_right₀ (by nlinarith [sq_nonneg ρ]) (by omega)
    _ ≤ 2 := pow_bound ρ n hρ

lemma Tel1 (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (i j M : ℕ) :
    ∏ k ∈ range M, R1 P n ρ k i j =
      1 + ∑ m ∈ range M, Complex.I * ((ρ : ℂ) * f P n m i j) * ∏ k ∈ range m, R1 P n ρ k i j := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [prod_range_succ, sum_range_succ, ← add_assoc, ← ih]
    unfold R1
    ring

lemma Tel2 (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (i j m : ℕ) :
    ∏ k ∈ range m, R1 P n ρ k i j =
      1 + ∑ s ∈ range m, Complex.I * ((ρ : ℂ) * f P n s i j) * Pr P n ρ (s + 1) m i j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ih, sum_range_succ]
    have e1 : Pr P n ρ (m + 1) (m + 1) i j = 1 := by unfold Pr; simp
    have e2 : ∀ s ∈ range m, Complex.I * ((ρ : ℂ) * f P n s i j) * Pr P n ρ (s + 1) (m + 1) i j =
        Complex.I * ((ρ : ℂ) * f P n s i j) * Pr P n ρ (s + 1) m i j * R1 P n ρ m i j := by
      intro s hs
      unfold Pr
      rw [prod_Ico_succ_top (by have := mem_range.mp hs; omega)]
      ring
    rw [e1, sum_congr rfl e2, ← sum_mul]
    unfold R1
    ring

/-- The pairing of the grid array `d` with a test function. -/
noncomputable def ip (P : Finset (ℝ × ℝ)) (n : ℕ) (g : ℕ → ℕ → ℂ) : ℂ :=
  ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), (d P n i j : ℂ) * g i j

lemma ip_add (P : Finset (ℝ × ℝ)) (n : ℕ) (g h : ℕ → ℕ → ℂ) :
    ip P n (fun i j => g i j + h i j) = ip P n g + ip P n h := by
  unfold ip
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

lemma ip_smul (P : Finset (ℝ × ℝ)) (n : ℕ) (c : ℂ) (g : ℕ → ℕ → ℂ) :
    ip P n (fun i j => c * g i j) = c * ip P n g := by
  unfold ip
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

lemma ip_sum (P : Finset (ℝ × ℝ)) (n : ℕ) (S : Finset ℕ) (g : ℕ → ℕ → ℕ → ℂ) :
    ip P n (fun i j => ∑ m ∈ S, g m i j) = ∑ m ∈ S, ip P n (g m) := by
  unfold ip
  simp only [mul_sum]
  rw [Finset.sum_comm (s := S)]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm (s := S)]

lemma ip_one_im (P : Finset (ℝ × ℝ)) (n : ℕ) : (ip P n (fun _ _ => 1)).im = 0 := by
  unfold ip
  simp [Complex.im_sum]

lemma norm_ip (P : Finset (ℝ × ℝ)) (n : ℕ) (g : ℕ → ℕ → ℂ) (B : ℝ)
    (hg : ∀ i j, ‖g i j‖ ≤ B) :
    ‖ip P n g‖ ≤ B * ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| := by
  unfold ip
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hg i j) (abs_nonneg _)

lemma blk_mono {c c' i i' : ℕ} (h : c ≤ c') (he : blk c i = blk c i') : blk c' i = blk c' i' := by
  unfold blk at *
  have e : ∀ x : ℕ, x / 2 ^ (c' + 1) = x / 2 ^ (c + 1) / 2 ^ (c' - c) := by
    intro x
    rw [Nat.div_div_eq_div_mul, ← pow_add, show c + 1 + (c' - c) = c' + 1 by omega]
  rw [e i, e i', he]

lemma rad_mono {c c' i i' : ℕ} (h : c < c') (he : blk c i = blk c i') : rad c' i = rad c' i' := by
  unfold blk at he
  unfold rad
  have e : ∀ x : ℕ, x / 2 ^ c' = x / 2 ^ (c + 1) / 2 ^ (c' - (c + 1)) := by
    intro x
    rw [Nat.div_div_eq_div_mul, ← pow_add, show c + 1 + (c' - (c + 1)) = c' by omega]
  rw [e i, e i', he]

lemma f_inv (P : Finset (ℝ × ℝ)) (n k cx cy i i' j j' : ℕ) (hx : cx < n - k) (hy : cy < k)
    (h1 : blk cx i = blk cx i') (h2 : blk cy j = blk cy j') : f P n k i j = f P n k i' j' := by
  unfold f
  rw [blk_mono hx.le h1, blk_mono hy.le h2, rad_mono hx h1, rad_mono hy h2]

/-- The coefficient function of the product term `f m · f s · Π_{s<k<m} (1 + iρ f k)`. -/
noncomputable def tau (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (s m i j : ℕ) : ℂ :=
  (sig P n m (blk (n - m) i) (blk m j) * (rad m j : ℂ)) *
    (sig P n s (blk (n - s) i) (blk s j) * (rad (n - s) i : ℂ)) * Pr P n ρ (s + 1) m i j

lemma tau_inv (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (s m : ℕ) (hsm : s < m) (hm : m ≤ n) :
    Inv (n - m) s (tau P n ρ s m) := by
  intro i i' j j' h1 h2
  unfold tau
  have hPr : Pr P n ρ (s + 1) m i j = Pr P n ρ (s + 1) m i' j' := by
    unfold Pr
    refine prod_congr rfl fun k hk => ?_
    rw [mem_Ico] at hk
    unfold R1
    rw [f_inv P n k (n - m) s i i' j j' (by omega) (by omega) h1 h2]
  rw [hPr, h1, blk_mono (show s ≤ m by omega) h2, rad_mono hsm h2,
    blk_mono (show n - m ≤ n - s by omega) h1, h2, rad_mono (show n - m < n - s by omega) h1]

lemma norm_tau (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (hρ : ρ ^ 2 * (n + 1) ≤ 1) (s m : ℕ)
    (hm : m ≤ n) (i j : ℕ) : ‖tau P n ρ s m i j‖ ≤ 2 := by
  unfold tau
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_rad, norm_rad, mul_one, mul_one]
  have h1 := norm_sig P n m (blk (n - m) i) (blk m j)
  have h2 := norm_sig P n s (blk (n - s) i) (blk s j)
  have h3 := norm_Pr P n ρ hρ (s + 1) m i j (by omega)
  have h4 := norm_nonneg (sig P n m (blk (n - m) i) (blk m j))
  have h5 := norm_nonneg (sig P n s (blk (n - s) i) (blk s j))
  have h6 := norm_nonneg (Pr P n ρ (s + 1) m i j)
  have h7 := mul_le_mul (mul_le_mul h1 h2 h5 zero_le_one) h3 h6 (by norm_num)
  linarith

lemma prod_term (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (hρ : ρ ^ 2 * (n + 1) ≤ 1) (s m : ℕ)
    (hsm : s < m) (hm : m ≤ n) :
    ‖ip P n (fun i j => f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j)‖ ≤
      2 * (5 / 4) * (P.card : ℝ) * dl n (n - m) * dl n s := by
  have e : ip P n (fun i j => f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j) =
      ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)),
        (d P n i j : ℂ) * tau P n ρ s m i j * (rad (n - m) i : ℂ) * (rad s j : ℂ) := by
    unfold ip
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    unfold tau f
    ring
  rw [e]
  exact KB' P n (n - m) s (Nat.sub_le n m) (by omega) _ (tau_inv P n ρ s m hsm hm) 2
    (fun i _ j _ => norm_tau P n ρ hρ s m hm i j)

lemma geom2 (m : ℕ) : ∑ s ∈ range m, (2 : ℝ) ^ s ≤ 2 ^ m := by
  have : ∀ m : ℕ, ∑ s ∈ range m, (2 : ℝ) ^ s + 1 = 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, pow_succ]; linarith
  linarith [this m]

lemma sum_dl (n m : ℕ) : ∑ s ∈ range m, dl n s ≤ dl n m := by
  unfold dl
  rw [← sum_mul]
  exact mul_le_mul_of_nonneg_right (geom2 m) (by unfold hh; positivity)

lemma prod_terms_sum (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (hρ : ρ ^ 2 * (n + 1) ≤ 1) (m : ℕ)
    (hm : m ≤ n) :
    ∑ s ∈ range m,
      ‖ip P n (fun i j => f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j)‖ ≤
      (5 / 2) * (P.card : ℝ) / (4 * 2 ^ n) := by
  calc _ ≤ ∑ s ∈ range m, 2 * (5 / 4) * (P.card : ℝ) * dl n (n - m) * dl n s :=
        sum_le_sum fun s hs => prod_term P n ρ hρ s m (mem_range.mp hs) hm
    _ = 2 * (5 / 4) * (P.card : ℝ) * dl n (n - m) * ∑ s ∈ range m, dl n s := by rw [mul_sum]
    _ ≤ 2 * (5 / 4) * (P.card : ℝ) * dl n (n - m) * dl n m := by
        have := (dl_pos n (n - m)).le
        exact mul_le_mul_of_nonneg_left (sum_dl n m) (by positivity)
    _ = 2 * (5 / 4) * (P.card : ℝ) * (dl n (n - m) * dl n m) := by ring
    _ = (5 / 2) * (P.card : ℝ) / (4 * 2 ^ n) := by
        rw [dl_prod n m hm]; ring

/-- The expansion of the Riesz product. -/
lemma riesz_expand (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (i j : ℕ) :
    ∏ k ∈ range (n + 1), R1 P n ρ k i j =
      1 + ((Complex.I * (ρ : ℂ)) * ∑ m ∈ range (n + 1), f P n m i j +
        (-(ρ : ℂ) ^ 2) * ∑ m ∈ range (n + 1), ∑ s ∈ range m,
          f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j) := by
  rw [Tel1]
  congr 1
  simp_rw [Tel2]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have e : ∀ s ∈ range m, -(ρ : ℂ) ^ 2 * (f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j) =
      Complex.I * ((ρ : ℂ) * f P n m i j) *
        (Complex.I * ((ρ : ℂ) * f P n s i j) * Pr P n ρ (s + 1) m i j) := by
    intro s _
    linear_combination (-(ρ : ℂ) ^ 2 * f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j) * hI
  rw [sum_congr rfl e, ← mul_sum]
  ring

lemma riesz_lower (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ^ 2 * (n + 1) ≤ 1) (hN : 2 * (P.card : ℝ) ≤ 2 ^ n) :
    ρ * ((n + 1) * ((P.card : ℝ) / (32 * 2 ^ n))) -
        ρ ^ 2 * ((n + 1) * ((5 / 2) * (P.card : ℝ) / (4 * 2 ^ n))) ≤
      2 * ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| := by
  set Z := ip P n (fun i j => ∏ k ∈ range (n + 1), R1 P n ρ k i j) with hZ
  have hZ1 : Z.im ≤ 2 * ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| := by
    refine (Complex.im_le_norm Z).trans (norm_ip P n _ 2 fun i j => ?_)
    have := norm_Pr P n ρ hρ 0 (n + 1) i j le_rfl
    unfold Pr at this
    rwa [← range_eq_Ico] at this
  set M := ∑ m ∈ range (n + 1), ip P n (f P n m) with hM
  set E := ∑ m ∈ range (n + 1), ∑ s ∈ range m,
    ip P n (fun i j => f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j) with hEd
  have hZ2 : Z = ip P n (fun _ _ => 1) + ((Complex.I * (ρ : ℂ)) * M + (-(ρ : ℂ) ^ 2) * E) := by
    rw [hZ]
    simp_rw [riesz_expand]
    rw [ip_add, ip_add, ip_smul, ip_smul, ip_sum]
    congr 3
    rw [ip_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [ip_sum]
  have hMre : (n + 1) * ((P.card : ℝ) / (32 * 2 ^ n)) ≤ M.re := by
    rw [hM, Complex.re_sum]
    calc (n + 1) * ((P.card : ℝ) / (32 * 2 ^ n)) =
          ∑ m ∈ range (n + 1), (P.card : ℝ) / (32 * 2 ^ n) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := sum_le_sum fun m hm => main_term P n m (by have := mem_range.mp hm; omega) hN
  have hE : ‖E‖ ≤ (n + 1) * ((5 / 2) * (P.card : ℝ) / (4 * 2 ^ n)) := by
    rw [hEd]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ m ∈ range (n + 1), (5 / 2) * (P.card : ℝ) / (4 * 2 ^ n) :=
          sum_le_sum fun m hm => (norm_sum_le _ _).trans
            (prod_terms_sum P n ρ hρ m (by have := mem_range.mp hm; omega))
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hZim : Z.im = ρ * M.re - ρ ^ 2 * E.im := by
    rw [hZ2]
    simp [ip_one_im, Complex.add_im, Complex.mul_im]
    rw [show ((ρ : ℂ)) ^ 2 = ((ρ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_im,
      Complex.ofReal_re]
    ring
  have hEim : E.im ≤ ‖E‖ := Complex.im_le_norm E
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  nlinarith

/-! ## Part D: the discrete theorem -/

lemma norm_f (P : Finset (ℝ × ℝ)) (n k i j : ℕ) : ‖f P n k i j‖ ≤ 1 := by
  rw [f_eq, Complex.norm_real, Real.norm_eq_abs]; exact abs_fR P n k i j

theorem disc_bound (P : Finset (ℝ × ℝ)) (n : ℕ) (hN1 : 2 * (P.card : ℝ) ≤ 2 ^ n)
    (hN2 : (2 : ℝ) ^ n ≤ 4 * P.card) :
    Real.sqrt (n + 1) / 5120 ≤
      ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| := by
  set S := ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| with hS
  have hX : (0 : ℝ) < 2 ^ n := by positivity
  set Y : ℝ := (P.card : ℝ) / 2 ^ n with hY
  have hY1 : 1 / 4 ≤ Y := by rw [hY, le_div_iff₀ hX]; linarith
  have hY2 : Y ≤ 1 / 2 := by rw [hY, div_le_iff₀ hX]; linarith
  -- the single-function bound
  have h0 : Y / 32 ≤ S := by
    have hm := main_term P n 0 (Nat.zero_le n) hN1
    have hn := norm_ip P n (f P n 0) 1 (fun i j => norm_f P n 0 i j)
    have hre := Complex.re_le_norm (ip P n (f P n 0))
    have e : (P.card : ℝ) / (32 * 2 ^ n) = Y / 32 := by rw [hY]; field_simp
    unfold ip at hn hre
    rw [e] at hm
    linarith
  -- the Riesz product bound
  set q := Real.sqrt (n + 1) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hqq : q ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  have hρ0 : 0 ≤ 1 / q := by positivity
  have hρ : (1 / q) ^ 2 * (n + 1) ≤ 1 := by
    rw [div_pow, hqq]; field_simp; exact le_refl _
  have hR := riesz_lower P n (1 / q) hρ0 hρ hN1
  have e1 : 1 / q * ((n + 1) * ((P.card : ℝ) / (32 * 2 ^ n))) = q * Y / 32 := by
    rw [← hqq, hY]; field_simp
  have e2 : (1 / q) ^ 2 * ((n + 1) * ((5 / 2) * (P.card : ℝ) / (4 * 2 ^ n))) = 5 / 8 * Y := by
    rw [← hqq, hY]; field_simp; ring
  rw [e1, e2] at hR
  by_cases hc : q ≤ 40
  · nlinarith
  · push Not at hc
    nlinarith

/-! ## Part E: the grid lemma (the only measure theory) and the final theorem -/

open MeasureTheory

/-- The anchored-box discrepancy `#(P ∩ (0,u] × (0,v]) - |P| u v` (as in the brief). -/
noncomputable def disc (P : Finset (ℝ × ℝ)) (u v : ℝ) : ℝ :=
  ((P.filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card : ℝ) - P.card * u * v

noncomputable def ind (x v : ℝ) : ℝ := if x ≤ v then 1 else 0

lemma ind_mono (x : ℝ) : Monotone (ind x) := by
  intro a b hab
  unfold ind
  split_ifs with h1 h2 h2 <;> first | exact absurd (h1.trans hab) h2 | norm_num

lemma ind_nonneg (x v : ℝ) : 0 ≤ ind x v := by unfold ind; split_ifs <;> norm_num

lemma mono_sum (P : Finset (ℝ × ℝ)) (w sel : ℝ × ℝ → ℝ) (hw : ∀ p, 0 ≤ w p) :
    Monotone (fun v => ∑ p ∈ P, w p * ind (sel p) v) := by
  intro a b hab
  exact sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (ind_mono _ hab) (hw p)

lemma F1 (x c e : ℝ) (hce : c ≤ e) : ∫ v in c..e, ind x v = G x e - G x c := by
  unfold G
  rcases le_or_gt x c with h1 | h1
  · rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun v hv => by
      rw [Set.uIcc_of_le hce] at hv
      simp [ind, h1.trans hv.1])]
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    simp
  rcases lt_or_ge e x with h2 | h2
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun v hv => by
      rw [Set.uIcc_of_le hce] at hv
      have : ¬ x ≤ v := by linarith [hv.2]
      simp [ind, this])]
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    simp
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)
      ((ind_mono x).intervalIntegrable) ((ind_mono x).intervalIntegrable)]
    have hA : ∫ v in c..x, ind x v = 0 := by
      have hae : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ x := by
        rw [ae_iff]; simp
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
      · simp
      filter_upwards [hae] with v hv hvI
      rw [Set.uIoc_of_le h1.le] at hvI
      have : ¬ x ≤ v := by
        intro h; exact hv (le_antisymm hvI.2 h)
      simp [ind, this]
    have hB : ∫ v in x..e, ind x v = e - x := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun v hv => by
        rw [Set.uIcc_of_le h2] at hv
        simp [ind, hv.1])]
      simp
    rw [hA, hB, max_eq_left (by linarith), max_eq_right (by linarith)]
    ring

lemma disc_eq (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1)
    (u v : ℝ) : disc P u v = ∑ p ∈ P, ind p.1 u * ind p.2 v - P.card * u * v := by
  unfold disc
  rw [natCast_card_filter]
  congr 1
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨h1, -, h3, -⟩ := hP p hp
  unfold ind
  by_cases hu : p.1 ≤ u <;> by_cases hv : p.2 ≤ v <;> simp [hu, hv, h1, h3]

lemma hh_pos (n : ℕ) : 0 < hh n := by unfold hh; positivity

lemma cell_le (n i : ℕ) : (i : ℝ) * hh n ≤ ((i : ℝ) + 1) * hh n := by
  have := hh_pos n; nlinarith

lemma a_nonneg (n j : ℕ) (x : ℝ) : 0 ≤ a n j x := by
  unfold a G
  have := cell_le n j
  have : max ((j : ℝ) * hh n - x) 0 ≤ max (((j : ℝ) + 1) * hh n - x) 0 :=
    max_le_max (by linarith) le_rfl
  linarith

/-- The inner cell integral `∫_{cell j} disc P u v dv`. -/
noncomputable def g (P : Finset (ℝ × ℝ)) (n j : ℕ) (u : ℝ) : ℝ :=
  ∑ p ∈ P, a n j p.2 * ind p.1 u - P.card * u * al n j

lemma int_disc_v (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1)
    (u c e : ℝ) : IntervalIntegrable (fun v => disc P u v) volume c e := by
  simp_rw [disc_eq P hP u]
  have h1 : IntervalIntegrable (fun v => ∑ p ∈ P, ind p.1 u * ind p.2 v) volume c e :=
    (mono_sum P (fun p => ind p.1 u) (fun p => p.2) (fun p => ind_nonneg _ _)).intervalIntegrable
  exact h1.sub (Continuous.intervalIntegrable (by fun_prop) _ _)

lemma int_g (P : Finset (ℝ × ℝ)) (n j : ℕ) (c e : ℝ) :
    IntervalIntegrable (g P n j) volume c e := by
  unfold g
  have h1 : IntervalIntegrable (fun u => ∑ p ∈ P, a n j p.2 * ind p.1 u) volume c e :=
    (mono_sum P (fun p => a n j p.2) (fun p => p.1) (fun p => a_nonneg _ _ _)).intervalIntegrable
  exact h1.sub (Continuous.intervalIntegrable (by fun_prop) _ _)

lemma inner_eq (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1)
    (n j : ℕ) (u : ℝ) :
    ∫ v in ((j : ℝ) * hh n)..(((j : ℝ) + 1) * hh n), disc P u v = g P n j u := by
  simp_rw [disc_eq P hP u]
  have hle := cell_le n j
  have hlin : ∫ v in ((j : ℝ) * hh n)..(((j : ℝ) + 1) * hh n), (P.card : ℝ) * u * v =
      (P.card : ℝ) * u * (((((j : ℝ) + 1) * hh n) ^ 2 - ((j : ℝ) * hh n) ^ 2) / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]
  rw [intervalIntegral.integral_sub
    ((mono_sum P (fun p => ind p.1 u) (fun p => p.2) (fun p => ind_nonneg _ _)).intervalIntegrable)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_finsetSum (fun p _ =>
      ((ind_mono p.2).intervalIntegrable).const_mul _)]
  rw [hlin]
  simp only [intervalIntegral.integral_const_mul, F1 _ _ _ hle]
  unfold g a al
  rw [mul_comm]
  congr 1
  exact sum_congr rfl fun p _ => by ring

lemma outer_eq (P : Finset (ℝ × ℝ)) (n i j : ℕ) :
    ∫ u in ((i : ℝ) * hh n)..(((i : ℝ) + 1) * hh n), g P n j u = d P n i j := by
  unfold g
  have hle := cell_le n i
  have hlin : ∫ x in ((i : ℝ) * hh n)..(((i : ℝ) + 1) * hh n), (P.card : ℝ) * x * al n j =
      (P.card : ℝ) * (((((i : ℝ) + 1) * hh n) ^ 2 - ((i : ℝ) * hh n) ^ 2) / 2) * al n j := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
  rw [intervalIntegral.integral_sub
    ((mono_sum P (fun p => a n j p.2) (fun p => p.1) (fun p => a_nonneg _ _ _)).intervalIntegrable)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_finsetSum (fun p _ =>
      ((ind_mono p.1).intervalIntegrable).const_mul _)]
  rw [hlin]
  simp only [intervalIntegral.integral_const_mul, F1 _ _ _ hle]
  unfold d a al
  congr 1
  exact sum_congr rfl fun p _ => by ring

lemma hh_total (n : ℕ) : (2 : ℝ) ^ (n + 1) * hh n = 1 := by
  unfold hh; field_simp

lemma split1 (n : ℕ) (φ : ℝ → ℝ) (hφ : IntervalIntegrable φ volume 0 1) :
    ∑ i ∈ range (2 ^ (n + 1)), |∫ u in ((i : ℝ) * hh n)..(((i : ℝ) + 1) * hh n), φ u| ≤
      ∫ u in (0 : ℝ)..1, |φ u| := by
  have hpt : ∀ k : ℕ, k < 2 ^ (n + 1) → IntervalIntegrable (fun u => |φ u|) volume
      ((k : ℝ) * hh n) (((k : ℝ) + 1) * hh n) := by
    intro k hk
    have h0 : (0 : ℝ) ≤ (k : ℝ) * hh n := by have := hh_pos n; positivity
    have h1 : ((k : ℝ) + 1) * hh n ≤ 1 := by
      have : ((k : ℝ) + 1) ≤ 2 ^ (n + 1) := by exact_mod_cast hk
      have := hh_pos n
      nlinarith [hh_total n]
    refine hφ.abs.mono_set (Set.uIcc_subset_uIcc ?_ ?_)
    · rw [Set.uIcc_of_le zero_le_one]; exact ⟨h0, by linarith [cell_le n k]⟩
    · rw [Set.uIcc_of_le zero_le_one]; exact ⟨by linarith [cell_le n k], h1⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * hh n) (n := 2 ^ (n + 1)) (f := fun u => |φ u|) (μ := volume)
    (fun k hk => by
      have := hpt k hk
      simpa using this)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, Nat.cast_pow, Nat.cast_ofNat,
    hh_total] at hsum
  rw [← hsum]
  exact sum_le_sum fun i _ => intervalIntegral.abs_integral_le_integral_abs (cell_le n i)

lemma abs_disc_le (P : Finset (ℝ × ℝ)) (u v : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) : |disc P u v| ≤ 2 * P.card := by
  unfold disc
  have h1 : ((P.filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card : ℝ) ≤ P.card := by
    exact_mod_cast card_filter_le _ _
  have h2 : (0 : ℝ) ≤ ((P.filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card : ℝ) :=
    Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have h3 : 0 ≤ (P.card : ℝ) * u * v := by
    have := hu.1; have := hv.1; positivity
  have h4 : (P.card : ℝ) * u * v ≤ P.card := by
    have : u * v ≤ 1 := by nlinarith [hu.1, hu.2, hv.1, hv.2]
    nlinarith
  rw [abs_le]; constructor <;> linarith

lemma meas_disc (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) :
    Measurable fun q : ℝ × ℝ => |disc P q.1 q.2| := by
  have e : (fun q : ℝ × ℝ => |disc P q.1 q.2|) =
      fun q => |∑ p ∈ P, ind p.1 q.1 * ind p.2 q.2 - P.card * q.1 * q.2| := by
    funext q; rw [disc_eq P hP]
  rw [e]
  refine Measurable.abs (Measurable.sub ?_ (by fun_prop))
  refine Finset.measurable_sum _ fun p _ => Measurable.mul ?_ ?_
  · unfold ind
    exact Measurable.ite (measurableSet_le measurable_const measurable_fst) measurable_const
      measurable_const
  · unfold ind
    exact Measurable.ite (measurableSet_le measurable_const measurable_snd) measurable_const
      measurable_const

lemma int_F (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) :
    IntervalIntegrable (fun u => ∫ v in (0 : ℝ)..1, |disc P u v|) volume 0 1 := by
  have e : (fun u => ∫ v in (0 : ℝ)..1, |disc P u v|) =
      fun u => ∫ v, (fun q : ℝ × ℝ => |disc P q.1 q.2|) (u, v) ∂(volume.restrict (Set.Ioc 0 1)) := by
    funext u; exact intervalIntegral.integral_of_le zero_le_one
  have hsm : StronglyMeasurable (fun u => ∫ v in (0 : ℝ)..1, |disc P u v|) := by
    rw [e]; exact (meas_disc P hP).stronglyMeasurable.integral_prod_right'
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine IntegrableOn.of_bound measure_Ioc_lt_top hsm.aestronglyMeasurable (2 * P.card)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := 2 * P.card) (f := fun v => |disc P u v|) (fun v hv => by
      rw [Set.uIoc_of_le zero_le_one] at hv
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_disc_le P u v ⟨hu.1.le, hu.2⟩ ⟨hv.1.le, hv.2⟩)
  simpa using this

theorem grid (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) (n : ℕ) :
    ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| ≤
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc P u v| := by
  have hin : ∀ u, ∑ j ∈ range (2 ^ (n + 1)), |g P n j u| ≤ ∫ v in (0 : ℝ)..1, |disc P u v| := by
    intro u
    have := split1 n (fun v => disc P u v) (int_disc_v P hP u 0 1)
    simpa only [inner_eq P hP] using this
  have hout : ∀ j, ∑ i ∈ range (2 ^ (n + 1)), |d P n i j| ≤ ∫ u in (0 : ℝ)..1, |g P n j u| := by
    intro j
    have := split1 n (g P n j) (int_g P n j 0 1)
    simpa only [outer_eq P] using this
  have hsumint : IntervalIntegrable (fun u => ∑ j ∈ range (2 ^ (n + 1)), |g P n j u|) volume 0 1 := by
    have := IntervalIntegrable.sum (range (2 ^ (n + 1))) (f := fun j u => |g P n j u|)
      (μ := volume) (a := 0) (b := 1) (fun j _ => (int_g P n j 0 1).abs)
    rw [Finset.sum_fn] at this
    exact this
  rw [sum_comm]
  calc ∑ j ∈ range (2 ^ (n + 1)), ∑ i ∈ range (2 ^ (n + 1)), |d P n i j|
      ≤ ∑ j ∈ range (2 ^ (n + 1)), ∫ u in (0 : ℝ)..1, |g P n j u| := sum_le_sum fun j _ => hout j
    _ = ∫ u in (0 : ℝ)..1, ∑ j ∈ range (2 ^ (n + 1)), |g P n j u| :=
        (intervalIntegral.integral_finsetSum fun j _ => (int_g P n j 0 1).abs).symm
    _ ≤ ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc P u v| :=
        intervalIntegral.integral_mono_on zero_le_one hsumint (int_F P hP) fun u _ => hin u

/-- **Halász's theorem** (hypothesis `H1`): `c √(log |P|) ≤ ∫∫ |disc P|`, with `c = 1/5120`. -/
theorem halasz : ∃ cH : ℝ, 0 < cH ∧ ∀ P : Finset (ℝ × ℝ), 2 ≤ P.card →
    (∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) →
    cH * Real.sqrt (Real.log P.card) ≤ ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc P u v| := by
  refine ⟨1 / 5120, by norm_num, fun P hP2 hP => ?_⟩
  set N := P.card with hNd
  have hN0 : N ≠ 0 := by omega
  set l := Nat.log 2 N with hl
  have h1 : 2 ^ l ≤ N := Nat.pow_log_le_self 2 hN0
  have h2 : N < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  set n := l + 2 with hn
  have hA : 2 * (N : ℝ) ≤ 2 ^ n := by
    have : 2 * N ≤ 2 ^ n := by rw [hn, pow_succ]; omega
    exact_mod_cast this
  have hB : (2 : ℝ) ^ n ≤ 4 * N := by
    have : 2 ^ n ≤ 4 * N := by rw [hn, pow_add]; omega
    exact_mod_cast this
  have hD := disc_bound P n hA hB
  have hG := grid P hP n
  have hlog : Real.log N ≤ n + 1 := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
    have hle : (N : ℝ) ≤ 2 ^ n := by linarith
    have h3 : Real.log N ≤ Real.log ((2 : ℝ) ^ n) := Real.log_le_log hNpos hle
    rw [Real.log_pow] at h3
    have h4 := Real.log_two_lt_d9
    have h5 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hsq : Real.sqrt (Real.log N) ≤ Real.sqrt (n + 1) := Real.sqrt_le_sqrt hlog
  linarith

end Halasz

theorem E1221i_step_H1 : OMA.R_Erdos1221_erdos_1221_parts_i_R1.H1 := Halasz.halasz


end StepH1

section StepH2

/-!
# Korsky's Proposition 6.4 (one-sided bound on `M_n`)

Formalization of S. Korsky, *A Resolution of the de Bruijn–Erdős Consecutive-Gap Problem*,
arXiv:2609.07196 (CC BY 4.0), Section 6: Lemma 6.1 (total displacement of the `kr`-steps from the
zero-sum identity for the `r`-spans), Lemma 6.2 (the `L¹` comparison
`Z_t(D) ≤ ((1+q)D/E) Z_{(1+q)t}(E) + qD + 8kA + O(kr/t)` via the injections `B_s ∘ F_t`),
Lemma 6.3 (`Z_t(r) ≤ A`) and Proposition 6.4 (the dyadic chain from `√(Ar)` to `r`).
The one-sided hypothesis used here is `n M_n^(r) - r ≤ A eventually`.

Implementation notes. All times are integers: the continuous shift average of Lemma 6.2 is
replaced by a finite family of shifts `jδ` (realized at integer intermediate times) together
with an exact discrete convolution identity, followed by a limit in the mesh `δ → 0`.
Constants: `C₂ = 64`, `C₃ = 172 e⁴ + 24`.
-/

open Filter Finset MeasureTheory

namespace E1221P64

-- Part A: analysis of arc indicators

/-- `ind p x l = 1` iff the point `p` lies in the arc `(x, x + l]` of `ℝ/ℤ`. -/
noncomputable def ind (p x l : ℝ) : ℝ :=
  if 0 < Int.fract (p - x) ∧ Int.fract (p - x) ≤ l then 1 else 0

/-- Number of the first `n` points in the arc `(x, x + l]`. -/
noncomputable def N (a : ℕ → ℝ) (n : ℕ) (x l : ℝ) : ℝ := ∑ j ∈ range n, ind (a j) x l

/-- `Z_n(D) = ∫ (N_n((x, x + D/n]) - D)_+ dx`. -/
noncomputable def Z (a : ℕ → ℝ) (n : ℕ) (D : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, max (N a n x (D / n) - D) 0

lemma ind_nonneg (p x l : ℝ) : 0 ≤ ind p x l := by unfold ind; split_ifs <;> norm_num

lemma ind_le_one (p x l : ℝ) : ind p x l ≤ 1 := by unfold ind; split_ifs <;> norm_num

lemma ind_add_int (p x l : ℝ) (z : ℤ) : ind (p + z) x l = ind p x l := by
  unfold ind; rw [show p + z - x = (p - x) + z by ring, Int.fract_add_intCast]

lemma ind_congr {p p' : ℝ} (z : ℤ) (h : p' = p + z) (x l : ℝ) : ind p' x l = ind p x l := by
  rw [h, ind_add_int]

lemma ind_x_add (p x c l : ℝ) : ind p (x + c) l = ind (p - c) x l := by
  unfold ind; rw [show p - (x + c) = p - c - x by ring]

lemma ind_periodic (p l : ℝ) : Function.Periodic (fun x => ind p x l) 1 := by
  intro x
  show ind p (x + 1) l = ind p x l
  unfold ind; rw [show p - (x + 1) = (p - x) - 1 by ring, Int.fract_sub_one]

lemma ind_meas (p l : ℝ) : Measurable (fun x => ind p x l) := by
  unfold ind
  refine Measurable.ite ?_ measurable_const measurable_const
  have hf : Measurable (fun x : ℝ => Int.fract (p - x)) :=
    measurable_fract.comp (measurable_const.sub measurable_id)
  exact measurableSet_Ioc.preimage hf

/-- Measurable and bounded. -/
def Good (f : ℝ → ℝ) : Prop := Measurable f ∧ ∃ M, ∀ x, |f x| ≤ M

lemma Good.ii {f : ℝ → ℝ} (hf : Good f) (a b : ℝ) : IntervalIntegrable f volume a b := by
  obtain ⟨hm, M, hM⟩ := hf
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne hm.aestronglyMeasurable
    (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hM x))

lemma good_const (c : ℝ) : Good (fun _ => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩

lemma good_ind (p l : ℝ) : Good (fun x => ind p x l) :=
  ⟨ind_meas p l, 1, fun x => by
    rw [abs_of_nonneg (ind_nonneg _ _ _)]; exact ind_le_one _ _ _⟩

lemma Good.add {f g : ℝ → ℝ} (hf : Good f) (hg : Good g) : Good (fun x => f x + g x) := by
  obtain ⟨hf, M, hM⟩ := hf; obtain ⟨hg, M', hM'⟩ := hg
  exact ⟨hf.add hg, M + M', fun x => (abs_add_le _ _).trans (add_le_add (hM x) (hM' x))⟩

lemma Good.neg {f : ℝ → ℝ} (hf : Good f) : Good (fun x => - f x) := by
  obtain ⟨hf, M, hM⟩ := hf
  exact ⟨hf.neg, M, fun x => by rw [abs_neg]; exact hM x⟩

lemma Good.sub {f g : ℝ → ℝ} (hf : Good f) (hg : Good g) : Good (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma Good.mul_const {f : ℝ → ℝ} (hf : Good f) (c : ℝ) : Good (fun x => c * f x) := by
  obtain ⟨hf, M, hM⟩ := hf
  exact ⟨measurable_const.mul hf, |c| * M, fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg c)⟩

lemma Good.max0 {f : ℝ → ℝ} (hf : Good f) : Good (fun x => max (f x) 0) := by
  obtain ⟨hf, M, hM⟩ := hf
  refine ⟨hf.max measurable_const, M, fun x => ?_⟩
  have := hM x
  rw [abs_le] at this ⊢
  constructor
  · have : 0 ≤ M := le_trans (abs_nonneg _) (hM x)
    linarith [le_max_right (f x) 0]
  · exact max_le this.2 (le_trans (abs_nonneg _) (hM x))

lemma Good.abs {f : ℝ → ℝ} (hf : Good f) : Good (fun x => |f x|) := by
  obtain ⟨hf, M, hM⟩ := hf
  exact ⟨continuous_abs.measurable.comp hf, M, fun x => by rw [abs_abs]; exact hM x⟩

lemma Good.comp_add {f : ℝ → ℝ} (hf : Good f) (c : ℝ) : Good (fun x => f (x + c)) := by
  obtain ⟨hf, M, hM⟩ := hf
  exact ⟨hf.comp (measurable_id.add_const c), M, fun x => hM _⟩

lemma good_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, Good (f i)) :
    Good (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_const 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (mem_insert_self _ _)).add (ih fun j hj => hf j (mem_insert_of_mem hj))

lemma good_N (a : ℕ → ℝ) (n : ℕ) (l : ℝ) : Good (fun x => N a n x l) :=
  good_sum _ _ (fun j _ => good_ind (a j) l)

lemma N_periodic (a : ℕ → ℝ) (n : ℕ) (l : ℝ) : Function.Periodic (fun x => N a n x l) 1 := by
  intro x
  show ∑ j ∈ range n, ind (a j) (x + 1) l = ∑ j ∈ range n, ind (a j) x l
  exact Finset.sum_congr rfl (fun j _ => ind_periodic (a j) l x)

lemma N_nonneg (a : ℕ → ℝ) (n : ℕ) (x l : ℝ) : 0 ≤ N a n x l :=
  Finset.sum_nonneg (fun j _ => ind_nonneg _ _ _)

/-- Translation invariance of `∫₀¹` for `1`-periodic functions. -/
lemma int_trans (f : ℝ → ℝ) (hf : Function.Periodic f 1) (c : ℝ) :
    ∫ x in (0:ℝ)..1, f (x + c) = ∫ x in (0:ℝ)..1, f x := by
  rw [intervalIntegral.integral_comp_add_right f c, show (0:ℝ) + c = c by ring,
    show (1:ℝ) + c = c + 1 by ring, hf.intervalIntegral_add_eq c 0, zero_add]

/-- `∫₀¹ ind p x l dx = l`. -/
lemma int_ind (p l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) : ∫ x in (0:ℝ)..1, ind p x l = l := by
  set g : ℝ → ℝ := fun w => if 0 < Int.fract w ∧ Int.fract w ≤ l then 1 else 0 with hgdef
  have hgm : Measurable g := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_Ioc.preimage measurable_fract
  have hgG : Good g := ⟨hgm, 1, fun w => by
    simp only [hgdef]; split_ifs <;> norm_num⟩
  have hper : Function.Periodic g 1 := fun w => by simp only [hgdef, Int.fract_add_one]
  calc ∫ x in (0:ℝ)..1, ind p x l = ∫ x in (0:ℝ)..1, g (p - x) := rfl
    _ = ∫ x in p - 1..p - 0, g x := intervalIntegral.integral_comp_sub_left g p
    _ = ∫ x in p - 1..p - 1 + 1, g x := by congr 1 <;> ring
    _ = ∫ x in (0:ℝ)..0 + 1, g x := hper.intervalIntegral_add_eq _ _
    _ = (∫ x in (0:ℝ)..l, g x) + ∫ x in l..1, g x := by
        rw [zero_add, intervalIntegral.integral_add_adjacent_intervals (hgG.ii _ _) (hgG.ii _ _)]
    _ = (∫ x in (0:ℝ)..l, (1:ℝ)) + ∫ x in l..1, (0:ℝ) := by
        congr 1
        · apply intervalIntegral.integral_congr_ae
          refine Eventually.of_forall (fun x hx => ?_)
          rw [Set.uIoc_of_le hl0] at hx
          have : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1.le, by linarith [hx.2]⟩
          simp only [hgdef, this]; rw [if_pos ⟨hx.1, hx.2⟩]
        · apply intervalIntegral.integral_congr_ae
          refine Eventually.of_forall (fun x hx => ?_)
          rw [Set.uIoc_of_le hl1.le] at hx
          simp only [hgdef]
          rw [if_neg]
          rintro ⟨h0, h1⟩
          rcases hx.2.lt_or_eq with h | h
          · rw [Int.fract_eq_self.2 ⟨by linarith [hx.1], h⟩] at h1; linarith [hx.1]
          · rw [h] at h0; simp at h0
    _ = l := by simp

lemma int_N (a : ℕ → ℝ) (n : ℕ) (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) :
    ∫ x in (0:ℝ)..1, N a n x l = n * l := by
  unfold N
  rw [intervalIntegral.integral_finsetSum (fun j _ => (good_ind (a j) l).ii 0 1)]
  simp [int_ind _ l hl0 hl1]

/-- `fract (y + c) = fract y + c - z` for some integer `z`. -/
lemma fract_add_eq (y c : ℝ) : ∃ z : ℤ, Int.fract (y + c) = Int.fract y + c - z := by
  refine ⟨⌊Int.fract y + c⌋, ?_⟩
  have e : y + c = (Int.fract y + c) + ((⌊y⌋ : ℤ) : ℝ) := by
    rw [← Int.self_sub_floor y]; ring
  rw [e, Int.fract_add_intCast, ← Int.self_sub_floor]

/-- Pointwise: moving a point by `e ∈ [0,1)` changes the arc indicator only on two short arcs. -/
lemma ind_diff_pt (p x l e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) (hl0 : 0 ≤ l) (hl1 : l < 1) :
    |ind p x l - ind (p + e) x l| ≤ ind (p + e) x e + ind (p - l + e) x e := by
  have hw0 := Int.fract_nonneg (p - x)
  have hw1 := Int.fract_lt_one (p - x)
  obtain ⟨z1, h1⟩ := fract_add_eq (p - x) e
  obtain ⟨z2, h2⟩ := fract_add_eq (p - x) (e - l)
  rw [show p - x + e = p + e - x by ring] at h1
  rw [show p - x + (e - l) = p - l + e - x by ring] at h2
  have hv1 := Int.fract_nonneg (p + e - x)
  have hv1' := Int.fract_lt_one (p + e - x)
  have hv2 := Int.fract_nonneg (p - l + e - x)
  have hv2' := Int.fract_lt_one (p - l + e - x)
  have hz1a : z1 ≤ 1 := by
    have : (z1 : ℝ) < 2 := by linarith
    exact_mod_cast (show (z1:ℝ) ≤ 1 by
      have : z1 < 2 := by exact_mod_cast this
      exact_mod_cast (by omega : z1 ≤ 1))
  have hz1b : 0 ≤ z1 := by
    have : (-1 : ℝ) < z1 := by linarith
    have : (-1 : ℤ) < z1 := by exact_mod_cast this
    omega
  have hz2a : z2 ≤ 1 := by
    have : (z2 : ℝ) < 2 := by linarith
    have : z2 < 2 := by exact_mod_cast this
    omega
  have hz2b : -1 ≤ z2 := by
    have : (-2 : ℝ) < z2 := by linarith
    have : (-2 : ℤ) < z2 := by exact_mod_cast this
    omega
  set w := Int.fract (p - x) with hw
  set v1 := Int.fract (p + e - x) with hv1d
  set v2 := Int.fract (p - l + e - x) with hv2d
  have key1 : (0 < w ∧ w ≤ l) → ¬(0 < v1 ∧ v1 ≤ l) → (0 < v2 ∧ v2 ≤ e) := by
    rintro ⟨hw0', hwl⟩ hnot
    have hgt : l < w + e := by
      interval_cases z1
      · by_contra hc; push Not at hc; exact hnot ⟨by push_cast at h1; linarith, by push_cast at h1; linarith⟩
      · push_cast at h1; linarith
    have hz : z2 = 0 := by
      have h3 : (-1 : ℝ) < z2 := by linarith
      have h4 : (z2 : ℝ) < 1 := by linarith
      have : (-1 : ℤ) < z2 := by exact_mod_cast h3
      have : z2 < 1 := by exact_mod_cast h4
      omega
    rw [hz] at h2; push_cast at h2
    constructor <;> linarith
  have key2 : ¬(0 < w ∧ w ≤ l) → (0 < v1 ∧ v1 ≤ l) → (0 < v1 ∧ v1 ≤ e) := by
    rintro hnot ⟨hv0, hvl⟩
    refine ⟨hv0, ?_⟩
    interval_cases z1
    · push_cast at h1
      by_contra hc; push Not at hc
      exact hnot ⟨by linarith, by linarith⟩
    · push_cast at h1; linarith
  unfold ind
  by_cases hA : 0 < w ∧ w ≤ l <;> by_cases hB : 0 < v1 ∧ v1 ≤ l
  · rw [if_pos hA, if_pos hB, sub_self, abs_zero]
    split_ifs <;> norm_num
  · rw [if_pos hA, if_neg hB, if_pos (key1 hA hB)]
    split_ifs <;> norm_num
  · rw [if_neg hA, if_pos hB, if_pos (key2 hA hB)]
    split_ifs <;> norm_num
  · rw [if_neg hA, if_neg hB, sub_self, abs_zero]
    split_ifs <;> norm_num

/-- Integrated form of `ind_diff_pt`. -/
lemma int_diff_e (p q l e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) (hl0 : 0 ≤ l) (hl1 : l < 1)
    (z : ℤ) (hq : q = p + e + z) :
    ∫ x in (0:ℝ)..1, |ind p x l - ind q x l| ≤ 2 * e := by
  have hq' : ∀ x, ind q x l = ind (p + e) x l := fun x => ind_congr z hq x l
  calc ∫ x in (0:ℝ)..1, |ind p x l - ind q x l|
      ≤ ∫ x in (0:ℝ)..1, (ind (p + e) x e + ind (p - l + e) x e) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact ((good_ind p l).sub (good_ind q l)).abs.ii 0 1
        · exact ((good_ind (p + e) e).add (good_ind (p - l + e) e)).ii 0 1
        · intro x _; rw [hq']; exact ind_diff_pt p x l e he0 he1 hl0 hl1
    _ = 2 * e := by
        rw [intervalIntegral.integral_add ((good_ind _ e).ii 0 1) ((good_ind _ e).ii 0 1),
          int_ind _ e he0 he1, int_ind _ e he0 he1]; ring

lemma int_ind_diff (p η l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) :
    ∫ x in (0:ℝ)..1, |ind p x l - ind (p + η) x l| ≤ 2 * |η| := by
  rcases le_or_gt 0 η with hη | hη
  · have h := int_diff_e p (p + η) l (Int.fract η) (Int.fract_nonneg _) (Int.fract_lt_one _)
      hl0 hl1 ⌊η⌋ (by rw [← Int.self_sub_floor]; ring)
    have : Int.fract η ≤ |η| := by
      rw [abs_of_nonneg hη, ← Int.self_sub_floor]
      have : (0:ℝ) ≤ ⌊η⌋ := by exact_mod_cast Int.floor_nonneg.2 hη
      linarith
    linarith
  · have h := int_diff_e (p + η) p l (Int.fract (-η)) (Int.fract_nonneg _) (Int.fract_lt_one _)
      hl0 hl1 ⌊-η⌋ (by rw [← Int.self_sub_floor]; ring)
    have e1 : ∀ x, |ind p x l - ind (p + η) x l| = |ind (p + η) x l - ind p x l| :=
      fun x => abs_sub_comm _ _
    simp only [e1]
    have : Int.fract (-η) ≤ |η| := by
      rw [abs_of_neg hη, ← Int.self_sub_floor]
      have : (0:ℝ) ≤ ⌊-η⌋ := by exact_mod_cast Int.floor_nonneg.2 (by linarith)
      linarith
    linarith

/-- Additivity of arcs: `(y, y+s+t] = (y, y+s] ⊔ (y+s, y+s+t]`. -/
lemma ind_add (p y s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1) :
    ind p y (s + t) = ind p y s + ind p (y + s) t := by
  have hw0 := Int.fract_nonneg (p - y)
  have hw1 := Int.fract_lt_one (p - y)
  obtain ⟨z, hz⟩ := fract_add_eq (p - y) (-s)
  rw [show p - y + -s = p - (y + s) by ring] at hz
  have hv0 := Int.fract_nonneg (p - (y + s))
  have hv1 := Int.fract_lt_one (p - (y + s))
  have hza : z ≤ 0 := by
    have : (z : ℝ) < 1 := by linarith
    have : z < 1 := by exact_mod_cast this
    omega
  have hzb : -1 ≤ z := by
    have : (-2 : ℝ) < z := by linarith
    have : (-2 : ℤ) < z := by exact_mod_cast this
    omega
  unfold ind
  rw [hz]
  interval_cases z <;> push_cast at hz ⊢ <;> simp only [ite_and] <;> split_ifs <;>
    (try push Not at *) <;> first | linarith | norm_num

lemma ind_prod (p x l L : ℝ) (hL : 0 ≤ L) (hl : 0 ≤ l) (hlL : l + L < 1) :
    ind p x l * ind (p + L) x l ≤ ind p x (l - L) := by
  have hw0 := Int.fract_nonneg (p - x)
  have hw1 := Int.fract_lt_one (p - x)
  obtain ⟨z, hz⟩ := fract_add_eq (p - x) L
  rw [show p - x + L = p + L - x by ring] at hz
  have hv0 := Int.fract_nonneg (p + L - x)
  have hv1 := Int.fract_lt_one (p + L - x)
  have hza : z ≤ 1 := by
    have : (z : ℝ) < 2 := by linarith
    have : z < 2 := by exact_mod_cast this
    omega
  have hzb : 0 ≤ z := by
    have : (-1 : ℝ) < z := by linarith
    have : (-1 : ℤ) < z := by exact_mod_cast this
    omega
  unfold ind
  rw [hz]
  interval_cases z <;> push_cast at hz ⊢ <;> simp only [ite_and] <;> split_ifs <;>
    (try push Not at *) <;> first | linarith | norm_num

lemma int_ind_le (p l : ℝ) (hl1 : l < 1) : ∫ x in (0:ℝ)..1, ind p x l ≤ max l 0 := by
  rcases le_or_gt 0 l with hl | hl
  · rw [int_ind p l hl hl1]; exact le_max_left _ _
  · have : ∀ x, ind p x l = 0 := by
      intro x; unfold ind; rw [if_neg]; rintro ⟨h1, h2⟩; linarith
    simp only [this]; simp

lemma N_add (a : ℕ → ℝ) (n : ℕ) (y s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1) :
    N a n y (s + t) = N a n y s + N a n (y + s) t := by
  unfold N; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => ind_add _ _ _ _ hs ht hst)

lemma N_split (a : ℕ → ℝ) (n : ℕ) (y δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ P : ℕ, (P : ℝ) * δ < 1 → N a n y (P * δ) = ∑ i ∈ range P, N a n (y + i * δ) δ := by
  intro P
  induction P with
  | zero =>
    intro _
    simp only [Nat.cast_zero, zero_mul, range_zero, sum_empty]
    unfold N
    apply Finset.sum_eq_zero
    intro j _; unfold ind; rw [if_neg]; rintro ⟨h1, h2⟩; linarith
  | succ P ih =>
    intro hP
    push_cast at hP
    have hP' : (P : ℝ) * δ < 1 := by nlinarith
    rw [Finset.sum_range_succ, ← ih hP']
    push_cast
    rw [show ((P : ℝ) + 1) * δ = P * δ + δ by ring]
    exact N_add a n y _ _ (by positivity) hδ (by linarith)

/-- Discrete convolution identity. -/
lemma N_conv (a : ℕ → ℝ) (n : ℕ) (x δ : ℝ) (hδ : 0 ≤ δ) (P L : ℕ) (hP : (P : ℝ) * δ < 1)
    (hL : (L : ℝ) * δ < 1) :
    ∑ j ∈ range L, N a n (x + j * δ) (P * δ) = ∑ i ∈ range P, N a n (x + i * δ) (L * δ) := by
  simp_rw [N_split a n _ δ hδ P hP, N_split a n _ δ hδ L hL]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  congr 1; ring

lemma int_N_shift (a : ℕ → ℝ) (n : ℕ) (c l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) :
    ∫ x in (0:ℝ)..1, N a n (x + c) l = n * l := by
  rw [int_trans (fun x => N a n x l) (N_periodic a n l) c, int_N a n l hl0 hl1]

lemma Z_nonneg (a : ℕ → ℝ) (n : ℕ) (D : ℝ) : 0 ≤ Z a n D :=
  intervalIntegral.integral_nonneg (by norm_num) (fun x _ => le_max_right _ _)

/-- Robustness: `Z_m(E) ≤ Z_m(T) + (E - T)` for `T ≤ E`. -/
lemma Z_robust (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (T E : ℝ) (hT : 0 < T) (hTE : T ≤ E)
    (hE : E / m < 1) : Z a m E ≤ Z a m T + (E - T) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hsplit : ∀ x, N a m x (E / m) = N a m x (T / m) + N a m (x + T / m) ((E - T) / m) := by
    intro x
    rw [← N_add a m x _ _ (by positivity) (div_nonneg (by linarith) hmR.le)
      (by rw [← add_div]; ring_nf; ring_nf at hE; linarith)]
    congr 1; field_simp; ring
  unfold Z
  calc ∫ x in (0:ℝ)..1, max (N a m x (E / m) - E) 0
      ≤ ∫ x in (0:ℝ)..1, (max (N a m x (T / m) - T) 0 + N a m (x + T / m) ((E - T) / m)) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact ((good_N a m _).sub (good_const E)).max0.ii 0 1
        · exact (((good_N a m _).sub (good_const T)).max0.add ((good_N a m _).comp_add _)).ii 0 1
        · intro x _
          rw [hsplit x]
          have := N_nonneg a m (x + T / m) ((E - T) / m)
          apply max_le
          · linarith [le_max_left (N a m x (T / m) - T) 0]
          · linarith [le_max_right (N a m x (T / m) - T) 0]
    _ = (∫ x in (0:ℝ)..1, max (N a m x (T / m) - T) 0) + (E - T) := by
        rw [intervalIntegral.integral_add (((good_N a m _).sub (good_const T)).max0.ii 0 1)
          (((good_N a m _).comp_add _).ii 0 1),
          int_N_shift a m _ _ (div_nonneg (by linarith) hmR.le)
            (by rw [div_lt_one hmR]; rw [div_lt_one hmR] at hE; linarith)]
        field_simp

lemma fract_shift (y w : ℝ) (h0 : 0 ≤ Int.fract y + w) (h1 : Int.fract y + w < 1) :
    Int.fract (y + w) = Int.fract y + w := by
  have e : y + w = (Int.fract y + w) + ((⌊y⌋ : ℤ) : ℝ) := by
    rw [← Int.self_sub_floor]; ring
  rw [e, Int.fract_add_intCast, Int.fract_eq_self.2 ⟨h0, h1⟩]

-- Part B: the sorted structure

section sorted

open Erdos1221

variable {a : ℕ → ℝ} {n r : ℕ}

lemma sp_eq (i : Fin n) :
    sortedPoint a n i = Int.fract (a (Tuple.sort (pts a n) i : ℕ)) := rfl

lemma sp_nonneg (i : Fin n) : 0 ≤ sortedPoint a n i := Int.fract_nonneg _

lemma sp_lt_one (i : Fin n) : sortedPoint a n i < 1 := Int.fract_lt_one _

lemma sp_strictMono (ha : Function.Injective fun k => Int.fract (a k)) :
    StrictMono (sortedPoint a n) := by
  apply (Tuple.monotone_sort (pts a n)).strictMono_of_injective
  intro i j h
  have : ((Tuple.sort (pts a n) i : Fin n) : ℕ) = (Tuple.sort (pts a n) j : ℕ) := ha h
  exact (Tuple.sort (pts a n)).injective (Fin.ext this)

lemma u_eq (hn : 0 < n) (j : ℕ) :
    unrolled a n j = sortedPoint a n ⟨j % n, Nat.mod_lt j hn⟩ + ((j / n : ℕ) : ℝ) := by
  unfold unrolled; rw [dif_pos hn]

lemma u_lt (hn : 0 < n) (i : ℕ) (hi : i < n) : unrolled a n i = sortedPoint a n ⟨i, hi⟩ := by
  rw [u_eq hn]
  have h1 : (⟨i % n, Nat.mod_lt i hn⟩ : Fin n) = ⟨i, hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
  rw [h1, Nat.div_eq_of_lt hi]; simp

lemma u_add (hn : 0 < n) (j q : ℕ) : unrolled a n (j + n * q) = unrolled a n j + q := by
  rw [u_eq hn, u_eq hn]
  have h1 : (⟨(j + n * q) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨j % n, Nat.mod_lt j hn⟩ :=
    Fin.ext (by simp [Nat.add_mul_mod_self_left])
  have h2 : (j + n * q) / n = j / n + q := by rw [Nat.add_mul_div_left _ _ hn]
  rw [h1, h2]; push_cast; ring

lemma u_strictMono (hn : 0 < n) (ha : Function.Injective fun k => Int.fract (a k)) :
    StrictMono (unrolled a n) := by
  intro j j' h
  rw [u_eq hn, u_eq hn]
  rcases (Nat.div_le_div_right h.le : j / n ≤ j' / n).lt_or_eq with hlt | heq
  · have h1 := sp_lt_one (a := a) ⟨j % n, Nat.mod_lt j hn⟩
    have h2 := sp_nonneg (a := a) ⟨j' % n, Nat.mod_lt j' hn⟩
    have h3 : ((j / n : ℕ) : ℝ) + 1 ≤ ((j' / n : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith
  · have hmod : j % n < j' % n := by
      have h1 := Nat.div_add_mod j n
      have h2 := Nat.div_add_mod j' n
      rw [heq] at h1
      generalize n * (j' / n) = M at h1 h2
      omega
    rw [heq]
    have := sp_strictMono (n := n) ha (show (⟨j % n, Nat.mod_lt j hn⟩ : Fin n) <
      ⟨j' % n, Nat.mod_lt j' hn⟩ from hmod)
    linarith

lemma rSpan_mod (hn : 0 < n) (i : ℕ) : rSpan a n r i = rSpan a n r (i % n) := by
  unfold rSpan
  have e1 : i + r = (i % n + r) + n * (i / n) := by
    have := Nat.mod_add_div i n
    generalize n * (i / n) = M at this ⊢
    omega
  have e2 : i = i % n + n * (i / n) := (Nat.mod_add_div i n).symm
  rw [e1, u_add hn, show unrolled a n i = unrolled a n (i % n + n * (i / n)) by rw [← e2],
    u_add hn]
  ring

lemma min_le_rSpan (hn : 0 < n) (i : ℕ) : minSpan a n r ≤ rSpan a n r i := by
  rw [rSpan_mod hn]
  exact ciInf_le (f := fun i : Fin n => rSpan a n r i) (Set.finite_range _).bddBelow (⟨i % n, Nat.mod_lt _ hn⟩ : Fin n)

lemma rSpan_le_max (hn : 0 < n) (i : ℕ) : rSpan a n r i ≤ maxSpan a n r := by
  rw [rSpan_mod hn]
  exact le_ciSup (f := fun i : Fin n => rSpan a n r i) (Set.finite_range _).bddAbove (⟨i % n, Nat.mod_lt _ hn⟩ : Fin n)

lemma unrolled_add_n (hn : 0 < n) (j : ℕ) : unrolled a n (j + n) = unrolled a n j + 1 := by
  unfold unrolled
  rw [dif_pos hn, dif_pos hn]
  have h1 : (j + n) % n = j % n := Nat.add_mod_right j n
  have h2 : (j + n) / n = j / n + 1 := by rw [Nat.add_div_right j hn]
  simp only [h1, h2]
  push_cast
  ring

/-- Each one-step shift of the starting index adds exactly `1` to the sum (telescoping). -/
lemma sum_step (hn : 0 < n) (s : ℕ) :
    ∑ i ∈ range n, (unrolled a n (i + s + 1) - unrolled a n (i + s)) = 1 := by
  have h := Finset.sum_range_sub (fun i => unrolled a n (i + s)) n
  have e : ∀ i ∈ range n, unrolled a n (i + s + 1) - unrolled a n (i + s) =
      unrolled a n (i + 1 + s) - unrolled a n (i + s) := by
    intro i _; rw [show i + s + 1 = i + 1 + s by ring]
  rw [Finset.sum_congr rfl e, h, show n + s = s + n by ring, unrolled_add_n hn, zero_add]
  ring

/-- The average-span identity: the `n` cyclic `r`-spans sum to `r`. -/
lemma sum_rSpan (hn : 0 < n) (r : ℕ) : ∑ i ∈ range n, rSpan a n r i = r := by
  induction r with
  | zero => simp [rSpan]
  | succ r ih =>
    have e : ∀ i ∈ range n, rSpan a n (r + 1) i =
        rSpan a n r i + (unrolled a n (i + r + 1) - unrolled a n (i + r)) := by
      intro i _; unfold rSpan; rw [show i + (r + 1) = i + r + 1 by ring]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih, sum_step hn]
    push_cast; ring

lemma rel_pos (hn : 0 < n) (ha : Function.Injective fun k => Int.fract (a k)) (i l : ℕ)
    (hi : i < n) (hl : l < n) :
    Int.fract (sortedPoint a n ⟨(i + l) % n, Nat.mod_lt _ hn⟩ - sortedPoint a n ⟨i, hi⟩) =
      unrolled a n (i + l) - unrolled a n i := by
  have e1 := u_eq (a := a) hn (i + l)
  have e2 := u_lt (a := a) hn i hi
  have hmono := u_strictMono hn ha
  have h0 : unrolled a n i ≤ unrolled a n (i + l) := hmono.monotone (by omega)
  have h1 : unrolled a n (i + l) < unrolled a n i + 1 := by
    have := hmono (show i + l < i + n * 1 by omega)
    rw [u_add hn] at this; push_cast at this; linarith
  have e3 : sortedPoint a n ⟨(i + l) % n, Nat.mod_lt _ hn⟩ - sortedPoint a n ⟨i, hi⟩ =
      (unrolled a n (i + l) - unrolled a n i) - (((i + l) / n : ℕ) : ℝ) := by
    rw [e1, e2]; ring
  rw [e3, Int.fract_sub_natCast, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]

lemma fract_fract_sub (p x : ℝ) : Int.fract (Int.fract p - x) = Int.fract (p - x) := by
  have : Int.fract p - x = (p - x) - ((⌊p⌋ : ℤ) : ℝ) := by rw [← Int.self_sub_floor]; ring
  rw [this, Int.fract_sub_intCast]


lemma fract_sub_eq (p q : ℝ) : Int.fract (Int.fract p - Int.fract q) = Int.fract (p - q) := by
  rw [fract_fract_sub, show p - Int.fract q = (p - q) + ((⌊q⌋ : ℤ) : ℝ) by
    rw [← Int.self_sub_floor q]; ring, Int.fract_add_intCast]

lemma rSpan_periodic (hn : 0 < n) (i : ℕ) : rSpan a n r (i + n) = rSpan a n r i := by
  unfold rSpan
  rw [show i + n + r = (i + r) + n by ring, unrolled_add_n hn, unrolled_add_n hn]; ring

/-- The forward step length from point `j` (sequence index) by `K` places, at time `N`. -/
noncomputable def Lk (a : ℕ → ℝ) (N K j : ℕ) : ℝ :=
  if h : j < N then unrolled a N (((Tuple.sort (pts a N)).symm ⟨j, h⟩ : ℕ) + K) -
    unrolled a N ((Tuple.sort (pts a N)).symm ⟨j, h⟩ : ℕ) else 0

/-- The forward `K`-step map on sequence indices, at time `N`. -/
noncomputable def Fk (a : ℕ → ℝ) (N K j : ℕ) : ℕ :=
  if h : j < N then ((Tuple.sort (pts a N)) ⟨(((Tuple.sort (pts a N)).symm ⟨j, h⟩ : ℕ) + K) % N,
    Nat.mod_lt _ (by omega)⟩ : ℕ) else 0

lemma Fk_lt {N K j : ℕ} (hj : j < N) : Fk a N K j < N := by
  unfold Fk; rw [dif_pos hj]; exact Fin.is_lt _

lemma Fk_inj {N K j j' : ℕ} (hj : j < N) (hj' : j' < N) (h : Fk a N K j = Fk a N K j') :
    j = j' := by
  unfold Fk at h; rw [dif_pos hj, dif_pos hj'] at h
  set σ := Tuple.sort (pts a N)
  have h1 := σ.injective (Fin.ext h)
  have h2 : (((σ.symm ⟨j, hj⟩ : Fin N) : ℕ) + K) % N = (((σ.symm ⟨j', hj'⟩ : Fin N) : ℕ) + K) % N :=
    congrArg Fin.val h1
  have h3 : ((σ.symm ⟨j, hj⟩ : Fin N) : ℕ) = σ.symm ⟨j', hj'⟩ := by
    have := Nat.ModEq.add_right_cancel' K h2
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt (Fin.is_lt _), Nat.mod_eq_of_lt (Fin.is_lt _)] at this
  have h4 := σ.symm.injective (Fin.ext h3)
  simpa using congrArg Fin.val h4

lemma Fk_pos {N K j : ℕ} (hj : j < N) : ∃ z : ℤ, a (Fk a N K j) = a j + Lk a N K j + z := by
  have hN : 0 < N := by omega
  unfold Fk Lk; rw [dif_pos hj, dif_pos hj]
  set σ := Tuple.sort (pts a N) with hσ
  set i := σ.symm ⟨j, hj⟩ with hi
  have hsi : σ i = ⟨j, hj⟩ := by rw [hi, Equiv.apply_symm_apply]
  have e1 : unrolled a N (i + K) = Int.fract (a (σ ⟨((i : ℕ) + K) % N, Nat.mod_lt _ hN⟩ : ℕ)) +
      (((i : ℕ) + K) / N : ℕ) := by
    rw [u_eq hN]; rfl
  have e2 : unrolled a N i = Int.fract (a j) := by
    rw [u_lt hN i i.is_lt, Fin.eta, sp_eq]
    show Int.fract (a (σ i : ℕ)) = _
    rw [hsi]
  rw [e1, e2]
  show ∃ z : ℤ, a (σ ⟨((i : ℕ) + K) % N, Nat.mod_lt _ hN⟩ : ℕ) = _
  generalize a (σ ⟨((i : ℕ) + K) % N, Nat.mod_lt _ hN⟩ : ℕ) = b
  generalize ((i : ℕ) + K) / N = c
  refine ⟨⌊b⌋ - ⌊a j⌋ - c, ?_⟩
  simp only [← Int.self_sub_floor]
  push_cast; ring

lemma Lk_eq {N K j : ℕ} (hj : j < N) :
    ∃ i < N, Lk a N K j = unrolled a N (i + K) - unrolled a N i :=
  ⟨((Tuple.sort (pts a N)).symm ⟨j, hj⟩ : ℕ), Fin.is_lt _, by unfold Lk; rw [dif_pos hj]⟩

lemma sum_Lk (N K : ℕ) (φ : ℝ → ℝ) :
    ∑ j ∈ range N, φ (Lk a N K j) = ∑ i ∈ range N, φ (unrolled a N (i + K) - unrolled a N i) := by
  rw [Finset.sum_range, Finset.sum_range]
  set σ := Tuple.sort (pts a N)
  have h : ∀ j : Fin N, Lk a N K j =
      unrolled a N ((σ.symm j : ℕ) + K) - unrolled a N (σ.symm j : ℕ) := by
    intro j; unfold Lk; rw [dif_pos j.is_lt]
  simp_rw [h]
  exact Equiv.sum_comp σ.symm (fun i : Fin N => φ (unrolled a N ((i : ℕ) + K) - unrolled a N i))

lemma sum_shift (f : ℕ → ℝ) (hf : ∀ i, f (i + n) = f i) (c : ℕ) :
    ∑ i ∈ range n, f (i + c) = ∑ i ∈ range n, f i := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h1 : ∑ i ∈ range (n + 1), f (i + c) = ∑ i ∈ range n, f (i + c) + f (n + c) :=
      Finset.sum_range_succ _ _
    have h2 : ∑ i ∈ range (n + 1), f (i + c) = ∑ i ∈ range n, f (i + 1 + c) + f (0 + c) :=
      Finset.sum_range_succ' _ _
    rw [← ih]
    have e : ∀ i ∈ range n, f (i + (c + 1)) = f (i + 1 + c) := fun i _ => by
      rw [show i + (c + 1) = i + 1 + c by ring]
    rw [Finset.sum_congr rfl e]
    have : f (n + c) = f (0 + c) := by rw [zero_add, add_comm, hf]
    linarith

/-- Korsky, Lemma 6.1 (integer times): the `kr`-steps deviate in total by at most `k` times
the total deviation of the `r`-spans. -/
lemma L61 (hn : 0 < n) (k : ℕ) :
    ∑ i ∈ range n, |unrolled a n (i + k * r) - unrolled a n i - ((k * r : ℕ) : ℝ) / n| ≤
      k * ∑ i ∈ range n, |rSpan a n r i - r / n| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ∀ i, unrolled a n (i + (k + 1) * r) - unrolled a n i - (((k + 1) * r : ℕ) : ℝ) / n =
        (unrolled a n (i + k * r) - unrolled a n i - ((k * r : ℕ) : ℝ) / n) +
          (rSpan a n r (i + k * r) - r / n) := by
      intro i; unfold rSpan; rw [show i + k * r + r = i + (k + 1) * r by ring]; push_cast; ring
    have hsh := sum_shift (n := n) (fun i => |rSpan a n r i - r / n|)
      (fun i => by simp only [rSpan_periodic hn]) (k * r)
    calc _ ≤ ∑ i ∈ range n, (|unrolled a n (i + k * r) - unrolled a n i - ((k * r : ℕ) : ℝ) / n| +
            |rSpan a n r (i + k * r) - r / n|) := by
          apply Finset.sum_le_sum; intro i _; rw [e]; exact abs_add_le _ _
      _ = _ := Finset.sum_add_distrib
      _ ≤ k * ∑ i ∈ range n, |rSpan a n r i - r / n| + ∑ i ∈ range n, |rSpan a n r i - r / n| := by
          rw [hsh]; linarith [ih]
      _ = _ := by push_cast; ring

lemma dev_sum_zero (hn : 0 < n) : ∑ i ∈ range n, (rSpan a n r i - r / n) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_sub_distrib, sum_rSpan hn, Finset.sum_const, card_range, nsmul_eq_mul]
  field_simp; ring

lemma abs_eq_neg (y : ℝ) : |y| = 2 * max (-y) 0 + y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
  · rw [abs_of_neg h, max_eq_left (by linarith)]; ring

lemma abs_eq_pos (y : ℝ) : |y| = 2 * max y 0 - y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h, max_eq_left h]; ring
  · rw [abs_of_neg h, max_eq_right h.le]; ring

/-- Under `r - n m_n ≤ A`, the total deviation of the spans is at most `2A`. -/
lemma dev_of_min (hn : 0 < n) (A : ℝ) (hA : 0 ≤ A) (h : (r : ℝ) - n * minSpan a n r ≤ A) :
    ∑ i ∈ range n, |rSpan a n r i - r / n| ≤ 2 * A := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : ∀ i ∈ range n, max (-(rSpan a n r i - r / n)) 0 ≤ A / n := by
    intro i _
    have h1 := min_le_rSpan (a := a) (r := r) hn i
    have h2 : (r - A) / n ≤ minSpan a n r := by rw [div_le_iff₀ hnR]; linarith
    apply max_le
    · have : (r : ℝ) / n - (r - A) / n = A / n := by ring
      linarith
    · positivity
  simp_rw [abs_eq_neg (rSpan a n r _ - r / n)]
  rw [Finset.sum_add_distrib, dev_sum_zero hn, ← Finset.mul_sum]
  have := Finset.sum_le_sum hb
  rw [Finset.sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ hnR.ne'] at this
  linarith

/-- Under `n M_n - r ≤ A`, the total deviation of the spans is at most `2A`. -/
lemma dev_of_max (hn : 0 < n) (A : ℝ) (hA : 0 ≤ A) (h : (n : ℝ) * maxSpan a n r ≤ r + A) :
    ∑ i ∈ range n, |rSpan a n r i - r / n| ≤ 2 * A := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : ∀ i ∈ range n, max (rSpan a n r i - r / n) 0 ≤ A / n := by
    intro i _
    have h1 := rSpan_le_max (a := a) (r := r) hn i
    have h2 : maxSpan a n r ≤ (r + A) / n := by rw [le_div_iff₀ hnR]; linarith
    apply max_le
    · have : (r + A) / n - (r : ℝ) / n = A / n := by ring
      linarith
    · positivity
  simp_rw [abs_eq_pos (rSpan a n r _ - r / n)]
  rw [Finset.sum_sub_distrib, dev_sum_zero hn, ← Finset.mul_sum]
  have := Finset.sum_le_sum hb
  rw [Finset.sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ hnR.ne'] at this
  linarith

/-- Fewer than `r` points lie strictly inside the forward `r`-step arc. -/
lemma O1 (hN : 0 < n) (ha : Function.Injective fun k => Int.fract (a k)) {j : ℕ} (hj : j < n) :
    ((range n).filter (fun j' => 0 < Int.fract (a j' - a j) ∧
      Int.fract (a j' - a j) < Lk a n r j)).card ≤ r - 1 := by
  set σ := Tuple.sort (pts a n) with hσ
  set i := σ.symm ⟨j, hj⟩ with hi
  have hLi : Lk a n r j = unrolled a n (i + r) - unrolled a n i := by unfold Lk; rw [dif_pos hj]
  have hsi : σ i = ⟨j, hj⟩ := by rw [hi, Equiv.apply_symm_apply]
  calc _ ≤ ((Ioo 0 r).image fun l => ((σ ⟨((i : ℕ) + l) % n, Nat.mod_lt _ hN⟩ : Fin n) : ℕ)).card :=
        card_le_card ?_
    _ ≤ (Ioo 0 r).card := card_image_le
    _ = r - 1 := by simp
  intro j' hj'
  rw [mem_filter, mem_range] at hj'
  obtain ⟨hj'N, h0, h1⟩ := hj'
  rw [mem_image]
  set i' := σ.symm ⟨j', hj'N⟩ with hi'
  have hsi' : σ i' = ⟨j', hj'N⟩ := by rw [hi', Equiv.apply_symm_apply]
  set l := ((i' : ℕ) + n - i) % n with hl
  have hln : l < n := Nat.mod_lt _ hN
  have hil : (⟨((i : ℕ) + l) % n, Nat.mod_lt _ hN⟩ : Fin n) = i' := by
    apply Fin.ext
    simp only [hl, Nat.add_mod_mod]
    rw [show (i : ℕ) + ((i' : ℕ) + n - i) = i' + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt i'.is_lt]
  have hrel := rel_pos hN ha i l i.is_lt hln
  rw [hil, Fin.eta] at hrel
  have hfr : Int.fract (a j' - a j) = unrolled a n (i + l) - unrolled a n i := by
    rw [← hrel, sp_eq, sp_eq, hsi, hsi', fract_sub_eq]
  rw [hfr] at h0 h1
  rw [hLi] at h1
  refine ⟨l, ?_, by rw [hil, hsi']⟩
  rw [mem_Ioo]
  have hmono := u_strictMono hN ha
  constructor
  · rcases Nat.eq_zero_or_pos l with h | h
    · rw [h, add_zero] at h0; simp at h0
    · exact h
  · have : unrolled a n (i + l) < unrolled a n (i + r) := by linarith
    have := hmono.lt_iff_lt.1 this; omega

lemma Lk_nonneg (hN : 0 < n) (ha : Function.Injective fun k => Int.fract (a k)) {K j : ℕ}
    (hj : j < n) : 0 ≤ Lk a n K j := by
  obtain ⟨i, _, hi⟩ := Lk_eq (a := a) (K := K) hj
  rw [hi]
  have := (u_strictMono hN ha).monotone (show i ≤ i + K by omega); linarith

/-- Combinatorial core of Korsky's Lemma 6.3. -/
lemma L63_comb (hN : 0 < n) (ha : Function.Injective fun k => Int.fract (a k)) (hr : 1 ≤ r)
    (x l : ℝ) (hl : l < 1) :
    max (N a n x l - r) 0 ≤ ∑ j ∈ range n, ind (a j) x (l - Lk a n r j) := by
  classical
  set Q := (range n).filter (fun j => 0 < Int.fract (a j - x) ∧ Int.fract (a j - x) ≤ l) with hQ
  set Q' := (range n).filter (fun j => 0 < Int.fract (a j - x) ∧
    Int.fract (a j - x) ≤ l - Lk a n r j) with hQ'
  have hN1 : N a n x l = Q.card := by
    unfold N ind; rw [Finset.sum_boole]
  have hS : ∑ j ∈ range n, ind (a j) x (l - Lk a n r j) = Q'.card := by
    unfold ind; rw [Finset.sum_boole]
  rw [hN1, hS]
  have hsub : Q' ⊆ Q := by
    intro j hj
    rw [hQ', mem_filter] at hj
    rw [hQ, mem_filter]
    exact ⟨hj.1, hj.2.1, by linarith [hj.2.2, Lk_nonneg hN ha (K := r) (mem_range.1 hj.1)]⟩
  set g : ℕ → ℕ := fun j => (Q.filter (fun j' => Int.fract (a j - x) < Int.fract (a j' - x))).card
    with hg
  have key : ∀ j1 ∈ Q, ∀ j2 ∈ Q, Int.fract (a j1 - x) < Int.fract (a j2 - x) → g j2 < g j1 := by
    intro j1 _ j2 hj2 hlt
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨j2, mem_filter.2 ⟨hj2, hlt⟩, fun h => lt_irrefl _ (mem_filter.1 h).2⟩
    · intro j' hj'
      rw [mem_filter] at hj' ⊢
      exact ⟨hj'.1, lt_trans hlt hj'.2⟩
  have hcard : (Q \ Q').card ≤ r := by
    have hmaps : Set.MapsTo g (Q \ Q' : Finset ℕ) (range r : Finset ℕ) := by
      intro j hj
      rw [coe_sdiff, Set.mem_sdiff, mem_coe, mem_coe] at hj
      obtain ⟨hjQ, hjQ'⟩ := hj
      have hjQ2 := hjQ
      rw [hQ, mem_filter, mem_range] at hjQ2
      obtain ⟨hjn, hw0, hwl⟩ := hjQ2
      have hgt : l < Int.fract (a j - x) + Lk a n r j := by
        by_contra hc; push Not at hc
        exact hjQ' (by rw [hQ', mem_filter]; exact ⟨mem_range.2 hjn, hw0, by linarith⟩)
      rw [mem_coe, mem_range]
      have hle : g j ≤ r - 1 := by
        refine le_trans (card_le_card ?_) (O1 hN ha hjn)
        intro j' hj'
        rw [mem_filter, hQ, mem_filter, mem_range] at hj'
        obtain ⟨⟨hj'n, hw'0, hw'l⟩, hlt⟩ := hj'
        rw [mem_filter, mem_range]
        have hfr : Int.fract (a j' - a j) = Int.fract (a j' - x) - Int.fract (a j - x) := by
          rw [Int.fract_eq_iff]
          have t1 := Int.fract_lt_one (a j' - x)
          have t2 := Int.fract_nonneg (a j - x)
          refine ⟨by linarith, by linarith, ⌊a j' - x⌋ - ⌊a j - x⌋, ?_⟩
          rw [← Int.self_sub_floor (a j' - x), ← Int.self_sub_floor (a j - x)]; push_cast; ring
        rw [hfr]
        exact ⟨hj'n, by linarith, by linarith⟩
      omega
    have hinj : Set.InjOn g (Q \ Q' : Finset ℕ) := by
      intro j1 hj1 j2 hj2 hgg
      rw [coe_sdiff, Set.mem_sdiff, mem_coe] at hj1 hj2
      by_contra hne
      have hneq : Int.fract (a j1 - x) ≠ Int.fract (a j2 - x) := by
        intro heq
        obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 heq
        have : Int.fract (a j1) = Int.fract (a j2) := Int.fract_eq_fract.2 ⟨z, by linarith⟩
        exact hne (ha this)
      rcases lt_or_gt_of_ne hneq with h | h
      · have := key j1 hj1.1 j2 hj2.1 h; omega
      · have := key j2 hj2.1 j1 hj1.1 h; omega
    calc (Q \ Q').card ≤ (range r).card := card_le_card_of_injOn g hmaps hinj
      _ = r := card_range r
  have : Q.card ≤ Q'.card + r := by
    have := card_sdiff_add_card_eq_card hsub; omega
  apply max_le
  · have : (Q.card : ℝ) ≤ Q'.card + r := by exact_mod_cast this
    linarith
  · positivity

/-- Korsky, Lemma 6.3 (integer times): `Z_m(r) ≤ A`. -/
lemma L63 (hN : 0 < n) (ha : Function.Injective fun k => Int.fract (a k)) (hr : 1 ≤ r)
    (hrn : r < n) (A : ℝ) (hdev : ∑ i ∈ range n, |rSpan a n r i - r / n| ≤ 2 * A) :
    Z a n r ≤ A := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hN
  have hl1 : (r : ℝ) / n < 1 := by
    rw [div_lt_one hnR]; exact_mod_cast hrn
  have hgood : ∀ j ∈ range n, Good (fun x => ind (a j) x ((r : ℝ) / n - Lk a n r j)) :=
    fun j _ => good_ind _ _
  unfold Z
  calc ∫ x in (0:ℝ)..1, max (N a n x (r / n) - r) 0
      ≤ ∫ x in (0:ℝ)..1, ∑ j ∈ range n, ind (a j) x ((r : ℝ) / n - Lk a n r j) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact ((good_N a n _).sub (good_const _)).max0.ii 0 1
        · exact (good_sum _ _ hgood).ii 0 1
        · intro x _; exact L63_comb hN ha hr x _ hl1
    _ = ∑ j ∈ range n, ∫ x in (0:ℝ)..1, ind (a j) x ((r : ℝ) / n - Lk a n r j) :=
        intervalIntegral.integral_finsetSum (fun j hj => (hgood j hj).ii 0 1)
    _ ≤ ∑ j ∈ range n, max ((r : ℝ) / n - Lk a n r j) 0 := by
        apply Finset.sum_le_sum; intro j hj
        exact int_ind_le _ _ (by linarith [Lk_nonneg hN ha (K := r) (mem_range.1 hj)])
    _ = ∑ i ∈ range n, max (-(rSpan a n r i - r / n)) 0 := by
        rw [sum_Lk n r (fun L => max ((r : ℝ) / n - L) 0)]
        apply Finset.sum_congr rfl; intro i _; unfold rSpan; congr 1; ring
    _ ≤ A := by
        have h := hdev
        simp_rw [abs_eq_neg (rSpan a n r _ - r / n)] at h
        rw [Finset.sum_add_distrib, dev_sum_zero hN, ← Finset.mul_sum] at h
        linarith

end sorted


-- Part C: Korsky's Lemma 6.2 (averaged comparison), at integer times

section L62

open Erdos1221

variable {a : ℕ → ℝ} {r : ℕ} {A : ℝ}

/-- The standing hypothesis at all times `N ≥ n₀`: total deviation of spans at most `2A`. -/
def SpanDev (a : ℕ → ℝ) (r : ℕ) (A : ℝ) (n₀ : ℕ) : Prop :=
  0 < n₀ ∧ ∀ N, n₀ ≤ N → ∑ i ∈ range N, |rSpan a N r i - r / N| ≤ 2 * A

lemma sum_Lk_dev {n₀ N : ℕ} (hyp : SpanDev a r A n₀) (hN : n₀ ≤ N) (k : ℕ) :
    ∑ j ∈ range N, |Lk a N (k * r) j - ((k * r : ℕ) : ℝ) / N| ≤ k * (2 * A) := by
  have hN0 : 0 < N := lt_of_lt_of_le hyp.1 hN
  rw [sum_Lk N (k * r) (fun L => |L - ((k * r : ℕ) : ℝ) / N|)]
  exact le_trans (L61 hN0 k) (mul_le_mul_of_nonneg_left (hyp.2 N hN) (Nat.cast_nonneg k))

/-- The injection `B_s ∘ F_n : P_n → P_s` with its displacement. -/
lemma inj_shift {n₀ n s : ℕ} (hyp : SpanDev a r A n₀) (hn : n₀ ≤ n) (hs : n ≤ s) (k : ℕ) :
    ∃ τ : ℕ → ℕ, ∃ η : ℕ → ℝ, (∀ j < n, τ j < s) ∧
      (∀ j < n, ∀ j' < n, τ j = τ j' → j = j') ∧
      (∀ j < n, ∃ z : ℤ, a (τ j) =
        a j + (((k * r : ℕ) : ℝ) / n - ((k * r : ℕ) : ℝ) / s) + η j + z) ∧
      ∑ j ∈ range n, |η j| ≤ 4 * k * A := by
  set K := k * r with hK
  have himg : (range s).image (Fk a s K) = range s := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy; rw [mem_image] at hy; obtain ⟨x, hx, rfl⟩ := hy
      exact mem_range.2 (Fk_lt (mem_range.1 hx))
    · rw [card_image_of_injOn]
      intro x hx y hy h; exact Fk_inj (mem_range.1 hx) (mem_range.1 hy) h
  have hsurj : ∀ y, y < s → ∃ x, x < s ∧ Fk a s K x = y := by
    intro y hy
    have : y ∈ (range s).image (Fk a s K) := by rw [himg]; exact mem_range.2 hy
    obtain ⟨x, hx, h⟩ := mem_image.1 this
    exact ⟨x, mem_range.1 hx, h⟩
  choose! G hG using hsurj
  have hFn : ∀ j < n, Fk a n K j < s := fun j hj => lt_of_lt_of_le (Fk_lt hj) hs
  refine ⟨fun j => G (Fk a n K j),
    fun j => (Lk a n K j - (K : ℝ) / n) - (Lk a s K (G (Fk a n K j)) - (K : ℝ) / s), ?_, ?_, ?_, ?_⟩
  · intro j hj; exact (hG _ (hFn j hj)).1
  · intro j hj j' hj' h
    have h1 := (hG _ (hFn j hj)).2
    have h2 := (hG _ (hFn j' hj')).2
    simp only at h
    rw [h] at h1
    exact Fk_inj hj hj' (h1.symm.trans h2)
  · intro j hj
    obtain ⟨z1, hz1⟩ := Fk_pos (a := a) (K := K) (hG _ (hFn j hj)).1
    obtain ⟨z2, hz2⟩ := Fk_pos (a := a) (N := n) (K := K) hj
    rw [(hG _ (hFn j hj)).2] at hz1
    refine ⟨z2 - z1, ?_⟩
    push_cast
    linarith
  · have e1 := sum_Lk_dev hyp hn k
    have e2 := sum_Lk_dev hyp (le_trans hn hs) k
    have hinjG : ∀ j ∈ range n, ∀ j' ∈ range n, G (Fk a n K j) = G (Fk a n K j') → j = j' := by
      intro j hj j' hj' h
      have h1 := (hG _ (hFn j (mem_range.1 hj))).2
      have h2 := (hG _ (hFn j' (mem_range.1 hj'))).2
      rw [h] at h1
      exact Fk_inj (mem_range.1 hj) (mem_range.1 hj') (h1.symm.trans h2)
    have e3 : ∑ j ∈ range n, |Lk a s K (G (Fk a n K j)) - (K : ℝ) / s| ≤
        ∑ j ∈ range s, |Lk a s K j - (K : ℝ) / s| := by
      rw [← Finset.sum_image (g := fun j => G (Fk a n K j))
        (f := fun y => |Lk a s K y - (K : ℝ) / s|) hinjG]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy; obtain ⟨j, hj, rfl⟩ := mem_image.1 hy
        exact mem_range.2 (hG _ (hFn j (mem_range.1 hj))).1
      · intro _ _ _; exact abs_nonneg _
    calc ∑ j ∈ range n, |(Lk a n K j - (K : ℝ) / n) - (Lk a s K (G (Fk a n K j)) - (K : ℝ) / s)|
        ≤ ∑ j ∈ range n, (|Lk a n K j - (K : ℝ) / n| +
            |Lk a s K (G (Fk a n K j)) - (K : ℝ) / s|) :=
          Finset.sum_le_sum (fun j _ => abs_sub _ _)
      _ = _ := Finset.sum_add_distrib
      _ ≤ k * (2 * A) + k * (2 * A) := add_le_add e1 (le_trans e3 e2)
      _ = 4 * k * A := by ring

/-- Realizing a shift `u` by an integer time `s`. -/
lemma realize (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m) (κ u : ℝ) (hκ : 0 < κ) (hu0 : 0 ≤ u)
    (hu : u ≤ κ / n - κ / m) :
    ∃ s : ℕ, n ≤ s ∧ s ≤ m ∧ 0 ≤ κ / n - κ / s - u ∧ κ / n - κ / s - u ≤ κ / n ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hn hnm)
  set d := κ / n - u with hd
  have hdm : κ / m ≤ d := by linarith
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hdm
  set X := κ / d with hX
  have hXn : (n : ℝ) ≤ X := by
    rw [hX, le_div_iff₀ hd0, hd, mul_sub, mul_div_cancel₀ _ hnR.ne']
    nlinarith
  have hXm : X ≤ m := by
    rw [hX, div_le_iff₀ hd0]
    have := mul_le_mul_of_nonneg_left hdm hmR.le
    rw [mul_div_cancel₀ _ hmR.ne'] at this; linarith
  have hX0 : 0 < X := lt_of_lt_of_le hnR hXn
  refine ⟨⌈X⌉₊, ?_, Nat.ceil_le.2 hXm, ?_, ?_⟩
  · exact_mod_cast le_trans hXn (Nat.le_ceil X)
  · have hs := Nat.le_ceil X
    have : κ / (⌈X⌉₊ : ℝ) ≤ κ / X := div_le_div_of_nonneg_left hκ.le hX0 hs
    have e : κ / X = d := by rw [hX]; field_simp
    linarith
  · have hs := Nat.le_ceil X
    have hs1 := Nat.ceil_lt_add_one hX0.le
    have hsp : (0 : ℝ) < ⌈X⌉₊ := lt_of_lt_of_le hX0 hs
    have e : κ / n - κ / (⌈X⌉₊ : ℝ) - u = κ * ((⌈X⌉₊ : ℝ) - X) / (X * ⌈X⌉₊) := by
      have : d = κ / X := by rw [hX]; field_simp
      rw [show κ / n - κ / (⌈X⌉₊ : ℝ) - u = d - κ / (⌈X⌉₊ : ℝ) by ring, this]
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : κ * ((⌈X⌉₊ : ℝ) - X) ≤ κ := by nlinarith
    have h2 : (n : ℝ) ^ 2 ≤ X * ⌈X⌉₊ := by nlinarith
    nlinarith

lemma inj_u {n₀ n m : ℕ} (hyp : SpanDev a r A n₀) (k : ℕ) (hκ : 1 ≤ k * r) (hn : n₀ ≤ n)
    (hnm : n ≤ m) (u : ℝ) (hu0 : 0 ≤ u)
    (hu : u ≤ ((k * r : ℕ) : ℝ) / n - ((k * r : ℕ) : ℝ) / m) :
    ∃ τ : ℕ → ℕ, ∃ η : ℕ → ℝ, (∀ j < n, τ j < m) ∧
      (∀ j < n, ∀ j' < n, τ j = τ j' → j = j') ∧
      (∀ j < n, ∃ z : ℤ, a (τ j) = a j + u + η j + z) ∧
      ∑ j ∈ range n, |η j| ≤ 4 * k * A + ((k * r : ℕ) : ℝ) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le hyp.1 hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hκR : (0 : ℝ) < ((k * r : ℕ) : ℝ) := by exact_mod_cast hκ
  obtain ⟨s, hns, hsm, he0, he1⟩ := realize n m hn0 hnm _ u hκR hu0 hu
  obtain ⟨τ, η, h1, h2, h3, h4⟩ := inj_shift hyp hn hns k
  set e := ((k * r : ℕ) : ℝ) / n - ((k * r : ℕ) : ℝ) / s - u with he
  refine ⟨τ, fun j => η j + e, fun j hj => lt_of_lt_of_le (h1 j hj) hsm, h2, ?_, ?_⟩
  · intro j hj
    obtain ⟨z, hz⟩ := h3 j hj
    exact ⟨z, by rw [hz, he]; ring⟩
  · calc ∑ j ∈ range n, |η j + e| ≤ ∑ j ∈ range n, (|η j| + e) :=
          Finset.sum_le_sum (fun j _ => by
            have := abs_add_le (η j) e; rw [abs_of_nonneg he0] at this; exact this)
      _ = ∑ j ∈ range n, |η j| + n * e := by
          rw [Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
      _ ≤ 4 * k * A + n * (((k * r : ℕ) : ℝ) / n ^ 2) :=
          add_le_add h4 (mul_le_mul_of_nonneg_left he1 hnR.le)
      _ = 4 * k * A + ((k * r : ℕ) : ℝ) / n := by field_simp

lemma count_cmp {n m : ℕ} (τ : ℕ → ℕ) (η : ℕ → ℝ) (u : ℝ) (hτ : ∀ j < n, τ j < m)
    (hinj : ∀ j < n, ∀ j' < n, τ j = τ j' → j = j')
    (hpos : ∀ j < n, ∃ z : ℤ, a (τ j) = a j + u + η j + z) (x l : ℝ) :
    N a n x l ≤ N a m (x + u) l + ∑ j ∈ range n, |ind (a j) x l - ind (a j + η j) x l| := by
  have h1 : ∀ j ∈ range n, ind (a j) x l ≤
      ind (a (τ j)) (x + u) l + |ind (a j) x l - ind (a j + η j) x l| := by
    intro j hj
    obtain ⟨z, hz⟩ := hpos j (mem_range.1 hj)
    have : ind (a (τ j)) (x + u) l = ind (a j + η j) x l := by
      rw [ind_x_add, ind_congr z (show a (τ j) - u = (a j + η j) + z by rw [hz]; ring)]
    rw [this]; linarith [le_abs_self (ind (a j) x l - ind (a j + η j) x l)]
  have h2 : ∑ j ∈ range n, ind (a (τ j)) (x + u) l ≤ N a m (x + u) l := by
    rw [← Finset.sum_image (g := τ) (f := fun y => ind (a y) (x + u) l)
      (fun j hj j' hj' h => hinj j (mem_range.1 hj) j' (mem_range.1 hj') h)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy; obtain ⟨j, hj, rfl⟩ := mem_image.1 hy
      exact mem_range.2 (hτ j (mem_range.1 hj))
    · intro _ _ _; exact ind_nonneg _ _ _
  unfold N
  calc ∑ j ∈ range n, ind (a j) x l
      ≤ ∑ j ∈ range n, (ind (a (τ j)) (x + u) l + |ind (a j) x l - ind (a j + η j) x l|) :=
        Finset.sum_le_sum h1
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := by unfold N at h2; linarith

lemma int_R (n : ℕ) (η : ℕ → ℝ) (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) :
    ∫ x in (0:ℝ)..1, ∑ j ∈ range n, |ind (a j) x l - ind (a j + η j) x l| ≤
      2 * ∑ j ∈ range n, |η j| := by
  rw [intervalIntegral.integral_finsetSum
    (fun j _ => ((good_ind _ l).sub (good_ind _ l)).abs.ii 0 1), Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => int_ind_diff _ _ l hl0 hl1)

lemma good_R (n : ℕ) (η : ℕ → ℝ) (l : ℝ) :
    Good (fun x => ∑ j ∈ range n, |ind (a j) x l - ind (a j + η j) x l|) :=
  good_sum _ _ (fun j _ => ((good_ind _ l).sub (good_ind _ l)).abs)

lemma Zshift_periodic (m : ℕ) (l E : ℝ) :
    Function.Periodic (fun x => max (N a m x l - E) 0) 1 := by
  intro x; show max (N a m (x + 1) l - E) 0 = max (N a m x l - E) 0
  have h := N_periodic a m l x
  simp only at h
  rw [h]

/-- Lemma 6.2 before the limit in the mesh `P`. -/
lemma L62_PL {n₀ n m : ℕ} (hyp : SpanDev a r A n₀) (k : ℕ) (hκ : 1 ≤ k * r) (hn : n₀ ≤ n)
    (hnm : n ≤ m) (D : ℝ) (hD : 0 < D) (hDn : D / n < 1) (P L : ℕ) (hP : 1 ≤ P) (hL : 1 ≤ L)
    (hLδ : (L : ℝ) * (D / n / P) ≤ ((k * r : ℕ) : ℝ) / n - ((k * r : ℕ) : ℝ) / m)
    (hLδ1 : (L : ℝ) * (D / n / P) < 1) :
    Z a n D ≤ ((P : ℝ) / L) * Z a m (m * (L * (D / n / P))) + (m - n) * D / n +
      (8 * k * A + 2 * ((k * r : ℕ) : ℝ) / n) := by
  have hn0 : 0 < n := lt_of_lt_of_le hyp.1 hn
  have hm0 : 0 < m := lt_of_lt_of_le hn0 hnm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  set lam := D / n with hlam
  set δ := lam / P with hδ
  set ℓ := (L : ℝ) * δ with hℓ
  set E := (m : ℝ) * ℓ with hE
  set κ := ((k * r : ℕ) : ℝ) with hκdef
  have hlam0 : 0 < lam := by positivity
  have hδ0 : 0 < δ := by positivity
  have hPδ : (P : ℝ) * δ = lam := by rw [hδ]; field_simp
  have hex : ∀ j : ℕ, j < L → ∃ τ : ℕ → ℕ, ∃ η : ℕ → ℝ, (∀ i < n, τ i < m) ∧
      (∀ i < n, ∀ i' < n, τ i = τ i' → i = i') ∧
      (∀ i < n, ∃ z : ℤ, a (τ i) = a i + j * δ + η i + z) ∧
      ∑ i ∈ range n, |η i| ≤ 4 * k * A + κ / n := by
    intro j hj
    have hjL : (j : ℝ) ≤ L := by exact_mod_cast hj.le
    exact inj_u hyp k hκ hn hnm (j * δ) (by positivity)
      (le_trans (mul_le_mul_of_nonneg_right hjL hδ0.le) hLδ)
  choose! τ η hτ hinj hpos hsum using hex
  set R : ℕ → ℝ → ℝ := fun j x => ∑ i ∈ range n, |ind (a i) x lam - ind (a i + η j i) x lam|
    with hR
  have hpt : ∀ x, max (N a n x lam - D) 0 ≤
      (1 / (L : ℝ)) * ∑ i ∈ range P, max (N a m (x + i * δ) ℓ - E) 0 + (m - n) * D / n +
        (1 / (L : ℝ)) * ∑ j ∈ range L, R j x := by
    intro x
    have h1 : ∀ j ∈ range L, N a n x lam ≤ N a m (x + j * δ) lam + R j x := fun j hj =>
      count_cmp (τ j) (η j) (j * δ) (hτ j (mem_range.1 hj)) (hinj j (mem_range.1 hj))
        (hpos j (mem_range.1 hj)) x lam
    have h2 : (L : ℝ) * N a n x lam ≤
        ∑ j ∈ range L, N a m (x + j * δ) lam + ∑ j ∈ range L, R j x := by
      rw [← Finset.sum_add_distrib]
      have := Finset.sum_le_sum h1
      rw [Finset.sum_const, card_range, nsmul_eq_mul] at this
      exact this
    have hconv := N_conv a m x δ hδ0.le P L (by rw [hPδ]; exact hDn) hLδ1
    rw [hPδ] at hconv
    rw [hconv] at h2
    have h3 : ∑ i ∈ range P, (N a m (x + i * δ) ℓ - E) ≤
        ∑ i ∈ range P, max (N a m (x + i * δ) ℓ - E) 0 :=
      Finset.sum_le_sum (fun i _ => le_max_left _ _)
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul] at h3
    have hPE : (P : ℝ) * E = L * (m * D / n) := by
      rw [hE, hℓ, hδ, hlam]; field_simp
    have hRnn : 0 ≤ ∑ j ∈ range L, R j x :=
      Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
    have hMnn : 0 ≤ ∑ i ∈ range P, max (N a m (x + i * δ) ℓ - E) 0 :=
      Finset.sum_nonneg (fun i _ => le_max_right _ _)
    have hc : 0 ≤ (m - n) * D / n := by
      apply div_nonneg _ hnR.le; exact mul_nonneg (by linarith) hD.le
    set M := ∑ i ∈ range P, max (N a m (x + i * δ) ℓ - E) 0 with hM
    set Rs := ∑ j ∈ range L, R j x with hRs
    rw [← hℓ] at h2
    have h4 : (L : ℝ) * N a n x lam ≤ M + L * (m * D / n) + Rs := by linarith
    have h5 : N a n x lam ≤ (1 / (L : ℝ)) * M + m * D / n + (1 / (L : ℝ)) * Rs := by
      rw [show (1 / (L : ℝ)) * M + m * D / n + (1 / (L : ℝ)) * Rs =
        (M + L * (m * D / n) + Rs) / L by field_simp]
      rw [le_div_iff₀ hLR]; linarith
    have h6 : (m - n) * D / n = m * D / n - D := by field_simp
    apply max_le
    · rw [h6]; linarith
    · positivity
  have hgR : ∀ j, Good (R j) := fun j => good_R n (η j) lam
  have hg1 : Good (fun x => (1 / (L : ℝ)) * ∑ i ∈ range P, max (N a m (x + i * δ) ℓ - E) 0) :=
    (good_sum _ _ (fun i _ => (((good_N a m ℓ).sub (good_const E)).max0).comp_add _)).mul_const _
  have hg3 : Good (fun x => (1 / (L : ℝ)) * ∑ j ∈ range L, R j x) :=
    (good_sum _ _ (fun j _ => hgR j)).mul_const _
  have hint1 : ∫ x in (0:ℝ)..1, (1 / (L : ℝ)) * ∑ i ∈ range P, max (N a m (x + i * δ) ℓ - E) 0 =
      ((P : ℝ) / L) * Z a m E := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      (fun i _ => ((((good_N a m ℓ).sub (good_const E)).max0).comp_add _).ii 0 1)]
    have : ∀ i ∈ range P, ∫ x in (0:ℝ)..1, max (N a m (x + i * δ) ℓ - E) 0 = Z a m E := by
      intro i _
      rw [int_trans (fun x => max (N a m x ℓ - E) 0) (Zshift_periodic m ℓ E)]
      unfold Z
      rw [show E / m = ℓ by rw [hE]; field_simp]
    rw [Finset.sum_congr rfl this, Finset.sum_const, card_range, nsmul_eq_mul]
    ring
  have hint3 : ∫ x in (0:ℝ)..1, (1 / (L : ℝ)) * ∑ j ∈ range L, R j x ≤
      8 * k * A + 2 * κ / n := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      (fun j _ => (hgR j).ii 0 1)]
    have : ∀ j ∈ range L, ∫ x in (0:ℝ)..1, R j x ≤ 8 * k * A + 2 * κ / n := by
      intro j hj
      have := int_R (a := a) n (η j) lam hlam0.le hDn
      have h2 := hsum j (mem_range.1 hj)
      simp only [hR]
      have : 2 * (4 * k * A + κ / n) = 8 * k * A + 2 * κ / n := by ring
      linarith
    have hs := Finset.sum_le_sum this
    rw [Finset.sum_const, card_range, nsmul_eq_mul] at hs
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hLR]
    linarith
  unfold Z
  calc ∫ x in (0:ℝ)..1, max (N a n x (D / n) - D) 0
      ≤ ∫ x in (0:ℝ)..1, ((1 / (L : ℝ)) * ∑ i ∈ range P, max (N a m (x + i * δ) ℓ - E) 0 +
          (m - n) * D / n + (1 / (L : ℝ)) * ∑ j ∈ range L, R j x) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact ((good_N a n _).sub (good_const D)).max0.ii 0 1
        · exact ((hg1.add (good_const _)).add hg3).ii 0 1
        · intro x _; exact hpt x
    _ = ((P : ℝ) / L) * Z a m E + (m - n) * D / n +
          ∫ x in (0:ℝ)..1, (1 / (L : ℝ)) * ∑ j ∈ range L, R j x := by
        rw [intervalIntegral.integral_add ((hg1.add (good_const _)).ii 0 1) (hg3.ii 0 1),
          intervalIntegral.integral_add (hg1.ii 0 1) ((good_const _).ii 0 1), hint1]
        simp
    _ ≤ _ := by
        unfold Z
        linarith

/-- Korsky, Lemma 6.2 (integer times, exact target scale `T`). -/
lemma L62 {n₀ n m : ℕ} (hyp : SpanDev a r A n₀) (k : ℕ) (hκ : 1 ≤ k * r) (hn : n₀ ≤ n)
    (hnm : n ≤ m) (D T : ℝ) (hD : 0 < D) (hDn : D / n < 1) (hT : 0 < T)
    (hTn : T * n < ((k * r : ℕ) : ℝ) * (m - n)) (hκn : ((k * r : ℕ) : ℝ) / n < 1) :
    Z a n D ≤ (m * D / (n * T)) * Z a m T + (m - n) * D / n +
      (8 * k * A + 2 * ((k * r : ℕ) : ℝ) / n) := by
  have hn0 : 0 < n := lt_of_lt_of_le hyp.1 hn
  have hm0 : 0 < m := lt_of_lt_of_le hn0 hnm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  set κ := ((k * r : ℕ) : ℝ) with hκdef
  set lam := D / n with hlam
  have hlam0 : 0 < lam := by positivity
  set gap := κ / n - κ / m - T / m with hgap
  have hgap0 : 0 < gap := by
    have : gap = (κ * (m - n) - T * n) / (n * m) := by rw [hgap]; field_simp; try ring
    rw [this]; apply div_pos (by linarith) (by positivity)
  set B := (m * D / (n * T)) * Z a m T + (m - n) * D / n + (8 * k * A + 2 * κ / n) with hB
  by_contra hcon
  push Not at hcon
  set ε := Z a n D - B with hε
  have hε0 : 0 < ε := by linarith
  obtain ⟨P, hP⟩ := exists_nat_gt (1 + lam / gap + (m * lam) ^ 2 / (T * ε))
  have hP1 : 1 ≤ P := by
    have : (1 : ℝ) < P := by
      have : 0 ≤ lam / gap + (m * lam) ^ 2 / (T * ε) := by positivity
      linarith
    exact_mod_cast this.le
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP1
  set δ := lam / P with hδ
  have hδ0 : 0 < δ := by positivity
  have hδgap : δ < gap := by
    rw [hδ, div_lt_iff₀ hPR]
    have : lam / gap < P := by
      have : 0 ≤ (m * lam) ^ 2 / (T * ε) := by positivity
      linarith
    rw [div_lt_iff₀ hgap0] at this; linarith
  set L := ⌈T / (m * δ)⌉₊ with hLdef
  have hq0 : 0 < T / (m * δ) := by positivity
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hq0).ne'
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hLge : T / (m * δ) ≤ L := Nat.le_ceil _
  have hLlt : (L : ℝ) < T / (m * δ) + 1 := Nat.ceil_lt_add_one hq0.le
  have hEge : T ≤ m * (L * δ) := by
    rw [div_le_iff₀ (by positivity)] at hLge; linarith
  have hElt : m * (L * δ) < T + m * δ := by
    have := mul_lt_mul_of_pos_right hLlt (show (0:ℝ) < m * δ by positivity)
    rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul] at this; linarith
  have hLδ : (L : ℝ) * δ ≤ κ / n - κ / m := by
    have : (L : ℝ) * δ < T / m + δ := by
      rw [div_add' _ _ _ hmR.ne', lt_div_iff₀ hmR]; linarith
    linarith
  have hκm : 0 ≤ κ / m := by positivity
  have hLδ1 : (L : ℝ) * δ < 1 := by linarith
  have h1 := L62_PL hyp k hκ hn hnm D hD hDn P L hP1 hL1 hLδ hLδ1
  have h2 := Z_robust a m hm0 T (m * (L * δ)) hT hEge
    (by rw [show (m : ℝ) * (L * δ) / m = L * δ by field_simp]; exact hLδ1)
  have hPL : (P : ℝ) / L = m * lam / (m * (L * δ)) := by
    rw [hδ]; field_simp
  have hPL2 : (P : ℝ) / L ≤ m * lam / T := by
    rw [hPL]; exact div_le_div_of_nonneg_left (by positivity) hT hEge
  have hZT := Z_nonneg a m T
  have h3 : ((P : ℝ) / L) * Z a m (m * (L * δ)) ≤ (m * lam / T) * (Z a m T + m * δ) := by
    calc ((P : ℝ) / L) * Z a m (m * (L * δ)) ≤ ((P : ℝ) / L) * (Z a m T + m * δ) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (m * lam / T) * (Z a m T + m * δ) :=
          mul_le_mul_of_nonneg_right hPL2 (by positivity)
  have h4 : (m * lam / T) * (m * δ) < ε := by
    have e : (m * lam / T) * (m * δ) = (m * lam) ^ 2 / (T * P) := by rw [hδ]; field_simp
    rw [e, div_lt_iff₀ (by positivity)]
    have : (m * lam) ^ 2 / (T * ε) < P := by
      have : 0 ≤ lam / gap := by positivity
      linarith
    rw [div_lt_iff₀ (by positivity)] at this
    linarith [show ε * (T * P) = P * (T * ε) by ring]
  have e5 : m * D / (n * T) = m * lam / T := by rw [hlam]; field_simp
  have : Z a n D ≤ B + (m * lam / T) * (m * δ) := by
    have expand : (m * lam / T) * (Z a m T + m * δ) =
        (m * lam / T) * Z a m T + (m * lam / T) * (m * δ) := by ring
    rw [hB, e5]; linarith
  linarith

end L62


-- Part D: Korsky's Proposition 6.4 (the dyadic chain)

section P64

open Erdos1221

variable {a : ℕ → ℝ} {r : ℕ} {A : ℝ}

/-- The chain of times: `t₀ = ⌈n(1+2θ)⌉`, `t_{i+1} = ⌈t_i (1+3θ)⌉`. -/
noncomputable def tseq (θ : ℝ) (n : ℕ) : ℕ → ℕ
  | 0 => ⌈(n : ℝ) * (1 + 2 * θ)⌉₊
  | i + 1 => ⌈(tseq θ n i : ℝ) * (1 + 3 * θ)⌉₊

lemma tseq_zero_bounds (θ : ℝ) (hθ : 0 ≤ θ) (n : ℕ) :
    (n : ℝ) * (1 + 2 * θ) ≤ tseq θ n 0 ∧ (tseq θ n 0 : ℝ) < n * (1 + 2 * θ) + 1 :=
  ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩

lemma tseq_succ_bounds (θ : ℝ) (hθ : 0 ≤ θ) (n i : ℕ) :
    (tseq θ n i : ℝ) * (1 + 3 * θ) ≤ tseq θ n (i + 1) ∧
      (tseq θ n (i + 1) : ℝ) < tseq θ n i * (1 + 3 * θ) + 1 :=
  ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩

lemma tseq_ge (θ : ℝ) (hθ : 0 ≤ θ) (n : ℕ) : ∀ i, (n : ℝ) ≤ tseq θ n i := by
  intro i
  induction i with
  | zero =>
    have := (tseq_zero_bounds θ hθ n).1
    have : (n : ℝ) ≤ n * (1 + 2 * θ) := by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith
  | succ i ih =>
    have := (tseq_succ_bounds θ hθ n i).1
    have : (tseq θ n i : ℝ) ≤ tseq θ n i * (1 + 3 * θ) := by
      nlinarith [(Nat.cast_nonneg (tseq θ n i) : (0:ℝ) ≤ tseq θ n i)]
    linarith

lemma tseq_mono (θ : ℝ) (hθ : 0 ≤ θ) (n i : ℕ) : tseq θ n i ≤ tseq θ n (i + 1) := by
  have := (tseq_succ_bounds θ hθ n i).1
  have : (tseq θ n i : ℝ) ≤ tseq θ n i * (1 + 3 * θ) := by
    nlinarith [(Nat.cast_nonneg (tseq θ n i) : (0:ℝ) ≤ tseq θ n i)]
  exact_mod_cast (by linarith : (tseq θ n i : ℝ) ≤ tseq θ n (i + 1))

set_option maxHeartbeats 1000000 in
/-- The dyadic chain, by backward induction from the terminal scale `r` (Lemma 6.3). -/
lemma chain {n₀ : ℕ} (hyp : SpanDev a r A n₀) (ha : Function.Injective fun k => Int.fract (a k))
    (hr : 1 ≤ r) (θ T0 : ℝ) (h : ℕ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 8)
    (hT0 : T0 * 2 ^ h = r) (hT0K : T0 ≤ r * θ) (hT0K2 : r * θ < 2 * T0) (hAθ : A = r * θ ^ 2)
    (n : ℕ) (hn₀ : n₀ ≤ n) (hn1 : (2 : ℝ) ^ h * r < n) (hn2 : 4 / θ ^ 2 ≤ n) :
    ∀ d, d ≤ h → Z a (tseq θ n (h - d)) (T0 * 2 ^ (h - d)) ≤
      T0 * 2 ^ (h - d) * ((1 + 4 * θ) ^ d * (θ ^ 2 + 21 * θ * d)) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hT0pos : 0 < T0 := by nlinarith
  have hge : ∀ i, (n : ℝ) ≤ tseq θ n i := tseq_ge θ hθ0.le n
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℝ) < 2 ^ h * r := by positivity
    linarith
  have hθt : ∀ i, 4 / θ ^ 2 ≤ (tseq θ n i : ℝ) := fun i => le_trans hn2 (hge i)
  intro d
  induction d with
  | zero =>
    intro _
    simp only [Nat.sub_zero, pow_zero, Nat.cast_zero, mul_zero, add_zero, one_mul]
    rw [hT0]
    have htn : n₀ ≤ tseq θ n h := by
      have := hge h
      exact le_trans hn₀ (by exact_mod_cast this)
    have hrt : r < tseq θ n h := by
      have h2 : (r : ℝ) ≤ 2 ^ h * r := by
        have : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
        nlinarith
      have := hge h
      exact_mod_cast (by linarith : (r : ℝ) < tseq θ n h)
    have := L63 (lt_of_lt_of_le hyp.1 htn) ha hr hrt A (hyp.2 _ htn)
    rw [hAθ] at this; exact this
  | succ d ih =>
    intro hd
    have ih' := ih (by omega)
    set i := h - (d + 1) with hi
    have hi1 : h - d = i + 1 := by omega
    rw [hi1] at ih'
    set t := tseq θ n i with ht
    set t' := tseq θ n (i + 1) with ht'
    have htR : (n : ℝ) ≤ t := hge i
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hnpos htR
    have hθt1 : 1 ≤ θ * t := by
      have h1 := hθt i
      have h2 : 4 / θ ^ 2 * θ = 4 / θ := by field_simp
      have h3 : (1 : ℝ) ≤ 4 / θ := by rw [le_div_iff₀ hθ0]; linarith
      nlinarith
    have hθt2 : 2 * r ≤ θ * T0 * t := by
      have h1 := hθt i
      have : θ * T0 * (4 / θ ^ 2) = 4 * T0 / θ := by field_simp
      have h4 : 2 * (r : ℝ) ≤ 4 * T0 / θ := by rw [le_div_iff₀ hθ0]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ θ * T0)]
    obtain ⟨hs1, hs2⟩ := tseq_succ_bounds θ hθ0.le n i
    rw [← ht, ← ht'] at hs1 hs2
    have htt : t ≤ t' := tseq_mono θ hθ0.le n i
    have htn₀ : n₀ ≤ t := le_trans hn₀ (by exact_mod_cast htR)
    set w : ℝ := 2 ^ i with hw
    have hwpos : 0 < w := by positivity
    have hwh : w ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) (by omega)
    have hκ : 1 ≤ 2 ^ i * r := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hκR : ((2 ^ i * r : ℕ) : ℝ) = w * r := by rw [hw]; push_cast; ring
    have hTi : T0 * w ≤ r := by
      rw [← hT0]; exact mul_le_mul_of_nonneg_left hwh hT0pos.le
    have hpow : T0 * 2 ^ (i + 1) = 2 * (T0 * w) := by rw [hw, pow_succ]; ring
    have hDn : T0 * w / t < 1 := by
      rw [div_lt_one htpos]
      have : (r : ℝ) ≤ 2 ^ h * r := by
        have : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
        nlinarith
      linarith
    have hTn : T0 * 2 ^ (i + 1) * t < ((2 ^ i * r : ℕ) : ℝ) * (t' - t) := by
      rw [hκR, hpow]
      have h1 : 3 * θ * t ≤ t' - t := by linarith
      have h2 : 2 * T0 < 3 * θ * r := by linarith
      have h3 : 2 * (T0 * w) * t = (2 * T0) * (w * t) := by ring
      have h4 : (2 * T0) * (w * t) < (3 * θ * r) * (w * t) :=
        mul_lt_mul_of_pos_right h2 (by positivity)
      have h5 : (3 * θ * r) * (w * t) = (w * r) * (3 * θ * t) := by ring
      have h6 : (w * r) * (3 * θ * t) ≤ (w * r) * (t' - t) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    have hκn : ((2 ^ i * r : ℕ) : ℝ) / t < 1 := by
      rw [hκR, div_lt_one htpos]
      have : w * r ≤ 2 ^ h * r := mul_le_mul_of_nonneg_right hwh (by positivity)
      linarith
    have hL := L62 hyp (2 ^ i) hκ htn₀ htt (T0 * w) (T0 * 2 ^ (i + 1)) (by positivity) hDn
      (by positivity) hTn hκn
    rw [hκR] at hL
    push_cast at hL
    rw [← hw] at hL
    -- bounds on the pieces
    set Bd := (1 + 4 * θ) ^ d * (θ ^ 2 + 21 * θ * d) with hBd
    have hBd0 : 0 ≤ Bd := by positivity
    have hratio : (t' : ℝ) ≤ t * (1 + 4 * θ) := by linarith
    have hc1 : (t' : ℝ) * (T0 * w) / (t * (T0 * 2 ^ (i + 1))) ≤ (1 + 4 * θ) / 2 := by
      rw [hpow, div_le_div_iff₀ (by positivity) (by norm_num)]
      have := mul_le_mul_of_nonneg_right hratio (by positivity : (0:ℝ) ≤ 2 * (T0 * w))
      linarith
    have hZ1 : Z a t' (T0 * 2 ^ (i + 1)) ≤ 2 * (T0 * w) * Bd := by rw [← hpow]; exact ih'
    have hterm1 : (t' : ℝ) * (T0 * w) / (t * (T0 * 2 ^ (i + 1))) * Z a t' (T0 * 2 ^ (i + 1)) ≤
        (1 + 4 * θ) * (T0 * w) * Bd := by
      have hZ0 := Z_nonneg a t' (T0 * 2 ^ (i + 1))
      calc _ ≤ (1 + 4 * θ) / 2 * Z a t' (T0 * 2 ^ (i + 1)) :=
            mul_le_mul_of_nonneg_right hc1 hZ0
        _ ≤ (1 + 4 * θ) / 2 * (2 * (T0 * w) * Bd) :=
            mul_le_mul_of_nonneg_left hZ1 (by positivity)
        _ = _ := by ring
    have hterm2 : ((t' : ℝ) - t) * (T0 * w) / t ≤ 4 * θ * (T0 * w) := by
      rw [div_le_iff₀ htpos]
      have : (t' : ℝ) - t ≤ 4 * θ * t := by linarith
      have := mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ T0 * w)
      linarith
    have hterm3 : 8 * w * A ≤ 16 * θ * (T0 * w) := by
      rw [hAθ]
      have h1 := mul_lt_mul_of_pos_left hT0K2 hθ0
      have : r * θ ^ 2 ≤ 2 * θ * T0 := by nlinarith
      have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 8 * w)
      linarith
    have hterm4 : 2 * (w * r) / t ≤ θ * (T0 * w) := by
      rw [div_le_iff₀ htpos]
      have := mul_le_mul_of_nonneg_left hθt2 hwpos.le
      linarith only [this]
    have hstep : (1 + 4 * θ) * Bd + 21 * θ ≤ (1 + 4 * θ) ^ (d + 1) * (θ ^ 2 + 21 * θ * (d + 1)) := by
      have hp : 1 ≤ (1 + 4 * θ) ^ (d + 1) := one_le_pow₀ (by linarith only [hθ0])
      have h2 := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 21 * θ)
      have e : (1 + 4 * θ) ^ (d + 1) * (θ ^ 2 + 21 * θ * (d + 1)) =
          (1 + 4 * θ) * Bd + 21 * θ * (1 + 4 * θ) ^ (d + 1) := by rw [hBd, pow_succ]; ring
      rw [e]; linarith
    have hfin : Z a t (T0 * w) ≤ (T0 * w) * ((1 + 4 * θ) * Bd + 21 * θ) := by
      linarith only [hL, hterm1, hterm2, hterm3, hterm4]
    push_cast
    calc Z a t (T0 * w) ≤ (T0 * w) * ((1 + 4 * θ) * Bd + 21 * θ) := hfin
      _ ≤ (T0 * w) * ((1 + 4 * θ) ^ (d + 1) * (θ ^ 2 + 21 * θ * (d + 1))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)

end P64


-- Part E: Proposition 6.4, final form

section final

open Erdos1221

variable {a : ℕ → ℝ} {r : ℕ} {A : ℝ}

lemma N_zero_len (a : ℕ → ℝ) (n : ℕ) (x : ℝ) : N a n x 0 = 0 := by
  unfold N; apply Finset.sum_eq_zero; intro j _; unfold ind; rw [if_neg]
  rintro ⟨h1, h2⟩; linarith

/-- At integer times `∫ Δ = 0`, so `∫ |Δ| = 2 Z`. -/
lemma int_abs_eq (a : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (D : ℝ) (hD : 0 ≤ D) (hDn : D / n < 1) :
    ∫ x in (0:ℝ)..1, |N a n x (D / n) - D| = 2 * Z a n D := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hg := (good_N a n (D / n)).sub (good_const D)
  simp_rw [abs_eq_pos (N a n _ (D / n) - D)]
  rw [intervalIntegral.integral_sub ((hg.max0.mul_const 2).ii 0 1) (hg.ii 0 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub ((good_N a n _).ii 0 1) ((good_const D).ii 0 1),
    int_N a n _ (div_nonneg hD hnR.le) hDn]
  unfold Z
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]
  rw [mul_div_cancel₀ _ hnR.ne']; ring

set_option maxHeartbeats 2000000 in
/-- Korsky, Proposition 6.4: under the span hypothesis at all times `≥ n₀`, for all large `n`
and all `0 ≤ D ≤ √(Ar)/log²(r/A)`, `∫ |N_n(x, D/n) - D| dx ≤ C₃ A`. -/
theorem core (r : ℕ) (A : ℝ) (hA : 1 ≤ A) (hrA : 64 * A ≤ r) (a : ℕ → ℝ)
    (ha : Function.Injective fun k => Int.fract (a k)) (n₀ : ℕ) (hyp : SpanDev a r A n₀) :
    ∃ N₁ : ℕ, ∀ n, N₁ ≤ n → ∀ D : ℝ, 0 ≤ D → D ≤ √(A * r) / Real.log (r / A) ^ 2 →
      ∫ x in (0:ℝ)..1, |N a n x (D / n) - D| ≤ (172 * Real.exp 4 + 24) * A := by
  have hrR : (64 : ℝ) ≤ r := by linarith
  have hr : 1 ≤ r := by exact_mod_cast (show (1 : ℝ) ≤ r by linarith)
  have hrpos : (0 : ℝ) < r := by linarith
  have hApos : (0 : ℝ) < A := by linarith
  set θ := √(A / r) with hθ
  have hθsq : θ ^ 2 = A / r := Real.sq_sqrt (by positivity)
  have hθ0 : 0 < θ := Real.sqrt_pos.2 (by positivity)
  have hAθ : A = r * θ ^ 2 := by rw [hθsq]; field_simp
  have hθ1 : θ ≤ 1 / 8 := by
    have : θ ^ 2 ≤ 1 / 64 := by rw [hθsq, div_le_iff₀ hrpos]; linarith
    nlinarith
  have hsqrt : √(A * r) = r * θ := by
    rw [show A * r = (r * θ) ^ 2 by rw [mul_pow, hθsq]; field_simp]
    exact Real.sqrt_sq (by positivity)
  set Λ := Real.log (r / A) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hApos]
    have := Real.exp_one_lt_d9
    nlinarith
  -- the dyadic exponent `h`
  have hex : ∃ h : ℕ, (r : ℝ) / 2 ^ h ≤ r * θ := by
    obtain ⟨h, hh⟩ := pow_unbounded_of_one_lt (1 / θ) (by norm_num : (1 : ℝ) < 2)
    refine ⟨h, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hθ0] at hh
    nlinarith
  classical
  set h := Nat.find hex with hhdef
  have hspec : (r : ℝ) / 2 ^ h ≤ r * θ := Nat.find_spec hex
  have hh0 : h ≠ 0 := by
    intro h0
    rw [h0, pow_zero, div_one] at hspec
    nlinarith
  have hmin : ¬ ((r : ℝ) / 2 ^ (h - 1) ≤ r * θ) := Nat.find_min hex (by omega)
  push Not at hmin
  have h2h : (2 : ℝ) ^ h = 2 * 2 ^ (h - 1) := by
    rw [← pow_succ']; congr 1; omega
  set T0 := (r : ℝ) / 2 ^ h with hT0def
  have hT0 : T0 * 2 ^ h = r := by rw [hT0def]; field_simp
  have hT0K2 : r * θ < 2 * T0 := by
    rw [hT0def, h2h]
    have : (r : ℝ) / (2 * 2 ^ (h - 1)) * 2 = r / 2 ^ (h - 1) := by field_simp
    linarith
  have hT0pos : 0 < T0 := by positivity
  have hpθ : θ * 2 ^ (h - 1) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hmin
    nlinarith
  have hθh : θ * h ≤ 1 := by
    have h1 : h - 1 < 2 ^ (h - 1) := Nat.lt_two_pow_self
    have h2 : (h : ℝ) ≤ 2 ^ (h - 1) := by
      have : h ≤ 2 ^ (h - 1) := by omega
      exact_mod_cast this
    nlinarith
  have hhΛ : (h : ℝ) ≤ 2 * Λ := by
    have h1 : ((2 : ℝ) ^ (h - 1)) ^ 2 < r / A := by
      have hX : (θ * 2 ^ (h - 1)) ^ 2 < 1 := by
        have h0 : 0 ≤ θ * 2 ^ (h - 1) := by positivity
        nlinarith
      rw [mul_pow, hθsq, div_mul_eq_mul_div, div_lt_one hrpos] at hX
      rw [lt_div_iff₀ hApos]; linarith
    have h2 := Real.log_lt_log (by positivity) h1
    rw [← pow_mul, Real.log_pow] at h2
    have hl2 := Real.log_two_gt_d9
    have h3 : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    push_cast at h2
    rw [h3] at h2
    have : ((h : ℝ) - 1) * 1 ≤ ((h : ℝ) - 1) * (2 * Real.log 2) := by
      rcases le_or_gt (h : ℝ) 1 with hle | hlt
      · have : (h : ℝ) = 1 := by
          have : (1 : ℝ) ≤ h := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hh0
          linarith
        rw [this]; simp
      · exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have : ((h : ℝ) - 1) * (2 * Real.log 2) = (2 * ((h : ℝ) - 1)) * Real.log 2 := by ring
    linarith
  -- the time threshold
  set S := √(A * r) / Λ ^ 2 with hS
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((n₀ : ℝ) + S + 2 ^ h * r + 4 / θ ^ 2 + 2 * r / A + 1)
  refine ⟨N₁, fun n hn D hD0 hDS => ?_⟩
  have hnR : (N₁ : ℝ) ≤ n := by exact_mod_cast hn
  have hS0 : 0 ≤ S := by positivity
  have hpos1 : (0 : ℝ) ≤ 2 ^ h * r := by positivity
  have hpos2 : (0 : ℝ) ≤ 4 / θ ^ 2 := by positivity
  have hpos3 : (0 : ℝ) ≤ 2 * r / A := by positivity
  have hn₀ : n₀ ≤ n := by exact_mod_cast (show (n₀ : ℝ) ≤ n by linarith)
  have hnS : S < n := by linarith
  have hn1 : (2 : ℝ) ^ h * r < n := by linarith
  have hn2 : 4 / θ ^ 2 ≤ n := by linarith
  have hn3 : 2 * r / A ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hn0 : 0 < n := by exact_mod_cast hnpos
  have hDn : D / n < 1 := by rw [div_lt_one hnpos]; linarith
  rw [int_abs_eq a n hn0 D hD0 hDn]
  have hC : 0 ≤ (172 * Real.exp 4 + 24) * A := by positivity
  rcases hD0.lt_or_eq with hDpos | hD0'
  swap
  · rw [← hD0']
    unfold Z
    simp only [zero_div, N_zero_len, sub_zero, max_self, intervalIntegral.integral_const,
      smul_eq_mul, mul_zero]
    exact hC
  -- the chain at `d = h`
  have hθn : 1 ≤ θ * n := by
    have h3 : (1 : ℝ) ≤ 4 / θ := by rw [le_div_iff₀ hθ0]; linarith
    have : 4 / θ ^ 2 * θ = 4 / θ := by field_simp
    nlinarith
  have hch := chain hyp ha hr θ T0 h hθ0 hθ1 hT0 hspec hT0K2 hAθ n hn₀ hn1 hn2 h le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at hch
  set B := (1 + 4 * θ) ^ h * (θ ^ 2 + 21 * θ * h) with hB
  obtain ⟨ht1, ht2⟩ := tseq_zero_bounds θ hθ0.le n
  set t0 := tseq θ n 0 with ht0
  have hnt : n ≤ t0 := by
    have : (0 : ℝ) ≤ n * θ := by positivity
    have : (n : ℝ) ≤ t0 := by linarith only [ht1, this]
    exact_mod_cast this
  have hTn : T0 * n < ((1 * r : ℕ) : ℝ) * (t0 - n) := by
    push_cast
    have h1 : 2 * θ * n ≤ t0 - n := by linarith
    have h2 : T0 ≤ r * θ := hspec
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ r)
    have h4 := mul_le_mul_of_nonneg_right h2 hnpos.le
    have h5 : 0 < (r : ℝ) * θ * n := by positivity
    linarith only [h3, h4, h5]
  have hκn : ((1 * r : ℕ) : ℝ) / n < 1 := by
    push_cast; rw [div_lt_one hnpos]
    have : (r : ℝ) ≤ 2 ^ h * r := by
      have : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
      nlinarith
    linarith
  have hL := L62 hyp 1 (by simpa using hr) hn₀ hnt D T0 hDpos hDn hT0pos hTn hκn
  push_cast at hL
  -- numerical bounds
  have hcoef : (t0 : ℝ) / n ≤ 2 := by
    rw [div_le_iff₀ hnpos]
    have := mul_le_mul_of_nonneg_right hθ1 hnpos.le
    linarith only [ht2, hθn, this]
  have hB0 : 0 ≤ B := by positivity
  have hexp : (1 + 4 * θ) ^ h ≤ Real.exp 4 := by
    calc (1 + 4 * θ) ^ h ≤ (Real.exp (4 * θ)) ^ h :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (4 * θ)]) h
      _ = Real.exp (h * (4 * θ)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 4 := Real.exp_le_exp.2 (by linarith only [hθh])
  have hDS' : D * Λ ^ 2 ≤ r * θ := by
    rw [hS, hsqrt, le_div_iff₀ (by positivity)] at hDS; exact hDS
  have hDθ0 : 0 ≤ D * θ := by positivity
  have hDθ : D * θ * Λ ^ 2 ≤ A := by
    have := mul_le_mul_of_nonneg_right hDS' hθ0.le
    rw [hAθ]; linarith only [this]
  have hΛ2 : 1 ≤ Λ ^ 2 := by nlinarith only [hΛ1]
  have hDθ1 : D * θ ≤ A := by
    have := mul_le_mul_of_nonneg_left hΛ2 hDθ0
    linarith only [this, hDθ]
  have hDθΛ : D * θ * Λ ≤ A := by
    have := mul_le_mul_of_nonneg_left hΛ1 (by positivity : (0:ℝ) ≤ D * θ * Λ)
    linarith only [this, hDθ]
  have hDB : D * (θ ^ 2 + 21 * θ * h) ≤ 43 * A := by
    have e1 : D * θ ^ 2 ≤ A := by
      have := mul_le_mul_of_nonneg_left (show θ ≤ 1 by linarith only [hθ1]) hDθ0
      linarith only [this, hDθ1]
    have e2 : D * θ * h ≤ 2 * A := by
      have := mul_le_mul_of_nonneg_left hhΛ hDθ0
      linarith only [this, hDθΛ]
    linarith only [e1, e2]
  have hterm1 : (t0 : ℝ) * D / (n * T0) * Z a t0 T0 ≤ 86 * Real.exp 4 * A := by
    have hZ0 := Z_nonneg a t0 T0
    have e : (t0 : ℝ) * D / (n * T0) * Z a t0 T0 ≤ (t0 : ℝ) * D / (n * T0) * (T0 * B) :=
      mul_le_mul_of_nonneg_left hch (by positivity)
    have e2 : (t0 : ℝ) * D / (n * T0) * (T0 * B) = ((t0 : ℝ) / n) * (D * B) := by
      field_simp
    have e3 : D * B ≤ Real.exp 4 * (43 * A) := by
      rw [hB, show D * ((1 + 4 * θ) ^ h * (θ ^ 2 + 21 * θ * h)) =
        (1 + 4 * θ) ^ h * (D * (θ ^ 2 + 21 * θ * h)) by ring]
      exact mul_le_mul hexp hDB (by positivity) (by positivity)
    have e4 : ((t0 : ℝ) / n) * (D * B) ≤ 2 * (Real.exp 4 * (43 * A)) :=
      mul_le_mul hcoef e3 (by positivity) (by norm_num)
    linarith
  have hterm2 : ((t0 : ℝ) - n) * D / n ≤ 3 * A := by
    rw [div_le_iff₀ hnpos]
    have h1 : (t0 : ℝ) - n ≤ 3 * θ * n := by linarith only [ht2, hθn]
    have h2 := mul_le_mul_of_nonneg_right h1 hD0
    have h3 := mul_le_mul_of_nonneg_left hDθ1 (by positivity : (0:ℝ) ≤ 3 * n)
    linarith only [h2, h3]
  have hterm3 : 2 * (r : ℝ) / n ≤ A := by
    rw [div_le_iff₀ hnpos]; rw [div_le_iff₀ hApos] at hn3; linarith
  have hZ : Z a n D ≤ (86 * Real.exp 4 + 12) * A := by
    simp only [one_mul, mul_one] at hL
    linarith only [hL, hterm1, hterm2, hterm3]
  linarith

end final

end E1221P64

namespace E1221P64

lemma card_eq_N_and (a : ℕ → ℝ) (n : ℕ) (x l : ℝ) :
    (((Finset.range n).filter fun j => 0 < Int.fract (a j - x) ∧ Int.fract (a j - x) ≤ l).card
      : ℝ) = N a n x l := by
  rw [Finset.natCast_card_filter]; unfold N
  apply Finset.sum_congr rfl; intro j _; unfold ind
  by_cases hc : 0 < Int.fract (a j - x) ∧ Int.fract (a j - x) ≤ l
  · rw [if_pos hc]
  · rw [if_neg hc]

end E1221P64

open Filter E1221P64 in
theorem E1221i_step_H2 : OMA.R_Erdos1221_erdos_1221_parts_i_R1.H2 := by
  refine ⟨64, 172 * Real.exp 4 + 24, ?_⟩
  intro r A hA hrA a ha hev
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hev
  have hyp : SpanDev a r A (max n₁ 1) :=
    ⟨by omega, fun N hN => dev_of_max (by omega) A (by linarith)
      (hn₁ N (le_trans (le_max_left _ _) hN))⟩
  obtain ⟨N₁, hN⟩ := core r A hA hrA a ha _ hyp
  refine eventually_atTop.2 ⟨N₁, fun n hn D hD0 hDS => ?_⟩
  simp only [card_eq_N_and]
  exact hN n hn D hD0 hDS


end StepH2

section StepH3

/-!
Proof of hypothesis `H3` of reduction R1 of `Erdos1221.erdos_1221.parts.i`, following
Korsky (arXiv:2609.07196, CC BY 4.0), Lemma 7.2.

Let `L = ⌊S⌋`, let the regularity hold for all `n ≥ n₀ ≥ 1`, take `N` large and `w = L / N`.
For an anchor `x`, `P_x` consists of the points `(fract (a i - x) / w, (i + 1) / N)` for the
`i < N` with `a i` in the arc `(x, x + w]`; it has `M_x = cnt a N x w` points and
`disc P_x u v = G_x(u,v) - M_x u v`, where `G_x(u,v)` counts the `i < N` with `i + 1 ≤ N v` and
`a i` in `(x, x + u w]`, i.e. `G_x(u,v) = cnt a ⌊N v⌋ x (u w)`. Writing `n = ⌊N v⌋`,
`|G_x - L u v| ≤ |cnt a n x (u w) - n u w| + w`, and the regularity hypothesis with
`D = n u w ≤ L ≤ S` bounds the `x`-integral by `B + w` when `n ≥ n₀`; when `n < n₀`
(so `v < n₀ / N`) the integrand is at most `n₀ + L`. By Tonelli,
`∫ₓ ∫∫ |G_x - L u v| ≤ B + ε` with `ε = L / N + (n₀ + L) n₀ / N < 1/2`, while
`∫ₓ |M_x - L| ≤ B` (regularity with `n = N`, `D = L`). Hence
`Φ(x) = ∫∫ |G_x - L u v| + (3/2) |M_x - L|` has integral `< 3 B`, so some `x` has `Φ(x) < 3 B`.
For this `x`, `|M_x - L| < 2 B ≤ L / 2` gives `|P_x| ≥ L / 2`, and
`∫∫ |disc P_x| ≤ ∫∫ |G_x - L u v| + |M_x - L| ≤ Φ(x) < 3 B`.
All integrals are handled as lower Lebesgue integrals on `(0, 1]`.
-/

namespace E1221Defs

/-- Number of the first `n` points in the arc `(x, x + len]` of the circle `ℝ/ℤ` (the expression the
reduction's hypotheses spell out). -/
noncomputable def cnt (a : ℕ → ℝ) (n : ℕ) (x len : ℝ) : ℕ :=
  ((Finset.range n).filter fun j => 0 < Int.fract (a j - x) ∧ Int.fract (a j - x) ≤ len).card

/-- The anchored-box discrepancy `#(P ∩ (0,u] × (0,v]) - |P| u v`. -/
noncomputable def disc (P : Finset (ℝ × ℝ)) (u v : ℝ) : ℝ :=
  ((P.filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card : ℝ) - P.card * u * v

end E1221Defs

open E1221Defs

namespace OMA.H3proofI

open Filter MeasureTheory Set OMA.R_Erdos1221_erdos_1221_parts_i_R1
open scoped ENNReal

lemma meas_card {X : Type*} [MeasurableSpace X] (N : ℕ) (P : ℕ → X → Prop)
    [∀ i x, Decidable (P i x)] (hP : ∀ i, MeasurableSet {x | P i x}) :
    Measurable fun x => ((((Finset.range N).filter fun i => P i x).card : ℕ) : ℝ) := by
  simp_rw [Finset.card_filter]
  push_cast
  exact Finset.measurable_sum _ fun i _ => Measurable.ite (hP i) measurable_const measurable_const

lemma meas_fract (c : ℝ) {X : Type*} [MeasurableSpace X] {f : X → ℝ} (hf : Measurable f) :
    Measurable fun x => Int.fract (c - f x) :=
  measurable_fract.comp (measurable_const.sub hf)

lemma meas_cnt (a : ℕ → ℝ) (n : ℕ) (len : ℝ) : Measurable fun x => (cnt a n x len : ℝ) := by
  unfold cnt
  exact meas_card n (fun i x => 0 < Int.fract (a i - x) ∧ Int.fract (a i - x) ≤ len) fun i =>
    (measurableSet_lt measurable_const (meas_fract _ measurable_id)).inter
      (measurableSet_le (meas_fract _ measurable_id) measurable_const)

lemma cnt_le (a : ℕ → ℝ) (n : ℕ) (x len : ℝ) : (cnt a n x len : ℝ) ≤ n := by
  unfold cnt
  exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le

lemma vol1 : volume (Ioc (0 : ℝ) 1) = 1 := by simp [Real.volume_Ioc]

lemma hyp_lint (a : ℕ → ℝ) (n : ℕ) (len D B : ℝ)
    (h : ∫ x in (0 : ℝ)..1, |(cnt a n x len : ℝ) - D| ≤ B) :
    ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(cnt a n x len : ℝ) - D| ≤ ENNReal.ofReal B := by
  rw [intervalIntegral.integral_of_le zero_le_one] at h
  have hi : IntegrableOn (fun x => |(cnt a n x len : ℝ) - D|) (Ioc (0 : ℝ) 1) := by
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      ((meas_cnt a n len).sub measurable_const).abs.aestronglyMeasurable (n + |D|)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h0 : (0 : ℝ) ≤ cnt a n x len := Nat.cast_nonneg _
    have h1 := cnt_le a n x len
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith [neg_abs_le D, neg_le_abs D, le_abs_self D]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

lemma int_le_lint (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∫ x in (0 : ℝ)..1, f x ≤ (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (f x)).toReal := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  by_cases hi : Integrable f (volume.restrict (Ioc (0 : ℝ) 1))
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) hi.aestronglyMeasurable]
  · rw [integral_undef hi]; exact ENNReal.toReal_nonneg

/-- The count `G_x(u,v)`. -/
noncomputable def ct (a : ℕ → ℝ) (N : ℕ) (w x u v : ℝ) : ℕ :=
  ((Finset.range N).filter fun i =>
    0 < Int.fract (a i - x) ∧ Int.fract (a i - x) ≤ u * w ∧ (i : ℝ) + 1 ≤ N * v).card

/-- The point set `P_x`. -/
noncomputable def PP (a : ℕ → ℝ) (N : ℕ) (w x : ℝ) : Finset (ℝ × ℝ) :=
  ((Finset.range N).filter fun i => 0 < Int.fract (a i - x) ∧ Int.fract (a i - x) ≤ w).image
    fun i => (Int.fract (a i - x) / w, ((i : ℝ) + 1) / N)

lemma PP_inj (a : ℕ → ℝ) (N : ℕ) (w x : ℝ) (hN : 0 < N) :
    Function.Injective fun i : ℕ => (Int.fract (a i - x) / w, ((i : ℝ) + 1) / N) := by
  intro i j h
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : ((i : ℝ) + 1) / N = ((j : ℝ) + 1) / N := congrArg Prod.snd h
  rw [div_left_inj' hN'] at h2
  exact_mod_cast (by linarith : (i : ℝ) = j)

lemma PP_card (a : ℕ → ℝ) (N : ℕ) (w x : ℝ) (hN : 0 < N) :
    (PP a N w x).card = cnt a N x w := by
  unfold PP cnt
  rw [Finset.card_image_of_injective _ (PP_inj a N w x hN)]

lemma PP_mem (a : ℕ → ℝ) (N : ℕ) (w x : ℝ) (hN : 0 < N) (hw : 0 < w) :
    ∀ p ∈ PP a N w x, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1 := by
  intro p hp
  unfold PP at hp
  rw [Finset.mem_image] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨hiN, h1, h2⟩ := hi
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hiN' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hiN
  refine ⟨div_pos h1 hw, (div_le_one hw).mpr h2, by positivity, (div_le_one hNr).mpr hiN'⟩

lemma disc_card (a : ℕ → ℝ) (N : ℕ) (w x u v : ℝ) (hN : 0 < N) (hw : 0 < w) (hu1 : u ≤ 1) :
    ((PP a N w x).filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card =
      ct a N w x u v := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold PP ct
  rw [Finset.filter_image, Finset.card_image_of_injective _ (PP_inj a N w x hN),
    Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  simp only
  rw [div_le_iff₀ hw, div_le_iff₀ hNr]
  constructor
  · rintro ⟨⟨h1, -⟩, -, h3, -, h4⟩
    exact ⟨h1, h3, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by nlinarith⟩, div_pos h1 hw, h2, by positivity, by linarith⟩

lemma disc_eq (a : ℕ → ℝ) (N : ℕ) (w x u v : ℝ) (hN : 0 < N) (hw : 0 < w) (hu1 : u ≤ 1) :
    disc (PP a N w x) u v = (ct a N w x u v : ℝ) - cnt a N x w * u * v := by
  unfold disc
  rw [disc_card a N w x u v hN hw hu1, PP_card a N w x hN]

lemma ct_eq_cnt (a : ℕ → ℝ) (N : ℕ) (w x u v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ct a N w x u v = cnt a ⌊(N : ℝ) * v⌋₊ x (u * w) := by
  unfold ct cnt
  have hfl : ⌊(N : ℝ) * v⌋₊ ≤ N := Nat.floor_le_of_le (by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith)
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  have key : (i : ℝ) + 1 ≤ N * v ↔ i < ⌊(N : ℝ) * v⌋₊ := by
    rw [Nat.lt_iff_add_one_le, Nat.le_floor_iff (by positivity)]
    push_cast
    rfl
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨key.mp h3, h1, h2⟩
  · rintro ⟨hin, h1, h2⟩
    exact ⟨by omega, h1, h2, key.mpr hin⟩

lemma meas_ct (a : ℕ → ℝ) (N : ℕ) (w : ℝ) :
    Measurable fun p : (ℝ × ℝ) × ℝ => (ct a N w p.1.1 p.1.2 p.2 : ℝ) := by
  have hS : ∀ i : ℕ, MeasurableSet {p : (ℝ × ℝ) × ℝ | 0 < Int.fract (a i - p.1.1) ∧
      Int.fract (a i - p.1.1) ≤ p.1.2 * w ∧ (i : ℝ) + 1 ≤ N * p.2} := by
    intro i
    have hf : Measurable fun p : (ℝ × ℝ) × ℝ => Int.fract (a i - p.1.1) :=
      meas_fract _ measurable_fst.fst
    have hg : Measurable fun p : (ℝ × ℝ) × ℝ => p.1.2 * w := measurable_fst.snd.mul_const w
    have hh : Measurable fun p : (ℝ × ℝ) × ℝ => (N : ℝ) * p.2 := measurable_snd.const_mul _
    exact (measurableSet_lt measurable_const hf).inter
      ((measurableSet_le hf hg).inter (measurableSet_le measurable_const hh))
  exact meas_card (X := (ℝ × ℝ) × ℝ) N (fun i p => 0 < Int.fract (a i - p.1.1) ∧
    Int.fract (a i - p.1.1) ≤ p.1.2 * w ∧ (i : ℝ) + 1 ≤ N * p.2) hS

lemma swap3 (k : (ℝ × ℝ) × ℝ → ℝ≥0∞) (hk : Measurable k) (μ : Measure ℝ) [SFinite μ] :
    ∫⁻ x, ∫⁻ u, ∫⁻ v, k ((x, u), v) ∂μ ∂μ ∂μ = ∫⁻ u, ∫⁻ v, ∫⁻ x, k ((x, u), v) ∂μ ∂μ ∂μ := by
  rw [lintegral_lintegral_swap (f := fun x u => ∫⁻ v, k ((x, u), v) ∂μ)
    (hk.lintegral_prod_right').aemeasurable]
  refine lintegral_congr fun u => ?_
  exact lintegral_lintegral_swap (f := fun x v => k ((x, u), v))
    ((hk.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).aemeasurable)

lemma inner_bound (a : ℕ → ℝ) (N L n0 : ℕ) (B S : ℝ) (hN : 0 < N) (hn0 : 1 ≤ n0) (hB : 0 ≤ B)
    (hLS : (L : ℝ) ≤ S)
    (hreg : ∀ n ≥ n0, ∀ D : ℝ, 0 ≤ D → D ≤ S →
      ∫ x in (0 : ℝ)..1, |(cnt a n x (D / n) : ℝ) - D| ≤ B)
    (u v : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) (hv : v ∈ Ioc (0 : ℝ) 1) :
    ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(ct a N ((L : ℝ) / N) x u v : ℝ) - L * u * v| ≤
      ENNReal.ofReal (B + L / N) +
        (Iio ((n0 : ℝ) / N)).indicator (fun _ => ENNReal.ofReal (n0 + L)) v := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set w : ℝ := L / N with hw
  have hwN : w * N = L := by rw [hw]; field_simp
  have hw0 : 0 ≤ w := by positivity
  set n := ⌊(N : ℝ) * v⌋₊ with hn
  have hnv : (n : ℝ) ≤ N * v := Nat.floor_le (by positivity)
  have hnv' : (N : ℝ) * v < n + 1 := Nat.lt_floor_add_one _
  have hct : ∀ x, ct a N w x u v = cnt a n x (u * w) := fun x =>
    ct_eq_cnt a N w x u v hv0.le hv1
  by_cases hnn : n0 ≤ n
  · have hnpos : (0 : ℝ) < n := by
      have : 1 ≤ n := hn0.trans hnn
      exact_mod_cast this
    have hD := hreg n hnn (n * u * w) (by positivity) (by
      have h1 : (n : ℝ) ≤ N := by nlinarith
      have h2 : (n : ℝ) * u ≤ N := by nlinarith
      have h3 : (n : ℝ) * u * w ≤ N * w := mul_le_mul_of_nonneg_right h2 hw0
      linarith)
    have hDn : (n : ℝ) * u * w / n = u * w := by field_simp
    rw [hDn] at hD
    have hL := hyp_lint a n (u * w) _ B hD
    calc ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|
        ≤ ∫⁻ x in Ioc (0 : ℝ) 1, (ENNReal.ofReal |(cnt a n x (u * w) : ℝ) - n * u * w| +
            ENNReal.ofReal w) := by
          refine lintegral_mono fun x => ?_
          rw [hct x, ← ENNReal.ofReal_add (abs_nonneg _) hw0]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : (cnt a n x (u * w) : ℝ) - L * u * v =
              ((cnt a n x (u * w) : ℝ) - n * u * w) + u * w * (n - N * v) := by
            rw [← hwN]; ring
          rw [e]
          refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
          have h1 : 0 ≤ u * w := by positivity
          rw [abs_le]
          constructor
          · nlinarith [mul_le_mul_of_nonneg_left (le_of_lt (by linarith : (N : ℝ) * v - n < 1)) h1,
              mul_le_mul_of_nonneg_right hu1 hw0]
          · nlinarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ N * v - n)]
      _ = (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(cnt a n x (u * w) : ℝ) - n * u * w|) +
            ENNReal.ofReal w := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, vol1, mul_one]
      _ ≤ ENNReal.ofReal B + ENNReal.ofReal w := add_le_add hL le_rfl
      _ = ENNReal.ofReal (B + w) := (ENNReal.ofReal_add hB hw0).symm
      _ ≤ _ := le_self_add
  · push Not at hnn
    have hvn : v ∈ Iio ((n0 : ℝ) / N) := by
      rw [mem_Iio, lt_div_iff₀ hNr]
      have : (n : ℝ) + 1 ≤ n0 := by exact_mod_cast hnn
      linarith
    rw [indicator_of_mem hvn]
    refine le_trans ?_ le_add_self
    calc ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|
        ≤ ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (n0 + L) := by
          refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
          rw [hct x]
          have h0 : (0 : ℝ) ≤ cnt a n x (u * w) := Nat.cast_nonneg _
          have h1 := cnt_le a n x (u * w)
          have h2 : (n : ℝ) ≤ n0 := by exact_mod_cast hnn.le
          have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
          have h3 : 0 ≤ (L : ℝ) * u * v := by positivity
          have h4 : (L : ℝ) * u * v ≤ L := by
            have : u * v ≤ 1 := by nlinarith
            nlinarith
          rw [abs_le]
          constructor <;> linarith
      _ = ENNReal.ofReal (n0 + L) := by rw [setLIntegral_const, vol1, mul_one]

lemma outer_bound (a : ℕ → ℝ) (N L n0 : ℕ) (B S : ℝ) (hN : 0 < N) (hn0 : 1 ≤ n0) (hB : 0 ≤ B)
    (hLS : (L : ℝ) ≤ S)
    (hreg : ∀ n ≥ n0, ∀ D : ℝ, 0 ≤ D → D ≤ S →
      ∫ x in (0 : ℝ)..1, |(cnt a n x (D / n) : ℝ) - D| ≤ B) :
    ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1, ∫⁻ x in Ioc (0 : ℝ) 1,
        ENNReal.ofReal |(ct a N ((L : ℝ) / N) x u v : ℝ) - L * u * v| ≤
      ENNReal.ofReal (B + L / N) + ENNReal.ofReal (n0 + L) * ENNReal.ofReal (n0 / N) := by
  have hc : ∀ u : ℝ, ∫⁻ v in Ioc (0 : ℝ) 1, (ENNReal.ofReal (B + L / N) +
      (Iio ((n0 : ℝ) / N)).indicator (fun _ => ENNReal.ofReal (n0 + L)) v) =
      ENNReal.ofReal (B + L / N) +
        ENNReal.ofReal (n0 + L) * volume.restrict (Ioc (0 : ℝ) 1) (Iio ((n0 : ℝ) / N)) := by
    intro u
    rw [lintegral_add_left measurable_const, setLIntegral_const, vol1, mul_one,
      lintegral_indicator_const measurableSet_Iio]
  have hm : volume.restrict (Ioc (0 : ℝ) 1) (Iio ((n0 : ℝ) / N)) ≤ ENNReal.ofReal (n0 / N) := by
    rw [Measure.restrict_apply measurableSet_Iio]
    calc volume (Iio ((n0 : ℝ) / N) ∩ Ioc 0 1) ≤ volume (Ioc (0 : ℝ) (n0 / N)) :=
          measure_mono fun y hy => ⟨hy.2.1, le_of_lt hy.1⟩
      _ = ENNReal.ofReal (n0 / N) := by rw [Real.volume_Ioc, sub_zero]
  calc ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1, ∫⁻ x in Ioc (0 : ℝ) 1,
        ENNReal.ofReal |(ct a N ((L : ℝ) / N) x u v : ℝ) - L * u * v|
      ≤ ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1, (ENNReal.ofReal (B + L / N) +
          (Iio ((n0 : ℝ) / N)).indicator (fun _ => ENNReal.ofReal (n0 + L)) v) :=
        setLIntegral_mono' measurableSet_Ioc fun u hu => setLIntegral_mono' measurableSet_Ioc
          fun v hv => inner_bound a N L n0 B S hN hn0 hB hLS hreg u v hu hv
    _ = ENNReal.ofReal (B + L / N) +
          ENNReal.ofReal (n0 + L) * volume.restrict (Ioc (0 : ℝ) 1) (Iio ((n0 : ℝ) / N)) := by
        rw [lintegral_congr fun u => hc u, setLIntegral_const, vol1, mul_one]
    _ ≤ _ := by gcongr

theorem solution : H3 := by
  intro a ha B S hB hS hBL hev
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp hev
  set n0 := n1 + 1 with hn0d
  have hn0 : 1 ≤ n0 := by omega
  have hreg : ∀ n ≥ n0, ∀ D : ℝ, 0 ≤ D → D ≤ S →
      ∫ x in (0 : ℝ)..1, |(cnt a n x (D / n) : ℝ) - D| ≤ B := fun n hn => hn1 n (by omega)
  set L := ⌊S⌋₊ with hLd
  have hLS : (L : ℝ) ≤ S := Nat.floor_le (by linarith)
  have hB0 : 0 ≤ B := by linarith
  set K := L + (n0 + L) * n0 with hKd
  set N := n0 + 4 * K + 1 with hNd
  have hN : 0 < N := by omega
  have hNn0 : n0 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hLpos : (0 : ℝ) < L := by linarith
  set w : ℝ := L / N with hw
  have hw0 : 0 < w := by positivity
  have hsmall : (L : ℝ) / N + (n0 + L) * (n0 / N) < 1 / 2 := by
    have h4 : (4 * K : ℝ) < N := by exact_mod_cast (by omega : 4 * K < N)
    have hK : (K : ℝ) = L + (n0 + L) * n0 := by rw [hKd]; push_cast; ring
    have e : (L : ℝ) / N + (n0 + L) * (n0 / N) = K / N := by rw [hK]; field_simp
    rw [e, div_lt_iff₀ hNr]
    linarith
  -- the regularity at `n = N`, `D = L`
  have hM : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(cnt a N x w : ℝ) - L| ≤ ENNReal.ofReal B :=
    hyp_lint a N w L B (hreg N hNn0 L (Nat.cast_nonneg _) hLS)
  have hMmeas : Measurable fun x => ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|) :=
    ENNReal.measurable_ofReal.comp
      ((((meas_cnt a N w).sub measurable_const).abs).const_mul _)
  have hk : Measurable fun p : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal |(ct a N w p.1.1 p.1.2 p.2 : ℝ) - L * p.1.2 * p.2| :=
    ENNReal.measurable_ofReal.comp
      (((meas_ct a N w).sub ((measurable_const.mul measurable_fst.snd).mul measurable_snd)).abs)
  have hswap : (∫⁻ x in Ioc (0 : ℝ) 1, ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) =
      ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1, ∫⁻ x in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v| := swap3 _ hk _
  have hH : (∫⁻ x in Ioc (0 : ℝ) 1, ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) ≤
      ENNReal.ofReal (B + L / N) + ENNReal.ofReal (n0 + L) * ENNReal.ofReal (n0 / N) := by
    rw [hswap]; exact outer_bound a N L n0 B S hN hn0 hB0 hLS hreg
  have htotal : ∫⁻ x in Ioc (0 : ℝ) 1, ((∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) +
      ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|)) < ENNReal.ofReal (3 * B) := by
    rw [lintegral_add_right _ hMmeas]
    have e2 : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|) =
        ENNReal.ofReal (3 / 2) *
          ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(cnt a N x w : ℝ) - L| := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr fun x => ENNReal.ofReal_mul (by norm_num)
    rw [e2]
    calc _ ≤ ENNReal.ofReal (B + L / N) + ENNReal.ofReal (n0 + L) * ENNReal.ofReal (n0 / N) +
          ENNReal.ofReal (3 / 2) * ENNReal.ofReal B := add_le_add hH (by gcongr)
      _ = ENNReal.ofReal (B + L / N + (n0 + L) * (n0 / N) + 3 / 2 * B) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ < ENNReal.ofReal (3 * B) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
          linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, (∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) +
      ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|) < ENNReal.ofReal (3 * B) := by
    by_contra hcon
    push Not at hcon
    have : ENNReal.ofReal (3 * B) ≤ ∫⁻ x in Ioc (0 : ℝ) 1, ((∫⁻ u in Ioc (0 : ℝ) 1,
        ∫⁻ v in Ioc (0 : ℝ) 1, ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) +
        ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|)) := by
      calc ENNReal.ofReal (3 * B) = ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (3 * B) := by
            rw [setLIntegral_const, vol1, mul_one]
        _ ≤ _ := lintegral_mono hcon
    exact absurd (this.trans_lt htotal) (lt_irrefl _)
  -- the chosen anchor `x`
  have h1 : ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|) < ENNReal.ofReal (3 * B) :=
    lt_of_le_of_lt le_add_self hx
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h1
  have hF : ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |disc (PP a N w x) u v| ≤
      (∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
        ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) +
        ENNReal.ofReal |(cnt a N x w : ℝ) - L| := by
    calc _ ≤ ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
          (ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v| +
            ENNReal.ofReal |(cnt a N x w : ℝ) - L|) := by
          refine setLIntegral_mono' measurableSet_Ioc fun u hu => setLIntegral_mono'
            measurableSet_Ioc fun v hv => ?_
          rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
            disc_eq a N w x u v hN hw0 hu.2]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : (ct a N w x u v : ℝ) - cnt a N x w * u * v =
              ((ct a N w x u v : ℝ) - L * u * v) + (L - cnt a N x w) * (u * v) := by ring
          rw [e]
          refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
          rw [abs_mul, abs_sub_comm]
          have huv0 : 0 ≤ u * v := mul_nonneg hu.1.le hv.1.le
          have huv : |u * v| ≤ 1 := by
            rw [abs_of_nonneg huv0]; nlinarith [hu.1, hu.2, hv.1, hv.2]
          calc |(cnt a N x w : ℝ) - L| * |u * v| ≤ |(cnt a N x w : ℝ) - L| * 1 :=
                mul_le_mul_of_nonneg_left huv (abs_nonneg _)
            _ = _ := mul_one _
      _ = _ := by
          have hin : ∀ u : ℝ, ∫⁻ v in Ioc (0 : ℝ) 1,
              (ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v| +
                ENNReal.ofReal |(cnt a N x w : ℝ) - L|) =
              (∫⁻ v in Ioc (0 : ℝ) 1, ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) +
                ENNReal.ofReal |(cnt a N x w : ℝ) - L| := by
            intro u
            rw [lintegral_add_right _ measurable_const, setLIntegral_const, vol1, mul_one]
          simp_rw [hin]
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, vol1, mul_one]
  have hF2 : ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |disc (PP a N w x) u v| < ENNReal.ofReal (3 * B) := by
    refine lt_of_le_of_lt (hF.trans ?_) hx
    gcongr
    linarith [abs_nonneg ((cnt a N x w : ℝ) - L)]
  refine ⟨PP a N w x, PP_mem a N w x hN hw0, ?_, ?_⟩
  · rw [PP_card a N w x hN]
    have := (abs_lt.mp (by linarith : |(cnt a N x w : ℝ) - L| < 2 * B)).1
    have h4 : 4 * B ≤ (L : ℝ) := hBL
    linarith
  · have hne : ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
        ENNReal.ofReal |disc (PP a N w x) u v| ≠ ⊤ := (hF2.trans ENNReal.ofReal_lt_top).ne
    calc ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc (PP a N w x) u v|
        ≤ (∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal
            (∫ v in (0 : ℝ)..1, |disc (PP a N w x) u v|)).toReal :=
          int_le_lint _ fun u =>
            intervalIntegral.integral_nonneg zero_le_one fun v _ => abs_nonneg _
      _ ≤ (∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
            ENNReal.ofReal |disc (PP a N w x) u v|).toReal := by
          refine ENNReal.toReal_mono hne (lintegral_mono fun u => ?_)
          exact (ENNReal.ofReal_le_ofReal (int_le_lint _ fun v => abs_nonneg _)).trans
            ENNReal.ofReal_toReal_le
      _ ≤ 3 * B := ENNReal.toReal_le_of_le_ofReal (by positivity) hF2.le

end OMA.H3proofI

theorem E1221i_step_H3 : OMA.R_Erdos1221_erdos_1221_parts_i_R1.H3 := OMA.H3proofI.solution


end StepH3

theorem OMA.solution : type_of% @Erdos1221.erdos_1221.parts.i :=
  OMA.R_Erdos1221_erdos_1221_parts_i_R1.main E1221i_step_H1 E1221i_step_H2 E1221i_step_H3

