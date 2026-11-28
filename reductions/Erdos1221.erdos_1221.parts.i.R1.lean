import FormalConjectures.ErdosProblems.«1221»

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

/-- Number of the first `n` points in the arc `(x, x + len]` of the circle `ℝ/ℤ`. -/
noncomputable def cnt (a : ℕ → ℝ) (n : ℕ) (x len : ℝ) : ℕ :=
  ((Finset.range n).filter fun j => 0 < Int.fract (a j - x) ∧ Int.fract (a j - x) ≤ len).card

/-- The anchored-box discrepancy `#(P ∩ (0,u] × (0,v]) - |P| u v`. -/
noncomputable def disc (P : Finset (ℝ × ℝ)) (u v : ℝ) : ℝ :=
  ((P.filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card : ℝ) - P.card * u * v

/-- Halász's `L¹` lower bound for planar discrepancy (the paper's Theorem 7.1). -/
def H1 : Prop :=
  ∃ cH : ℝ, 0 < cH ∧ ∀ P : Finset (ℝ × ℝ), 2 ≤ P.card →
    (∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) →
    cH * Real.sqrt (Real.log P.card) ≤ ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc P u v|

/-- `L¹` short-arc regularity from the one-sided bound `n M_n - r ≤ A` (the paper's Lemmas
6.1–6.3 and Proposition 6.4). -/
def H2 : Prop :=
  ∃ C₂ C₃ : ℝ, ∀ (r : ℕ) (A : ℝ), 1 ≤ A → C₂ * A ≤ r →
    ∀ a : ℕ → ℝ, Function.Injective (fun k ↦ Int.fract (a k)) →
    (∀ᶠ n : ℕ in atTop, (n : ℝ) * maxSpan a n r ≤ r + A) →
    ∀ᶠ n : ℕ in atTop, ∀ D : ℝ, 0 ≤ D → D ≤ Real.sqrt (A * r) / Real.log (r / A) ^ 2 →
      ∫ x in (0 : ℝ)..1, |(cnt a n x (D / n) : ℝ) - D| ≤ C₃ * A

/-- From `L¹` short-arc regularity to a planar point set with small `L¹` discrepancy (the paper's
Lemma 7.2, before Halász's theorem is applied). -/
def H3 : Prop :=
  ∀ a : ℕ → ℝ, Function.Injective (fun k ↦ Int.fract (a k)) → ∀ B S : ℝ, 1 ≤ B → 8 ≤ S →
    4 * B ≤ ⌊S⌋₊ →
    (∀ᶠ n : ℕ in atTop, ∀ D : ℝ, 0 ≤ D → D ≤ S →
      ∫ x in (0 : ℝ)..1, |(cnt a n x (D / n) : ℝ) - D| ≤ B) →
    ∃ P : Finset (ℝ × ℝ), (∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) ∧
      (⌊S⌋₊ : ℝ) / 2 ≤ P.card ∧
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc P u v| ≤ 3 * B

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
        ∫ x in (0 : ℝ)..1, |(cnt a n x (D / n) : ℝ) - D| ≤ B₀ * A :=
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

