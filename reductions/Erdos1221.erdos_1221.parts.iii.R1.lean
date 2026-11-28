import FormalConjectures.ErdosProblems.«1221»

/-!
Reduction R1 of `Erdos1221.erdos_1221.parts.iii`: `r(μ_r - 1) → ∞`.

Following Korsky, *A Resolution of the de Bruijn–Erdős Consecutive-Gap Problem*
(arXiv:2609.07196, CC BY 4.0), Theorem 1.1 (ratio part), Sections 2–5. For a sequence whose
consecutive `r`-span ratio stays below `1 + A/r` with `A = log r / 1000`:
* H2 (Sections 2–3, Lemma 2.1 and Proposition 3.1): the point counts in short arcs are then
  regular, `|N_n((x, x + D/n]) - D| ≤ 3A + C₁A/log(r/A)` for `0 ≤ D ≤ S = √(Ar)/log²(r/A)`.
* H3 (Section 4, Lemma 4.2): such regularity yields a list of `⌊S⌋` points of `[0,1)` all of
  whose prefixes have discrepancy at most that bound.
* H1 (Larcher; the paper's Theorem 4.1): every list of `L ≥ L₀` points of `[0,1)` has a prefix
  of discrepancy at least `(log L)/60` (the paper uses Larcher's sharper constant; any fixed
  constant works for this target).
`main` carries out Section 5: since `3/1000 < 1/120`, these are incompatible for large `r`, so
every admissible sequence has `limsup M/m ≥ 1 + log r/(1000 r)`, hence so does `μ_r`, which beats
`1 + K/r` for every fixed `K` and all large `r`.
-/

namespace OMA.R_Erdos1221_erdos_1221_parts_iii_R1

open Filter Erdos1221
open scoped ENNReal

/-- Larcher's finite-prefix discrepancy lower bound (the paper's Theorem 4.1). -/
def H1 : Prop :=
  ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ z : ℕ → ℝ, (∀ i < L, 0 ≤ z i ∧ z i < 1) →
    ∃ j ≤ L, ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
      Real.log L / 60 ≤ |(((Finset.range j).filter fun i => z i < u).card : ℝ) - j * u|

/-- Short-arc regularity from a bounded span ratio (the paper's Lemma 2.1 and Proposition 3.1,
with Section 5's steps (b)–(c)). -/
def H2 : Prop :=
  ∃ C₀ C₁ : ℝ, 0 < C₁ ∧ ∀ (r : ℕ) (A : ℝ), 1 ≤ A → C₀ * A ≤ r →
    ∀ a : ℕ → ℝ, Function.Injective (fun k ↦ Int.fract (a k)) → ∀ C : ℝ, 0 ≤ C → C < A →
    (∀ᶠ n : ℕ in atTop, ENNReal.ofReal (maxSpan a n r) / ENNReal.ofReal (minSpan a n r) ≤
        ENNReal.ofReal (1 + C / r)) →
    ∀ᶠ n : ℕ in atTop, ∀ x D : ℝ, 0 ≤ D → D ≤ Real.sqrt (A * r) / Real.log (r / A) ^ 2 →
      |(((Finset.range n).filter fun j => 0 < Int.fract (a j - x) ∧ Int.fract (a j - x) ≤ D / n).card : ℝ) - D| ≤ 3 * A + C₁ * A / Real.log (r / A)

/-- From short-arc regularity to a list with small prefix discrepancies (the paper's Lemma 4.2). -/
def H3 : Prop :=
  ∀ a : ℕ → ℝ, Function.Injective (fun k ↦ Int.fract (a k)) → ∀ B S : ℝ, 1 ≤ B → 2 ≤ S →
    (∀ᶠ n : ℕ in atTop, ∀ x D : ℝ, 0 ≤ D → D ≤ S → |(((Finset.range n).filter fun j => 0 < Int.fract (a j - x) ∧ Int.fract (a j - x) ≤ D / n).card : ℝ) - D| ≤ B) →
    ∃ z : ℕ → ℝ, (∀ i < ⌊S⌋₊, 0 ≤ z i ∧ z i < 1) ∧ ∀ j ≤ ⌊S⌋₊, ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      |(((Finset.range j).filter fun i => z i < u).card : ℝ) - j * u| ≤ B

/-! ### The asymptotic arithmetic of Section 5 -/

lemma log_le_two_sqrt {y : ℝ} (hy : 0 ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h := Real.log_le_rpow_div hy (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  linarith

set_option maxHeartbeats 2000000 in
/-- All the size conditions needed in Section 5 hold for large `r`. -/
lemma eventually_conditions (C₀ C₁ : ℝ) (hC₁ : 0 < C₁) (L₀ : ℕ) :
    ∀ᶠ r : ℕ in atTop,
      let A : ℝ := Real.log r / 1000
      let Λ : ℝ := Real.log (r / A)
      let S : ℝ := Real.sqrt (A * r) / Λ ^ 2
      1 ≤ A ∧ C₀ * A ≤ r ∧ 2 ≤ S ∧ L₀ ≤ ⌊S⌋₊ ∧ 0 < Λ ∧
        3 * A + C₁ * A / Λ < Real.log ⌊S⌋₊ / 60 := by
  -- choose a threshold `Y` for `y = log r`
  have hL0 : 0 ≤ Real.log ((L₀ : ℝ) + 2) := Real.log_nonneg (by have := L₀.cast_nonneg (α := ℝ); linarith)
  have hc1 := sq_nonneg (C₁ / 50 + 1)
  have hc0 := sq_nonneg (C₀ / 25 + 1)
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, 160000 ≤ Y ∧ (C₁ / 50 + 1) ^ 2 * 16 ≤ Y ∧
      4 * Real.log ((L₀ : ℝ) + 2) + 100 ≤ Y ∧ (C₀ / 25 + 1) ^ 2 ≤ Y :=
    ⟨160000 + (C₁ / 50 + 1) ^ 2 * 16 + (4 * Real.log ((L₀ : ℝ) + 2) + 100) + (C₀ / 25 + 1) ^ 2,
      by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨hY1, hY2, hY3, hY4⟩ := hY
  have hlog : Tendsto (fun r : ℕ => Real.log (r : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop Y, eventually_gt_atTop 0] with r hr hr0
  intro A Λ S
  set y := Real.log (r : ℝ) with hy
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
  have hy0 : 0 ≤ y := by linarith
  have hsy : 400 ≤ Real.sqrt y := by
    rw [show (400 : ℝ) = Real.sqrt (400 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0
  -- A ≥ 1
  have hA : 1 ≤ A := by simp only [A]; linarith
  have hApos : 0 < A := by linarith
  -- log A ≤ 2 √y
  have hlogA : Real.log A ≤ 2 * Real.sqrt y := by
    have h1 : Real.log A ≤ Real.log y := Real.log_le_log hApos (by simp only [A]; linarith)
    linarith [log_le_two_sqrt hy0]
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA
  -- Λ = y - log A, and y/2 ≤ Λ ≤ y
  have hΛ : Λ = y - Real.log A := by
    simp only [Λ]; rw [Real.log_div hrpos.ne' hApos.ne']
  have hΛlo : y / 2 ≤ Λ := by rw [hΛ]; nlinarith
  have hΛhi : Λ ≤ y := by rw [hΛ]; linarith
  have hΛpos : 0 < Λ := by linarith
  -- log S ≥ y/2 - 2 log y ≥ y/2 - 4 √y
  have hAr : 0 < A * r := by positivity
  have hSpos : 0 < S := by simp only [S]; positivity
  have hlogS : y / 2 - 4 * Real.sqrt y ≤ Real.log S := by
    have e1 : Real.log S = Real.log (A * r) / 2 - 2 * Real.log Λ := by
      simp only [S]
      rw [Real.log_div (Real.sqrt_pos.mpr hAr).ne' (by positivity), Real.log_sqrt hAr.le,
        Real.log_pow]
      push_cast; ring
    have e2 : Real.log (A * r) = Real.log A + y := by
      rw [Real.log_mul hApos.ne' hrpos.ne']
    have e3 : Real.log Λ ≤ Real.log y := Real.log_le_log hΛpos hΛhi
    have e4 := log_le_two_sqrt hy0
    rw [e1, e2]; nlinarith
  -- S is large
  have h16 : 4 * Real.sqrt y ≤ y / 4 := by nlinarith
  have hlogS2 : Real.log (L₀ + 2) + 1 ≤ Real.log S := by linarith
  have hSbig : (L₀ : ℝ) + 2 ≤ S := by
    have h := Real.exp_le_exp.mpr (le_trans (by linarith : Real.log (L₀ + 2) ≤ Real.log (L₀ + 2) + 1)
      hlogS2)
    rwa [Real.exp_log (by positivity), Real.exp_log hSpos] at h
  have hS2 : 2 ≤ S := by have := L₀.cast_nonneg (α := ℝ); linarith
  have hfl : L₀ ≤ ⌊S⌋₊ := by
    rw [Nat.le_floor_iff hSpos.le]; linarith
  -- log ⌊S⌋ ≥ log S - log 2
  have hflpos : (0 : ℝ) < ⌊S⌋₊ := by
    have : (1 : ℝ) ≤ ⌊S⌋₊ := by exact_mod_cast Nat.le_floor (by norm_num; linarith)
    linarith
  have hfl2 : S / 2 ≤ (⌊S⌋₊ : ℝ) := by have := Nat.lt_floor_add_one S; linarith
  have hlogfl : Real.log S - Real.log 2 ≤ Real.log ⌊S⌋₊ := by
    have := Real.log_le_log (by positivity) hfl2
    rw [Real.log_div hSpos.ne' (by norm_num)] at this; linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  -- B is small
  have hB : 3 * A + C₁ * A / Λ ≤ 3 * y / 1000 + C₁ / 500 := by
    have : C₁ * A / Λ ≤ C₁ / 500 := by
      rw [div_le_iff₀ hΛpos]; simp only [A]; nlinarith
    simp only [A] at this ⊢; linarith
  have hC₁y : C₁ / 50 + 1 ≤ Real.sqrt y / 4 := by
    have : (C₁ / 50 + 1) * 4 ≤ Real.sqrt y := by
      rw [show (C₁ / 50 + 1) * 4 = Real.sqrt (((C₁ / 50 + 1) * 4) ^ 2) by
        rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  -- C₀ A ≤ r
  have hC0 : C₀ * A ≤ r := by
    have h1 : y ≤ 2 * Real.sqrt (r : ℝ) := log_le_two_sqrt hrpos.le
    have h2 : Real.sqrt (r : ℝ) ^ 2 = r := Real.sq_sqrt hrpos.le
    have hs0 : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
    have h3 : C₀ / 50 ≤ Real.sqrt (r : ℝ) := by nlinarith [sq_nonneg (C₀ / 25)]
    simp only [A]
    rcases le_or_gt C₀ 0 with h | h
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left h1 h.le, mul_le_mul_of_nonneg_right h3 hs0]
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
  have hC₁s : C₁ / 500 ≤ Real.sqrt y / 4 - 1 := by linarith
  have hfin : 3 * y / 1000 + C₁ / 500 + 1 < (y / 2 - 4 * Real.sqrt y - 1) / 60 := by
    have hss : 400 * Real.sqrt y ≤ y := by nlinarith
    linarith
  refine ⟨hA, hC0, hS2, hfl, hΛpos, ?_⟩
  linarith

theorem main : H1 → H2 → H3 → type_of% @Erdos1221.erdos_1221.parts.iii := by
  rintro ⟨L₀, hL⟩ ⟨C₀, C₁, hC₁, h2⟩ h3 K
  have hK : ∀ᶠ r : ℕ in atTop, 1000 * K < Real.log r :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (1000 * K)
  filter_upwards [eventually_conditions C₀ C₁ hC₁ L₀, hK, eventually_gt_atTop 0] with r hc hKr hr0
  dsimp only at hc
  obtain ⟨hA, hC0, hS2, hfl, hΛpos, hBS⟩ := hc
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
  have hB1 : 1 ≤ 3 * (Real.log r / 1000) + C₁ * (Real.log r / 1000) / Real.log (r / (Real.log r / 1000)) := by
    have : 0 ≤ C₁ * (Real.log r / 1000) / Real.log (r / (Real.log r / 1000)) := by positivity
    linarith
  -- every admissible sequence has limsup ratio ≥ 1 + A / r
  have key : ∀ a : ℕ → ℝ, Function.Injective (fun k ↦ Int.fract (a k)) →
      ENNReal.ofReal (1 + (Real.log r / 1000) / r) ≤
        limsup (fun n : ℕ => ENNReal.ofReal (maxSpan a n r) / ENNReal.ofReal (minSpan a n r))
          atTop := by
    intro a ha
    by_contra hlt
    push Not at hlt
    obtain ⟨b, hb1, hb2⟩ := exists_between hlt
    have hbtop : b ≠ ⊤ := ne_top_of_lt hb2
    have hbr : b.toReal < 1 + (Real.log r / 1000) / r := ENNReal.toReal_lt_of_lt_ofReal hb2
    set C : ℝ := max 0 ((b.toReal - 1) * r) with hCdef
    have hCA : C < Real.log r / 1000 := by
      refine max_lt (by linarith) ?_
      have : (b.toReal - 1) < (Real.log r / 1000) / r := by linarith
      calc (b.toReal - 1) * r < ((Real.log r / 1000) / r) * r := by
            exact mul_lt_mul_of_pos_right this hrpos
        _ = Real.log r / 1000 := by field_simp
    have hbC : b ≤ ENNReal.ofReal (1 + C / r) := by
      rw [← ENNReal.ofReal_toReal hbtop]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (b.toReal - 1) * r ≤ C := le_max_right _ _
      have h2' : b.toReal - 1 ≤ C / r := by rw [le_div_iff₀ hrpos]; linarith
      linarith
    have hev := (eventually_lt_of_limsup_lt hb1).mono (fun n h => h.le.trans hbC)
    have hreg := h2 r _ hA hC0 a ha C (le_max_left _ _) hCA hev
    obtain ⟨z, hz, hzB⟩ := h3 a ha _ _ hB1 hS2 hreg
    obtain ⟨j, hj, u, hu0, hu1, hge⟩ := hL _ hfl z hz
    have := hzB j hj u hu0 hu1
    linarith
  have hmu : ENNReal.ofReal (1 + (Real.log r / 1000) / r) ≤ mu r :=
    le_iInf₂ fun a ha => key a ha
  refine lt_of_lt_of_le ?_ hmu
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have : K / r < (Real.log r / 1000) / r := div_lt_div_of_pos_right (by linarith) hrpos
  linarith

end OMA.R_Erdos1221_erdos_1221_parts_iii_R1
