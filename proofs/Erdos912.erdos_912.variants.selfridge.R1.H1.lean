import OMAReductions.R_Erdos912_erdos_912_variants_selfridge_R1
import Mathlib.NumberTheory.Chebyshev

open Finset Filter Asymptotics

namespace OMASelfridge

set_option maxHeartbeats 1000000 in
lemma core (n : ℕ) (hL : 40000 ≤ Real.log n) (hL3 : Real.log n ^ 3 ≤ n) :
    Real.log 2 / 4 * √((n : ℝ) / Real.log n) ≤
      (((Nat.primesLE ⌊√((n : ℝ) * Real.log n)⌋₊).filter
        (fun p => p ≤ n ∧ n < p * p)).card : ℝ) ∧
    ((Nat.primesLE ⌊√((n : ℝ) * Real.log n)⌋₊).card : ℝ) ≤
      (4 * Real.log 4 + 1) * √((n : ℝ) / Real.log n) := by
  have hl2a : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hl2b : Real.log 2 < (0.7 : ℝ) := by
    have := Real.log_two_lt_d9; linarith
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  generalize hLdef : Real.log (n : ℝ) = L at hL hL3 ⊢
  generalize hxdef : (n : ℝ) = x at hLdef hL3 ⊢
  have hL0 : 0 < L := by linarith
  have hLL : 1 ≤ L * L := by nlinarith
  have hxL : L ≤ x := by
    have h := mul_le_mul_of_nonneg_left hLL hL0.le
    have h' : L * (L * L) = L ^ 3 := by ring
    linarith
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  -- Y and r
  set Y := √(x / L) with hY
  set r := √L with hr
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hYY : Y * Y = x / L := Real.mul_self_sqrt (by positivity)
  have hrr : r * r = L := Real.mul_self_sqrt hL0.le
  have hr200 : 200 ≤ r := by
    rw [hr]; apply Real.le_sqrt_of_sq_le; linarith
  have hYL : L ≤ Y := by
    rw [hY]; apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hL0]; nlinarith
  have hX : √(x * L) = Y * L := by
    have h : x * L = (x / L) * L ^ 2 := by field_simp
    rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq hL0.le]
  have hsx : √x = Y * r := by
    have h : x = (x / L) * L := by field_simp
    rw [hY, hr, ← Real.sqrt_mul (by positivity), ← h]
  rw [hX]
  have hXx : Y * L ≤ x := by
    rw [← hX, Real.sqrt_le_iff]
    exact ⟨hx0.le, by nlinarith⟩
  have hXbig : L * L ≤ Y * L := by nlinarith
  have hX1 : 1 < Y * L := by nlinarith
  have hX0 : 0 ≤ Y * L := by nlinarith
  have hsqX : √(Y * L) ≤ Y := by
    rw [Real.sqrt_le_iff]
    exact ⟨hY0, by nlinarith⟩
  -- upper bound on π ⌊X⌋
  have hlogX : L / 2 ≤ Real.log (Y * L) := by
    rw [← hX, Real.log_sqrt (by positivity), Real.log_mul hx0.ne' hL0.ne', hLdef]
    have : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    linarith
  have hlogsX : L / 4 ≤ Real.log √(Y * L) := by
    rw [Real.log_sqrt hX0]; linarith
  have hupper : (Nat.primeCounting ⌊Y * L⌋₊ : ℝ) ≤ (4 * Real.log 4 + 1) * Y := by
    have h := Chebyshev.pi_le_log4_mul_div hX1
    have h1 : Real.log 4 * (Y * L) / Real.log √(Y * L) ≤ Real.log 4 * (Y * L) / (L / 4) := by
      apply div_le_div_of_nonneg_left _ (by positivity) hlogsX
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      positivity
    have h2 : Real.log 4 * (Y * L) / (L / 4) = 4 * Real.log 4 * Y := by
      field_simp
    linarith
  -- lower bound on π ⌊X⌋
  set N := ⌊Y * L⌋₊ with hN
  have hNle : (N : ℝ) ≤ Y * L := Nat.floor_le hX0
  have hNgt : Y * L < N + 1 := Nat.lt_floor_add_one _
  have hN2 : (2 : ℝ) ≤ N := by nlinarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN0 : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogN : Real.log N ≤ L := by
    rw [← hLdef]
    exact Real.log_le_log hN0 (by linarith)
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + L := by
    rw [← hLdef, ← Real.log_mul (by norm_num) hx0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hlower : Real.log 2 / 2 * Y ≤ (Nat.primeCounting N : ℝ) := by
    have h := Chebyshev.pi_ge N
    rw [div_le_iff₀ hlogN0] at h
    have hpi0 : (0 : ℝ) ≤ Nat.primeCounting N := Nat.cast_nonneg _
    have h1 : (Nat.primeCounting N : ℝ) * Real.log N ≤ (Nat.primeCounting N : ℝ) * L :=
      mul_le_mul_of_nonneg_left hlogN hpi0
    have h2 : (Y * L - 1) * Real.log 2 ≤ N * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      linarith
    have e1 : L * L * 0.345 ≤ L * L * (Real.log 2 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : 40000 * L ≤ L * L := mul_le_mul_of_nonneg_right hL hL0.le
    have e3 : L * L * (Real.log 2 / 2) ≤ (Y * L) * (Real.log 2 / 2) :=
      mul_le_mul_of_nonneg_right hXbig (by linarith)
    have h4 : 2 * Real.log 2 + L ≤ (Y * L) * (Real.log 2 / 2) := by linarith
    have h3 : Real.log 2 / 2 * Y * L ≤ (Nat.primeCounting N : ℝ) * L := by
      have h5 : (Y * L - 1) * Real.log 2 = Y * L * Real.log 2 - Real.log 2 := by ring
      have h6 : (Y * L) * (Real.log 2 / 2) = Y * L * Real.log 2 / 2 := by ring
      have h7 : Real.log 2 / 2 * Y * L = Y * L * Real.log 2 / 2 := by ring
      linarith
    exact le_of_mul_le_mul_right h3 hL0
  -- upper bound on π ⌊√x⌋
  have hsx1 : 1 < √x := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hx1
  have hlogssx : Real.log √(√x) = L / 4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hx0.le, hLdef]; ring
  have hM : (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ Real.log 2 / 4 * Y := by
    have h := Chebyshev.pi_le_log4_mul_div hsx1
    rw [← hxdef, Real.nat_floor_real_sqrt_eq_nat_sqrt, hxdef, hlogssx, hsx] at h
    have hYr0 : 0 ≤ Y * r := mul_nonneg hY0 hr0
    have h1 : Real.log 4 * (Y * r) / (L / 4) ≤ Real.log 2 / 8 * Y := by
      rw [div_le_iff₀ (by positivity), hl4]
      have e : 64 * (Y * r) ≤ Y * L := by
        have := mul_le_mul_of_nonneg_left (show (64 : ℝ) ≤ r by linarith) hYr0
        have h' : Y * r * r = Y * L := by rw [mul_assoc, hrr]
        linarith
      have e' := mul_le_mul_of_nonneg_left e (show (0 : ℝ) ≤ Real.log 2 / 32 by linarith)
      have h8 : Real.log 2 / 32 * (64 * (Y * r)) = 2 * Real.log 2 * (Y * r) := by ring
      have h9 : Real.log 2 / 32 * (Y * L) = Real.log 2 / 8 * Y * (L / 4) := by ring
      linarith
    have h2 : √(Y * r) ≤ Real.log 2 / 8 * Y := by
      rw [Real.sqrt_le_iff]
      refine ⟨by have := mul_nonneg (show (0 : ℝ) ≤ Real.log 2 / 8 by linarith) hY0; linarith, ?_⟩
      have hYr : r * r ≤ Y := by rw [hrr]; exact hYL
      have hlsq : (0.47 : ℝ) ≤ Real.log 2 ^ 2 := by nlinarith
      have hrr2 : 200 * r ≤ r * r := mul_le_mul_of_nonneg_right hr200 hr0
      have hc0 : 0.47 * (r * r) ≤ Real.log 2 ^ 2 * (r * r) :=
        mul_le_mul_of_nonneg_right hlsq (mul_nonneg hr0 hr0)
      have hc1 : Real.log 2 ^ 2 * (r * r) ≤ Real.log 2 ^ 2 * Y :=
        mul_le_mul_of_nonneg_left hYr (by positivity)
      have hc2 : 64 * r ≤ Real.log 2 ^ 2 * Y := by linarith
      have h10 : Y * (64 * r) ≤ Y * (Real.log 2 ^ 2 * Y) := mul_le_mul_of_nonneg_left hc2 hY0
      have h11 : (Real.log 2 / 8 * Y) ^ 2 = Y * (Real.log 2 ^ 2 * Y) / 64 := by ring
      have h12 : Y * (64 * r) = 64 * (Y * r) := by ring
      linarith
    linarith
  -- counting
  have hNn : N ≤ n := by
    have : (N : ℝ) ≤ (n : ℝ) := by rw [hxdef]; linarith
    exact_mod_cast this
  have hsub : Nat.primesLE N ⊆
      (Nat.primesLE N).filter (fun p => p ≤ n ∧ n < p * p) ∪ Nat.primesLE (Nat.sqrt n) := by
    intro p hp
    by_cases hc : p ≤ n ∧ n < p * p
    · exact mem_union_left _ (mem_filter.2 ⟨hp, hc⟩)
    · apply mem_union_right
      rw [Nat.mem_primesLE] at hp ⊢
      refine ⟨?_, hp.2⟩
      rw [Nat.le_sqrt]
      by_contra hlt
      exact hc ⟨hp.1.trans hNn, by omega⟩
  have hcard : (Nat.primesLE N).card ≤
      ((Nat.primesLE N).filter (fun p => p ≤ n ∧ n < p * p)).card +
        (Nat.primesLE (Nat.sqrt n)).card :=
    (card_le_card hsub).trans (card_union_le _ _)
  rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hcard
  have hcardR : (Nat.primeCounting N : ℝ) ≤
      (((Nat.primesLE N).filter (fun p => p ≤ n ∧ n < p * p)).card : ℝ) +
        (Nat.primeCounting (Nat.sqrt n) : ℝ) := by exact_mod_cast hcard
  refine ⟨by linarith, ?_⟩
  rw [Nat.primesLE_card_eq_primeCounting]
  exact hupper

end OMASelfridge

theorem OMA.solution : OMA.R_Erdos912_erdos_912_variants_selfridge_R1.H1 := by
  refine ⟨Real.log 2 / 4, 4 * Real.log 4 + 1, ?_, ?_, ?_⟩
  · have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
  · have := Real.log_pos (show (1 : ℝ) < 4 by norm_num); positivity
  · have h1 : ∀ᶠ n : ℕ in atTop, 40000 ≤ Real.log (n : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 40000
    have h2 : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ 3 ≤ n := by
      have hb := (Real.isLittleO_pow_log_id_atTop (n := 3)).bound one_pos
      have hb' := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually hb
      filter_upwards [hb'] with n hn
      have h3 : Real.log (n : ℝ) ^ 3 ≤ ‖Real.log (n : ℝ) ^ 3‖ := Real.le_norm_self _
      have h4 : ‖(id (n : ℝ))‖ = n := by simp
      linarith
    filter_upwards [h1, h2] with n hn1 hn2
    exact OMASelfridge.core n hn1 hn2
