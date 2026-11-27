import OMAReductions.R_Erdos912_erdos_912_variants_selfridge_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Chebyshev's bounds at the two prime cutoffs in the Erdős–Selfridge estimate. -/

-- Credit: @dk8827

open Finset Filter
open scoped Topology

namespace OMA.SelfridgePrimeCount

private theorem log_le_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ √x := by
  have h : 0 < √x / 2 := by positivity
  have heq : Real.log (√x / 2) = Real.log x / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx.le]
  linarith only [Real.log_le_sub_one_of_pos h, heq, Real.log_two_lt_d9]

private theorem prime_count_upper {x : ℝ} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 5 * x / Real.log x := by
  have hx' : 0 < x := zero_lt_one.trans hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hroot : √x ≤ x / Real.log x := by
    apply (le_div_iff₀ hl).2
    calc
      _ ≤ √x * √x := mul_le_mul_of_nonneg_left (log_le_sqrt hx') (Real.sqrt_nonneg _)
      _ = x := by rw [← pow_two, Real.sq_sqrt hx'.le]
  have hp := Chebyshev.pi_le_log4_mul_div hx
  rw [Real.log_sqrt hx'.le] at hp
  have hl4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith only [Real.log_two_lt_d9]
  have he : Real.log 4 * x / (Real.log x / 2) = (2 * Real.log 4) * (x / Real.log x) := by ring
  rw [he] at hp
  have hmul := mul_le_mul_of_nonneg_right (show 2 * Real.log 4 ≤ 4 by linarith only [hl4])
    (div_nonneg hx'.le hl.le)
  rw [mul_div_assoc]
  linarith only [hp, hroot, hmul]

private theorem prime_count_lower {x : ℝ} (hx : 256 ≤ x) :
    x / (4 * Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx1 : 1 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hlogx : Real.log (x + 2) ≤ x / 8 := by
    apply (log_le_sqrt (by linarith : 0 < x + 2)).trans
    apply Real.sqrt_le_iff.2
    refine ⟨by linarith, ?_⟩
    nlinarith only [hx, mul_nonneg (show 0 ≤ x - 256 by linarith) (show 0 ≤ x by linarith)]
  have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
    (show 0 ≤ x - 1 by linarith)
  have hnum : x / 4 ≤ (x - 1) * Real.log 2 - Real.log (x + 2) :=
    by linarith only [hmul, hlogx, hx]
  calc
    x / (4 * Real.log x) = (x / 4) / Real.log x := by ring
    _ ≤ _ := (div_le_div_of_nonneg_right hnum hL.le).trans (Chebyshev.pi_ge' hx1)

set_option maxHeartbeats 800000 in
theorem scaled :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      let X := √((n : ℝ) * Real.log n)
      let P := Nat.primesLE ⌊X⌋₊
      c * √((n : ℝ) / Real.log n) ≤ ((P.filter (fun p => p ≤ n ∧ n < p * p)).card : ℝ) ∧
      (P.card : ℝ) ≤ C * √((n : ℝ) / Real.log n) := by
  refine ⟨1 / 8, 10, by norm_num, by norm_num, ?_⟩
  have hLtop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hLtop.eventually_ge_atTop 10000, eventually_ge_atTop (1 : ℕ)] with n hL hn
  let L := Real.log (n : ℝ)
  let X := √((n : ℝ) * L)
  let Y := √((n : ℝ) / L)
  let Z := √(n : ℝ)
  let E := √L
  let P := Nat.primesLE ⌊X⌋₊
  let Q := Nat.primesLE ⌊Z⌋₊
  let R := P.filter (fun p => p ≤ n ∧ n < p * p)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLn : L ≤ n := by linarith [Real.log_le_sub_one_of_pos hn0]
  have hZ0 : 0 < Z := Real.sqrt_pos.2 hn0
  have hY0 : 0 < Y := Real.sqrt_pos.2 (div_pos hn0 hL0)
  have hX0 : 0 < X := Real.sqrt_pos.2 (mul_pos hn0 hL0)
  have hE0 : 0 < E := Real.sqrt_pos.2 hL0
  have hElo : 100 ≤ E := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 100) hL0.le).2
    norm_num
    exact hL
  have hZlo : 100 ≤ Z := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 100) hn0.le).2
    norm_num
    exact_mod_cast (show (10000 : ℝ) ≤ L from hL).trans hLn
  have hXm : 256 ≤ X := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 256) (mul_nonneg hn0.le hL0.le)).2
    have hN : (10000 : ℝ) ≤ n := (show (10000 : ℝ) ≤ L from hL).trans hLn
    have h := mul_le_mul (show (10000 : ℝ) ≤ n from hN) (show 10000 ≤ L from hL) (by norm_num) hn0.le
    linarith only [h]
  have hZX : Z ≤ X := by
    apply Real.sqrt_le_sqrt
    nlinarith only [mul_le_mul_of_nonneg_left hL1 hn0.le]
  have hXn : X ≤ n := Real.sqrt_le_iff.2 ⟨hn0.le, by
    nlinarith only [mul_le_mul_of_nonneg_left hLn hn0.le]⟩
  have hXY : X = Y * L := by
    calc
      X = √((n : ℝ) / L * L ^ 2) := by
        apply congrArg Real.sqrt
        field_simp
      _ = _ := by rw [Real.sqrt_mul (div_nonneg hn0.le hL0.le), Real.sqrt_sq hL0.le]
  have hZY : Z = Y * E := by
    dsimp only [Z, Y, E]
    rw [← Real.sqrt_mul (div_nonneg hn0.le hL0.le), div_mul_cancel₀ _ hL0.ne']
  have hE2 : E ^ 2 = L := Real.sq_sqrt hL0.le
  have hlogXlo : L / 2 ≤ Real.log X := by
    have h := Real.log_le_log hZ0 hZX
    rwa [show Real.log Z = L / 2 from Real.log_sqrt hn0.le] at h
  have hlogXhi : Real.log X ≤ L := Real.log_le_log hX0 hXn
  have hlogX0 : 0 < Real.log X := by linarith
  have hPhi : (P.card : ℝ) ≤ 10 * Y := by
    rw [Nat.primesLE_card_eq_primeCounting]
    refine (prime_count_upper (show 1 < X by linarith only [hXm])).trans ?_
    apply (div_le_iff₀ hlogX0).2
    nlinarith only [hXY, mul_le_mul_of_nonneg_left hlogXlo hY0.le]
  have hPlo : Y / 4 ≤ (P.card : ℝ) := by
    rw [Nat.primesLE_card_eq_primeCounting]
    refine le_trans ?_ (prime_count_lower hXm)
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.log X)).2
    nlinarith only [hXY, mul_le_mul_of_nonneg_left hlogXhi hY0.le]
  have hQhi : (Q.card : ℝ) ≤ Y / 8 := by
    rw [Nat.primesLE_card_eq_primeCounting]
    refine (prime_count_upper (show 1 < Z by linarith only [hZlo])).trans ?_
    rw [show Real.log Z = L / 2 from Real.log_sqrt hn0.le, hZY]
    apply (div_le_iff₀ (by positivity : 0 < L / 2)).2
    have he : 80 * E ≤ L := by
      have h := mul_le_mul_of_nonneg_right hElo hE0.le
      nlinarith only [h, hE2, hE0]
    nlinarith only [mul_le_mul_of_nonneg_left he hY0.le]
  have hsubset : Q ⊆ P := by
    intro p hp
    obtain ⟨h, hprime⟩ := Nat.mem_primesLE.1 hp
    exact Nat.mem_primesLE.2 ⟨h.trans (Nat.floor_mono hZX), hprime⟩
  have hR : R = P \ Q := by
    ext p
    simp only [R, mem_filter, Finset.mem_sdiff]
    apply and_congr_right
    intro hp
    obtain ⟨hpX, hprime⟩ := Nat.mem_primesLE.1 hp
    have hp' : (p : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).1 hpX
    have hpn : p ≤ n := by exact_mod_cast hp'.trans hXn
    rw [and_iff_right hpn, Nat.mem_primesLE, and_iff_left hprime, Nat.le_floor_iff hZ0.le, not_le]
    change n < p * p ↔ √(n : ℝ) < (p : ℝ)
    rw [Real.sqrt_lt hn0.le (by positivity), pow_two]
    exact_mod_cast Iff.rfl
  have hc := card_sdiff_add_card_eq_card hsubset
  rw [← hR] at hc
  have heq : (R.card : ℝ) + Q.card = P.card := by exact_mod_cast hc
  exact ⟨by change (1 / 8 : ℝ) * Y ≤ (R.card : ℝ); linarith only [hPlo, hQhi, heq], hPhi⟩

end OMA.SelfridgePrimeCount


theorem OMA.solution : OMA.R_Erdos912_erdos_912_variants_selfridge_R1.H1 :=
  OMA.SelfridgePrimeCount.scaled
