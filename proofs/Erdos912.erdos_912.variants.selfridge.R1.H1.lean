import OMAReductions.R_Erdos912_erdos_912_variants_selfridge_R1
import Mathlib

-- Step Erdos912.erdos_912.variants.selfridge.R1.H1: hypothesis H1 of reduction Erdos912.erdos_912.variants.selfridge.R1
-- Credit: @ivillar
-- H1: with X = √(n log n), eventually c √(n / log n) ≤ #{p ≤ X prime : p ≤ n < p²} and
--     π(X) ≤ C √(n / log n).
--
-- Proof: write L = log n and s = √(n / L), so X = s L and √n = s √L. For large n
-- (L ≥ 65536 and L³ ≤ n, from log = o(id) and log^3 = o(id)) we have L ≤ s.
-- Upper bound: Mathlib's Chebyshev.pi_le_log4_mul_div gives π(X) ≤ 4 log 4 · s + √X ≤ (4 log 4 + 1) s.
-- Lower bound: Chebyshev.pi_ge' gives π(X) ≥ s log 2 - 2, the primes p ≤ X with p² ≤ n are
-- at most π(⌊√n⌋) ≤ 4 log 4 √n / L + n^(1/4) ≤ (log 2 / 4) s, and every p ≤ X is ≤ n.
-- Hence the count is at least (3/4) s log 2 - 2 ≥ (log 2 / 2) s.

open Real Finset Filter

namespace OMA.Selfridge912

set_option maxHeartbeats 1600000 in
theorem main_bounds (n : ℕ) (hL : 65536 ≤ Real.log n) (hn3 : Real.log n ^ 3 ≤ n) :
    Real.log 2 / 2 * √((n : ℝ) / Real.log n) ≤
      (((Nat.primesLE ⌊√((n : ℝ) * Real.log n)⌋₊).filter
        (fun p => p ≤ n ∧ n < p * p)).card : ℝ) ∧
    ((Nat.primesLE ⌊√((n : ℝ) * Real.log n)⌋₊).card : ℝ) ≤
      (4 * Real.log 4 + 1) * √((n : ℝ) / Real.log n) := by
  set L := Real.log n with hLdef
  have hL0 : 0 < L := by linarith
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [hLdef, h, Nat.cast_zero, Real.log_zero] at hL
      linarith
    · exact_mod_cast h
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  set s := √((n : ℝ) / L) with hs
  have hs2 : s ^ 2 = n / L := Real.sq_sqrt (by positivity)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hLs : L ≤ s := by
    rw [hs, Real.le_sqrt hL0.le (by positivity), le_div_iff₀ hL0]
    nlinarith
  have hX : √((n : ℝ) * L) = s * L := by
    have e : (n : ℝ) * L = (n / L) * L ^ 2 := by field_simp
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hL0.le]
  have hsqn : √(n : ℝ) = s * √L := by
    have e : (n : ℝ) = (n / L) * L := by field_simp
    conv_lhs => rw [e]
    rw [Real.sqrt_mul (by positivity)]
  have hsqL : 256 ≤ √L := by
    rw [Real.le_sqrt (by norm_num) hL0.le]
    linarith
  have hsqL2 : √L * √L = L := Real.mul_self_sqrt hL0.le
  set X := √((n : ℝ) * L) with hXdef
  have hXpos : 0 < X := by rw [hX]; positivity
  have hX2 : 2 ≤ X := by rw [hX]; nlinarith
  have hlogX : Real.log X = (L + Real.log L) / 2 := by
    rw [hXdef, Real.log_sqrt (by positivity), Real.log_mul hnpos.ne' hL0.ne']
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlogLle : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hlogX1 : L / 2 ≤ Real.log X := by rw [hlogX]; linarith
  have hlogX2 : Real.log X ≤ L := by rw [hlogX]; linarith
  have hL3 : L ≤ L ^ 3 := by
    have h1 : 1 ≤ L ^ 2 := by nlinarith
    nlinarith
  have hLn : L ≤ n := hL3.trans hn3
  have hXn : X ≤ n := by
    have e : (s * L) ^ 2 = n * L := by
      rw [mul_pow, hs2]
      field_simp
    rw [hX]
    nlinarith
  -- upper bound for the number of primes up to X
  have hup := Chebyshev.pi_le_log4_mul_div (x := X) (by linarith)
  have hlogsqX : Real.log √X = Real.log X / 2 := Real.log_sqrt hXpos.le
  have hsqX : √X ≤ s := by
    calc √X ≤ √(s ^ 2) := Real.sqrt_le_sqrt (by rw [hX]; nlinarith)
      _ = s := Real.sqrt_sq hs0.le
  have hlsX : 0 < Real.log √X := by rw [hlogsqX]; linarith
  have hfirst : Real.log 4 * X / Real.log √X ≤ 4 * Real.log 4 * s := by
    rw [div_le_iff₀ hlsX, hlogsqX]
    have h4 : 0 ≤ Real.log 4 := by rw [hlog4]; linarith
    have e : Real.log 4 * X = Real.log 4 * s * L := by rw [hX]; ring
    nlinarith [mul_le_mul_of_nonneg_left hlogX1 (mul_nonneg h4 hs0.le)]
  have hPcard : ((Nat.primesLE ⌊X⌋₊).card : ℝ) = Nat.primeCounting ⌊X⌋₊ := by
    rw [Nat.primesLE_card_eq_primeCounting]
  have hupper : ((Nat.primesLE ⌊X⌋₊).card : ℝ) ≤ (4 * Real.log 4 + 1) * s := by
    rw [hPcard]
    linarith
  -- lower bound for the number of primes up to X
  have hlow := Chebyshev.pi_ge' (x := X) (by linarith)
  have hlogX0 : 0 < Real.log X := by linarith
  have hlog2X : Real.log (X + 2) ≤ Real.log 2 + Real.log X := by
    rw [← Real.log_mul (by norm_num) hXpos.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hXL : 4 * L ≤ X := by rw [hX]; nlinarith
  have hXlog : X * (1 / 2) ≤ X * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith) hXpos.le
  have hN0 : 0 ≤ (X - 1) * Real.log 2 - Real.log (X + 2) := by
    have e : (X - 1) * Real.log 2 = X * Real.log 2 - Real.log 2 := by ring
    rw [e]
    linarith
  have hlow2 : ((X - 1) * Real.log 2 - Real.log (X + 2)) / L ≤
      ((X - 1) * Real.log 2 - Real.log (X + 2)) / Real.log X :=
    div_le_div_of_nonneg_left hN0 hlogX0 hlogX2
  have hlow3 : s * Real.log 2 - 2 ≤ ((X - 1) * Real.log 2 - Real.log (X + 2)) / L := by
    rw [le_div_iff₀ hL0]
    have e1 : (s * Real.log 2 - 2) * L = X * Real.log 2 - 2 * L := by rw [hX]; ring
    have e2 : (X - 1) * Real.log 2 = X * Real.log 2 - Real.log 2 := by ring
    rw [e1, e2]
    linarith
  have hpiX : s * Real.log 2 - 2 ≤ (Nat.primeCounting ⌊X⌋₊ : ℝ) := by linarith
  -- upper bound for the primes up to the square root of n
  have hsqn1 : 1 < √(n : ℝ) := by rw [hsqn]; nlinarith
  have hupsq := Chebyshev.pi_le_log4_mul_div (x := √(n : ℝ)) hsqn1
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt] at hupsq
  have hlogsqsq : Real.log √(√(n : ℝ)) = L / 4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hnpos.le]
    ring
  rw [hlogsqsq] at hupsq
  have hterm1 : Real.log 4 * √(n : ℝ) / (L / 4) ≤ Real.log 2 / 8 * s := by
    rw [div_le_iff₀ (by positivity), hsqn, hlog4]
    have hl0 : 0 < Real.log 2 := by linarith
    have key : 64 ≤ √L := by linarith
    have hA : 0 ≤ Real.log 2 * s * √L := by positivity
    have hk := mul_le_mul_of_nonneg_left key hA
    have e : Real.log 2 / 8 * s * (L / 4) = Real.log 2 * s * √L * √L / 32 := by
      rw [mul_assoc (Real.log 2 * s) √L √L, hsqL2]
      ring
    rw [e]
    nlinarith [hk]
  have hterm2 : √(√(n : ℝ)) ≤ Real.log 2 / 8 * s := by
    have ht0 : 0 ≤ Real.log 2 / 8 * s := by positivity
    calc √(√(n : ℝ)) ≤ √((Real.log 2 / 8 * s) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [hsqn]
          have hsL : 0 < √L := by linarith
          have hsbig : 256 * √L ≤ s := by nlinarith
          have hc : (1 : ℝ) / 200 ≤ (Real.log 2 / 8) ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hsbig hs0.le]
      _ = Real.log 2 / 8 * s := Real.sqrt_sq ht0
  have hpisq : (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ Real.log 2 / 4 * s := by linarith
  -- the primes up to X that exceed the square root of n
  have hsub : (Nat.primesLE ⌊X⌋₊).filter (fun p => ¬ (p ≤ n ∧ n < p * p)) ⊆
      Nat.primesLE (Nat.sqrt n) := by
    intro p hp
    simp only [Finset.mem_filter, Nat.mem_primesLE] at hp ⊢
    obtain ⟨⟨hpX, hpp⟩, hnot⟩ := hp
    have hpn : p ≤ n := le_trans hpX (Nat.floor_le_of_le hXn)
    refine ⟨Nat.le_sqrt.mpr ?_, hpp⟩
    by_contra h
    exact hnot ⟨hpn, by omega⟩
  have hcsub := Finset.card_le_card hsub
  rw [Nat.primesLE_card_eq_primeCounting] at hcsub
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Nat.primesLE ⌊X⌋₊) (fun p => p ≤ n ∧ n < p * p)
  rw [Nat.primesLE_card_eq_primeCounting] at hsplit
  have hsplitR : (((Nat.primesLE ⌊X⌋₊).filter (fun p => p ≤ n ∧ n < p * p)).card : ℝ)
      + (((Nat.primesLE ⌊X⌋₊).filter (fun p => ¬ (p ≤ n ∧ n < p * p))).card : ℝ)
      = Nat.primeCounting ⌊X⌋₊ := by exact_mod_cast hsplit
  have hcsubR : (((Nat.primesLE ⌊X⌋₊).filter (fun p => ¬ (p ≤ n ∧ n < p * p))).card : ℝ)
      ≤ Nat.primeCounting (Nat.sqrt n) := by exact_mod_cast hcsub
  refine ⟨?_, hupper⟩
  nlinarith

theorem selfridge_bounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    let X := √((n : ℝ) * Real.log n)
    let P := Nat.primesLE ⌊X⌋₊
    c * √((n : ℝ) / Real.log n) ≤ ((P.filter (fun p => p ≤ n ∧ n < p * p)).card : ℝ) ∧
    (P.card : ℝ) ≤ C * √((n : ℝ) / Real.log n) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / 2, 4 * Real.log 4 + 1, by positivity, by positivity, ?_⟩
  have h1 : ∀ᶠ n : ℕ in atTop, 65536 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 65536
  have h2 : ∀ᶠ n : ℕ in atTop, Real.log n ^ 3 ≤ n := by
    have hb := (Real.isLittleO_pow_log_id_atTop (n := 3)).bound one_pos
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hb] with n hn
    simp only [id, one_mul, Real.norm_eq_abs] at hn
    calc Real.log n ^ 3 ≤ |Real.log n ^ 3| := le_abs_self _
      _ ≤ |(n : ℝ)| := hn
      _ = n := abs_of_nonneg (Nat.cast_nonneg n)
  filter_upwards [h1, h2] with n hn1 hn2
  exact main_bounds n hn1 hn2

end OMA.Selfridge912

theorem OMA.solution : OMA.R_Erdos912_erdos_912_variants_selfridge_R1.H1 := by
  unfold OMA.R_Erdos912_erdos_912_variants_selfridge_R1.H1
  exact OMA.Selfridge912.selfridge_bounds
