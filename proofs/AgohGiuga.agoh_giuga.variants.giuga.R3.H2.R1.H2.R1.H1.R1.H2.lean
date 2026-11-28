import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H2_R1_H1_R1
import Mathlib

open Finset

namespace PrimeLogarithmicSum

private def trial (n d : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 => (n % d != 0) && trial n (d + 1) len

private theorem trial_spec (n d len : ℕ) :
    trial n d len = true ↔ ∀ k : ℕ, d ≤ k → k < d + len → ¬ k ∣ n := by
  induction len generalizing d with
  | zero => simp only [trial, add_zero, true_iff]; omega
  | succ len ih =>
    simp only [trial, Bool.and_eq_true, bne_iff_ne, ih, Nat.dvd_iff_mod_eq_zero]
    constructor
    · rintro ⟨h, hs⟩ k lo hi
      by_cases eq : k = d
      · simpa [eq] using h
      · exact hs k (by omega) (by omega)
    · intro h
      exact ⟨h d (by omega) (by omega), fun k lo hi => h k (by omega) (by omega)⟩

private def sieve (n : ℕ) : Bool :=
  decide (2 ≤ n) && trial n 2 (n.sqrt - 1)

private theorem sieve_spec (n : ℕ) : sieve n = true ↔ n.Prime := by
  simp only [sieve, Bool.and_eq_true, decide_eq_true_eq, trial_spec]
  constructor
  · rintro ⟨hn, h⟩
    by_contra notPrime
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have hs := Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self (by omega) notPrime)
    exact h n.minFac fac.two_le (by omega) (Nat.minFac_dvd n)
  · intro hp
    refine ⟨hp.two_le, fun k lo hi => ?_⟩
    have sk := Nat.sqrt_lt_self hp.one_lt
    have : k < n := by omega
    exact (Nat.prime_def_lt'.mp hp).2 k lo this

private def basis : ℕ := 33145029365917644537041586451002838777754047982048976093256545773949681076083753038263261851007891975336318712022358509317861766127318306017798990

private theorem basis_eq : primorial 363 = basis := by decide +kernel

private def validPrime (n : ℕ) : Bool :=
  if n ≤ 363 then sieve n else Nat.gcd n basis == 1

private theorem validPrime_spec {n : ℕ} (bound : n ≤ 131072) (h : validPrime n = true) :
    n.Prime := by
  by_cases low : n ≤ 363
  · exact (sieve_spec _).mp (by simpa [validPrime, low] using h)
  · have cop : Nat.gcd n basis = 1 := by simpa [validPrime, low] using h
    by_contra bad
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have small := Nat.minFac_sq_le_self (show 0 < n by omega) bad
    have fd : n.minFac ≤ 363 := by
      by_contra! h
      have sq := Nat.pow_le_pow_left (show 364 ≤ n.minFac by omega) 2
      omega
    have div : n.minFac ∣ Nat.gcd n basis := Nat.dvd_gcd (Nat.minFac_dvd n)
      (basis_eq ▸ fac.dvd_primorial_iff.mpr fd)
    rw [cop] at div
    exact fac.ne_one (Nat.dvd_one.mp div)

private def denominator (a k : ℕ) : ℕ :=
  3 * 10000000000 * (a + 2 ^ k) ^ 3

private def numerator (a k : ℕ) : ℕ :=
  3 * k * 6931471803 * (a + 2 ^ k) ^ 3 +
    6 * 10000000000 * (a - 2 ^ k) * (a + 2 ^ k) ^ 2 +
    2 * 10000000000 * (a - 2 ^ k) ^ 3

private theorem lower_log {a k : ℕ} (hk : 2 ^ k ≤ a) :
    (numerator a k : ℝ) / (denominator a k : ℝ) ≤ Real.log a := by
  let q : ℝ := (2 : ℝ) ^ k
  let A : ℝ := a
  have hq : 0 < q := by dsimp [q]; positivity
  have hle : q ≤ A := by dsimp [q, A]; exact_mod_cast hk
  have ha : 0 < A := hq.trans_le hle
  have pos : 0 < A + q := by positivity
  let t := (A - q) / (A + q)
  have h0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hle) pos.le
  have h1 : t < 1 := (div_lt_one pos).2 (by linarith)
  have h := Real.sum_range_le_log_div h0 h1 2
  norm_num [Finset.sum_range_succ] at h
  have eq : (1 + t) / (1 - t) = A / q := by
    have den : 1 - t ≠ 0 := by linarith
    dsimp [t] at den ⊢
    field_simp [hq.ne', pos.ne', den]
    <;> ring
  rw [eq, Real.log_div ha.ne' hq.ne'] at h
  have lg : Real.log q = k * Real.log 2 := by dsimp [q]; rw [Real.log_pow]
  rw [lg] at h
  have log2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by
    have h' := Real.log_two_gt_d9.le
    norm_num at h' ⊢
    exact h'
  have scaled := mul_le_mul_of_nonneg_left log2 (Nat.cast_nonneg k : 0 ≤ (k : ℝ))
  have identity :
      (numerator a k : ℝ) / (denominator a k : ℝ) =
        (k : ℝ) * (6931471803 / 10000000000) + 2 * (t + t ^ 3 / 3) := by
    unfold numerator denominator
    push_cast [Nat.cast_sub hk]
    have nz : (a : ℝ) + (2 : ℝ) ^ k ≠ 0 := pos.ne'
    dsimp [t, A, q]
    field_simp [nz]
    <;> ring
  rw [identity]
  change _ ≤ Real.log A
  linarith only [h, scaled]

private def scaled (n : ℕ) : ℕ :=
  if validPrime n then
    let k := Nat.log 2 n
    10000000 * numerator n k / (n * denominator n k)
  else 0

private theorem scaled_le {n : ℕ} (prime : n.Prime) :
    (scaled n : ℝ) ≤ 10000000 * (Real.log n / n) := by
  by_cases ok : validPrime n = true
  · let k := Nat.log 2 n
    have hk : 2 ^ k ≤ n := Nat.pow_log_le_self 2 prime.ne_zero
    have np : 0 < (n : ℝ) := by exact_mod_cast prime.pos
    have dp : 0 < (denominator n k : ℝ) := by
      unfold denominator
      push_cast
      positivity
    rw [scaled, if_pos ok]
    change ((10000000 * numerator n k / (n * denominator n k) : ℕ) : ℝ) ≤ _
    calc
      _ ≤ (10000000 : ℝ) * (numerator n k : ℝ) / ((n : ℝ) * (denominator n k : ℝ)) := by
        apply (le_div_iff₀ (mul_pos np dp)).mpr
        exact_mod_cast Nat.div_mul_le_self (10000000 * numerator n k) (n * denominator n k)
      _ = 10000000 * (((numerator n k : ℝ) / (denominator n k : ℝ)) / n) := by
        field_simp [np.ne', dp.ne']
      _ ≤ 10000000 * (Real.log n / n) := by
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (lower_log hk) np.le) (by norm_num)
  · rw [scaled, if_neg ok, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (div_nonneg
      (Real.log_nonneg (by exact_mod_cast prime.one_le)) (Nat.cast_nonneg n))

private def chunk (i : ℕ) : ℕ :=
  ∑ j ∈ range 4096, scaled (4096 * i + j)

private theorem chunks (m : ℕ) :
    ∑ i ∈ range m, chunk i = ∑ n ∈ range (4096 * m), scaled n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, Nat.mul_succ, sum_range_add]
    rfl

private def totals : ℕ → ℕ
  | 0 => 70055534
  | 1 => 6827285
  | 2 => 4032988
  | 3 => 2895903
  | 4 => 2201809
  | 5 => 1841279
  | 6 => 1527079
  | 7 => 1305487
  | 8 => 1191391
  | 9 => 1033204
  | 10 => 968807
  | 11 => 851886
  | 12 => 807217
  | 13 => 753892
  | 14 => 676012
  | 15 => 632517
  | 16 => 599453
  | 17 => 584883
  | 18 => 545313
  | 19 => 508430
  | 20 => 478138
  | 21 => 470389
  | 22 => 446356
  | 23 => 419777
  | 24 => 419834
  | 25 => 382529
  | 26 => 371585
  | 27 => 358223
  | 28 => 349699
  | 29 => 346487
  | 30 => 324869
  | 31 => 319947
  | _ => 0

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk0 : chunk 0 = totals 0 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk1 : chunk 1 = totals 1 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk2 : chunk 2 = totals 2 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk3 : chunk 3 = totals 3 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk4 : chunk 4 = totals 4 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk5 : chunk 5 = totals 5 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk6 : chunk 6 = totals 6 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk7 : chunk 7 = totals 7 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk8 : chunk 8 = totals 8 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk9 : chunk 9 = totals 9 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk10 : chunk 10 = totals 10 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk11 : chunk 11 = totals 11 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk12 : chunk 12 = totals 12 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk13 : chunk 13 = totals 13 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk14 : chunk 14 = totals 14 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk15 : chunk 15 = totals 15 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk16 : chunk 16 = totals 16 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk17 : chunk 17 = totals 17 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk18 : chunk 18 = totals 18 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk19 : chunk 19 = totals 19 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk20 : chunk 20 = totals 20 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk21 : chunk 21 = totals 21 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk22 : chunk 22 = totals 22 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk23 : chunk 23 = totals 23 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk24 : chunk 24 = totals 24 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk25 : chunk 25 = totals 25 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk26 : chunk 26 = totals 26 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk27 : chunk 27 = totals 27 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk28 : chunk 28 = totals 28 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk29 : chunk 29 = totals 29 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk30 : chunk 30 = totals 30 := by decide +kernel

set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
private theorem chunk31 : chunk 31 = totals 31 := by decide +kernel

private theorem checked (i : ℕ) (hi : i < 32) : chunk i = totals i := by
  interval_cases i
  · exact chunk0
  · exact chunk1
  · exact chunk2
  · exact chunk3
  · exact chunk4
  · exact chunk5
  · exact chunk6
  · exact chunk7
  · exact chunk8
  · exact chunk9
  · exact chunk10
  · exact chunk11
  · exact chunk12
  · exact chunk13
  · exact chunk14
  · exact chunk15
  · exact chunk16
  · exact chunk17
  · exact chunk18
  · exact chunk19
  · exact chunk20
  · exact chunk21
  · exact chunk22
  · exact chunk23
  · exact chunk24
  · exact chunk25
  · exact chunk26
  · exact chunk27
  · exact chunk28
  · exact chunk29
  · exact chunk30
  · exact chunk31

private theorem exact_total : (∑ n ∈ range 131072, scaled n) = 104528202 := by
  change (∑ n ∈ range (4096 * 32), scaled n) = _
  rw [← chunks]
  calc
    (∑ i ∈ range 32, chunk i) = ∑ i ∈ range 32, totals i :=
      Finset.sum_congr rfl fun i hi => checked i (Finset.mem_range.mp hi)
    _ = 104528202 := by decide +kernel

theorem lower : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H2_R1_H1_R1.H2 := by
  classical
  let S := (range 131072).filter Nat.Prime
  let T := (Ioc 0 (2 ^ 17 : ℕ)).filter Nat.Prime
  have subset : S ⊆ T := by
    intro p h
    obtain ⟨hp, hprime⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hprime.pos,
      by have h := mem_range.mp hp; norm_num; omega⟩, hprime⟩
  have totals_eq : (∑ p ∈ S, scaled p) = 104528202 := by
    change (∑ p ∈ (range 131072).filter Nat.Prime, scaled p) = _
    rw [sum_filter, ← exact_total]
    apply sum_congr rfl
    intro p hp
    by_cases h : p.Prime
    · simp [h]
    · have not_valid : ¬ validPrime p = true := by
        intro hv
        exact h (validPrime_spec (by have hh := mem_range.mp hp; omega) hv)
      simp [h, scaled, not_valid]
  have hsum : (104528202 : ℝ) ≤ 10000000 * ∑ p ∈ S, Real.log (p : ℝ) / p := by
    calc
      (104528202 : ℝ) = ((∑ p ∈ S, scaled p : ℕ) : ℝ) := by
        exact_mod_cast totals_eq.symm
      _ ≤ _ := by
        rw [Nat.cast_sum, mul_sum]
        exact sum_le_sum fun p hp => scaled_le (mem_filter.mp hp).2
  have hlog := Real.log_two_lt_d9
  have hs : 15 * Real.log 2 ≤ ∑ p ∈ S, Real.log (p : ℝ) / p := by
    linarith
  exact hs.trans (sum_le_sum_of_subset_of_nonneg subset (by
    intro p hp _
    have hprime := (mem_filter.mp hp).2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg p)))

end PrimeLogarithmicSum

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H2_R1_H1_R1.H2 :=
  PrimeLogarithmicSum.lower