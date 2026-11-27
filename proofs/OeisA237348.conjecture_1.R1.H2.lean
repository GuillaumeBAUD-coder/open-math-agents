import OMAReductions.R_OeisA237348_conjecture_1_R1
import Mathlib.Data.Nat.Choose.Factorization

-- Step OeisA237348.conjecture_1.R1.H2
-- Credit: @caa1982

open Nat Finset

private lemma two_pow_le_central_binom (n : ℕ) : 2 ^ n ≤ (2 * n).choose n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    have h2 := Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ 2 * (m + 1) by omega)
    rw [show 2 * m - m = m by omega] at h1
    rw [show 2 * (m + 1) - (m + 1) = m + 1 by omega] at h2
    have hfac : (2 * (m + 1)).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      ring
    have hmfac : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
    have hrel : (m + 1) * (2 * (m + 1)).choose (m + 1) = 2 * (2 * m + 1) * (2 * m).choose m := by
      have hpos : 0 < (m + 1) * m.factorial * m.factorial :=
        Nat.mul_pos (Nat.mul_pos (Nat.succ_pos m) (Nat.factorial_pos m)) (Nat.factorial_pos m)
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc (m + 1) * (2 * (m + 1)).choose (m + 1) * ((m + 1) * m.factorial * m.factorial)
          = (2 * (m + 1)).choose (m + 1) * ((m + 1) * m.factorial) * ((m + 1) * m.factorial) := by ring
        _ = (2 * (m + 1)).factorial := by rw [← hmfac]; exact h2
        _ = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := hfac
        _ = (2 * m + 2) * (2 * m + 1) * ((2 * m).choose m * m.factorial * m.factorial) := by rw [h1]
        _ = 2 * (2 * m + 1) * (2 * m).choose m * ((m + 1) * m.factorial * m.factorial) := by ring
    have hle : (m + 1) * (2 * (2 * m).choose m) ≤ (m + 1) * (2 * (m + 1)).choose (m + 1) := by
      rw [hrel]
      nlinarith
    have hstep : 2 * (2 * m).choose m ≤ (2 * (m + 1)).choose (m + 1) :=
      Nat.le_of_mul_le_mul_left hle (Nat.succ_pos m)
    rw [pow_succ']
    exact (Nat.mul_le_mul_left 2 ih).trans hstep

private lemma prime_count_lower (k : ℕ) (hk : 1 ≤ k) :
    2 ^ (k - 1) ≤ k * Nat.count Nat.Prime (2 ^ k + 1) := by
  set n := 2 ^ (k - 1)
  have hn_pos : 0 < n := pow_pos (by decide) _
  have h2n : 2 * n = 2 ^ k := by
    rw [← _root_.pow_succ', Nat.sub_add_cancel hk]
  have hcb_pos : 0 < (2 * n).choose n := Nat.choose_pos (by omega)
  have hprod_eq : (2 * n).choose n =
      ∏ q ∈ ((2 * n).choose n).primeFactors, q ^ (((2 * n).choose n).factorization q) :=
    Nat.prod_primeFactors_pow_factorization hcb_pos.ne'
  have hprod_le : (2 * n).choose n ≤ (2 * n) ^ (((2 * n).choose n).primeFactors.card) := by
    calc (2 * n).choose n
        = ∏ q ∈ ((2 * n).choose n).primeFactors, q ^ (((2 * n).choose n).factorization q) := hprod_eq
      _ ≤ ∏ _q ∈ ((2 * n).choose n).primeFactors, (2 * n) := by
          apply Finset.prod_le_prod'
          intro q _
          exact Nat.pow_factorization_choose_le (by omega)
      _ = (2 * n) ^ (((2 * n).choose n).primeFactors.card) := by simp
  have hsub : ((2 * n).choose n).primeFactors ⊆ (Finset.range (2 * n + 1)).filter Nat.Prime := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ (2 * n).choose n := Nat.dvd_of_mem_primeFactors hq
    have hqle : q ≤ 2 * n := by
      have h1 : (2 * n).choose n ∣ (2 * n).factorial :=
        ⟨n.factorial * (2 * n - n).factorial, by
          rw [← mul_assoc]; exact (Nat.choose_mul_factorial_mul_factorial (by omega)).symm⟩
      exact hqp.dvd_factorial.mp (hqdvd.trans h1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hqp⟩
  have hcard : ((2 * n).choose n).primeFactors.card ≤ Nat.count Nat.Prime (2 ^ k + 1) := by
    rw [Nat.count_eq_card_filter_range, ← h2n]
    exact Finset.card_le_card hsub
  have hpow : 2 ^ n ≤ 2 ^ (k * Nat.count Nat.Prime (2 ^ k + 1)) := by
    calc 2 ^ n ≤ (2 * n).choose n := two_pow_le_central_binom n
      _ ≤ (2 * n) ^ (((2 * n).choose n).primeFactors.card) := hprod_le
      _ = (2 ^ k) ^ (((2 * n).choose n).primeFactors.card) := by rw [h2n]
      _ ≤ (2 ^ k) ^ (Nat.count Nat.Prime (2 ^ k + 1)) :=
          Nat.pow_le_pow_right (pow_pos (by decide) k) hcard
      _ = 2 ^ (k * Nat.count Nat.Prime (2 ^ k + 1)) := (pow_mul 2 k _).symm
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow

private lemma nth_prime_le_two_pow {m k : ℕ} (hk : 1 ≤ k) (hm : m * k < 2 ^ (k - 1)) :
    Nat.nth Nat.Prime m ≤ 2 ^ k := by
  have hcnt := prime_count_lower k hk
  have hlt : m < Nat.count Nat.Prime (2 ^ k + 1) := by
    by_contra hge
    push Not at hge
    have : k * Nat.count Nat.Prime (2 ^ k + 1) ≤ m * k := by
      rw [mul_comm]; exact Nat.mul_le_mul_right k hge
    omega
  have hnth := Nat.nth_lt_of_lt_count hlt
  omega

private lemma five_mul_lt_pow (t : ℕ) (ht : 12 ≤ t) : 5 * t < 2 ^ (t - 5) := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [show m + 1 - 5 = (m - 5) + 1 by omega, pow_succ']
    omega

private lemma six_mul_lt_pow (t : ℕ) (ht : 12 ≤ t) : 6 * t < 2 ^ (t - 2) := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [show m + 1 - 2 = (m - 2) + 1 by omega, pow_succ']
    omega

theorem OMA.solution : OMA.R_OeisA237348_conjecture_1_R1.H2 := by
  intro d hd
  refine ⟨max 12 (2 * d), fun t ht => ?_⟩
  have ht12 : 12 ≤ t := le_trans (le_max_left _ _) ht
  have ht2d : 2 * d ≤ t := le_trans (le_max_right _ _) ht
  dsimp only
  have h1 : Nat.nth Nat.Prime (16 ^ (t + 1) - 1) ≤ 2 ^ (5 * t) := by
    apply nth_prime_le_two_pow (by omega)
    have h16 : 16 ^ (t + 1) = 2 ^ (4 * t + 4) := by
      rw [show (16 : ℕ) = 2 ^ 4 by decide, ← pow_mul]
      congr 1
    have hlt5 := five_mul_lt_pow t ht12
    calc (16 ^ (t + 1) - 1) * (5 * t)
        ≤ 16 ^ (t + 1) * (5 * t) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = 2 ^ (4 * t + 4) * (5 * t) := by rw [h16]
      _ < 2 ^ (4 * t + 4) * 2 ^ (t - 5) := Nat.mul_lt_mul_of_pos_left hlt5 (pow_pos (by decide) _)
      _ = 2 ^ (5 * t - 1) := by rw [← pow_add]; congr 1; omega
  have h2 : Nat.nth Nat.Prime (Nat.nth Nat.Prime (16 ^ (t + 1) - 1) - 1) ≤ 2 ^ (6 * t - 1) := by
    apply nth_prime_le_two_pow (by omega)
    have hlt6 := six_mul_lt_pow t ht12
    calc (Nat.nth Nat.Prime (16 ^ (t + 1) - 1) - 1) * (6 * t - 1)
        ≤ 2 ^ (5 * t) * (6 * t) :=
          Nat.mul_le_mul ((Nat.sub_le _ _).trans h1) (Nat.sub_le _ _)
      _ < 2 ^ (5 * t) * 2 ^ (t - 2) := Nat.mul_lt_mul_of_pos_left hlt6 (pow_pos (by decide) _)
      _ = 2 ^ (6 * t - 1 - 1) := by rw [← pow_add]; congr 1; omega
  have h2d : 2 * d ≤ 2 ^ (6 * t - 1) := by
    have hlin : t ≤ 2 ^ t := Nat.lt_two_pow_self.le
    have hpow : 2 ^ t ≤ 2 ^ (6 * t - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact ht2d.trans (hlin.trans hpow)
  have h64 : 2 ^ (6 * t - 1) + 2 ^ (6 * t - 1) = 64 ^ t := by
    rw [← two_mul, ← _root_.pow_succ', show 6 * t - 1 + 1 = 6 * t by omega, pow_mul]
    rfl
  omega
