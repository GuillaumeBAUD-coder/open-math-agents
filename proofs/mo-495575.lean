import OMAStatements.S_mo_495575

/-!
# Proof of MathOverflow 495575

For all integers `k ≥ 4`,
`(-1 : ℚ)^(k - 1) / k < ∑ m ∈ Finset.Ico 2 k, ((-1 : ℚ)^m / m) * (1 / (k - m)^m + 1 / (k - m + 1)^m)`.

For `4 ≤ k < 28`, we verify directly by finite computation over `ℚ`.
For `k ≥ 28`, we isolate `m = 2`, `m = 3`, `m = 4`, and `m = k - 1`, and bound every intermediate
term `5 ≤ m ≤ k - 2` below by `-(1 / (10 * k^4))` using `(k - m)^m ≥ 4 * k^4`, which leaves a
strictly positive net margin of at least `7 / (10 * k^3)`.
-/

namespace OMA.MO495575

open Finset

private def term (k m : ℕ) : ℚ :=
  ((-1 : ℚ) ^ m / (m : ℚ)) *
    (1 / ((k - m : ℕ) : ℚ) ^ m + 1 / ((k - m + 1 : ℕ) : ℚ) ^ m)

private lemma pow_three_half_ge : ∀ n : ℕ, 15 ≤ n → 4 * (2 * n) ^ 4 ≤ 3 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h1 : 4 * (2 * (n + 1)) ^ 4 ≤ 3 * (4 * (2 * n) ^ 4) := by
      have hsub : 2 * n ^ 4 ≥ 4 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1 := by
        have : n ^ 3 ≥ 15 * n ^ 2 := by nlinarith
        have : n ^ 4 ≥ 15 * n ^ 3 := by nlinarith
        nlinarith
      have hstep : 16 * (n + 1) ^ 4 ≤ 48 * n ^ 4 := by nlinarith
      linarith [show (2 * (n + 1)) ^ 4 = 16 * (n + 1) ^ 4 by ring,
                show (2 * n) ^ 4 = 16 * n ^ 4 by ring]
    calc 4 * (2 * (n + 1)) ^ 4 ≤ 3 * (4 * (2 * n) ^ 4) := h1
      _ ≤ 3 * 3 ^ n := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (n + 1) := by ring

private lemma pow_two_ge_four_k4 : ∀ k : ℕ, 28 ≤ k → 4 * k ^ 4 ≤ 2 ^ (k - 2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hsub : k + 1 - 2 = (k - 2) + 1 := by omega
    rw [hsub, pow_succ]
    have hstep : (k + 1) ^ 4 ≤ 2 * k ^ 4 := by
      have h1 : k ^ 3 ≥ 28 * k ^ 2 := by nlinarith
      have h2 : k ^ 4 ≥ 28 * k ^ 3 := by nlinarith
      nlinarith
    calc 4 * (k + 1) ^ 4 ≤ 4 * (2 * k ^ 4) := Nat.mul_le_mul_left 4 hstep
      _ = (4 * k ^ 4) * 2 := by ring
      _ ≤ 2 ^ (k - 2) * 2 := Nat.mul_le_mul_right 2 ih

private lemma pow_two_ge_ten_k2 {k : ℕ} (hk : 28 ≤ k) : 10 * k ^ 2 ≤ 2 ^ (k - 1) := by
  have h := pow_two_ge_four_k4 k hk
  have h1 : 2 ^ (k - 2) ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 10 * k ^ 2 ≤ 4 * k ^ 4 := by
    have hk2 : 10 ≤ 4 * k ^ 2 := by nlinarith
    calc 10 * k ^ 2 ≤ (4 * k ^ 2) * k ^ 2 := Nat.mul_le_mul_right (k ^ 2) hk2
      _ = 4 * k ^ 4 := by ring
  omega

private lemma denom_ge_four_k4 {k m : ℕ} (hk : 28 ≤ k) (hm1 : 5 ≤ m) (hm2 : m ≤ k - 2) :
    4 * k ^ 4 ≤ (k - m) ^ m := by
  by_cases hlast : m = k - 2
  · subst hlast
    have : k - (k - 2) = 2 := by omega
    rw [this]
    exact pow_two_ge_four_k4 k hk
  · have h3 : 3 ≤ k - m := by omega
    by_cases h5 : m = 5
    · subst h5
      by_cases hk28 : k = 28
      · subst hk28; decide
      · have hk29 : (29 : ℤ) ≤ k := by omega
        have hsub : (k - 5 : ℤ) ^ 5 ≥ 4 * (k : ℤ) ^ 4 := by
          have hsq : (k : ℤ) ^ 2 ≥ 29 * k := by nlinarith
          have hcu : (k : ℤ) ^ 3 ≥ 29 * k ^ 2 := by nlinarith
          have hqu : (k : ℤ) ^ 4 ≥ 0 := by positivity
          have h1 : 0 ≤ ((k : ℤ) - 29) * (k : ℤ) ^ 4 := mul_nonneg (by linarith) hqu
          nlinarith [show ((k : ℤ) - 5) ^ 5 - 4 * (k : ℤ) ^ 4 =
            ((k : ℤ) - 29) * k ^ 4 + 250 * k ^ 3 - 1250 * k ^ 2 + 3125 * k - 3125 by ring]
        have hcast : ((k - 5 : ℕ) : ℤ) = (k : ℤ) - 5 := by omega
        have : (4 * k ^ 4 : ℤ) ≤ ((k - 5 : ℕ) : ℤ) ^ 5 := by rw [hcast]; linarith
        exact_mod_cast this
    · by_cases hmid : m ≤ k / 2
      · have hm6 : 6 ≤ m := by omega
        have hkm : k / 2 ≤ k - m := by omega
        have h1 : (k / 2) ^ 6 ≤ (k - m) ^ 6 := Nat.pow_le_pow_left hkm 6
        have h2 : (k - m) ^ 6 ≤ (k - m) ^ m := Nat.pow_le_pow_right (by omega) hm6
        have h3' : 4 * k ^ 4 ≤ (k / 2) ^ 6 := by
          set q := k / 2
          have hq14 : 14 ≤ q := by omega
          have hkq : k ≤ 2 * q + 1 := by omega
          have h4 : k ^ 4 ≤ (2 * q + 1) ^ 4 := Nat.pow_le_pow_left hkq 4
          have h5' : 4 * (2 * q + 1) ^ 4 ≤ q ^ 6 := by
            have hq2 : q ^ 2 ≥ 14 * q := by nlinarith
            have hq3 : q ^ 3 ≥ 14 * q ^ 2 := by nlinarith
            have hq4 : q ^ 4 ≥ 14 * q ^ 3 := by nlinarith
            have hq5 : q ^ 5 ≥ 14 * q ^ 4 := by nlinarith
            have hq6 : q ^ 6 ≥ 14 * q ^ 5 := by nlinarith
            nlinarith [show 4 * (2 * q + 1) ^ 4 =
              64 * q ^ 4 + 128 * q ^ 3 + 96 * q ^ 2 + 32 * q + 4 by ring]
          omega
        omega
      · have hmgt : k / 2 + 1 ≤ m := by omega
        have h1 : 3 ^ (k / 2 + 1) ≤ 3 ^ m := Nat.pow_le_pow_right (by decide) hmgt
        have h2 : 3 ^ m ≤ (k - m) ^ m := Nat.pow_le_pow_left h3 m
        have hn15 : 15 ≤ k / 2 + 1 := by omega
        have hpow := pow_three_half_ge (k / 2 + 1) hn15
        have hkle : k ≤ 2 * (k / 2 + 1) := by omega
        have hk4 : 4 * k ^ 4 ≤ 4 * (2 * (k / 2 + 1)) ^ 4 :=
          Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hkle 4)
        omega

private lemma term_nonneg_of_even {k m : ℕ} (he : Even m) : 0 ≤ term k m := by
  unfold term
  rw [he.neg_one_pow]
  positivity

private lemma term_ge_neg_tail {k m : ℕ} (hk : 28 ≤ k) (hm1 : 5 ≤ m) (hm2 : m ≤ k - 2) :
    -((1 : ℚ) / (10 * (k : ℚ) ^ 4)) ≤ term k m := by
  rcases Nat.even_or_odd m with he | ho
  · have h0 : 0 ≤ (1 : ℚ) / (10 * (k : ℚ) ^ 4) := by positivity
    linarith [term_nonneg_of_even (k := k) he]
  · unfold term
    rw [ho.neg_one_pow]
    have hkm_pos : (0 : ℚ) < ((k - m : ℕ) : ℚ) := by
      have : 0 < k - m := by omega
      exact_mod_cast this
    have hkm1_le : ((k - m : ℕ) : ℚ) ^ m ≤ ((k - m + 1 : ℕ) : ℚ) ^ m := by
      gcongr
      omega
    have hinv_le : (1 : ℚ) / ((k - m + 1 : ℕ) : ℚ) ^ m ≤ 1 / ((k - m : ℕ) : ℚ) ^ m :=
      one_div_le_one_div_of_le (pow_pos hkm_pos m) hkm1_le
    have hden : (4 * (k : ℚ) ^ 4) ≤ ((k - m : ℕ) : ℚ) ^ m := by
      exact_mod_cast denom_ge_four_k4 hk hm1 hm2
    have h4k4_pos : (0 : ℚ) < 4 * (k : ℚ) ^ 4 := by positivity
    have hinv_k4 : (1 : ℚ) / ((k - m : ℕ) : ℚ) ^ m ≤ 1 / (4 * (k : ℚ) ^ 4) :=
      one_div_le_one_div_of_le h4k4_pos hden
    have hm5 : (5 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1
    have h1m : (1 : ℚ) / (m : ℚ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hm5
    have hsum_le :
        (1 : ℚ) / ((k - m : ℕ) : ℚ) ^ m + 1 / ((k - m + 1 : ℕ) : ℚ) ^ m ≤
          2 / (4 * (k : ℚ) ^ 4) := by
      have : (1 : ℚ) / (4 * (k : ℚ) ^ 4) + 1 / (4 * (k : ℚ) ^ 4) = 2 / (4 * (k : ℚ) ^ 4) := by
        ring
      linarith
    have hsum_nonneg :
        0 ≤ (1 : ℚ) / ((k - m : ℕ) : ℚ) ^ m + 1 / ((k - m + 1 : ℕ) : ℚ) ^ m := by positivity
    have hmul :
        ((1 : ℚ) / (m : ℚ)) *
          (1 / ((k - m : ℕ) : ℚ) ^ m + 1 / ((k - m + 1 : ℕ) : ℚ) ^ m) ≤
        (1 / 5) * (2 / (4 * (k : ℚ) ^ 4)) :=
      mul_le_mul h1m hsum_le hsum_nonneg (by norm_num)
    have hsimp : (1 / 5 : ℚ) * (2 / (4 * (k : ℚ) ^ 4)) = 1 / (10 * (k : ℚ) ^ 4) := by ring
    have hneg : (-1 : ℚ) / (m : ℚ) = -((1 : ℚ) / (m : ℚ)) := by ring
    rw [hneg, neg_mul]
    linarith

private lemma sum_tail_ge {k : ℕ} (hk : 28 ≤ k) :
    -((1 : ℚ) / (10 * (k : ℚ) ^ 3)) ≤ ∑ m ∈ Ico 5 (k - 1), term k m := by
  have hcard : ((Ico 5 (k - 1)).card : ℚ) ≤ (k : ℚ) := by
    rw [Nat.card_Ico]
    exact_mod_cast (show k - 1 - 5 ≤ k by omega)
  have h1 : ∑ _m ∈ Ico 5 (k - 1), (-((1 : ℚ) / (10 * (k : ℚ) ^ 4))) ≤
      ∑ m ∈ Ico 5 (k - 1), term k m := by
    refine Finset.sum_le_sum fun m hm => ?_
    rw [Finset.mem_Ico] at hm
    exact term_ge_neg_tail hk hm.1 (by omega)
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have hkpos : (0 : ℚ) < (k : ℚ) := by positivity
  have hmul : ((Ico 5 (k - 1)).card : ℚ) / (10 * (k : ℚ) ^ 4) ≤
      (k : ℚ) / (10 * (k : ℚ) ^ 4) := by
    gcongr
  have heq : (k : ℚ) / (10 * (k : ℚ) ^ 4) = 1 / (10 * (k : ℚ) ^ 3) := by
    field_simp
  have hmul' : ((Ico 5 (k - 1)).card : ℚ) * (-((1 : ℚ) / (10 * (k : ℚ) ^ 4))) =
      -(((Ico 5 (k - 1)).card : ℚ) / (10 * (k : ℚ) ^ 4)) := by ring
  linarith

private lemma term_two_sub_last {k : ℕ} (hk : 28 ≤ k) :
    (2 : ℚ) / (k : ℚ) ^ 3 ≤
      1 / (2 * ((k - 2 : ℕ) : ℚ) ^ 2) + 1 / (2 * ((k - 1 : ℕ) : ℚ) ^ 2) -
        1 / ((k : ℚ) * ((k - 1 : ℕ) : ℚ)) := by
  have hk' : (28 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hk1 : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hk2 : ((k - 2 : ℕ) : ℚ) = (k : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hk1, hk2]
  have hkp : (0 : ℚ) < (k : ℚ) := by linarith
  have hk1p : (0 : ℚ) < (k : ℚ) - 1 := by linarith
  have hk2p : (0 : ℚ) < (k : ℚ) - 2 := by linarith
  have hpos : 0 < 2 * (k : ℚ) ^ 3 * ((k : ℚ) - 1) ^ 2 * ((k : ℚ) - 2) ^ 2 := by positivity
  rw [← sub_nonneg]
  have hrew :
      1 / (2 * ((k : ℚ) - 2) ^ 2) + 1 / (2 * ((k : ℚ) - 1) ^ 2) -
        1 / ((k : ℚ) * ((k : ℚ) - 1)) - 2 / (k : ℚ) ^ 3 =
      (13 * (k : ℚ) ^ 3 - 44 * (k : ℚ) ^ 2 + 48 * (k : ℚ) - 16) /
        (2 * (k : ℚ) ^ 3 * ((k : ℚ) - 1) ^ 2 * ((k : ℚ) - 2) ^ 2) := by
    field_simp
    ring
  rw [hrew]
  refine div_nonneg ?_ hpos.le
  nlinarith [show (k : ℚ) ^ 2 ≥ 28 * (k : ℚ) by nlinarith]

private lemma term_three_bound {k : ℕ} (hk : 28 ≤ k) :
    1 / (3 * ((k - 3 : ℕ) : ℚ) ^ 3) + 1 / (3 * ((k - 2 : ℕ) : ℚ) ^ 3) ≤ 1 / (k : ℚ) ^ 3 := by
  have hk' : (28 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hk2 : ((k - 2 : ℕ) : ℚ) = (k : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
  have hk3 : ((k - 3 : ℕ) : ℚ) = (k : ℚ) - 3 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hk2, hk3]
  have hkp : (0 : ℚ) < (k : ℚ) := by linarith
  have hk2p : (0 : ℚ) < (k : ℚ) - 2 := by linarith
  have hk3p : (0 : ℚ) < (k : ℚ) - 3 := by linarith
  have hle : 1 / (3 * ((k : ℚ) - 2) ^ 3) ≤ 1 / (3 * ((k : ℚ) - 3) ^ 3) := by
    gcongr
    linarith
  have h2 : 2 / (3 * ((k : ℚ) - 3) ^ 3) ≤ 1 / (k : ℚ) ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [show (k : ℚ) ^ 2 ≥ 28 * (k : ℚ) by nlinarith,
               show 3 * ((k : ℚ) - 3) ^ 3 - 2 * (k : ℚ) ^ 3 =
                 ((k : ℚ) - 27) * (k : ℚ) ^ 2 + 81 * ((k : ℚ) - 1) by ring]
  have hsum : 1 / (3 * ((k : ℚ) - 3) ^ 3) + 1 / (3 * ((k : ℚ) - 3) ^ 3) =
      2 / (3 * ((k : ℚ) - 3) ^ 3) := by ring
  linarith

private lemma last_term_diff {k : ℕ} (hk : 28 ≤ k) :
    -((1 : ℚ) / ((k : ℚ) * ((k - 1 : ℕ) : ℚ))) - 1 / (5 * (k : ℚ) ^ 3) ≤
      term k (k - 1) - (-1 : ℚ) ^ (k - 1) / (k : ℚ) := by
  have hsub1 : k - (k - 1) = 1 := by omega
  have hterm : term k (k - 1) =
      ((-1 : ℚ) ^ (k - 1) / ((k - 1 : ℕ) : ℚ)) * (1 + 1 / (2 : ℚ) ^ (k - 1)) := by
    unfold term
    rw [hsub1]
    norm_num
  rw [hterm]
  have hk' : (28 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hk1_pos : (0 : ℚ) < ((k - 1 : ℕ) : ℚ) := by
    have : 0 < k - 1 := by omega
    exact_mod_cast this
  have hk_pos : (0 : ℚ) < (k : ℚ) := by linarith
  have hk1_eq : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rcases Nat.even_or_odd (k - 1) with he | ho
  · rw [he.neg_one_pow]
    have h1 : 1 / (k : ℚ) ≤ 1 / ((k - 1 : ℕ) : ℚ) := by
      gcongr
      omega
    have h2 : (1 : ℚ) ≤ 1 + 1 / (2 : ℚ) ^ (k - 1) := by
      have : (0 : ℚ) ≤ 1 / (2 : ℚ) ^ (k - 1) := by positivity
      linarith
    have h3 : 1 / ((k - 1 : ℕ) : ℚ) ≤ 1 / ((k - 1 : ℕ) : ℚ) * (1 + 1 / (2 : ℚ) ^ (k - 1)) := by
      have hpos1 : (0 : ℚ) ≤ 1 / ((k - 1 : ℕ) : ℚ) := by positivity
      nlinarith
    have h4 : (0 : ℚ) ≤ 1 / ((k : ℚ) * ((k - 1 : ℕ) : ℚ)) := by positivity
    have h5 : (0 : ℚ) ≤ 1 / (5 * (k : ℚ) ^ 3) := by positivity
    linarith
  · rw [ho.neg_one_pow]
    have hfrac : (-1 : ℚ) / ((k - 1 : ℕ) : ℚ) - (-1 : ℚ) / (k : ℚ) =
        -((1 : ℚ) / ((k : ℚ) * ((k - 1 : ℕ) : ℚ))) := by
      rw [hk1_eq]
      have hk1p : (0 : ℚ) < (k : ℚ) - 1 := by linarith
      field_simp
      ring
    have hpow : (10 * (k : ℚ) ^ 2) ≤ (2 : ℚ) ^ (k - 1) := by
      exact_mod_cast pow_two_ge_ten_k2 hk
    have h5k3 : 5 * (k : ℚ) ^ 3 ≤ ((k - 1 : ℕ) : ℚ) * (2 : ℚ) ^ (k - 1) := by
      have hhalf : (k : ℚ) / 2 ≤ ((k - 1 : ℕ) : ℚ) := by rw [hk1_eq]; linarith
      nlinarith
    have hinv : 1 / (((k - 1 : ℕ) : ℚ) * (2 : ℚ) ^ (k - 1)) ≤ 1 / (5 * (k : ℚ) ^ 3) :=
      one_div_le_one_div_of_le (by positivity) h5k3
    have hexpand :
        (-1 : ℚ) / ((k - 1 : ℕ) : ℚ) * (1 + 1 / (2 : ℚ) ^ (k - 1)) - (-1 : ℚ) / (k : ℚ) =
        (-((1 : ℚ) / ((k : ℚ) * ((k - 1 : ℕ) : ℚ)))) -
          1 / (((k - 1 : ℕ) : ℚ) * (2 : ℚ) ^ (k - 1)) := by
      calc (-1 : ℚ) / ((k - 1 : ℕ) : ℚ) * (1 + 1 / (2 : ℚ) ^ (k - 1)) - (-1 : ℚ) / (k : ℚ)
          = ((-1 : ℚ) / ((k - 1 : ℕ) : ℚ) - (-1 : ℚ) / (k : ℚ)) -
              1 / (((k - 1 : ℕ) : ℚ) * (2 : ℚ) ^ (k - 1)) := by ring
        _ = _ := by rw [hfrac]
    rw [hexpand]
    linarith

private lemma main_large {k : ℕ} (hk : 28 ≤ k) :
    (-1 : ℚ) ^ (k - 1) / (k : ℚ) < ∑ m ∈ Ico 2 k, term k m := by
  have hsplit : ∑ m ∈ Ico 2 k, term k m =
      term k 2 + term k 3 + term k 4 + (∑ m ∈ Ico 5 (k - 1), term k m) + term k (k - 1) := by
    have h1 : Ico 2 k = insert (k - 1) (Ico 2 (k - 1)) := by
      ext m; simp only [mem_Ico, mem_insert]; omega
    have h2 : Ico 2 (k - 1) = insert 2 (Ico 3 (k - 1)) := by
      ext m; simp only [mem_Ico, mem_insert]; omega
    have h3 : Ico 3 (k - 1) = insert 3 (Ico 4 (k - 1)) := by
      ext m; simp only [mem_Ico, mem_insert]; omega
    have h4 : Ico 4 (k - 1) = insert 4 (Ico 5 (k - 1)) := by
      ext m; simp only [mem_Ico, mem_insert]; omega
    rw [h1, sum_insert (by simp),
        h2, sum_insert (by simp),
        h3, sum_insert (by simp),
        h4, sum_insert (by simp)]
    ring
  rw [hsplit]
  have ht2 : term k 2 = 1 / (2 * ((k - 2 : ℕ) : ℚ) ^ 2) + 1 / (2 * ((k - 1 : ℕ) : ℚ) ^ 2) := by
    unfold term
    have : k - 2 + 1 = k - 1 := by omega
    rw [this]
    norm_num
    ring
  have ht3 : term k 3 = -(1 / (3 * ((k - 3 : ℕ) : ℚ) ^ 3) + 1 / (3 * ((k - 2 : ℕ) : ℚ) ^ 3)) := by
    unfold term
    have : k - 3 + 1 = k - 2 := by omega
    rw [this]
    norm_num
    ring
  have ht4 : 0 ≤ term k 4 := term_nonneg_of_even (by decide)
  have htail := sum_tail_ge hk
  have h2 := term_two_sub_last hk
  have h3 := term_three_bound hk
  have hlast := last_term_diff hk
  have hk3_pos : (0 : ℚ) < 1 / (k : ℚ) ^ 3 := by positivity
  have he1 : (2 : ℚ) / (k : ℚ) ^ 3 = 2 * (1 / (k : ℚ) ^ 3) := by ring
  have he2 : (1 : ℚ) / (5 * (k : ℚ) ^ 3) = (1 / 5) * (1 / (k : ℚ) ^ 3) := by ring
  have he3 : (1 : ℚ) / (10 * (k : ℚ) ^ 3) = (1 / 10) * (1 / (k : ℚ) ^ 3) := by ring
  rw [ht2, ht3]
  linarith

private lemma sum_Ico_eq_list (f : ℕ → ℚ) (n : ℕ) (hn : 2 ≤ n) :
    ∑ m ∈ Ico 2 n, f m = ((List.range (n - 2)).map (fun i => f (i + 2))).sum := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih, show n + 1 - 2 = (n - 2) + 1 by omega,
        List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    congr 2
    omega

set_option maxHeartbeats 2000000 in
private lemma main_small_list :
    (List.range 24).all (fun i =>
      let k := i + 4
      decide ((-1 : ℚ) ^ (k - 1) / (k : ℚ) <
        ((List.range (k - 2)).map (fun j => term k (j + 2))).sum)) = true := by
  decide +kernel

private lemma main_small {k : ℕ} (hk1 : 4 ≤ k) (hk2 : k < 28) :
    (-1 : ℚ) ^ (k - 1) / (k : ℚ) < ∑ m ∈ Ico 2 k, term k m := by
  rw [sum_Ico_eq_list (term k) k (by omega)]
  have h := List.all_eq_true.mp main_small_list (k - 4) (List.mem_range.mpr (by omega))
  have hk_eq : k - 4 + 4 = k := by omega
  simpa only [hk_eq, decide_eq_true_eq] using h

end OMA.MO495575

theorem OMA.solution : type_of% @OMA.S_mo_495575.main := by
  intro k hk
  by_cases h : k < 28
  · exact OMA.MO495575.main_small hk h
  · exact OMA.MO495575.main_large (by omega)
