import OMAStatements.S_oeis_a286348
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a286348

open OMA.S_oeis_a286348

private lemma add_dvd_pow_add_pow_of_odd {a b : ℤ} {q : ℕ} (hq : Odd q) :
    (a + b) ∣ (a ^ q + b ^ q) := by
  obtain ⟨r, rfl⟩ := hq
  induction r with
  | zero => simp
  | succ r ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨a ^ 2 * c + b ^ (2 * r + 1) * (b - a), ?_⟩
    have h1 : a ^ (2 * (r + 1) + 1) + b ^ (2 * (r + 1) + 1) =
        a ^ 2 * (a ^ (2 * r + 1) + b ^ (2 * r + 1)) - b ^ (2 * r + 1) * (a ^ 2 - b ^ 2) := by
      rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega, pow_add, pow_add]
      ring
    rw [h1, hc]
    ring

private lemma pow_add_neg_pow_not_prime_of_pos {y : ℤ} (hy : 1 ≤ y) {q m : ℕ}
    (hq3 : 3 ≤ q) (hqodd : Odd q) (hm2 : 2 ≤ m) :
    ¬ ((1 + y) ^ (q * m) + (-y) ^ (q * m)).toNat.Prime := by
  intro hp
  set A : ℤ := (1 + y) ^ m
  set B : ℤ := (-y) ^ m
  have h1y : 2 ≤ 1 + y := by omega
  have hAm_ge : 4 ≤ A := by
    dsimp [A]
    have h2 : (2 : ℤ) ^ 2 ≤ (1 + y) ^ m := by
      calc (2 : ℤ) ^ 2 ≤ (1 + y) ^ 2 := by nlinarith
        _ ≤ (1 + y) ^ m := pow_le_pow_right₀ (by omega) hm2
    omega
  have hBm_abs : |B| = y ^ m := by
    dsimp [B]
    rw [abs_pow, abs_neg, abs_of_nonneg (by omega)]
  have hAm_gt_Bm : y ^ m + 3 ≤ A := by
    dsimp [A]
    have hsub : ∀ n : ℕ, 2 ≤ n → y ^ n + 3 ≤ (1 + y) ^ n := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ih =>
        rcases eq_or_lt_of_le hn with h2 | hlt
        · rw [← h2]; nlinarith
        · have ih' := ih (by omega)
          have hyn : 1 ≤ y ^ n := one_le_pow₀ (by omega)
          rw [pow_succ, pow_succ]
          nlinarith
    exact hsub m hm2
  have hAB_ge : 3 ≤ A + B := by
    have hneg : -(y ^ m) ≤ B := by
      have := neg_abs_le B
      rw [hBm_abs] at this
      exact this
    omega
  have hAB_dvd : (A + B) ∣ (A ^ q + B ^ q) := add_dvd_pow_add_pow_of_odd hqodd
  have hAq_eq : A ^ q + B ^ q = (1 + y) ^ (q * m) + (-y) ^ (q * m) := by
    dsimp [A, B]; rw [← pow_mul, ← pow_mul, mul_comm m q]
  rw [hAq_eq] at hAB_dvd
  -- Show `A + B < (1 + y) ^ (q * m) + (-y) ^ (q * m)`
  have hAB_lt : A + B < (1 + y) ^ (q * m) + (-y) ^ (q * m) := by
    rw [← hAq_eq]
    have hB_le : B ≤ y ^ m := by
      have := le_abs_self B
      rw [hBm_abs] at this
      exact this
    have hBq_ge : -((y ^ m) ^ q) ≤ B ^ q := by
      have h1 := neg_abs_le (B ^ q)
      rw [abs_pow, hBm_abs] at h1
      exact h1
    have hAq_sub : (A - y ^ m) * A ^ (q - 1) ≤ A ^ q - (y ^ m) ^ q := by
      have hgeo : ∀ n : ℕ, 1 ≤ n → (A - y ^ m) * A ^ (n - 1) ≤ A ^ n - (y ^ m) ^ n := by
        intro n hn
        induction n with
        | zero => omega
        | succ n ih =>
          rcases Nat.eq_zero_or_pos n with rfl | hnpos
          · simp
          · have ih' := ih hnpos
            have h1 : (A - y ^ m) * A ^ n = A * ((A - y ^ m) * A ^ (n - 1)) := by
              conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
              ring
            have hy_nonneg : 0 ≤ (y ^ m) ^ n := pow_nonneg (pow_nonneg (by omega) m) n
            have hdiff : 0 ≤ A - y ^ m := by omega
            have hstep : A * (A ^ n - (y ^ m) ^ n) ≤ A ^ (n + 1) - (y ^ m) ^ (n + 1) := by
              rw [pow_succ', pow_succ']
              nlinarith
            calc (A - y ^ m) * A ^ n
                = A * ((A - y ^ m) * A ^ (n - 1)) := h1
              _ ≤ A * (A ^ n - (y ^ m) ^ n) := mul_le_mul_of_nonneg_left ih' (by omega)
              _ ≤ A ^ (n + 1) - (y ^ m) ^ (n + 1) := hstep
      exact hgeo q (by omega)
    have hAq1 : A ^ 2 ≤ A ^ (q - 1) := pow_le_pow_right₀ (by omega) (by omega)
    have hprod : 3 * A ^ 2 ≤ (A - y ^ m) * A ^ (q - 1) := by
      calc 3 * A ^ 2 ≤ (A - y ^ m) * A ^ 2 := by nlinarith
        _ ≤ (A - y ^ m) * A ^ (q - 1) := mul_le_mul_of_nonneg_left hAq1 (by omega)
    nlinarith
  -- Convert divisibility to `ℕ` and contradict `Nat.Prime`!
  have hAB_pos : 0 < A + B := by omega
  have hN_pos : 0 < (1 + y) ^ (q * m) + (-y) ^ (q * m) := by omega
  have hdvd_nat : (A + B).toNat ∣ ((1 + y) ^ (q * m) + (-y) ^ (q * m)).toNat := by
    obtain ⟨c, hc⟩ := hAB_dvd
    have hc_pos : 0 ≤ c := by nlinarith
    refine ⟨c.toNat, ?_⟩
    zify
    rw [Int.toNat_of_nonneg hN_pos.le, Int.toNat_of_nonneg hAB_pos.le, Int.toNat_of_nonneg hc_pos]
    exact hc
  rcases hp.eq_one_or_self_of_dvd _ hdvd_nat with h1 | hself
  · omega
  · omega

private lemma prove_a286348 (y : ℤ) (x : ℕ)
    (hpos : 0 < (1 + y) ^ x + (-y) ^ x)
    (hprime : ((1 + y) ^ x + (-y) ^ x).toNat.Prime) :
    x = 0 ∨ (∃ k ≥ 1, x = 2 ^ k) ∨ (x.Prime ∧ Odd x) := by
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  by_cases hx1 : x = 1
  · subst hx1
    have h1 : ((1 + y) ^ 1 + (-y) ^ 1).toNat = 1 := by ring_nf; decide
    rw [h1] at hprime
    exact absurd hprime Nat.not_prime_one
  -- Now `2 ≤ x`. First dispose of `y = 0` and `y = -1`.
  by_cases hy0 : y = 0
  · subst hy0
    have h1 : ((1 + 0 : ℤ) ^ x + (-0 : ℤ) ^ x).toNat = 1 := by
      rw [add_zero, one_pow, neg_zero, zero_pow hx0, add_zero]; rfl
    rw [h1] at hprime
    exact absurd hprime Nat.not_prime_one
  by_cases hym1 : y = -1
  · subst hym1
    have h1 : ((1 + (-1 : ℤ)) ^ x + (-(-1 : ℤ)) ^ x).toNat = 1 := by
      rw [show (1 + (-1 : ℤ)) = 0 by ring, zero_pow hx0, zero_add,
        show -(-1 : ℤ) = 1 by ring, one_pow]; rfl
    rw [h1] at hprime
    exact absurd hprime Nat.not_prime_one
  -- Reduce to `1 ≤ y'` via symmetry `y ↦ -1 - y`!
  have hsym : ∃ y' : ℤ, 1 ≤ y' ∧ (1 + y') ^ x + (-y') ^ x = (1 + y) ^ x + (-y) ^ x := by
    by_cases h1 : 1 ≤ y
    · exact ⟨y, h1, rfl⟩
    · refine ⟨-1 - y, by omega, ?_⟩
      rw [show 1 + (-1 - y) = -y by ring, show -(-1 - y) = 1 + y by ring, add_comm]
  obtain ⟨y', hy', heq⟩ := hsym
  rw [← heq] at hprime
  -- Factor out the 2-part of `x`: write `x = 2 ^ k * u` with `Odd u`.
  set k := x.factorization 2
  set u := x / 2 ^ k
  have h2k_dvd : 2 ^ k ∣ x := Nat.ordProj_dvd x 2
  have hx_eq : x = u * 2 ^ k := by rw [Nat.div_mul_cancel h2k_dvd]
  have hu_odd : Odd u := by
    have hnd2 : ¬ 2 ∣ u := Nat.not_dvd_ordCompl Nat.prime_two hx0
    rw [Nat.odd_iff]; omega
  by_cases hu1 : u = 1
  · -- `x = 2 ^ k` with `k ≥ 1` (since `x ≥ 2`)!
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hu1, hk0] at hx_eq
      omega
    exact Or.inr (Or.inl ⟨k, hk1, by rw [hx_eq, hu1, one_mul]⟩)
  · -- `u ≥ 3` is odd.
    have hu3 : 3 ≤ u := by obtain ⟨r, hr⟩ := hu_odd; omega
    by_cases hk0 : k = 0
    · -- `x = u ≥ 3` is odd! If `x` is composite, let `q = x.minFac`, then `x = q * (x / q)`!
      have hxu : x = u := by rw [hx_eq, hk0]; simp
      by_cases hxp : x.Prime
      · exact Or.inr (Or.inr ⟨hxp, hxu ▸ hu_odd⟩)
      · set q := x.minFac
        have hqp : q.Prime := Nat.minFac_prime (by omega)
        have hqdvd : q ∣ x := Nat.minFac_dvd x
        have hqodd : Odd q := by
          rcases hqp.eq_two_or_odd with h2 | hodd
          · exfalso; rw [h2] at hqdvd
            obtain ⟨r, hr⟩ := hu_odd; omega
          · exact Nat.odd_iff.mpr hodd
        have hq3 : 3 ≤ q := by obtain ⟨r, hr⟩ := hqodd; have := hqp.two_le; omega
        have hm2 : 2 ≤ x / q := by
          have hsq : q * q ≤ x := by
            have h := Nat.minFac_sq_le_self (by omega) hxp
            rwa [pow_two] at h
          have hdiv : q * (x / q) = x := Nat.mul_div_cancel' hqdvd
          nlinarith
        have hx_fac : x = q * (x / q) := (Nat.mul_div_cancel' hqdvd).symm
        rw [hx_fac] at hprime
        exact absurd hprime (pow_add_neg_pow_not_prime_of_pos hy' hq3 hqodd hm2)
    · -- `k ≥ 1`, so `m = 2 ^ k ≥ 2` and `x = u * 2 ^ k` with `u ≥ 3` odd!
      have hm2 : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      rw [hx_eq] at hprime
      exact absurd hprime (pow_add_neg_pow_not_prime_of_pos hy' hu3 hu_odd hm2)

end OMA.P_oeis_a286348

theorem OMA.solution : type_of% @OMA.S_oeis_a286348.main :=
  OMA.P_oeis_a286348.prove_a286348
