import OMAStatements.S_oeis_a000139

namespace OMA.P_oeis_a000139

open OMA.S_oeis_a000139

private lemma choose_mul_fact (n k : ℕ) (hk : k ≤ n) :
    Nat.choose n k * (k.factorial * (n - k).factorial) = n.factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial hk
  linarith

private lemma a_linear_combo (n : ℕ) (hn : 1 ≤ n) :
    a n + 8 * Nat.choose (3 * n) (n - 1) =
      2 * Nat.choose (3 * n) n + Nat.choose (3 * n) (n + 1) := by
  set D := (2 * n + 1).factorial * (n + 1).factorial
  have hD_pos : 0 < D := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have h1 : Nat.choose (3 * n) n * D = (2 * n + 1) * (n + 1) * (3 * n).factorial := by
    have hc := choose_mul_fact (3 * n) n (by omega)
    have hsub : 3 * n - n = 2 * n := by omega
    rw [hsub] at hc
    have hf1 : (2 * n + 1).factorial = (2 * n + 1) * (2 * n).factorial := Nat.factorial_succ (2 * n)
    have hf2 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
    calc Nat.choose (3 * n) n * D
        = Nat.choose (3 * n) n * ((2 * n + 1).factorial * (n + 1).factorial) := rfl
      _ = (2 * n + 1) * (n + 1) * (Nat.choose (3 * n) n * (n.factorial * (2 * n).factorial)) := by
          rw [hf1, hf2]; ring
      _ = (2 * n + 1) * (n + 1) * (3 * n).factorial := by rw [hc]
  have h2 : Nat.choose (3 * n) (n - 1) * D = n * (n + 1) * (3 * n).factorial := by
    have hc := choose_mul_fact (3 * n) (n - 1) (by omega)
    have hsub : 3 * n - (n - 1) = 2 * n + 1 := by omega
    rw [hsub] at hc
    have hns : (n - 1) + 1 = n := by omega
    have hf1 : (n + 1).factorial = (n + 1) * (n * (n - 1).factorial) := by
      rw [Nat.factorial_succ]
      congr 1
      conv_lhs => rw [← hns]
      rw [Nat.factorial_succ, hns]
    calc Nat.choose (3 * n) (n - 1) * D
        = Nat.choose (3 * n) (n - 1) * ((2 * n + 1).factorial * (n + 1).factorial) := rfl
      _ = n * (n + 1) * (Nat.choose (3 * n) (n - 1) * ((n - 1).factorial * (2 * n + 1).factorial)) := by
          rw [hf1]; ring
      _ = n * (n + 1) * (3 * n).factorial := by rw [hc]
  have h3 : Nat.choose (3 * n) (n + 1) * D = (2 * n + 1) * (2 * n) * (3 * n).factorial := by
    have hc := choose_mul_fact (3 * n) (n + 1) (by omega)
    have hsub : 3 * n - (n + 1) = 2 * n - 1 := by omega
    rw [hsub] at hc
    have h2ns : (2 * n - 1) + 1 = 2 * n := by omega
    have hf1 : (2 * n + 1).factorial = (2 * n + 1) * (2 * n * (2 * n - 1).factorial) := by
      rw [Nat.factorial_succ]
      congr 1
      conv_lhs => rw [← h2ns]
      rw [Nat.factorial_succ, h2ns]
    calc Nat.choose (3 * n) (n + 1) * D
        = Nat.choose (3 * n) (n + 1) * ((2 * n + 1).factorial * (n + 1).factorial) := rfl
      _ = (2 * n + 1) * (2 * n) * (Nat.choose (3 * n) (n + 1) * ((n + 1).factorial * (2 * n - 1).factorial)) := by
          rw [hf1]; ring
      _ = (2 * n + 1) * (2 * n) * (3 * n).factorial := by rw [hc]
  have hpoly : (2 * Nat.choose (3 * n) n + Nat.choose (3 * n) (n + 1)) * D =
      2 * (3 * n).factorial + 8 * Nat.choose (3 * n) (n - 1) * D := by
    rw [add_mul, mul_assoc, h1, h3, mul_assoc 8, h2]
    ring
  have hdvd : D ∣ 2 * (3 * n).factorial := by
    have hle : 8 * Nat.choose (3 * n) (n - 1) ≤
        2 * Nat.choose (3 * n) n + Nat.choose (3 * n) (n + 1) := by
      apply Nat.le_of_mul_le_mul_right _ hD_pos
      linarith
    refine ⟨2 * Nat.choose (3 * n) n + Nat.choose (3 * n) (n + 1) - 8 * Nat.choose (3 * n) (n - 1), ?_⟩
    have hsub : (2 * Nat.choose (3 * n) n + Nat.choose (3 * n) (n + 1) -
        8 * Nat.choose (3 * n) (n - 1)) * D = 2 * (3 * n).factorial := by
      rw [Nat.sub_mul]
      exact Nat.sub_eq_of_eq_add hpoly
    linarith
  have ha_mul : a n * D = 2 * (3 * n).factorial := by
    unfold a
    exact Nat.div_mul_cancel hdvd
  apply Nat.eq_of_mul_eq_mul_right hD_pos
  rw [add_mul, ha_mul]
  linarith

private lemma odd_choose_iff_disjoint_bits :
    ∀ a b : ℕ, Odd (Nat.choose (a + b) a) ↔ ∀ i : ℕ, ¬ (a.testBit i ∧ b.testBit i) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b
    by_cases ha0 : a = 0
    · subst ha0
      simp
    · have hlucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := a + b) (k := a)
      have hmod2 : Nat.choose (a + b) a % 2 =
          (Nat.choose ((a + b) % 2) (a % 2) * Nat.choose ((a + b) / 2) (a / 2)) % 2 := by
        simpa [Nat.ModEq] using hlucas
      have hodd_iff : ∀ m : ℕ, Odd m ↔ m % 2 = 1 := fun m => Nat.odd_iff
      rw [hodd_iff, hmod2]
      by_cases hab1 : a % 2 = 1 ∧ b % 2 = 1
      · have hmod_zero : (a + b) % 2 = 0 := by omega
        rw [hmod_zero, hab1.1]
        simp only [Nat.choose_zero_succ, zero_mul, Nat.zero_mod, zero_ne_one, false_iff, not_forall,
          Classical.not_not]
        exact ⟨0, by simp [Nat.testBit_zero, hab1.1], by simp [Nat.testBit_zero, hab1.2]⟩
      · have hsum_div : (a + b) / 2 = a / 2 + b / 2 := by omega
        have hch_mod : Nat.choose ((a + b) % 2) (a % 2) = 1 := by
          have : (a % 2 = 0 ∧ b % 2 = 0) ∨ (a % 2 = 0 ∧ b % 2 = 1) ∨ (a % 2 = 1 ∧ b % 2 = 0) := by
            omega
          rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            simp [show (a + b) % 2 = (a % 2 + b % 2) % 2 by omega, h1, h2]
        rw [hch_mod, one_mul, hsum_div, ← hodd_iff]
        rw [ih (a / 2) (Nat.div_lt_self (by omega) (by decide)) (b / 2)]
        constructor
        · intro hdiv i
          cases i with
          | zero =>
            simp only [Nat.testBit_zero, decide_eq_true_eq]
            omega
          | succ i =>
            simpa [Nat.testBit_succ, Nat.shiftRight_eq_div_pow] using hdiv i
        · intro hall i
          have := hall (i + 1)
          simpa [Nat.testBit_succ, Nat.shiftRight_eq_div_pow] using this

private lemma disjoint_bits_iff_A022341 (n : ℕ) (hn : 1 ≤ n) :
    (∀ i : ℕ, ¬ ((n + 1).testBit i ∧ (2 * n - 1).testBit i)) ↔ IsA022341 n := by
  unfold IsA022341
  constructor
  · intro hdisj
    have hodd : n % 2 = 1 := by
      by_contra hev
      have h0 := hdisj 0
      simp only [Nat.testBit_zero, decide_eq_true_eq] at h0
      omega
    refine ⟨hodd, ?_⟩
    by_cases hmod4 : n % 4 = 3
    · -- Contradiction: let k be the number of trailing 1s of n (k ≥ 2); both n+1 and 2n-1 have bit k = 1!
      exfalso
      -- Write n + 1 = 2^k * (2*q + 1), then k ≥ 2
      set k := (n + 1).factorization 2
      have hk_ge2 : 2 ≤ k := by
        have h4dvd : 2 ^ 2 ∣ n + 1 := by omega
        exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).mp h4dvd
      have hpow_dvd : 2 ^ k ∣ n + 1 := Nat.ordProj_dvd (n + 1) 2
      have hnot_succ : ¬ (2 ^ (k + 1) ∣ n + 1) := by
        intro h
        have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).mp h
        omega
      obtain ⟨m, hm⟩ := hpow_dvd
      have hm_odd : m % 2 = 1 := by
        by_contra hev
        apply hnot_succ
        obtain ⟨t, ht⟩ : 2 ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
        exact ⟨t, by rw [hm, ht, pow_succ]; ring⟩
      have hbit1 : (n + 1).testBit k = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, hm, Nat.mul_div_cancel_left _ (by positivity)]
        simp [hm_odd]
      have hbit2 : (2 * n - 1).testBit k = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have h2n : 2 * n - 1 = 2 ^ k * (2 * m - 1) + (2 ^ k - 3) := by
          have h2k_ge4 : 4 ≤ 2 ^ k := by
            have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk_ge2
            simpa using this
          have hm1 : 1 ≤ m := by omega
          zify [show 1 ≤ 2 * n by omega, show 1 ≤ 2 * m by omega, show 3 ≤ 2 ^ k by omega]
          have hmz : (n : ℤ) + 1 = (2 ^ k : ℕ) * (m : ℤ) := by exact_mod_cast hm
          linarith
        have hrem_lt : 2 ^ k - 3 < 2 ^ k := by
          have : 4 ≤ 2 ^ k := by
            have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk_ge2
            simpa using this
          omega
        rw [h2n, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hrem_lt, add_zero]
        have : (2 * m - 1) % 2 = 1 := by omega
        simp [this]
      exact hdisj k ⟨hbit1, hbit2⟩
    · -- n % 4 = 1
      have hmod4_1 : n % 4 = 1 := by omega
      have hbit1_false : n.testBit 1 = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        simp only [pow_one, decide_eq_false_iff_not]
        omega
      intro i
      cases i with
      | zero =>
        simp [hbit1_false]
      | succ i =>
        have hd := hdisj (i + 2)
        have hpow_ge4 : 4 ∣ 2 ^ (i + 2) := by
          refine ⟨2 ^ i, ?_⟩
          ring
        have hdiv1 : (n + 1) / 2 ^ (i + 2) = n / 2 ^ (i + 2) := by
          have hq : n = 4 * (n / 4) + 1 := by omega
          obtain ⟨t, ht⟩ := hpow_ge4
          have h1 : (n + 1) / (4 * t) = ((n + 1) / 4) / t := (Nat.div_div_eq_div_mul _ _ _).symm
          have h2 : n / (4 * t) = (n / 4) / t := (Nat.div_div_eq_div_mul _ _ _).symm
          rw [ht, h1, h2]
          congr 1; omega
        have hdiv2 : (2 * n - 1) / 2 ^ (i + 2) = n / 2 ^ (i + 1) := by
          have hpow2 : 2 ^ (i + 2) = 2 * 2 ^ (i + 1) := by ring
          have hpow1 : 2 ∣ 2 ^ (i + 1) := ⟨2 ^ i, by ring⟩
          obtain ⟨t, ht⟩ := hpow1
          have h1 : (2 * n - 1) / (4 * t) = ((2 * n - 1) / 4) / t := (Nat.div_div_eq_div_mul _ _ _).symm
          have h2 : n / (2 * t) = (n / 2) / t := (Nat.div_div_eq_div_mul _ _ _).symm
          have h4t : 2 ^ (i + 2) = 4 * t := by omega
          rw [h4t, ht, h1, h2]
          congr 1; omega
        have hb1 : (n + 1).testBit (i + 2) = n.testBit (i + 2) := by
          simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv1]
        have hb2 : (2 * n - 1).testBit (i + 2) = n.testBit (i + 1) := by
          simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv2]
        rw [hb1, hb2] at hd
        tauto
  · rintro ⟨hodd, hfib⟩
    have hbit0 : n.testBit 0 = true := by simp [Nat.testBit_zero, hodd]
    have hbit1_false : n.testBit 1 = false := by
      have := hfib 0
      simp only [hbit0, true_and, Bool.not_eq_true] at this
      exact this
    have hmod4_1 : n % 4 = 1 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hbit1_false
      simp only [pow_one, decide_eq_false_iff_not] at hbit1_false
      omega
    intro i
    match i with
    | 0 =>
      simp only [Nat.testBit_zero, decide_eq_true_eq]
      omega
    | 1 =>
      have h21 : (2 * n - 1).testBit 1 = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        simp only [pow_one, decide_eq_false_iff_not]
        omega
      simp [h21]
    | j + 2 =>
      have hpow_ge4 : 4 ∣ 2 ^ (j + 2) := ⟨2 ^ j, by ring⟩
      have hdiv1 : (n + 1) / 2 ^ (j + 2) = n / 2 ^ (j + 2) := by
        obtain ⟨t, ht⟩ := hpow_ge4
        have h1 : (n + 1) / (4 * t) = ((n + 1) / 4) / t := (Nat.div_div_eq_div_mul _ _ _).symm
        have h2 : n / (4 * t) = (n / 4) / t := (Nat.div_div_eq_div_mul _ _ _).symm
        rw [ht, h1, h2]
        congr 1; omega
      have hdiv2 : (2 * n - 1) / 2 ^ (j + 2) = n / 2 ^ (j + 1) := by
        have hpow1 : 2 ∣ 2 ^ (j + 1) := ⟨2 ^ j, by ring⟩
        obtain ⟨t, ht⟩ := hpow1
        have h1 : (2 * n - 1) / (4 * t) = ((2 * n - 1) / 4) / t := (Nat.div_div_eq_div_mul _ _ _).symm
        have h2 : n / (2 * t) = (n / 2) / t := (Nat.div_div_eq_div_mul _ _ _).symm
        have h4t : 2 ^ (j + 2) = 4 * t := by
          have : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
          omega
        rw [h4t, ht, h1, h2]
        congr 1; omega
      have hb1 : (n + 1).testBit (j + 2) = n.testBit (j + 2) := by
        simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv1]
      have hb2 : (2 * n - 1).testBit (j + 2) = n.testBit (j + 1) := by
        simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv2]
      rw [hb1, hb2]
      have := hfib (j + 1)
      tauto

private theorem prove_main : ∀ n : ℕ, Odd (a n) ↔ IsA022341 n := by
  intro n
  cases n with
  | zero =>
    unfold a IsA022341
    simp
  | succ m =>
    set n := m + 1
    have hn : 1 ≤ n := Nat.succ_pos m
    have hcombo := a_linear_combo n hn
    have hpar : Odd (a n) ↔ Odd (Nat.choose (3 * n) (n + 1)) := by
      rw [Nat.odd_iff, Nat.odd_iff]
      omega
    rw [hpar]
    have hsum : (n + 1) + (2 * n - 1) = 3 * n := by omega
    rw [← hsum, odd_choose_iff_disjoint_bits (n + 1) (2 * n - 1)]
    exact disjoint_bits_iff_A022341 n hn

end OMA.P_oeis_a000139

theorem OMA.solution : type_of% @OMA.S_oeis_a000139.main :=
  OMA.P_oeis_a000139.prove_main
