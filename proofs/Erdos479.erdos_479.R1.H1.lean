import OMAReductions.R_Erdos479_erdos_479_R1
import Mathlib

namespace Erdos479H1

lemma lt_two_pow (m : ℕ) : m < 2 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    omega

lemma lt_three_pow (m : ℕ) : m < 3 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h : 3 ^ (m + 1) = 3 ^ m + 3 ^ m + 3 ^ m := by ring
    omega

lemma modEq_zero_of_dvd (n : ℕ) (h : n ∣ 2 ^ n) :
    (2 : ℤ) ^ n ≡ 0 [ZMOD (n : ℤ)] := by
  rw [Int.modEq_zero_iff_dvd]
  have hz : (n : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) := Int.ofNat_dvd.mpr h
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hz

lemma modEq_neg_one_of_dvd (n : ℕ) (h : (n : ℤ) ∣ (2 : ℤ) ^ n + 1) :
    (2 : ℤ) ^ n ≡ -1 [ZMOD (n : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  have heq : (-1 : ℤ) - (2 : ℤ) ^ n = -((2 : ℤ) ^ n + 1) := by ring
  rw [heq]
  exact dvd_neg.mpr h

lemma modEq_neg_two_of_dvd (n : ℕ) (h : n ∣ 2 ^ n + 2) :
    (2 : ℤ) ^ n ≡ -2 [ZMOD (n : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  have hz : (n : ℤ) ∣ ((2 ^ n + 2 : ℕ) : ℤ) := Int.ofNat_dvd.mpr h
  have hz' : (n : ℤ) ∣ (2 : ℤ) ^ n + 2 := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hz
  have heq : (-2 : ℤ) - (2 : ℤ) ^ n = -((2 : ℤ) ^ n + 2) := by ring
  rw [heq]
  exact dvd_neg.mpr hz'

lemma modEq_two_pow_of_dvd (n i : ℕ) (hle : i ≤ n) (h : n ∣ 2 ^ n - 2 ^ i) :
    (2 : ℤ) ^ n ≡ (2 : ℤ) ^ i [ZMOD (n : ℤ)] := by
  symm
  rw [Int.modEq_iff_dvd]
  have hpow : 2 ^ i ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hle
  have hz : (n : ℤ) ∣ ((2 ^ n - 2 ^ i : ℕ) : ℤ) := Int.ofNat_dvd.mpr h
  simpa only [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_ofNat] using hz

lemma three_pow_succ_dvd (m : ℕ) : (3 : ℤ) ^ (m + 1) ∣ (2 : ℤ) ^ (3 ^ m) + 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rcases ih with ⟨q, hq⟩
    set x : ℤ := (2 : ℤ) ^ (3 ^ m)
    set u : ℤ := (3 : ℤ) ^ m * q
    have hx : x = 3 * u - 1 := by
      have h3 : (3 : ℤ) ^ (m + 1) * q = 3 * u := by
        simp only [u]
        ring
      linarith
    have hpow : (2 : ℤ) ^ (3 ^ (m + 1)) = x ^ 3 := by
      have he : 3 ^ (m + 1) = 3 ^ m * 3 := by ring
      rw [he, pow_mul]
    refine ⟨q * (3 * u ^ 2 - 3 * u + 1), ?_⟩
    rw [hpow]
    calc
      x ^ 3 + 1 = (x + 1) * (x ^ 2 - x + 1) := by ring
      _ = ((3 : ℤ) ^ (m + 1) * q) * ((3 * u - 1) ^ 2 - (3 * u - 1) + 1) := by rw [hq, hx]
      _ = (3 : ℤ) ^ (m + 2) * (q * (3 * u ^ 2 - 3 * u + 1)) := by ring

lemma add_one_dvd_pow_odd_add_one_int (a : ℤ) (t : ℕ) :
    a + 1 ∣ a ^ (2 * t + 1) + 1 := by
  induction t with
  | zero =>
    simp
  | succ t ih =>
    rcases ih with ⟨c, hc⟩
    refine ⟨a ^ 2 * c - (a - 1), ?_⟩
    have he : 2 * (t + 1) + 1 = (2 * t + 1) + 2 := by omega
    rw [he, pow_add]
    calc
      a ^ (2 * t + 1) * a ^ 2 + 1 = a ^ 2 * (a ^ (2 * t + 1) + 1) - (a - 1) * (a + 1) := by ring
      _ = a ^ 2 * ((a + 1) * c) - (a - 1) * (a + 1) := by rw [hc]
      _ = (a + 1) * (a ^ 2 * c - (a - 1)) := by ring

lemma add_one_dvd_pow_odd_add_one (A : ℕ) {q : ℕ} (hq : Odd q) :
    A + 1 ∣ A ^ q + 1 := by
  rcases hq with ⟨t, rfl⟩
  apply Int.ofNat_dvd.mp
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
    add_one_dvd_pow_odd_add_one_int (A : ℤ) t

lemma odd_of_odd_mul_right {a b : ℕ} (h : Odd (a * b)) : Odd b := by
  rcases Nat.even_or_odd b with ⟨r, rfl⟩ | hb
  · rcases h with ⟨k, hk⟩
    have hmul : a * (r + r) = 2 * (a * r) := by ring
    omega
  · exact hb

def seqNegTwo : ℕ → ℕ
  | 0 => 6
  | m + 1 => 2 ^ (seqNegTwo m) + 2

lemma seqNegTwo_inv (m : ℕ) :
    m + 6 ≤ seqNegTwo m ∧
      seqNegTwo m % 4 = 2 ∧
      seqNegTwo m ∣ 2 ^ (seqNegTwo m) + 2 ∧
      (seqNegTwo m - 1) ∣ 2 ^ (seqNegTwo m) + 1 := by
  induction m with
  | zero =>
    dsimp [seqNegTwo]
    refine ⟨by decide, by decide, by decide, by decide⟩
  | succ m ih =>
    rcases ih with ⟨hle, hmod4, hdvd_plus2, hdvd_plus1⟩
    set n := seqNegTwo m
    have hn6 : 6 ≤ n := by omega
    have hn_lt : n < 2 ^ n + 2 := by
      have := lt_two_pow n
      omega
    have hle' : m + 1 + 6 ≤ 2 ^ n + 2 := by omega
    have hmod4' : (2 ^ n + 2) % 4 = 2 := by
      have hn_split : n = (n - 2) + 2 := by omega
      have hpow4 : 2 ^ n = 2 ^ (n - 2) * 4 := by
        conv_lhs => rw [hn_split, pow_add]
        ring
      omega
    have hdvd_plus2' : (2 ^ n + 2) ∣ 2 ^ (2 ^ n + 2) + 2 := by
      rcases hdvd_plus1 with ⟨q, hq⟩
      have hodd_pow1 : Odd (2 ^ n + 1) := by
        refine ⟨2 ^ (n - 1), ?_⟩
        have hn1 : n = (n - 1) + 1 := by omega
        conv_lhs => rw [hn1, pow_add]
        ring
      have hq_odd : Odd q := by
        rw [hq] at hodd_pow1
        exact odd_of_odd_mul_right hodd_pow1
      have hd1 : 2 ^ (n - 1) + 1 ∣ (2 ^ (n - 1)) ^ q + 1 :=
        add_one_dvd_pow_odd_add_one (2 ^ (n - 1)) hq_odd
      rw [← pow_mul, ← hq] at hd1
      have hd2 : 2 * (2 ^ (n - 1) + 1) ∣ 2 * (2 ^ (2 ^ n + 1) + 1) :=
        mul_dvd_mul_left 2 hd1
      have hlhs : 2 * (2 ^ (n - 1) + 1) = 2 ^ n + 2 := by
        have hn1 : n = (n - 1) + 1 := by omega
        conv_rhs => rw [hn1, pow_add]
        ring
      have hrhs : 2 * (2 ^ (2 ^ n + 1) + 1) = 2 ^ (2 ^ n + 2) + 2 := by
        have he : 2 ^ n + 2 = (2 ^ n + 1) + 1 := by omega
        conv_rhs => rw [he, pow_add]
        ring
      rw [hlhs, hrhs] at hd2
      exact hd2
    have hdvd_plus1' : (2 ^ n + 2 - 1) ∣ 2 ^ (2 ^ n + 2) + 1 := by
      rcases hdvd_plus2 with ⟨r, hr⟩
      have hr_odd : Odd r := by
        rcases Nat.even_or_odd r with ⟨t, rfl⟩ | hro
        · exfalso
          have hn4 : n = 4 * (n / 4) + 2 := by omega
          have hmul4 : n * (t + t) = 4 * ((n / 4) * (2 * t) + t) := by
            conv_lhs => rw [hn4]
            ring
          omega
        · exact hro
      have hd1 : 2 ^ n + 1 ∣ (2 ^ n) ^ r + 1 :=
        add_one_dvd_pow_odd_add_one (2 ^ n) hr_odd
      rw [← pow_mul, ← hr] at hd1
      have hsub : 2 ^ n + 2 - 1 = 2 ^ n + 1 := by omega
      rw [hsub]
      exact hd1
    change m + 1 + 6 ≤ 2 ^ n + 2 ∧
      (2 ^ n + 2) % 4 = 2 ∧
      (2 ^ n + 2) ∣ 2 ^ (2 ^ n + 2) + 2 ∧
      (2 ^ n + 2 - 1) ∣ 2 ^ (2 ^ n + 2) + 1
    exact ⟨hle', hmod4', hdvd_plus2', hdvd_plus1'⟩

lemma dvd_sub_of_modEq {a b m : ℕ} (h : a ≡ b [MOD m]) : m ∣ a - b := by
  change a % m = b % m at h
  refine ⟨a / m - b / m, ?_⟩
  rw [Nat.mul_sub]
  have ha := Nat.div_add_mod a m
  have hb := Nat.div_add_mod b m
  omega

lemma case_two_pow (i : ℕ) (hi : 1 ≤ i) :
    { n : ℕ | (2 : ℤ) ^ n ≡ (2 : ℤ) ^ i [ZMOD (n : ℤ)] }.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro B
  obtain ⟨a, u, hu_odd, hi_eq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : i ≠ 0)
  have hu_pos : 0 < u := by
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · simp at hi_eq
      omega
    · exact hpos
  set M := u.totient
  have hM_pos : 0 < M := Nat.totient_pos.mpr hu_pos
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max (max B i) 2) (by omega : M ≠ 0)
      (show (1 : ℕ).Coprime M by simp [Nat.Coprime])
  have hBp : B < p := lt_of_le_of_lt (le_trans (le_max_left B i) (le_max_left _ 2)) hp_gt
  have hip : i < p := lt_of_le_of_lt (le_trans (le_max_right B i) (le_max_left _ 2)) hp_gt
  have h2p : 2 < p := lt_of_le_of_lt (le_max_right _ 2) hp_gt
  have hpt : ∃ t : ℕ, p = 1 + M * t := by
    rcases (by omega : M = 1 ∨ 2 ≤ M) with hM1 | hM2
    · exact ⟨p - 1, by rw [hM1]; omega⟩
    · refine ⟨p / M, ?_⟩
      have hmod : p % M = 1 := by
        change p % M = 1 % M at hp_mod
        rw [Nat.mod_eq_of_lt hM2] at hp_mod
        exact hp_mod
      have hdiv := Nat.div_add_mod p M
      omega
  rcases hpt with ⟨t, hpt_eq⟩
  set n := i * p
  have hi_le_n : i ≤ n := Nat.le_mul_of_pos_right i (by omega)
  have hp_le_n : p ≤ n := Nat.le_mul_of_pos_left p (by omega)
  have hBn : B < n := lt_of_lt_of_le hBp hp_le_n
  have ha_le_i : a ≤ i := by
    have ha_lt : a < 2 ^ a := lt_two_pow a
    have h2a_le : 2 ^ a ≤ 2 ^ a * u := Nat.le_mul_of_pos_right (2 ^ a) hu_pos
    omega
  have ha_le_n : a ≤ n := le_trans ha_le_i hi_le_n
  have hdvd_2a : 2 ^ a ∣ 2 ^ n - 2 ^ i := by
    rcases pow_dvd_pow 2 ha_le_n with ⟨c1, hc1⟩
    rcases pow_dvd_pow 2 ha_le_i with ⟨c2, hc2⟩
    refine ⟨c1 - c2, ?_⟩
    rw [hc1, hc2, ← Nat.mul_sub]
  have hcop_2u : (2 : ℕ).Coprime u := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    rcases hu_odd with ⟨k, rfl⟩
    rintro ⟨c, hc⟩
    omega
  have hdvd_u : u ∣ 2 ^ n - 2 ^ i := by
    have heuler : 2 ^ M ≡ 1 [MOD u] := Nat.ModEq.pow_totient hcop_2u
    have hpow_m : (2 ^ M) ^ (i * t) ≡ 1 ^ (i * t) [MOD u] := heuler.pow (i * t)
    have hmul_m : 2 ^ i * (2 ^ M) ^ (i * t) ≡ 2 ^ i * 1 ^ (i * t) [MOD u] :=
      hpow_m.mul_left (2 ^ i)
    have hn_expand : 2 ^ n = 2 ^ i * (2 ^ M) ^ (i * t) := by
      have hne : n = i + M * (i * t) := by
        simp only [n, hpt_eq]
        ring
      rw [hne, pow_add, pow_mul]
    rw [ ← hn_expand, one_pow, mul_one] at hmul_m
    exact dvd_sub_of_modEq hmul_m
  have hcop_pow_u : (2 ^ a).Coprime u := hcop_2u.pow_left a
  have hdvd_i : i ∣ 2 ^ n - 2 ^ i := by
    have hd : 2 ^ a * u ∣ 2 ^ n - 2 ^ i :=
      hcop_pow_u.mul_dvd_of_dvd_of_dvd hdvd_2a hdvd_u
    rwa [← hi_eq] at hd
  have hcop_2p : (2 : ℕ).Coprime p := by
    apply Nat.Coprime.symm
    rw [hp_prime.coprime_iff_not_dvd]
    intro hp2
    have := Nat.le_of_dvd (by decide : 0 < 2) hp2
    omega
  have hdvd_p : p ∣ 2 ^ n - 2 ^ i := by
    have hfermat : 2 ^ p.totient ≡ 1 [MOD p] := Nat.ModEq.pow_totient hcop_2p
    rw [Nat.totient_prime hp_prime] at hfermat
    have hfermat2 : 2 ^ (p - 1) * 2 ≡ 1 * 2 [MOD p] := hfermat.mul_right 2
    have hp_sub : 2 ^ (p - 1) * 2 = 2 ^ p := by
      have hp1 : p = (p - 1) + 1 := by omega
      conv_rhs => rw [hp1, pow_add]
      ring
    rw [hp_sub, one_mul] at hfermat2
    have hpow_p : (2 ^ p) ^ i ≡ 2 ^ i [MOD p] := hfermat2.pow i
    have hn_p : (2 ^ p) ^ i = 2 ^ n := by
      rw [← pow_mul, mul_comm p i]
    rw [hn_p] at hpow_p
    exact dvd_sub_of_modEq hpow_p
  have hcop_ip : i.Coprime p := by
    apply Nat.Coprime.symm
    rw [hp_prime.coprime_iff_not_dvd]
    intro hpi
    have := Nat.le_of_dvd (by omega : 0 < i) hpi
    omega
  have hdvd_n : n ∣ 2 ^ n - 2 ^ i :=
    hcop_ip.mul_dvd_of_dvd_of_dvd hdvd_i hdvd_p
  exact ⟨n, modEq_two_pow_of_dvd n i hi_le_n hdvd_n, hBn⟩

end Erdos479H1

theorem prove_Erdos479_H1 :
    ∀ k : ℤ, (k = 0 ∨ k = -1 ∨ k = -2 ∨ ∃ i : ℕ, 1 ≤ i ∧ k = 2 ^ i) →
      { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Infinite := by
  intro k hk
  rcases hk with rfl | rfl | rfl | ⟨i, hi, rfl⟩
  · rw [Set.infinite_iff_exists_gt]
    intro B
    refine ⟨2 ^ (B + 1), ?_, ?_⟩
    · apply Erdos479H1.modEq_zero_of_dvd
      exact pow_dvd_pow 2 (le_of_lt (Erdos479H1.lt_two_pow (B + 1)))
    · have := Erdos479H1.lt_two_pow (B + 1)
      omega
  · rw [Set.infinite_iff_exists_gt]
    intro B
    refine ⟨3 ^ (B + 1), ?_, ?_⟩
    · apply Erdos479H1.modEq_neg_one_of_dvd
      have hd := Erdos479H1.three_pow_succ_dvd (B + 1)
      have hpow : ((3 ^ (B + 1) : ℕ) : ℤ) ∣ (3 : ℤ) ^ (B + 1 + 1) := by
        refine ⟨3, ?_⟩
        push_cast
        ring
      exact dvd_trans hpow hd
    · have := Erdos479H1.lt_three_pow (B + 1)
      omega
  · rw [Set.infinite_iff_exists_gt]
    intro B
    refine ⟨Erdos479H1.seqNegTwo B, ?_, ?_⟩
    · exact Erdos479H1.modEq_neg_two_of_dvd _ (Erdos479H1.seqNegTwo_inv B).2.2.1
    · have := (Erdos479H1.seqNegTwo_inv B).1
      omega
  · exact Erdos479H1.case_two_pow i hi

theorem OMA.solution : OMA.R_Erdos479_erdos_479_R1.H1 :=
  prove_Erdos479_H1
