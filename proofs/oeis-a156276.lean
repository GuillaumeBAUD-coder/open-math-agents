import OMAStatements.S_oeis_a156276

-- Credit: @mjsechrest2

namespace OMA.P_oeis_a156276

open OMA.S_oeis_a156276

private def A : ℕ → ℤ
  | n => 1 - ∑ k : Fin n, (n.choose k.1 : ℤ) * 5 * 10 ^ (n - k.1 - 1) * A k.1
decreasing_by exact k.isLt

private lemma eulerAt_eq_A_div (n : ℕ) :
    eulerAt (1 / 10) n = (A n : ℚ) / (10 : ℚ) ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [eulerAt, A]
    have hpow : (10 : ℚ) ^ n ≠ 0 := by positivity
    rw [eq_div_iff hpow]
    have h1 : ((1 / 10 : ℚ) ^ n) * (10 : ℚ) ^ n = 1 := by
      rw [← mul_pow]; norm_num
    rw [sub_mul, h1, mul_comm (1 / 2 : ℚ), mul_assoc, Finset.sum_mul]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [ih k.1 k.isLt]
    have hle : k.1 + 1 ≤ n := k.isLt
    have hexp : (10 : ℚ) ^ n = (10 : ℚ) ^ k.1 * (10 : ℚ) ^ (n - k.1 - 1) * 10 := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    have hkpow : (10 : ℚ) ^ k.1 ≠ 0 := by positivity
    rw [hexp]
    field_simp [hkpow]
    ring

private lemma A_mod_five (n : ℕ) : A n % 5 = 1 := by
  rw [A]
  have hdvd : (5 : ℤ) ∣ ∑ k : Fin n, (n.choose k.1 : ℤ) * 5 * 10 ^ (n - k.1 - 1) * A k.1 := by
    apply Finset.dvd_sum
    intro k _
    exact ⟨(n.choose k.1 : ℤ) * 10 ^ (n - k.1 - 1) * A k.1, by ring⟩
  obtain ⟨t, ht⟩ := hdvd
  rw [ht]
  omega

private lemma choose_two_mul_two (n : ℕ) : 2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  cases n with
  | zero => simp
  | succ k =>
    have hdiv : 2 ∣ (k + 1) * k := by
      rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨(2 * t + 1) * t, by ring⟩
      · exact ⟨(t + 1) * (2 * t + 1), by ring⟩
    have hnat : 2 * (k + 1).choose 2 = (k + 1) * k := by
      rw [Nat.choose_two_right, show k + 1 - 1 = k by omega, Nat.mul_div_cancel' hdiv]
    have hz : 2 * ((k + 1).choose 2 : ℤ) = ((k : ℤ) + 1) * (k : ℤ) := by exact_mod_cast hnat
    push_cast
    linarith

private lemma odd_choose_three_parity (m : ℕ) : ((2 * m + 1).choose 3 : ℤ) % 2 = (m : ℤ) % 2 := by
  have h1 : 6 * (2 * m + 1).choose 3 = (2 * m + 1) * (2 * m) * (2 * m - 1) := by
    cases m with
    | zero => decide
    | succ k =>
      have hrec := Nat.descFactorial_eq_factorial_mul_choose (2 * (k + 1) + 1) 3
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one, Nat.factorial] at hrec
      have hsub1 : 2 * (k + 1) + 1 - 1 = 2 * (k + 1) := by omega
      have hsub2 : 2 * (k + 1) + 1 - 2 = 2 * (k + 1) - 1 := by omega
      rw [hsub1, hsub2] at hrec
      norm_num at hrec
      linarith
  have h2 : 3 * (2 * m + 1).choose 3 = m * ((2 * m + 1) * (2 * m - 1)) := by
    have : 2 * (3 * (2 * m + 1).choose 3) = 2 * (m * ((2 * m + 1) * (2 * m - 1))) := by
      linarith
    omega
  cases m with
  | zero => decide
  | succ k =>
    have hz : 3 * ((2 * (k + 1) + 1).choose 3 : ℤ) =
        ((k + 1 : ℕ) : ℤ) * ((2 * (k + 1) + 1 : ℕ) : ℤ) * ((2 * (k + 1) - 1 : ℕ) : ℤ) := by
      have : 3 * (2 * (k + 1) + 1).choose 3 =
          (k + 1) * (2 * (k + 1) + 1) * (2 * (k + 1) - 1) := by
        linarith
      exact_mod_cast this
    have hodd1 : ((2 * (k + 1) + 1 : ℕ) : ℤ) % 2 = 1 := by omega
    have hodd2 : ((2 * (k + 1) - 1 : ℕ) : ℤ) % 2 = 1 := by omega
    have hprod : (((2 * (k + 1) + 1 : ℕ) : ℤ) * ((2 * (k + 1) - 1 : ℕ) : ℤ)) % 2 = 1 := by
      rw [Int.mul_emod, hodd1, hodd2]; norm_num
    have hmod : (3 * ((2 * (k + 1) + 1).choose 3 : ℤ)) % 2 = ((k + 1 : ℕ) : ℤ) % 2 := by
      rw [hz, mul_assoc, Int.mul_emod, hprod]
      omega
    omega

private lemma A_mod_eight (n : ℕ) :
    (Even n → A n % 8 = (1 - (n : ℤ)) % 8) ∧ (Odd n → A n % 8 = 4) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hsum_mod :
        (∑ k : Fin n, (n.choose k.1 : ℤ) * 5 * 10 ^ (n - k.1 - 1) * A k.1) % 8 =
        (∑ k : Fin n,
          if n - k.1 - 1 < 3 then (n.choose k.1 : ℤ) * 5 * 10 ^ (n - k.1 - 1) * A k.1 else 0) % 8 := by
      have hdiff :
          (8 : ℤ) ∣
            (∑ k : Fin n, (n.choose k.1 : ℤ) * 5 * 10 ^ (n - k.1 - 1) * A k.1) -
            (∑ k : Fin n,
              if n - k.1 - 1 < 3 then (n.choose k.1 : ℤ) * 5 * 10 ^ (n - k.1 - 1) * A k.1 else 0) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.dvd_sum
        intro k _
        split_ifs with hlt
        · simp
        · simp only [sub_zero]
          have hge : 3 ≤ n - k.1 - 1 := by omega
          have hdvd8 : (8 : ℤ) ∣ (10 : ℤ) ^ (n - k.1 - 1) := by
            have : (10 : ℤ) ^ (n - k.1 - 1) = (10 : ℤ) ^ 3 * (10 : ℤ) ^ (n - k.1 - 1 - 3) := by
              rw [← pow_add]; congr 1; omega
            rw [this]
            exact ⟨125 * (10 : ℤ) ^ (n - k.1 - 1 - 3), by ring⟩
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdvd8 _) _
      obtain ⟨t, ht⟩ := hdiff
      omega
    have hA_eq : A n % 8 =
        (1 - ∑ k : Fin n,
          if n - k.1 - 1 < 3 then (n.choose k.1 : ℤ) * 5 * 10 ^ (n - k.1 - 1) * A k.1 else 0) % 8 := by
      rw [A]
      omega
    rcases n with _ | _ | _ | n
    · exact ⟨fun _ => by rw [A]; norm_num, fun h => by rcases h with ⟨k, hk⟩; omega⟩
    · refine ⟨fun h => by rcases h with ⟨k, hk⟩; omega, fun _ => ?_⟩
      have h0 : A 0 = 1 := by rw [A]; norm_num
      rw [A]; simp [h0]
    · refine ⟨fun _ => ?_, fun h => by rcases h with ⟨k, hk⟩; omega⟩
      have h0 : A 0 = 1 := by rw [A]; norm_num
      have h1 : A 1 = -4 := by rw [A]; simp [h0]
      rw [A]; simp [Fin.sum_univ_two, h0, h1]
    · -- n + 3 >= 3
      set m := n + 3 with hm_def
      have hm3 : 3 ≤ m := by omega
      have hfin :
          (∑ k : Fin m,
            if m - k.1 - 1 < 3 then (m.choose k.1 : ℤ) * 5 * 10 ^ (m - k.1 - 1) * A k.1 else 0) =
          (m.choose (m - 1) : ℤ) * 5 * A (m - 1) +
          (m.choose (m - 2) : ℤ) * 50 * A (m - 2) +
          (m.choose (m - 3) : ℤ) * 500 * A (m - 3) := by
        let k1 : Fin m := ⟨m - 1, by omega⟩
        let k2 : Fin m := ⟨m - 2, by omega⟩
        let k3 : Fin m := ⟨m - 3, by omega⟩
        have hsub : (Finset.univ.filter fun k : Fin m => m - k.1 - 1 < 3) = {k1, k2, k3} := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, Fin.ext_iff, k1, k2, k3]
          omega
        rw [← Finset.sum_filter, hsub]
        have h12 : k1 ≠ k2 := by intro h; have := congrArg Fin.val h; dsimp [k1, k2] at this; omega
        have h13 : k1 ≠ k3 := by intro h; have := congrArg Fin.val h; dsimp [k1, k3] at this; omega
        have h23 : k2 ≠ k3 := by intro h; have := congrArg Fin.val h; dsimp [k2, k3] at this; omega
        rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
          Finset.sum_singleton]
        dsimp [k1, k2, k3]
        have he1 : m - (m - 1) - 1 = 0 := by omega
        have he2 : m - (m - 2) - 1 = 1 := by omega
        have he3 : m - (m - 3) - 1 = 2 := by omega
        rw [he1, he2, he3]
        ring
      rw [hfin] at hA_eq
      have hc1 : (m.choose (m - 1) : ℤ) = (m : ℤ) := by
        have := Nat.choose_symm (show 1 ≤ m by omega)
        rw [Nat.choose_one_right] at this
        exact_mod_cast this
      have hc2 : (m.choose (m - 2) : ℤ) = (m.choose 2 : ℤ) := by
        have := Nat.choose_symm (show 2 ≤ m by omega)
        exact_mod_cast this
      have hc3 : (m.choose (m - 3) : ℤ) = (m.choose 3 : ℤ) := by
        have := Nat.choose_symm (show 3 ≤ m by omega)
        exact_mod_cast this
      rw [hc1, hc2, hc3] at hA_eq
      constructor
      · intro heven
        rcases heven with ⟨r, hr⟩
        have hmr : m = 2 * r := by omega
        have hodd1 : Odd (m - 1) := ⟨r - 1, by omega⟩
        have hev2 : Even (m - 2) := ⟨r - 1, by omega⟩
        have hodd3 : Odd (m - 3) := ⟨r - 2, by omega⟩
        have hA1 : A (m - 1) % 8 = 4 := (ih (m - 1) (by omega)).2 hodd1
        have hA2 : A (m - 2) % 8 = (1 - ((m - 2 : ℕ) : ℤ)) % 8 := (ih (m - 2) (by omega)).1 hev2
        have hA3 : A (m - 3) % 8 = 4 := (ih (m - 3) (by omega)).2 hodd3
        have hc2m := choose_two_mul_two m
        have ht1 : ((m : ℤ) * 5 * A (m - 1)) % 8 = 0 := by
          have h4 : (4 : ℤ) ∣ A (m - 1) := by omega
          obtain ⟨q, hq⟩ := h4
          have hm' : (m : ℤ) = 2 * (r : ℤ) := by omega
          rw [hm', hq]
          have : 2 * (r : ℤ) * 5 * (4 * q) = 8 * (5 * (r : ℤ) * q) := by ring
          rw [this]
          omega
        have ht3 : ((m.choose 3 : ℤ) * 500 * A (m - 3)) % 8 = 0 := by
          have h4 : (4 : ℤ) ∣ A (m - 3) := by omega
          obtain ⟨q, hq⟩ := h4
          rw [hq]
          have : (m.choose 3 : ℤ) * 500 * (4 * q) = 8 * ((m.choose 3 : ℤ) * 250 * q) := by ring
          rw [this]
          omega
        have ht2 : ((m.choose 2 : ℤ) * 50 * A (m - 2)) % 8 = (2 * (r : ℤ)) % 8 := by
          have h50 : (m.choose 2 : ℤ) * 50 = 25 * (2 * (m.choose 2 : ℤ)) := by ring
          rw [h50, hc2m]
          have hA2' : A (m - 2) % 8 = (3 - 2 * (r : ℤ)) % 8 := by
            rw [hA2]; omega
          have hm' : (m : ℤ) = 2 * (r : ℤ) := by omega
          rw [hm']
          have hmod_mul : (25 * (2 * (r : ℤ) * (2 * (r : ℤ) - 1)) * A (m - 2)) % 8 =
              ((25 * (2 * (r : ℤ) * (2 * (r : ℤ) - 1))) % 8 * (A (m - 2) % 8)) % 8 :=
            Int.mul_emod _ _ 8
          rw [hmod_mul, hA2', ← Int.mul_emod]
          have hpoly : 25 * (2 * (r : ℤ) * (2 * (r : ℤ) - 1)) * (3 - 2 * (r : ℤ)) =
              2 * (r : ℤ) + 8 * (-25 * (r : ℤ) ^ 3 + 50 * (r : ℤ) ^ 2 - 19 * (r : ℤ)) := by ring
          rw [hpoly]
          omega
        rw [hA_eq]
        have htot : ((m : ℤ) * 5 * A (m - 1) + (m.choose 2 : ℤ) * 50 * A (m - 2) +
            (m.choose 3 : ℤ) * 500 * A (m - 3)) % 8 = (2 * (r : ℤ)) % 8 := by
          omega
        omega
      · intro hodd
        rcases hodd with ⟨r, hr⟩
        have hmr : m = 2 * r + 1 := by omega
        have hev1 : Even (m - 1) := ⟨r, by omega⟩
        have hodd2 : Odd (m - 2) := ⟨r - 1, by omega⟩
        have hev3 : Even (m - 3) := ⟨r - 1, by omega⟩
        have hA1 : A (m - 1) % 8 = (1 - ((m - 1 : ℕ) : ℤ)) % 8 := (ih (m - 1) (by omega)).1 hev1
        have hA2 : A (m - 2) % 8 = 4 := (ih (m - 2) (by omega)).2 hodd2
        have hA3 : A (m - 3) % 8 = (1 - ((m - 3 : ℕ) : ℤ)) % 8 := (ih (m - 3) (by omega)).1 hev3
        have ht2 : ((m.choose 2 : ℤ) * 50 * A (m - 2)) % 8 = 0 := by
          have h4 : (4 : ℤ) ∣ A (m - 2) := by omega
          obtain ⟨q, hq⟩ := h4
          rw [hq]
          have : (m.choose 2 : ℤ) * 50 * (4 * q) = 8 * ((m.choose 2 : ℤ) * 25 * q) := by ring
          rw [this]
          omega
        have ht1 : ((m : ℤ) * 5 * A (m - 1)) % 8 = (5 - 4 * (r : ℤ)) % 8 := by
          have hA1' : A (m - 1) % 8 = (1 - 2 * (r : ℤ)) % 8 := by rw [hA1]; omega
          have hm' : (m : ℤ) = 2 * (r : ℤ) + 1 := by omega
          rw [hm']
          have hmod_mul : ((2 * (r : ℤ) + 1) * 5 * A (m - 1)) % 8 =
              (((2 * (r : ℤ) + 1) * 5) % 8 * (A (m - 1) % 8)) % 8 := Int.mul_emod _ _ 8
          rw [hmod_mul, hA1', ← Int.mul_emod]
          have hsq : (r : ℤ) ^ 2 % 2 = (r : ℤ) % 2 := by
            rcases Int.even_or_odd (r : ℤ) with ⟨t, ht⟩ | ⟨t, ht⟩
            · rw [ht]
              have : (t + t) ^ 2 = 2 * (2 * t ^ 2) := by ring
              rw [this]; omega
            · rw [ht]
              have : (2 * t + 1) ^ 2 = 2 * (2 * t ^ 2 + 2 * t) + 1 := by ring
              rw [this]; omega
          have hpoly : (2 * (r : ℤ) + 1) * 5 * (1 - 2 * (r : ℤ)) =
              5 - 4 * (r : ℤ) ^ 2 - 8 * (2 * (r : ℤ) ^ 2) := by ring
          rw [hpoly]
          omega
        have ht3 : ((m.choose 3 : ℤ) * 500 * A (m - 3)) % 8 = (4 * (r : ℤ)) % 8 := by
          have hA3_odd : A (m - 3) % 2 = 1 := by omega
          have hch3 : (m.choose 3 : ℤ) % 2 = (r : ℤ) % 2 := by
            rw [hmr]; exact odd_choose_three_parity r
          have hprod : ((m.choose 3 : ℤ) * A (m - 3)) % 2 = (r : ℤ) % 2 := by
            rw [Int.mul_emod, hch3, hA3_odd]; omega
          have h500 : (m.choose 3 : ℤ) * 500 * A (m - 3) =
              4 * ((m.choose 3 : ℤ) * A (m - 3)) + 8 * (62 * (m.choose 3 : ℤ) * A (m - 3)) := by
            ring
          rw [h500]
          omega
        rw [hA_eq]
        omega

private lemma den_of_coprime (num : ℤ) (den : ℕ) (hden : 0 < den)
    (hcop : Nat.Coprime num.natAbs den) :
    ((num : ℚ) / (den : ℚ)).den = den := by
  let q : ℚ := ⟨num, den, hden.ne', hcop⟩
  have hq : (num : ℚ) / (den : ℚ) = q := Rat.num_div_den q
  rw [hq]

private lemma a_even (n : ℕ) (he : Even n) : a n = 10 ^ n := by
  unfold a
  rw [eulerAt_eq_A_div]
  have h5 : A n % 5 = 1 := A_mod_five n
  have h8 : A n % 8 = (1 - (n : ℤ)) % 8 := (A_mod_eight n).1 he
  have h2 : A n % 2 = 1 := by rcases he with ⟨r, rfl⟩; omega
  have hcop10 : Nat.Coprime (A n).natAbs 10 := by
    have hnd2 : ¬ (2 ∣ (A n).natAbs) := by
      intro h; have : (2 : ℤ) ∣ A n := Int.natCast_dvd.mpr h; omega
    have hnd5 : ¬ (5 ∣ (A n).natAbs) := by
      intro h; have : (5 : ℤ) ∣ A n := Int.natCast_dvd.mpr h; omega
    have hc2 : Nat.Coprime (A n).natAbs 2 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd2 |>.symm
    have hc5 : Nat.Coprime (A n).natAbs 5 := (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hnd5 |>.symm
    exact hc2.mul_right hc5
  simpa using den_of_coprime (A n) (10 ^ n) (by positivity) (hcop10.pow_right n)

private lemma a_odd (n : ℕ) (ho : Odd n) (hn : 3 ≤ n) : a n = 10 ^ n / 4 := by
  unfold a
  rw [eulerAt_eq_A_div]
  have h5 : A n % 5 = 1 := A_mod_five n
  have h8 : A n % 8 = 4 := (A_mod_eight n).2 ho
  have h4 : (4 : ℤ) ∣ A n := by omega
  obtain ⟨B, hB⟩ := h4
  have hB2 : B % 2 = 1 := by omega
  have hB5 : B % 5 ≠ 0 := by omega
  have h10div : 4 ∣ 10 ^ n := by
    have : 10 ^ n = 100 * 10 ^ (n - 2) := by
      rw [show (100 : ℕ) = 10 ^ 2 by rfl, ← pow_add]; congr 1; omega
    rw [this]
    exact ⟨25 * 10 ^ (n - 2), by ring⟩
  have heq : (A n : ℚ) / (10 : ℚ) ^ n = (B : ℚ) / ((10 ^ n / 4 : ℕ) : ℚ) := by
    rw [hB]
    have h10q : ((10 ^ n : ℕ) : ℚ) = 4 * ((10 ^ n / 4 : ℕ) : ℚ) := by
      exact_mod_cast (Nat.mul_div_cancel' h10div).symm
    push_cast at h10q ⊢
    rw [h10q]
    have hpos : ((10 ^ n / 4 : ℕ) : ℚ) ≠ 0 := by
      have : 0 < 10 ^ n / 4 := by
        have h100 : 100 ≤ 10 ^ n := by
          calc 100 = 10 ^ 2 := by rfl
            _ ≤ 10 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      exact_mod_cast this.ne'
    field_simp [hpos]
  rw [heq]
  have hcop10 : Nat.Coprime B.natAbs 10 := by
    have hnd2 : ¬ (2 ∣ B.natAbs) := by
      intro h; have : (2 : ℤ) ∣ B := Int.natCast_dvd.mpr h; omega
    have hnd5 : ¬ (5 ∣ B.natAbs) := by
      intro h; have : (5 : ℤ) ∣ B := Int.natCast_dvd.mpr h; omega
    have hc2 : Nat.Coprime B.natAbs 2 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd2 |>.symm
    have hc5 : Nat.Coprime B.natAbs 5 := (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hnd5 |>.symm
    exact hc2.mul_right hc5
  have hcop : Nat.Coprime B.natAbs (10 ^ n / 4) :=
    (hcop10.pow_right n).coprime_dvd_right (Nat.div_dvd_of_dvd h10div)
  have hpos : 0 < 10 ^ n / 4 := by
    have h100 : 100 ≤ 10 ^ n := by
      calc 100 = 10 ^ 2 := by rfl
        _ ≤ 10 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  exact den_of_coprime B (10 ^ n / 4) hpos hcop

end OMA.P_oeis_a156276

theorem OMA.solution : type_of% @OMA.S_oeis_a156276.main := by
  open OMA.S_oeis_a156276 OMA.P_oeis_a156276 in
  intro n hn
  rcases Nat.even_or_odd n with he | ho
  · have he2 : Even (n + 2) := by rcases he with ⟨k, rfl⟩; exact ⟨k + 1, by ring⟩
    rw [a_even (n + 2) he2, a_even n he, pow_add]
    ring
  · have hn3 : 3 ≤ n := by rcases ho with ⟨k, rfl⟩; omega
    have ho2 : Odd (n + 2) := by rcases ho with ⟨k, rfl⟩; exact ⟨k + 1, by ring⟩
    rw [a_odd (n + 2) ho2 (by omega), a_odd n ho hn3]
    have h10div : 4 ∣ 10 ^ n := by
      have : 10 ^ n = 100 * 10 ^ (n - 2) := by
        rw [show (100 : ℕ) = 10 ^ 2 by rfl, ← pow_add]; congr 1; omega
      rw [this]
      exact ⟨25 * 10 ^ (n - 2), by ring⟩
    rw [pow_add, show (10 : ℕ) ^ 2 = 100 by rfl, mul_comm (10 ^ n) 100,
      Nat.mul_div_assoc 100 h10div]
