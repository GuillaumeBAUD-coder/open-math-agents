import OMAReductions.R_wp_are_all_mersenne_numbers_of_prime_index_square_free_R1

/-!
# Proof of `wp-are-all-mersenne-numbers-of-prime-index-square-free.R1.H1`

Proves that if `p, q` are primes with `q ^ 2 ∣ 2 ^ p - 1`, then:
1. `q % (2 * p) = 1`: `q` is odd (since `2 ^ p - 1` is odd), `p` is odd (since `2 ^ 2 - 1 = 3` is
   squarefree), and `orderOf (2 : ZMod q) = p ∣ q - 1`, so `2 * p ∣ q - 1`.
2. `2 ^ (q - 1) % q ^ 2 = 1`: since `p ∣ q - 1` and `2 ^ p ≡ 1 [MOD q ^ 2]`, raising to the
   `(q - 1) / p` power yields `2 ^ (q - 1) ≡ 1 [MOD q ^ 2]`.
3. `100000 < q`: an exhaustive `decide +kernel` check via structurally recursive binary modular
   exponentiation (`pow2ModFuel`) shows the only odd primes `q ≤ 100000` with
   `2 ^ (q - 1) % q ^ 2 = 1` are `1093` and `3511`, and neither satisfies `q ^ 2 ∣ 2 ^ p - 1`
   with `p ∣ q - 1` (`1093 - 1 = 2^2 * 3 * 7 * 13`, `3511 - 1 = 2 * 3^3 * 5 * 13`, while
   `2 ^ 13 - 1 = 8191 < 1093 ^ 2`).
-/

namespace WpMersenneR1H1Proof

private def pow2ModFuel : ℕ → ℕ → ℕ → ℕ
  | 0, _, m => 1 % m
  | f + 1, e, m =>
    if e == 0 then 1 % m
    else
      let half := pow2ModFuel f (e / 2) m
      let sq := (half * half) % m
      if e % 2 == 1 then (sq + sq) % m else sq

private lemma pow2ModFuel_eq : ∀ (fuel e m : ℕ), e < 2 ^ fuel →
    pow2ModFuel fuel e m = 2 ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro e m he
    have he0 : e = 0 := by omega
    subst he0
    simp [pow2ModFuel]
  | succ f ih =>
    intro e m he
    unfold pow2ModFuel
    by_cases he0 : e = 0
    · subst he0; simp
    · have hbeq : (e == 0) = false := by simp [he0]
      rw [hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hdiv_lt : e / 2 < 2 ^ f := by
        rw [pow_succ] at he
        omega
      rw [ih (e / 2) m hdiv_lt]
      set q := e / 2
      have hsq : (2 ^ q % m * (2 ^ q % m)) % m = 2 ^ (2 * q) % m := by
        rw [← Nat.mul_mod, ← pow_add, show q + q = 2 * q by omega]
      rw [hsq]
      by_cases hodd : e % 2 = 1
      · have hodd_b : (e % 2 == 1) = true := by simp [hodd]
        rw [hodd_b]
        simp only [↓reduceIte]
        have hadd : (2 ^ (2 * q) % m + 2 ^ (2 * q) % m) % m = 2 ^ (2 * q + 1) % m := by
          rw [← Nat.add_mod, show 2 ^ (2 * q) + 2 ^ (2 * q) = 2 ^ (2 * q + 1) by
            rw [pow_succ]; omega]
        rw [hadd, show 2 * q + 1 = e by omega]
      · have hodd_b : (e % 2 == 1) = false := by simp [hodd]
        rw [hodd_b]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show 2 * q = e by omega]

private def hasSmallPrimeDiv (n : ℕ) : Bool :=
  n > 31 &&
  (n % 3 == 0 || n % 5 == 0 || n % 7 == 0 || n % 11 == 0 || n % 13 == 0 ||
   n % 17 == 0 || n % 19 == 0 || n % 23 == 0 || n % 29 == 0 || n % 31 == 0)

private lemma not_hasSmallPrimeDiv_of_prime {q : ℕ} (hq : q.Prime) :
    hasSmallPrimeDiv q = false := by
  unfold hasSmallPrimeDiv
  by_cases hgt : q > 31
  · have hnd : ∀ p : ℕ, p ≤ 31 → p.Prime → (q % p == 0) = false := by
      intro p hple hp
      have hne : p ≠ q := by omega
      have hndvd : ¬ p ∣ q := fun hd => by
        rcases (Nat.dvd_prime hq).mp hd with h1 | h2
        · exact hp.ne_one h1
        · exact hne h2
      simp [Nat.dvd_iff_mod_eq_zero.mpr.mt hndvd]
    have h3 := hnd 3 (by decide) (by decide)
    have h5 := hnd 5 (by decide) (by decide)
    have h7 := hnd 7 (by decide) (by decide)
    have h11 := hnd 11 (by decide) (by decide)
    have h13 := hnd 13 (by decide) (by decide)
    have h17 := hnd 17 (by decide) (by decide)
    have h19 := hnd 19 (by decide) (by decide)
    have h23 := hnd 23 (by decide) (by decide)
    have h29 := hnd 29 (by decide) (by decide)
    have h31 := hnd 31 (by decide) (by decide)
    simp [hgt, h3, h5, h7, h11, h13, h17, h19, h23, h29, h31]
  · simp [hgt]

private def checkWieferichOdd (n : ℕ) : Bool :=
  if n > 100000 || n == 1093 || n == 3511 || hasSmallPrimeDiv n then true
  else pow2ModFuel 17 (n - 1) (n * n) != 1

private def checkOddTree (lo : ℕ) : ℕ → Bool
  | 0 => checkWieferichOdd lo
  | d + 1 =>
    if lo > 100000 then true
    else checkOddTree lo d && checkOddTree (lo + 2 ^ (d + 1)) d

private lemma checkOddTree_sound : ∀ d lo : ℕ,
    checkOddTree lo d = true →
    ∀ k : ℕ, k < 2 ^ d → lo + 2 * k ≤ 100000 → checkWieferichOdd (lo + 2 * k) = true := by
  intro d
  induction d with
  | zero =>
    intro lo h k hk _
    have hk0 : k = 0 := by omega
    subst hk0
    simpa [checkOddTree] using h
  | succ d ih =>
    intro lo h k hk hle
    unfold checkOddTree at h
    have hlo : ¬ (lo > 100000) := by omega
    simp only [hlo, ↓reduceIte, Bool.and_eq_true] at h
    by_cases hlt : k < 2 ^ d
    · exact ih lo h.1 k hlt hle
    · have hk' : k - 2 ^ d < 2 ^ d := by
        rw [pow_succ] at hk
        omega
      have heq : lo + 2 ^ (d + 1) + 2 * (k - 2 ^ d) = lo + 2 * k := by
        rw [pow_succ]
        omega
      have hres := ih (lo + 2 ^ (d + 1)) h.2 (k - 2 ^ d) hk' (by omega)
      rwa [heq] at hres

-- 3 + 2 * (2^16 - 1) = 131073 > 100000, stops immediately once lo > 100000.
private lemma checkOddTree_all : checkOddTree 3 16 = true := by decide +kernel

private lemma wieferich_small_cases {q : ℕ} (hq : q.Prime) (hodd : q % 2 = 1)
    (hle : q ≤ 100000) (hw : 2 ^ (q - 1) % q ^ 2 = 1) : q = 1093 ∨ q = 3511 := by
  have hge3 : 3 ≤ q := by have := hq.two_le; omega
  set k := (q - 3) / 2
  have hq_eq : 3 + 2 * k = q := by omega
  have hk_lt : k < 2 ^ 16 := by omega
  have hok := checkOddTree_sound 16 3 checkOddTree_all k hk_lt (by omega)
  rw [hq_eq] at hok
  unfold checkWieferichOdd at hok
  by_cases h1093 : q = 1093
  · exact Or.inl h1093
  by_cases h3511 : q = 3511
  · exact Or.inr h3511
  have hnotgt : ¬ (q > 100000) := by omega
  have hsmall := not_hasSmallPrimeDiv_of_prime hq
  have hcond : (q > 100000 || q == 1093 || q == 3511 || hasSmallPrimeDiv q) = false := by
    simp [hnotgt, h1093, h3511, hsmall]
  rw [hcond] at hok
  simp only [Bool.false_eq_true, ↓reduceIte] at hok
  have hne : pow2ModFuel 17 (q - 1) (q * q) ≠ 1 := by simpa using hok
  rw [pow2ModFuel_eq 17 (q - 1) (q * q) (by omega), ← sq] at hne
  exact absurd hw hne

end WpMersenneR1H1Proof

theorem OMA.solution : OMA.R_wp_are_all_mersenne_numbers_of_prime_index_square_free_R1.H1 := by
  intro p q hp hq hdvd
  have h2p_ge : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hq_odd : q % 2 = 1 := by
    by_contra hev
    have h2q : 2 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
    have h2m : 2 ∣ 2 ^ p - 1 := dvd_trans h2q (dvd_trans (dvd_pow_self q (by decide)) hdvd)
    have h2pow : 2 ∣ 2 ^ p := dvd_pow_self 2 hp.ne_zero
    have hmod_m : (2 ^ p - 1) % 2 = 1 := by
      have : 2 ^ p ≥ 2 := by
        have := hp.two_le
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have := Nat.mod_eq_zero_of_dvd h2m
    omega
  have hp_odd : p ≠ 2 := by
    rintro rfl
    have h3 : q ^ 2 ∣ 3 := by simpa using hdvd
    have hle := Nat.le_of_dvd (by decide) h3
    have := hq.two_le
    nlinarith
  have hq_dvd : q ∣ 2 ^ p - 1 := dvd_trans (dvd_pow_self q (by decide)) hdvd
  have h2p_mod_q : 2 ^ p % q = 1 := by
    have h1 : 2 ^ p ≡ 1 [MOD q] := ((Nat.modEq_iff_dvd' h2p_ge).mpr hq_dvd).symm
    rw [Nat.ModEq, Nat.mod_eq_of_lt hq.one_lt] at h1
    exact h1
  -- Show p ∣ q - 1 via ZMod q
  have hp_dvd_q1 : p ∣ q - 1 := by
    have : Fact q.Prime := ⟨hq⟩
    have h2u : (2 : ZMod q) ≠ 0 := by
      intro h0
      have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h0)
      have := Nat.le_of_dvd (by decide) hd
      have := hq.two_le
      omega
    have h2p1 : (2 : ZMod q) ^ p = 1 := by
      have : ((2 ^ p : ℕ) : ZMod q) = (1 : ZMod q) := by
        rw [← ZMod.natCast_mod, h2p_mod_q]
        simp
      simpa using this
    have hord_dvd_p : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one h2p1
    have h2ne1 : (2 : ZMod q) ≠ 1 := by
      intro h1
      have h10 : (1 : ZMod q) = 0 := by linear_combination h1
      exact one_ne_zero h10
    have hord_ne1 : orderOf (2 : ZMod q) ≠ 1 := fun h1 => h2ne1 (orderOf_eq_one_iff.mp h1)
    have hord_eq : orderOf (2 : ZMod q) = p :=
      (Nat.dvd_prime hp).mp hord_dvd_p |>.resolve_left hord_ne1
    have hflt : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2u
    rw [← hord_eq]
    exact orderOf_dvd_of_pow_eq_one hflt
  have h2p_dvd_q1 : 2 * p ∣ q - 1 := by
    have h2_dvd : 2 ∣ q - 1 := by omega
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp_odd)
    exact hcop.mul_dvd_of_dvd_of_dvd h2_dvd hp_dvd_q1
  have hq_mod_2p : q % (2 * p) = 1 := by
    obtain ⟨t, ht⟩ := h2p_dvd_q1
    have hq1 : q = 2 * p * t + 1 := by have := hq.two_le; omega
    have h1lt : 1 < 2 * p := by have := hp.two_le; omega
    rw [hq1, Nat.mul_add_mod, Nat.mod_eq_of_lt h1lt]
  have hwieferich : 2 ^ (q - 1) % q ^ 2 = 1 := by
    obtain ⟨t, ht⟩ := hp_dvd_q1
    have hmod_p : 2 ^ p ≡ 1 [MOD q ^ 2] := ((Nat.modEq_iff_dvd' h2p_ge).mpr hdvd).symm
    have hmod_q1 : 2 ^ (q - 1) ≡ 1 [MOD q ^ 2] := by
      rw [ht, pow_mul]
      simpa using hmod_p.pow t
    have h1lt : 1 < q ^ 2 := by have := hq.two_le; nlinarith
    rw [Nat.ModEq, Nat.mod_eq_of_lt h1lt] at hmod_q1
    exact hmod_q1
  have hq_gt : 100000 < q := by
    by_contra hle
    have hcases := WpMersenneR1H1Proof.wieferich_small_cases hq hq_odd (by omega) hwieferich
    rcases hcases with rfl | rfl
    · -- q = 1093, q - 1 = 1092 = 4 * 3 * 7 * 13, so prime p ∣ 1092 implies p ≤ 13
      have hp_le : p ≤ 13 := by
        have hd : p ∣ 1092 := hp_dvd_q1
        have hfac : 1092 = 2 * (2 * (3 * (7 * 13))) := by norm_num
        rw [hfac] at hd
        rcases hp.dvd_mul.mp hd with h | hd
        · exact le_trans (Nat.le_of_dvd (by decide) h) (by decide)
        rcases hp.dvd_mul.mp hd with h | hd
        · exact le_trans (Nat.le_of_dvd (by decide) h) (by decide)
        rcases hp.dvd_mul.mp hd with h | hd
        · exact le_trans (Nat.le_of_dvd (by decide) h) (by decide)
        rcases hp.dvd_mul.mp hd with h | h
        · exact le_trans (Nat.le_of_dvd (by decide) h) (by decide)
        · exact Nat.le_of_dvd (by decide) h
      have hpos : 0 < 2 ^ p - 1 := by
        have := hp.two_le
        have : 4 ≤ 2 ^ p := calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) this
        omega
      have hle_pow : 2 ^ p - 1 ≤ 2 ^ 13 - 1 :=
        Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) hp_le) 1
      have hge_q2 : 1093 ^ 2 ≤ 2 ^ p - 1 := Nat.le_of_dvd hpos hdvd
      omega
    · -- q = 3511, q - 1 = 3510 = 2 * 27 * 5 * 13, so prime p ∣ 3510 implies p ≤ 13
      have hp_le : p ≤ 13 := by
        have hd : p ∣ 3510 := hp_dvd_q1
        have hfac : 3510 = 2 * (3 * (3 * (3 * (5 * 13)))) := by norm_num
        rw [hfac] at hd
        rcases hp.dvd_mul.mp hd with h | hd
        · exact le_trans (Nat.le_of_dvd (by decide) h) (by decide)
        rcases hp.dvd_mul.mp hd with h | hd
        · exact le_trans (Nat.le_of_dvd (by decide) h) (by decide)
        rcases hp.dvd_mul.mp hd with h | hd
        · exact le_trans (Nat.le_of_dvd (by decide) h) (by decide)
        rcases hp.dvd_mul.mp hd with h | hd
        · exact le_trans (Nat.le_of_dvd (by decide) h) (by decide)
        rcases hp.dvd_mul.mp hd with h | h
        · exact le_trans (Nat.le_of_dvd (by decide) h) (by decide)
        · exact Nat.le_of_dvd (by decide) h
      have hpos : 0 < 2 ^ p - 1 := by
        have := hp.two_le
        have : 4 ≤ 2 ^ p := calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) this
        omega
      have hle_pow : 2 ^ p - 1 ≤ 2 ^ 13 - 1 :=
        Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) hp_le) 1
      have hge_q2 : 3511 ^ 2 ≤ 2 ^ p - 1 := Nat.le_of_dvd hpos hdvd
      omega
  exact ⟨hwieferich, hq_mod_2p, hq_gt⟩
