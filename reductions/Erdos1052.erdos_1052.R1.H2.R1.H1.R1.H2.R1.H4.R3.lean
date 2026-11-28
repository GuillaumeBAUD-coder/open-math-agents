import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1

/-!
Write m for the exponent of 2 and z for the unique repeated odd prime of n.
For odd m, each prime q = 5 mod 6 dividing m is the order of 4 modulo z,
and its square cannot divide m. If 5 divides n, its successor consumes the
only factor 3 in the balance equation, sharply restricting the even classes
of m. If 5 is absent and m is even, a Fermat divisor supplies a prime of n
congruent to 2 modulo 3. Each remaining case asks for a uniform bound on m.
-/

-- Credit: @Pixelstorm44
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R3

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)

-- The balance equation permits only one source of a factor 3.
private theorem sources {n z : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hz : z.Prime) (h7 : 7 ≤ z)
    (hs : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) :
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ padicValNat 2 n + 1 → p ∣ n) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → p % 3 = 2 →
      Odd (padicValNat 2 n) → p = z) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → p % 3 = 2 → 5 ∣ n → p = 5 ∨ p = z) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → p % 3 = 2 → p ≠ z →
      ¬ 3 ∣ 1 + z ^ n.factorization z ∧ ¬ 9 ∣ p + 1) := by
  obtain ⟨hzn, hsimple⟩ := simple_of_unique_repeated hn.2.ne' hs
  obtain ⟨hP, E⟩ := kernel_balance_one hn (Nat.mem_primeFactors.mpr ⟨hz, hzn, hn.2.ne'⟩)
    (by omega) hsimple
  obtain ⟨_, mem, unique, clash, _, nosq, _, zclash⟩ := facts hP (prime_dvd_prime_pow hz) E
  let P := (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ))
  have inside {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hd : p ∣ n) (hpz : p ≠ z) : p ∈ P := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨h2, Nat.mem_primeFactors.mpr
      ⟨hp, hd, hn.2.ne'⟩⟩, by simpa using hpz⟩
  have h3 : 3 ∉ ({z} : Finset ℕ) := by simp; omega
  have h5 (h : 5 ∣ n) : 5 ∈ P := inside (by norm_num) (by decide) h (by omega)
  rw [← Nat.factorization_def n Nat.prime_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp h2 hd
    by_cases he : p = z
    · simpa [he] using hzn
    have hmem := mem p hp h2 (by simpa using he) hd
    exact Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_filter.mp hmem).1)
  · intro p hp h2 hd hr ho
    by_contra hne
    have hpow := ho.nat_add_dvd_pow_add_pow 2 1
    simp only [one_pow] at hpow
    exact clash 3 (by norm_num) (by decide) h3 hpow p (inside hp h2 hd hne) (by omega)
  · intro p hp h2 hd hr hf
    by_cases h : p = z
    · exact Or.inr h
    exact Or.inl (unique 3 (by norm_num) (by decide) h3 p (inside hp h2 hd h) 5 (h5 hf)
      (by omega) (by decide))
  · intro p hp h2 hd hr hpz
    have hm := inside hp h2 hd hpz
    exact ⟨fun h => zclash 3 (by norm_num) (by decide) h3 h p hm (by omega),
      nosq 3 (by norm_num) (by decide) h3 p hm⟩

private theorem succ_dvd_of_odd {a m : ℕ} (hm : Odd m) (ha : a ∣ m) :
    2 ^ a + 1 ∣ 2 ^ m + 1 := by
  obtain ⟨v, rfl⟩ := ha
  have hv := hm.of_dvd_nat (dvd_mul_left v a)
  simpa [pow_mul] using hv.nat_add_dvd_pow_add_pow (2 ^ a) 1

-- For an odd exponent a and q = 5 mod 6, the quotient
-- (2^(a*q)+1)/(2^a+1) is 2 mod 3 and is q modulo 2^a+1.
private theorem quotient_source {m z a q : ℕ} (hm : Odd m) (hq : q % 6 = 5)
    (hd : a * q ∣ m)
    (force : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ 2 ^ m + 1 → c % 3 = 2 → c = z) :
    ∃ Q : ℕ, z % 3 = 2 ∧ z ∣ Q ∧ Q ≡ q [MOD 2 ^ a + 1] ∧ Q ∣ 2 ^ (a * q) + 1 := by
  have ha : Odd a := hm.of_dvd_nat ((dvd_mul_right a q).trans hd)
  have hthree : 3 ∣ 2 ^ a + 1 := by simpa using ha.nat_add_dvd_pow_add_pow 2 1
  obtain ⟨Q, hQ, hQmod⟩ := exists_quot_mod (z := 2 ^ a) (Nat.odd_iff.mpr (by omega : q % 2 = 1))
  have hQ3 : Q ≡ q [MOD 3] := Nat.ModEq.of_dvd hthree hQmod
  obtain ⟨c, hc, hcQ, hc3⟩ := exists_prime_mod3 Q (by change Q % 3 = q % 3 at hQ3; omega)
  have hdQ : Q ∣ 2 ^ (a * q) + 1 := by
    rw [pow_mul, add_comm, hQ]
    exact dvd_mul_left _ _
  have hcm := hcQ.trans (hdQ.trans (succ_dvd_of_odd hm hd))
  have hc2 : c ≠ 2 := by
    rintro rfl
    have h2 := dvd_pow_self 2 (show m ≠ 0 by have := Nat.odd_iff.mp hm; omega)
    have := (Nat.dvd_add_right h2).mp hcm
    omega
  obtain rfl := force c hc hc2 hcm hc3
  exact ⟨Q, hc3, hcQ, hQmod, hdQ⟩

private theorem odd_prime_restriction {m z : ℕ} (hm : Odd m) (hz : z.Prime) (hz7 : 7 ≤ z)
    (force : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ 2 ^ m + 1 → c % 3 = 2 → c = z)
    {q : ℕ} (hp : q.Prime) (hr : q % 6 = 5) (hd : q ∣ m) :
    z % 3 = 2 ∧ z ∣ 2 ^ q + 1 ∧ 2 * q < z ∧ q = orderOf (4 : ZMod z) ∧ ¬ q ^ 2 ∣ m := by
  obtain ⟨Q, hz3, hzQ, _, hQ⟩ := quotient_source (a := 1) hm hr (by simpa using hd) force
  have hzd : z ∣ 2 ^ q + 1 := by simpa using hzQ.trans hQ
  have : Fact q.Prime := ⟨hp⟩
  have hzero := (ZMod.natCast_eq_zero_iff _ _).mpr hzd
  push_cast at hzero
  have hneg : (2 : ZMod z) ^ q = -1 := eq_neg_of_add_eq_zero_left hzero
  have hfour : (4 : ZMod z) ^ q = 1 := by
    rw [show (4 : ZMod z) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm, pow_mul, hneg]
    norm_num
  have hne : (4 : ZMod z) ≠ 1 := by
    intro he
    have hzero : ((3 : ℕ) : ZMod z) = 0 := by push_cast; linear_combination he
    exact (by omega : ¬ z ≤ 3) (Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff _ _).mp hzero))
  have hord := orderOf_eq_prime hfour hne
  have hzfact : Fact z.Prime := ⟨hz⟩
  have hfour0 : (4 : ZMod z) ≠ 0 := by
    intro he
    have : z ∣ 4 := (ZMod.natCast_eq_zero_iff _ _).mp (by exact_mod_cast he)
    have := Nat.le_of_dvd (by decide) this
    omega
  have hdiv := ZMod.orderOf_dvd_card_sub_one hfour0
  rw [hord] at hdiv
  obtain ⟨k, hk⟩ := hdiv
  have hzo := hz.eq_two_or_odd
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases k <;> simp_all <;> omega
  have hbound := Nat.mul_le_mul_left q hk2
  refine ⟨hz3, hzd, by rw [Nat.mul_comm] ; omega, hord.symm, ?_⟩
  intro hsq
  obtain ⟨R, _, hzR, hmod, _⟩ := quotient_source (a := q) hm hr (by simpa [pow_two] using hsq) force
  have hqr : z ∣ q := ((Nat.ModEq.of_dvd hzd hmod).dvd_iff (dvd_refl z)).mp hzR
  have he := (Nat.prime_dvd_prime_iff_eq hz hp).mp hqr
  omega

private theorem fermatWitness {m : ℕ} (hm : 4 ∣ m) (hm0 : m ≠ 0) :
    ∃ t u z k : ℕ, 2 ≤ t ∧ Odd u ∧ m = 2 ^ t * u ∧
      z.Prime ∧ z % 3 = 2 ∧ z ∣ Nat.fermatNumber t ∧
      z = k * 2 ^ (t + 2) + 1 ∧ z ∣ 2 ^ m + 1 := by
  obtain ⟨t, u, hu, ht⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  have ht2 : 2 ≤ t := by
    by_contra! hlt
    obtain ⟨v, hv⟩ := hu
    rw [ht, hv] at hm
    interval_cases t <;> norm_num at hm <;> omega
  have hmod : Nat.fermatNumber t % 3 = 2 := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
    have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
    have hpow := h4.pow (2 ^ s)
    change (2 ^ (2 ^ (s + 1)) + 1) % 3 = 2
    rw [pow_succ', pow_mul]
    change (4 ^ (2 ^ s) + 1) % 3 = 2
    change 4 ^ (2 ^ s) + 1 ≡ 2 [MOD 3]
    simpa using hpow.add_right 1
  obtain ⟨z, hz, hzd, hz3⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1.exists_prime_mod3 _ hmod
  obtain ⟨k, hk⟩ := Nat.fermat_primeFactors_one_lt t z (by omega) hz hzd
  refine ⟨t, u, z, k, ht2, hu, ht, hz, hz3, hzd, hk, hzd.trans ?_⟩
  simpa [Nat.fermatNumber, ht, pow_mul] using hu.nat_add_dvd_pow_add_pow (2 ^ 2 ^ t) 1

private theorem exact_power_class {t u m : ℕ} (hu : Odd u) (hm : m = 2 ^ t * u) :
    m % 2 ^ (t + 1) = 2 ^ t := by
  obtain ⟨v, rfl⟩ := hu
  rw [hm, pow_succ, Nat.mul_mod_mul_left]
  simp

-- A simple 5 already supplies 3. A Fermat divisor congruent to 2 mod 3
-- and different from 5 must then be the exceptional prime z.
private theorem five_present {m z : ℕ} (hm : 4 ∣ m) (hm0 : m ≠ 0)
    (hz : z < 2100)
    (hf : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ m + 1 → p % 3 = 2 → p = 5 ∨ p = z)
    (hex : ∀ t : ℕ, 4 ≤ t → t ≤ 9 → m % 2 ^ (t + 1) ≠ 2 ^ t) :
    (m % 8 = 4 ∧ z = 17) ∨ (m % 16 = 8 ∧ z = 257) := by
  obtain ⟨t, u, p, k, ht, hu, he, hp, hp3, hF, hk, hd⟩ := fermatWitness hm hm0
  have hk0 : 0 < k := by
    by_contra! h
    simp [show k = 0 by omega] at hk
    have := hp.one_lt
    omega
  have hlo : 2 ^ (t + 2) ≤ k * 2 ^ (t + 2) := Nat.le_mul_of_pos_left _ hk0
  have h16 : 16 ≤ 2 ^ (t + 2) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ t + 2)
  have hzp := (hf p hp (by omega) hd hp3).resolve_left (by omega)
  have ht10 : t < 10 := by
    by_contra! ht10
    have : 4096 ≤ 2 ^ (t + 2) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 12 ≤ t + 2)
    omega
  have hr := exact_power_class hu he
  have ht4 : t < 4 := by
    by_contra! h
    exact hex t h (by omega) hr
  rcases (by omega : t = 2 ∨ t = 3) with rfl | rfl
  · exact Or.inl ⟨hr, hzp ▸ (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).mp hF⟩
  · exact Or.inr ⟨hr, hzp ▸ (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257)).mp hF⟩

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime → 7 ≤ z → z < 2100 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    (z % 3 = 2 → Odd (n.factorization z) → n.factorization z % 6 = 1) →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) → (z % 3 = 1 → padicValNat 2 n % 6 ≠ 5) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    Odd (padicValNat 2 n) → ¬ 5 ∣ n →
    (∀ q : ℕ, q.Prime → q % 6 = 5 → q ∣ padicValNat 2 n →
      z % 3 = 2 ∧ z ∣ 2 ^ q + 1 ∧ 2 * q < z ∧ q = orderOf (4 : ZMod z) ∧ ¬ q ^ 2 ∣ padicValNat 2 n) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime → 7 ≤ z → z < 2100 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    (z % 3 = 2 → Odd (n.factorization z) → n.factorization z % 6 = 1) →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) → (z % 3 = 1 → padicValNat 2 n % 6 ≠ 5) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    5 ∣ n → (¬ 3 ∣ 1 + z ^ n.factorization z) →
    (padicValNat 2 n % 4 = 2 ∨ (padicValNat 2 n % 8 = 4 ∧ z = 17) ∨
      (padicValNat 2 n % 16 = 8 ∧ z = 257)) →
    padicValNat 2 n ≤ A

def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime → 7 ≤ z → z < 2100 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    (z % 3 = 2 → Odd (n.factorization z) → n.factorization z % 6 = 1) →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) → (z % 3 = 1 → padicValNat 2 n % 6 ≠ 5) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    (¬ 5 ∣ n) → (∃ t u p k : ℕ, 2 ≤ t ∧ Odd u ∧ padicValNat 2 n = 2 ^ t * u ∧
      p.Prime ∧ p ∣ n ∧ p % 3 = 2 ∧ p ∣ Nat.fermatNumber t ∧ p = k * 2 ^ (t + 2) + 1 ∧
      (p ≠ z → ¬ 3 ∣ 1 + z ^ n.factorization z ∧ ¬ 9 ∣ p + 1)) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.H4 := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩
  refine ⟨max A (max B C), ?_⟩
  intro n hn z hz h7 hlt hs he hseven h6 h10 h14 h65 h20 h28 h8 h16 h4096 hex
  let m := padicValNat 2 n
  obtain ⟨fromTwo, oddSource, fiveSource, noClash⟩ := sources hn hz h7 hs
  by_cases ho : Odd m
  · have hf : ¬ 5 ∣ n := by
      intro hd
      have := oddSource 5 (by norm_num) (by decide) hd (by decide) ho
      omega
    apply le_trans _ (le_max_left A (max B C))
    apply hA n hn z hz h7 hlt hs he hseven h6 h10 h14 h65 h20 h28 h8 h16 h4096 hex ho hf
    intro q hp hr hd
    exact odd_prime_restriction ho hz h7
      (fun c hc h2 hcm hc3 => oddSource c hc h2 (fromTwo c hc h2 hcm) hc3 ho) hp hr hd
  have hpar : m % 2 = 0 := by rw [Nat.odd_iff] at ho; omega
  have hm0 : m ≠ 0 := (dvd_iff_padicValNat_ne_zero hn.2.ne').mp (two_dvd_of_isUnitaryPerfect hn)
  by_cases hf : 5 ∣ n
  · apply le_trans _ ((le_max_left B C).trans (le_max_right A _))
    apply hB n hn z hz h7 hlt hs he hseven h6 h10 h14 h65 h20 h28 h8 h16 h4096 hex hf
      (noClash 5 (by norm_num) (by decide) hf (by decide) (by omega)).1
    by_cases h4 : 4 ∣ m
    · apply Or.inr
      apply five_present h4 hm0 hlt (fun p hp hp2 hd hp3 => fiveSource p hp hp2
        (fromTwo p hp hp2 hd) hp3 hf)
      intro t hlow hhigh
      apply hex
      interval_cases t <;> decide
    · exact Or.inl (by change m % 4 = 2; omega)
  · have h4 : 4 ∣ m := by
      by_contra h
      have hr : m % (2 * 2) = 2 := by omega
      have hd := one_add_pow_dvd_of_odd_mul (z := 2) hr
      have h5 : 5 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm 1 (2 ^ m)] at hd
      exact hf (fromTwo 5 (by norm_num) (by decide) h5)
    obtain ⟨t, u, p, k, ht, hu, hmu, hp, hp3, hpF, hk, hd⟩ := fermatWitness h4 hm0
    have hkpos : k ≠ 0 := by
      rintro rfl
      simp at hk
      exact hp.ne_one hk
    have hp2 : p ≠ 2 := by
      have hk1 : 0 < k := Nat.pos_of_ne_zero hkpos
      have hpow : 16 ≤ 2 ^ (t + 2) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ t + 2)
      have := Nat.le_mul_of_pos_left (2 ^ (t+2)) hk1
      omega
    have hpn := fromTwo p hp hp2 hd
    apply le_trans _ ((le_max_right B C).trans (le_max_right A _))
    apply hC n hn z hz h7 hlt hs he hseven h6 h10 h14 h65 h20 h28 h8 h16 h4096 hex hf
    exact ⟨t, u, p, k, ht, hu, hmu, hp, hpn, hp3, hpF, hk, noClash p hp hp2 hpn hp3⟩

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R3
