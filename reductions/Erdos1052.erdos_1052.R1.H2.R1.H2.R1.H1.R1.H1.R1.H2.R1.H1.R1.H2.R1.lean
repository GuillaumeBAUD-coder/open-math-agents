import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1
import Mathlib.NumberTheory.Fermat

/-!
# Fermat factors in the branch containing 19423

Write m for the exponent of 2 in n. The parent hypotheses give 16 ∣ m and
exclude m ≡ 32 modulo 64.

* If m ≡ 16 modulo 32, then 65537 divides 2^m + 1. For the exponent e of
  65537 in n, the unitary divisor product forces every odd prime divisor of
  65537^e + 1 to divide n. The excluded small primes 11, 8681, 17, and 257
  imply 16 ∣ e. The primes 1409 and 641 exclude two more residues for e.
  Similarly 193, 449, 5441, and 5953 rule out the odd factors 3, 7, 17,
  and 31 of m.
* Otherwise write m = 2^t u with u odd and t ≥ 6. The Fermat number
  F_t divides 2^m + 1 and has a prime factor z ≡ 2 modulo 3. Fermat's
  divisor congruence gives z ≡ 1 modulo 2^(t+2). A simple z would contribute
  a second factor of 3 to the unitary divisor sum, in addition to 5+1.
  Thus z is a repeated prime, and the parent's parity condition applies.

The two remaining statements ask for a uniform bound on m in each case.
-/

-- Credit: @Pixelstorm44
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H2_R1

-- Every prime-power component contributes its successor to the unitary divisor sum.
private theorem component {n b q : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hb : b.Prime) (hbn : b ∣ n) (hq : q.Prime) (hq2 : q ≠ 2)
    (hd : q ∣ b ^ n.factorization b + 1) : q ∣ n := by
  have hm : b ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hb, hbn, h.2.ne'⟩
  have ht : q ∣ 2 * n := by
    rw [← OMA.R_Erdos1052_erdos_1052_R1.prod_eq_two_mul h]
    exact (by simpa [Nat.add_comm] using hd : q ∣ 1 + b ^ n.factorization b).trans
      (Finset.dvd_prod_of_mem (fun p => 1 + p ^ n.factorization p) hm)
  exact (hq.dvd_mul.mp ht).resolve_left (fun hd2 => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd2))

-- A tested divisor at exponent d persists at every odd multiple of d.
private theorem liftTest {b d e q : ℕ} (hr : e % (2 * d) = d)
    (hq : q ∣ b ^ d + 1) : q ∣ b ^ e + 1 := by
  have he : e = d * (2 * (e / (2 * d)) + 1) := by
    have hh := Nat.div_add_mod e (2 * d)
    rw [hr] at hh
    nlinarith only [hh]
  have ht := Odd.nat_add_dvd_pow_add_pow (b ^ d) 1
    (n := 2 * (e / (2 * d)) + 1) ⟨_, rfl⟩
  rw [one_pow, ← pow_mul, ← he] at ht
  exact hq.trans ht

-- The Fermat factor belonging to the exact power of two in m supplies its own
-- prime congruent to 2 modulo 3, with the stronger Fermat divisor congruence.
private theorem fermatWitness {m : ℕ} (hm : 64 ∣ m) (hm0 : m ≠ 0) :
    ∃ t u z k : ℕ, 6 ≤ t ∧ Odd u ∧ m = 2 ^ t * u ∧
      z.Prime ∧ z % 3 = 2 ∧ z ∣ Nat.fermatNumber t ∧
      z = k * 2 ^ (t + 2) + 1 ∧ z ∣ 2 ^ m + 1 := by
  obtain ⟨t, u, hu, ht⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  have ht6 : 6 ≤ t := by
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
  refine ⟨t, u, z, k, ht6, hu, ht, hz, hz3, hzd, hk, hzd.trans ?_⟩
  simpa [Nat.fermatNumber, ht, pow_mul] using hu.nat_add_dvd_pow_add_pow (2 ^ 2 ^ t) 1


private theorem sixteen_of_residues {e : ℕ}
    (a : e % 2 ≠ 1) (b : e % 4 ≠ 2) (c : e % 8 ≠ 4) (d : e % 16 ≠ 8) : 16 ∣ e := by omega

private theorem high_of_residues {m : ℕ}
    (a : 16 ∣ m) (b : m % 64 ≠ 32) (c : m % 32 ≠ 16) : 64 ∣ m := by omega

private theorem omit_four {m : ℕ} (h : m % 32 = 16) (a : m % 96 ≠ 48)
    (b : m % 224 ≠ 112) (c : m % 544 ≠ 272) (e : m % 992 ≠ 496) :
    ∀ d ∈ ({3, 7, 17, 31} : Finset ℕ), ¬ d ∣ m := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · clear b c e
    omega
  · clear a c e
    omega
  · clear a b e
    omega
  · clear a b c
    omega

private theorem large_fermat_factor {z k t : ℕ} (hz : z.Prime) (ht : 6 ≤ t)
    (hk : z = k * 2 ^ (t + 2) + 1) : 5 < z := by
  have hk0 : 1 ≤ k := by
    by_contra! hh
    simp [show k = 0 by omega] at hk
    have := hz.two_le
    omega
  have h256 : 256 ≤ 2 ^ (t + 2) := Nat.pow_le_pow_right (by decide : 0 < 2) (show 8 ≤ t + 2 by omega)
  have hh := Nat.mul_le_mul_right (2 ^ (t + 2)) hk0
  simp only [one_mul] at hh
  omega

private theorem square_exponent {x : ℕ} (hx : 0 < x) (hd : 16 ∣ x) : 2 ≤ x := by omega

private theorem three_dvd_succ {x : ℕ} (hx : x % 3 = 2) : 3 ∣ x + 1 := by omega

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    8191 ∣ n → ¬ 7933 ∣ n → ¬ 16381 ∣ n → 19423 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 41348 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
        q = 8191 ∨ q = 19423) →
    padicValNat 2 n % 32 = 16 →
    65537 ∈ S → 16 ∣ n.factorization 65537 →
    n.factorization 65537 % 64 ≠ 32 → n.factorization 65537 % 128 ≠ 64 →
    (∀ d ∈ ({3, 7, 17, 31} : Finset ℕ), ¬ d ∣ padicValNat 2 n) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    8191 ∣ n → ¬ 7933 ∣ n → ¬ 16381 ∣ n → 19423 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 41348 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
        q = 8191 ∨ q = 19423) →
    (∃ t u z k : ℕ, 6 ≤ t ∧ Odd u ∧ padicValNat 2 n = 2 ^ t * u ∧
      z ∈ S ∧ Even (n.factorization z) ∧ z % 3 = 2 ∧
      z ∣ Nat.fermatNumber t ∧ z = k * 2 ^ (t + 2) + 1) →
    padicValNat 2 n ≤ A

set_option maxHeartbeats 3000000 in
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1.H2 := by
  intro lo hi
  obtain ⟨A, hA⟩ := lo
  obtain ⟨B, hB⟩ := hi
  refine ⟨max A B, ?_⟩
  intro n hn hns S hS ha hb h4 h3 h5 h7 h19 hsup h16 h32 h31 h223 h607 h3967 h48 hthin hge h8191 h79 h163 h194 hexc
  let m := padicValNat 2 n
  have hm2 : 2 ∣ n := dvd_of_one_le_padicValNat (le_trans (by norm_num) h48)
  have fromTwo {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hd : q ∣ 2 ^ m + 1) : q ∣ n :=
    component hn Nat.prime_two hm2 hq hq2 (by rwa [Nat.factorization_def _ Nat.prime_two])
  have excluded {q : ℕ} (hp : q.Prime) (hs : q < 25000) (hcore :
      q ∉ ({2, 3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ)) : ¬ q ∣ n := by
    intro hd
    have hsq : ¬ q ^ 2 ∣ n := fun h => (not_le.mpr hs)
      (hge q ((hS q).mpr ⟨hp, fun e => hcore (by simp [e]), h⟩))
    have h := hexc q hp hd hsq (lt_trans hs (by decide))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcore
    exact hcore h
  by_cases hlow : m % 32 = 16
  · have h655 : 65537 ∣ n := fromTwo (by norm_num) (by decide)
      (liftTest (d := 16) hlow (by decide))
    let e := n.factorization 65537
    have epos : 0 < e := (show Nat.Prime 65537 by norm_num).factorization_pos_of_dvd hn.2.ne' h655
    have bad {d q : ℕ} (hp : q.Prime) (hq2 : q ≠ 2) (hnq : ¬ q ∣ n)
        (hd : q ∣ 65537 ^ d + 1) : e % (2 * d) ≠ d :=
      fun hr => hnq (component hn (by norm_num) h655 hp hq2 (liftTest hr hd))
    have e1 : e % 2 ≠ 1 := bad (d := 1) (q := 11) (by norm_num) (by decide)
      (excluded (by norm_num) (by decide) (by decide)) (by decide)
    have e2 : e % 4 ≠ 2 := bad (d := 2) (q := 8681) (by norm_num) (by decide)
      (excluded (by norm_num) (by decide) (by decide)) (by decide)
    have e4 : e % 8 ≠ 4 := bad (d := 4) (q := 17) (by norm_num) (by decide)
      (excluded (by norm_num) (by decide) (by decide)) (by decide)
    have e8 : e % 16 ≠ 8 := bad (d := 8) (q := 257) (by norm_num) (by decide)
      (excluded (by norm_num) (by decide) (by decide)) (by decide)
    have e32 : e % 64 ≠ 32 := bad (d := 32) (q := 1409) (by norm_num) (by decide)
      (excluded (by norm_num) (by decide) (by decide)) (by decide)
    have e64 : e % 128 ≠ 64 := bad (d := 64) (q := 641) (by norm_num) (by decide)
      (excluded (by norm_num) (by decide) (by decide)) (by decide)
    have ed := sixteen_of_residues e1 e2 e4 e8
    have hs655 : 65537 ∈ S := (hS _).mpr ⟨by norm_num, by decide,
      ((show Nat.Prime 65537 by norm_num).pow_dvd_iff_le_factorization hn.2.ne').mpr (square_exponent epos ed)⟩
    have badm {d q : ℕ} (hp : q.Prime) (hq2 : q ≠ 2) (hnq : ¬ q ∣ n)
        (hd : q ∣ 2 ^ d + 1) : m % (2 * d) ≠ d :=
      fun hr => hnq (fromTwo hp hq2 (liftTest hr hd))
    have m3 : m % 96 ≠ 48 := badm (d := 48) (q := 193) (by norm_num) (by decide)
      (excluded (by norm_num) (by decide) (by decide)) (by decide)
    have m7 : m % 224 ≠ 112 := badm (d := 112) (q := 449) (by norm_num) (by decide)
      (excluded (by norm_num) (by decide) (by decide)) (by decide)
    have m17 : m % 544 ≠ 272 := badm (d := 272) (q := 5441) (by norm_num) (by decide)
      (excluded (by norm_num) (by decide) (by decide)) (by decide)
    have m31 : m % 992 ≠ 496 := badm (d := 496) (q := 5953) (by norm_num) (by decide)
      (excluded (by norm_num) (by decide) (by decide)) (by decide)
    apply le_trans (hA n hn hns S hS ha hb h4 h3 h5 h7 h19 hsup h16 h32 h31 h223 h607 h3967 h48 hthin hge h8191 h79 h163 h194 hexc hlow hs655 ed e32 e64 ?_) (le_max_left _ _)
    exact omit_four hlow m3 m7 m17 m31
  · have hm64 := high_of_residues h16 h32 hlow
    obtain ⟨t,u,z,k,ht,hu,hm,hz,hz3,hzF,hzk,hzd⟩ :=
      fermatWitness hm64 (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 48) h48))
    have hzbig := large_fermat_factor hz ht hzk
    have hz2 := ne_of_gt (lt_trans (by decide : 2 < 5) hzbig)
    have hzn := fromTwo hz hz2 hzd
    obtain ⟨K,K',P,hP,hK,_,_,E,hmem⟩ :=
      OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C7.setup7 hn hS hm2
    obtain ⟨_,_,unique,_,_,_,_,_⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1.facts hP hK E
    have n3 : 3 ∉ S := fun hs => (by decide : ¬ 25000 ≤ 3) (hge 3 hs)
    have n5 : 5 ∉ S := fun hs => (by decide : ¬ 25000 ≤ 5) (hge 5 hs)
    have p5 := (hmem 5).mpr ⟨by norm_num, by decide, h5, n5⟩
    have hzS : z ∈ S := by
      by_contra hh
      have pz := (hmem z).mpr ⟨hz, hz2, hzn, hh⟩
      have heq := unique 3 (by norm_num) (by decide) n3 z pz 5 p5 (three_dvd_succ hz3) (by decide)
      exact (ne_of_gt hzbig) heq
    have ev := (hsup S (Finset.Subset.refl S) (fun p hp => ⟨((hS p).mp hp).1, ha p hp⟩) hb).2 z hzS hz3
    exact (hB n hn hns S hS ha hb h4 h3 h5 h7 h19 hsup h16 h32 h31 h223 h607 h3967 h48 hthin hge h8191 h79 h163 h194 hexc
      ⟨t,u,z,k,ht,hu,hm,hzS,ev,hz3,hzF,hzk⟩).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H2_R1
