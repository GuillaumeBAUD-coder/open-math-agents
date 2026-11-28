import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H2.R1

/-!
Write a for the odd 2-adic valuation of n. For each prime power p^(k+1)
dividing a with p = 2 mod 3, the quotient
(2^(p^(k+1))+1)/(2^(p^k)+1) supplies a repeated odd prime r of n
with r = 2 mod 3 and ord_r(-2) exactly p^(k+1).
Thus distinct powers, even of the same prime, require distinct witnesses.
The remaining bounds concern the complementary prime powers and the
orders witnessed in the repeated-prime set.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 (exists_prime_mod3)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1
  (exists_quot_mod three_dvd_two_pow_add_one two_dvd_of_isUnitaryPerfect)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1
  (fact2_eq dvd_two_mul_of_src dvd_of_dvd_two_mul cop2 fact_pos)

/-- Bound the primary components of a at primes congruent to one modulo three. -/
def H1 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ q, q ∈ S ↔ q.Prime ∧ q ≠ 2 ∧ q ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    n.factorization 3 = 1 → padicValNat 2 n % 2 = 1 →
    ∀ p k : ℕ, p.Prime → p % 3 = 1 → p ^ k ∣ padicValNat 2 n → p ^ k ≤ B

/-- Bound the prime-power orders of -2 supported at repeated roots of 2^a+1
when both the root and the underlying order prime are two modulo three. -/
def H2 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ q, q ∈ S ↔ q.Prime ∧ q ≠ 2 ∧ q ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    n.factorization 3 = 1 → padicValNat 2 n % 2 = 1 →
    ∀ r ∈ S, r % 3 = 2 → r ∣ 2 ^ padicValNat 2 n + 1 →
    ∀ p k : ℕ, p.Prime → p % 3 = 2 → orderOf (-2 : ZMod r) = p ^ k → p ^ k ≤ B

theorem primitiveWitness {n p k : ℕ} {S : Finset ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ q, q ∈ S ↔ q.Prime ∧ q ≠ 2 ∧ q ^ 2 ∣ n)
    (simple : ∀ q ∈ n.primeFactors, q ≠ 2 → n.factorization q = 1 → q % 3 ≠ 2)
    (ha : Odd (padicValNat 2 n)) (hp : p.Prime) (hp3 : p % 3 = 2)
    (hd : p ^ (k+1) ∣ padicValNat 2 n) :
    ∃ r ∈ S, r % 3 = 2 ∧ r ∣ 2 ^ padicValNat 2 n + 1 ∧
      orderOf (-2 : ZMod r) = p ^ (k+1) := by
  have hpodd : Odd p := by
    obtain ⟨t, ht⟩ := hd
    rw [ht, pow_succ] at ha
    exact (Nat.odd_mul.mp (Nat.odd_mul.mp ha).1).2
  let z := 2 ^ (p ^ k)
  obtain ⟨Q, heq, hmod⟩ := exists_quot_mod (z := z) hpodd
  have hcon : Q ≡ p [MOD z+1] := hmod
  have hthree : 3 ∣ z+1 := three_dvd_two_pow_add_one (Nat.odd_iff.mp (hpodd.pow))
  obtain ⟨r, hr, hrQ, hr3⟩ := exists_prime_mod3 Q (Eq.trans (hcon.of_dvd hthree) hp3)
  have hlarge : r ∣ 2 ^ (p ^ (k+1)) + 1 := by
    rw [pow_succ, pow_mul, add_comm]
    change r ∣ 1 + z ^ p
    rw [heq]
    exact Dvd.dvd.mul_left hrQ _
  have hsmall : ¬ r ∣ z+1 := by
    intro hz
    have hrp : r ∣ p := ((hcon.of_dvd hz).dvd_iff dvd_rfl).mp hrQ
    have her := (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
    subst r
    let : Fact p.Prime := ⟨hp⟩
    have hzero := (ZMod.natCast_eq_zero_iff _ _).mpr hz
    change ((2 ^ (p ^ k) + 1 : ℕ) : ZMod p) = 0 at hzero
    push_cast at hzero
    rw [ZMod.pow_card_pow] at hzero
    have hdiv : p ∣ 3 := (ZMod.natCast_eq_zero_iff (3 : ℕ) p).mp (by norm_num at hzero ⊢; exact hzero)
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdiv
    omega
  have hroot : r ∣ 2 ^ padicValNat 2 n + 1 := by
    obtain ⟨t, ht⟩ := hd
    rw [ht] at ha ⊢
    have h := Odd.nat_add_dvd_pow_add_pow (2 ^ p ^ (k+1)) 1 (Nat.odd_mul.mp ha).2
    rw [one_pow, ← pow_mul] at h
    exact hlarge.trans h
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h := dvd_pow_self 2 (pow_ne_zero (k+1) hp.ne_zero)
    have := (Nat.dvd_add_right h).mp hlarge
    omega
  have hn0 := hn.2.ne'
  have htwo : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, two_dvd_of_isUnitaryPerfect hn, hn0⟩
  have hdiv := dvd_two_mul_of_src hn htwo (c := r) (by rwa [fact2_eq, add_comm])
  have hrn := dvd_of_dvd_two_mul (cop2 hr hr2) hdiv
  have hmem := Nat.mem_primeFactors.mpr ⟨hr, hrn, hn0⟩
  have hpos := fact_pos hmem
  have hne : n.factorization r ≠ 1 := fun h => simple r hmem hr2 h hr3
  refine ⟨r, (hS r).mpr ⟨hr, hr2, (hr.pow_dvd_iff_le_factorization hn0).mpr (by omega)⟩,
    hr3, hroot, ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  apply orderOf_eq_prime_pow
  · rw [(hpodd.pow : Odd (p ^ k)).neg_pow]
    intro h
    apply hsmall
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    change ((2 ^ (p ^ k) + 1 : ℕ) : ZMod r) = 0
    push_cast
    linear_combination -h
  · rw [(hpodd.pow : Odd (p ^ (k+1))).neg_pow]
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr hlarge
    push_cast at h
    linear_combination -h

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1.H2 := by
  rintro ⟨B, one⟩ ⟨C, two⟩
  refine ⟨(max (max B C) 1).factorial, ?_⟩
  intro n hn S hS hcard hbad h3 ha ha3 simple _ _
  have ha0 : padicValNat 2 n ≠ 0 := by omega
  apply Nat.le_of_dvd (Nat.factorial_pos _)
  apply (Nat.factorization_prime_le_iff_dvd ha0 (Nat.factorial_ne_zero _)).mp
  intro p hp
  cases he : (padicValNat 2 n).factorization p with
  | zero => simp
  | succ k =>
    have hd := (hp.pow_dvd_iff_le_factorization ha0).mpr he.ge
    apply (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp
    apply Nat.dvd_factorial (pow_pos hp.pos _)
    apply le_trans _ (le_max_left _ 1)
    have classes : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases classes with h | h | h
    · exfalso
      have hdiv := (dvd_pow_self p (Nat.succ_ne_zero k)).trans hd
      exact ha3 (Nat.mod_eq_zero_of_dvd ((Nat.dvd_of_mod_eq_zero h).trans hdiv))
    · exact (one n hn S hS hcard hbad h3 ha p _ hp h hd).trans (le_max_left ..)
    · obtain ⟨r, hr, hr3, hroot, hord⟩ := primitiveWitness hn hS simple (Nat.odd_iff.mpr ha) hp h hd
      exact (two n hn S hS hcard hbad h3 ha r hr hr3 hroot p _ hp h hord).trans (le_max_right ..)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H2_R1
