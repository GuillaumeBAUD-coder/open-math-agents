import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H4_R1
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Algebra.BigOperators.Ring.Nat

/-! Additional seed constraints on the 3-free 17 branch of Erdős #1052. -/

namespace Erdos1052SeedAmplification

open OMA.R_Erdos1052_erdos_1052_R1 (prod_eq_two_mul)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 (exists_prime_mod3)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (two_dvd_of_isUnitaryPerfect)

private theorem seed_ne_zero (x p j : ℕ) : (x ^ (p ^ j) + 1) ≠ 0 := Nat.succ_ne_zero _

private theorem seed_mod_three {x : ℕ} (hx : x % 3 = 1) (p j : ℕ) : (x ^ (p ^ j) + 1) % 3 = 2 := by
  rw [Nat.add_mod, Nat.pow_mod, hx]
  simp

private theorem seed_odd {x p : ℕ} (hx : Even x) (hp : p.Prime) (j : ℕ) :
    Odd ((x ^ (p ^ j) + 1)) :=
  (hx.pow_of_ne_zero (pow_ne_zero _ hp.ne_zero)).add_one

theorem seed_dvd_next {x p : ℕ} (hp : Odd p) (j : ℕ) : (x ^ (p ^ j) + 1) ∣ (x ^ (p ^ (j + 1)) + 1) := by
  rw [pow_succ p j, pow_mul]
  simpa only [one_pow] using Odd.nat_add_dvd_pow_add_pow (x ^ p ^ j) 1 hp

private theorem prime_dvd_all_seeds {x p : ℕ} (hp : Odd p) (hx : p ∣ x + 1) :
    ∀ j, p ∣ (x ^ (p ^ j) + 1) := by
  intro j
  induction j with
  | zero => simpa using hx
  | succ j ih => exact ih.trans (seed_dvd_next hp j)

private theorem quotient_val
    {x p j d r : ℕ} (hp : Odd p) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrDvd : r ∣ (x ^ (p ^ j) + 1)) (hd : (x ^ (p ^ (j + 1)) + 1) = (x ^ (p ^ j) + 1) * d) (hd0 : d ≠ 0) :
    padicValNat r d = padicValNat r p := by
  let : Fact r.Prime := ⟨hr⟩
  have hrNot : ¬r ∣ x ^ (p ^ j) := fun h =>
    hr.not_dvd_one ((Nat.dvd_add_iff_right h).mpr (show r ∣ x ^ (p ^ j) + 1 from hrDvd))
  have hlte := padicValNat.pow_add_pow (x := x ^ (p ^ j)) (y := 1)
    (hr.odd_of_ne_two hr2) hrDvd hrNot hp
  simp only [one_pow, ← pow_mul, ← pow_succ] at hlte
  change padicValNat r ((x ^ (p ^ (j + 1)) + 1)) =
    padicValNat r ((x ^ (p ^ j) + 1)) + padicValNat r p at hlte
  rw [hd, padicValNat.mul (seed_ne_zero x p j) hd0] at hlte
  exact Nat.add_left_cancel hlte

private theorem primitive_order_dvd
    {x p j q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hnew : q ∣ (x ^ (p ^ (j + 1)) + 1)) (hold : ¬ q ∣ (x ^ (p ^ j) + 1)) :
    p ^ (j + 1) ∣ q - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hpodd := hp.odd_of_ne_two hp2
  have hf := (ZMod.natCast_eq_zero_iff _ _).mpr hnew
  have hb : ¬ (((x ^ (p ^ j) + 1) : ℕ) : ZMod q) = 0 := fun h =>
    hold ((ZMod.natCast_eq_zero_iff _ _).mp h)
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hf hb
  have hF : (-(x : ZMod q)) ^ p ^ (j + 1) = 1 := by
    rw [(hpodd.pow).neg_pow]
    exact neg_eq_iff_eq_neg.mpr (eq_neg_of_add_eq_zero_left hf)
  have hB : ¬ (-(x : ZMod q)) ^ p ^ j = 1 := by
    rw [(hpodd.pow).neg_pow]
    intro he
    exact hb (by rw [neg_eq_iff_eq_neg.mp he, neg_add_cancel])
  have hnz : -(x : ZMod q) ≠ 0 := by
    intro hz
    rw [hz, zero_pow (pow_ne_zero _ hp.ne_zero)] at hF
    exact zero_ne_one hF
  have ho : orderOf (-(x : ZMod q)) = p ^ (j + 1) := orderOf_eq_prime_pow hB hF
  simpa only [ho] using ZMod.orderOf_dvd_card_sub_one hnz

/-- Every exponent stage contributes a new prime congruent to 2 modulo 3.
The new prime also has a controlled multiplicative order. -/
theorem primitive_prime
    {x p : ℕ} (hx : Even x) (hx3 : x % 3 = 1) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p % 3 = 2) (hpx : p ∣ x + 1) (j : ℕ) :
    ∃ q, q.Prime ∧ q % 3 = 2 ∧ q ∣ (x ^ (p ^ (j + 1)) + 1) ∧
      ¬ q ∣ (x ^ (p ^ j) + 1) ∧ p ^ (j + 1) ∣ q - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpodd := hp.odd_of_ne_two hp2
  obtain ⟨d, hd⟩ := seed_dvd_next (x := x) hpodd j
  have hd0 : d ≠ 0 := by
    intro h
    exact seed_ne_zero x p (j + 1) (by simpa [h] using hd)
  have hd3 : d % 3 = 1 := by
    have h := congrArg (fun n : ℕ => n % 3) hd
    rw [seed_mod_three hx3, Nat.mul_mod, seed_mod_three hx3] at h
    omega
  have hvd := quotient_val hpodd hp hp2 (prime_dvd_all_seeds hpodd hpx j) hd hd0
  rw [padicValNat_self] at hvd
  obtain ⟨k, hk⟩ := (dvd_iff_padicValNat_ne_zero hd0).mpr (by omega : padicValNat p d ≠ 0)
  have hk3 : k % 3 = 2 := by
    rw [hk, Nat.mul_mod, hp3] at hd3
    omega
  obtain ⟨q, hq, hqk, hq3⟩ := exists_prime_mod3 k hk3
  have hqd : q ∣ d := by rw [hk]; exact dvd_mul_of_dvd_right hqk p
  have hnew : q ∣ (x ^ (p ^ (j + 1)) + 1) := hd.symm ▸ dvd_mul_of_dvd_right hqd _
  have hq2 : q ≠ 2 := fun h => (Nat.not_even_iff_odd.mpr (seed_odd hx hp (j + 1))) (even_iff_two_dvd.mpr (h ▸ hnew))
  have hqne : q ≠ p := by
    intro he
    subst q
    have hpow : p ^ 2 ∣ d := by
      rw [hk, pow_two]
      exact Nat.mul_dvd_mul_left p hqk
    have := (padicValNat_dvd_iff_le hd0).mp hpow
    omega
  have hold : ¬ q ∣ (x ^ (p ^ j) + 1) := by
    intro hc
    let : Fact q.Prime := ⟨hq⟩
    have hval := quotient_val hpodd hq hq2 hc hd hd0
    have hval0 : padicValNat q d ≠ 0 := (dvd_iff_padicValNat_ne_zero hd0).mp hqd
    have hqp : q ∣ p := (dvd_iff_padicValNat_ne_zero hp.ne_zero).mpr (hval ▸ hval0)
    exact hqne ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp)
  exact ⟨q, hq, hq3, hnew, hold, primitive_order_dvd hp hp2 hq hnew hold⟩

theorem seed_has_distinct_primes
    {x p : ℕ} (hx : Even x) (hx3 : x % 3 = 1) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p % 3 = 2) (hpx : p ∣ x + 1) (j : ℕ) :
    ∃ U : Finset ℕ, U.card = j + 1 ∧ ∀ q ∈ U, q.Prime ∧ q % 3 = 2 ∧ q ∣ (x ^ (p ^ j) + 1) := by
  induction j with
  | zero =>
    refine ⟨{p}, by simp, ?_⟩
    intro q hq
    have h : q = p := Finset.mem_singleton.mp hq
    simpa [h] using And.intro hp (And.intro hp3 hpx)
  | succ j ih =>
    obtain ⟨U, hcard, hU⟩ := ih
    obtain ⟨q, hq, hq3, hqNew, hqOld, _⟩ := primitive_prime hx hx3 hp hp2 hp3 hpx j
    have hqU : q ∉ U := fun h => hqOld (hU q h).2.2
    refine ⟨insert q U, by rw [Finset.card_insert_of_notMem hqU, hcard], ?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with he | hrU
    · subst r
      exact ⟨hq, hq3, hqNew⟩
    · obtain ⟨hrp, hr3, hrd⟩ := hU r hrU
      exact ⟨hrp, hr3, hrd.trans (seed_dvd_next (hp.odd_of_ne_two hp2) j)⟩

private theorem two_power_seed_dvd {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (ha : padicValNat 2 n ≠ 0) : 2 ^ padicValNat 2 n + 1 ∣ n := by
  have h2 := two_dvd_of_isUnitaryPerfect h
  have h2m : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, h.2.ne'⟩
  have hd := (Finset.dvd_prod_of_mem (fun p => 1 + p ^ n.factorization p) h2m).trans
    (Dvd.intro 1 (by rw [prod_eq_two_mul h, mul_one]))
  rw [Nat.factorization_def n Nat.prime_two, add_comm 1] at hd
  have ho : Odd (2 ^ padicValNat 2 n + 1) :=
    ((by decide : Even (2 : ℕ)).pow_of_ne_zero ha).add_one
  have hc : Nat.Coprime (2 ^ padicValNat 2 n + 1) 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr (fun he => Nat.not_even_iff_odd.mpr ho (even_iff_two_dvd.mpr he))).symm
  exact hc.dvd_of_dvd_mul_left hd

private theorem seed16_dvd_two_seed {a j : ℕ} (ha : a % 8 = 4) (h17 : 17 ^ j ∣ a) :
    (16 ^ (17 ^ j) + 1) ∣ 2 ^ a + 1 := by
  have h4 : 4 ∣ a := ⟨a / 4, by omega⟩
  have hcop : Nat.Coprime 4 (17 ^ j) := (by decide : Nat.Coprime 4 17).pow_right _
  obtain ⟨m, hm⟩ := hcop.mul_dvd_of_dvd_of_dvd h4 h17
  have hOdd : Odd m := by
    rcases Nat.even_or_odd m with hE | hO
    · obtain ⟨l, hl⟩ := even_iff_two_dvd.mp hE
      have h8 : 8 ∣ a := ⟨17 ^ j * l, by rw [hm, hl]; ring⟩
      have := Nat.mod_eq_zero_of_dvd h8
      omega
    · exact hO
  have hEq : ((16 : ℕ) ^ (17 ^ j)) ^ m = 2 ^ a := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul, ← mul_assoc, ← hm]
  have hs := Odd.nat_add_dvd_pow_add_pow ((16 : ℕ) ^ (17 ^ j)) 1 hOdd
  rw [hEq, one_pow] at hs
  exact hs

private theorem square_of_seed16
    {n j q : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (ha : padicValNat 2 n % 8 = 4) (ha17 : 17 ^ j ∣ padicValNat 2 n)
    (hsimple : ∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1)
    (hqp : q.Prime) (hq3 : q % 3 = 2) (hqseed : q ∣ (16 ^ (17 ^ j) + 1)) :
    q ^ 2 ∣ n := by
  have hq2 : q ≠ 2 := fun he =>
    (Nat.not_even_iff_odd.mpr (seed_odd (x := 16) (p := 17) (by decide) (by decide) j))
      (even_iff_two_dvd.mpr (he ▸ hqseed))
  have hqd := (hqseed.trans (seed16_dvd_two_seed ha ha17)).trans (two_power_seed_dvd h (by omega))
  have hqf : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqd, h.2.ne'⟩
  have hq1 : n.factorization q ≠ 1 := fun he => by have := hsimple q hqf hq2 he; omega
  have hpos := hqp.factorization_pos_of_dvd h.2.ne' hqd
  exact (hqp.pow_dvd_iff_le_factorization h.2.ne').mpr (by omega)

/-- On the 17 branch, every factor of 17 in the two-adic exponent adds a
distinct repeated prime congruent to 2 modulo 3. -/
theorem repeated_count_of_seventeen_pow
    {n j : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (ha : padicValNat 2 n % 8 = 4) (ha17 : 17 ^ j ∣ padicValNat 2 n)
    (hsimple : ∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1) :
    j + 1 ≤ (S.filter (fun q => q % 3 = 2)).card := by
  obtain ⟨U, hcard, hU⟩ := seed_has_distinct_primes (x := 16) (p := 17)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j
  rw [← hcard]
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqp, hq3, hqseed⟩ := hU q hq
  have hq2 : q ≠ 2 := fun he =>
    (Nat.not_even_iff_odd.mpr (seed_odd (x := 16) (p := 17) (by decide) (by decide) j))
      (even_iff_two_dvd.mpr (he ▸ hqseed))
  have hqpow := square_of_seed16 h ha ha17 hsimple hqp hq3 hqseed
  exact Finset.mem_filter.mpr ⟨(hS q).mpr ⟨hqp, hq2, hqpow⟩, hq3⟩

/-- A prime from each noninitial seed stage enters the repeated support with
its prime-power order constraint. -/
theorem repeated_primitive_stage
    {n j : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (ha : padicValNat 2 n % 8 = 4) (ha17 : 17 ^ (j + 1) ∣ padicValNat 2 n)
    (hsimple : ∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1) :
    ∃ q ∈ S, q % 3 = 2 ∧ 17 ^ (j + 1) ∣ q - 1 ∧ ¬ q ∣ (16 ^ (17 ^ j) + 1) := by
  obtain ⟨q, hqp, hq3, hqseed, hold, hord⟩ := primitive_prime (x := 16) (p := 17)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j
  have hq2 : q ≠ 2 := fun he =>
    (Nat.not_even_iff_odd.mpr (seed_odd (x := 16) (p := 17) (by decide) (by decide) (j + 1)))
      (even_iff_two_dvd.mpr (he ▸ hqseed))
  exact ⟨q, (hS q).mpr ⟨hqp, hq2, square_of_seed16 h ha ha17 hsimple hqp hq3 hqseed⟩,
    hq3, hord, hold⟩

theorem seed17_valuation {a : ℕ} (ha : a % 8 = 4) :
    padicValNat 17 (2 ^ a + 1) = 1 + padicValNat 17 a := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  have h4 : 4 ∣ a := ⟨a / 4, by omega⟩
  obtain ⟨m, hm⟩ := h4
  have hOdd : Odd m := Nat.odd_iff.mpr (by omega)
  have hm0 : m ≠ 0 := (Odd.pos hOdd).ne'
  have hv := padicValNat.pow_add_pow (p := 17) (x := 16) (y := 1)
    (by decide) (by decide) (by decide) hOdd
  rw [hm, pow_mul, show (2 : ℕ)^4 = 16 by norm_num, padicValNat.mul (by decide) hm0,
    padicValNat.eq_zero_of_not_dvd (by decide : ¬ (17 : ℕ) ∣ 4), zero_add]
  simpa only [one_pow, show (16 : ℕ)+1 = 17 by norm_num, padicValNat_self] using hv

/-- The exponent of 17 in n is the sum of the seed contribution and all odd
component contributions. -/
theorem component17_balance {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (ha : padicValNat 2 n % 8 = 4) :
    n.factorization 17 = 1 + padicValNat 17 (padicValNat 2 n) +
      ∑ q ∈ n.primeFactors.erase 2, (1 + q ^ n.factorization q).factorization 17 := by
  have h2m : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, two_dvd_of_isUnitaryPerfect h, h.2.ne'⟩
  have h217 : (2 : ℕ).factorization 17 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  calc
    n.factorization 17 = (2 * n).factorization 17 := by
      rw [Nat.factorization_mul (by decide) h.2.ne', Finsupp.coe_add, Pi.add_apply, h217, zero_add]
    _ = _ := by
      rw [← prod_eq_two_mul h, Nat.factorization_prod (fun _ _ => by positivity),
        Finsupp.finsetSum_apply, ← Finset.add_sum_erase _ _ h2m,
        Nat.factorization_def n Nat.prime_two, add_comm 1,
        Nat.factorization_def _ (by decide : Nat.Prime 17), seed17_valuation ha]

/-- If the seed contributes just one copy of 17 and the total exponent of 17
is even, an odd number of odd components supply an odd number of copies. -/
theorem exists_odd_external_17_supplier {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (ha : padicValNat 2 n % 8 = 4) (ha17 : ¬ 17 ∣ padicValNat 2 n)
    (he : n.factorization 17 % 2 = 0) :
    ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ 17 ∧ Odd ((1 + q ^ n.factorization q).factorization 17) := by
  let f (q : ℕ) := (1 + q ^ n.factorization q).factorization 17
  have hbalance := component17_balance h ha
  rw [padicValNat.eq_zero_of_not_dvd ha17, add_zero] at hbalance
  have hodd : Odd (∑ q ∈ n.primeFactors.erase 2, f q) := Nat.odd_iff.mpr (by
    change n.factorization 17 = 1 + ∑ q ∈ n.primeFactors.erase 2, f q at hbalance
    omega)
  have hcard := (Finset.odd_sum_iff_odd_card_odd f).mp hodd
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (Odd.pos hcard)
  obtain ⟨hr, ho⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq2, hqf⟩ := Finset.mem_erase.mp hr
  refine ⟨q, hqf, hq2, ?_, ho⟩
  intro heq
  subst q
  have hpos := (by decide : Nat.Prime 17).factorization_pos_of_dvd h.2.ne'
    (Nat.dvd_of_mem_primeFactors hqf)
  have hpow : 17 ∣ (17 : ℕ) ^ n.factorization 17 := dvd_pow_self _ hpos.ne'
  have hno : ¬ 17 ∣ 1 + (17 : ℕ)^n.factorization 17 := fun hd =>
    (by decide : ¬ (17 : ℕ) ∣ 1) ((Nat.dvd_add_iff_left hpow).mpr hd)
  have hzero := Nat.factorization_eq_zero_of_not_dvd hno
  exact (Odd.pos ho).ne' hzero

theorem forced_354689_square {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (ha : padicValNat 2 n % 8 = 4) (ha17 : 17 ∣ padicValNat 2 n)
    (hsimple : ∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1) :
    354689 ^ 2 ∣ n := by
  exact square_of_seed16 (j := 1) h ha (by simpa using ha17) hsimple
    (by norm_num) (by decide) (by norm_num)

theorem simple_supplier_residue
    {n q : ℕ} (hq : q ∈ n.primeFactors) (hq2 : q ≠ 2) (he : n.factorization q = 1)
    (h3 : q % 3 = 1) (hOdd : Odd ((1 + q ^ n.factorization q).factorization 17)) :
    q % 102 = 67 := by
  have hq1 := Nat.odd_iff.mp ((Nat.prime_of_mem_primeFactors hq).odd_of_ne_two hq2)
  have hdiv : 17 ∣ 1 + q ^ n.factorization q :=
    ((by decide : Nat.Prime 17).dvd_iff_one_le_factorization (by positivity)).mpr (Odd.pos hOdd)
  rw [he, pow_one] at hdiv
  have hm := Nat.mod_eq_zero_of_dvd hdiv
  omega

theorem supplier_exponent_not_divisible_by_sixteen
    {n q : ℕ} (hq : q ∈ n.primeFactors) (hq17 : q ≠ 17)
    (hOdd : Odd ((1 + q ^ n.factorization q).factorization 17)) :
    n.factorization q % 16 ≠ 0 := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  have hqP := Nat.prime_of_mem_primeFactors hq
  have hz : (q : ZMod 17) ≠ 0 := fun hzero => hq17
    (((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 17) hqP).mp
      ((ZMod.natCast_eq_zero_iff q 17).mp hzero)).symm)
  have hpow : (q : ZMod 17) ^ 16 = 1 := ZMod.pow_card_sub_one_eq_one hz
  have hdiv : 17 ∣ 1 + q ^ n.factorization q :=
    ((by decide : Nat.Prime 17).dvd_iff_one_le_factorization (by positivity)).mpr (Odd.pos hOdd)
  have hzero := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  push_cast at hzero
  intro he
  obtain ⟨k, hk⟩ := (Nat.dvd_iff_mod_eq_zero).mpr he
  rw [hk, pow_mul, hpow, one_pow] at hzero
  exact (by decide : (1 : ZMod 17) + 1 ≠ 0) hzero

end Erdos1052SeedAmplification

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H4_R1_H2_R1

open Erdos1052SeedAmplification

/-- The seed supplies one copy of 17 and some simple component supplies an odd number. -/
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    ¬ 3 ∣ n → padicValNat 2 n % 2 = 0 → 125 ≤ padicValNat 2 n →
    (∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1) →
    (∀ q ∈ n.primeFactors, q % 3 = 2 → n.factorization q % 2 = 0) →
    (∃ z ∈ S, z % 3 = 2 ∧ z ∣ 2 ^ padicValNat 2 n + 1) →
    n.primeFactors.card % 2 = 1 →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ z ∧ z ∣ 1 + q ^ n.factorization q) →
    padicValNat 2 n % 8 = 4 → 17 ∈ S →
    (¬ 17 ∣ padicValNat 2 n) →
    (∃ q ∈ n.primeFactors, q % 102 = 67 ∧ n.factorization q = 1 ∧
      Odd ((1 + q ^ n.factorization q).factorization 17)) →
    padicValNat 2 n ≤ A

/-- The seed supplies one copy and all suppliers of an odd number of copies are repeated. -/
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    ¬ 3 ∣ n → padicValNat 2 n % 2 = 0 → 125 ≤ padicValNat 2 n →
    (∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1) →
    (∀ q ∈ n.primeFactors, q % 3 = 2 → n.factorization q % 2 = 0) →
    (∃ z ∈ S, z % 3 = 2 ∧ z ∣ 2 ^ padicValNat 2 n + 1) →
    n.primeFactors.card % 2 = 1 →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ z ∧ z ∣ 1 + q ^ n.factorization q) →
    padicValNat 2 n % 8 = 4 → 17 ∈ S →
    (¬ 17 ∣ padicValNat 2 n) →
    (¬ ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ 17 ∧ n.factorization q = 1 ∧
      Odd ((1 + q ^ n.factorization q).factorization 17)) →
    (∃ q ∈ S, q ≠ 17 ∧ n.factorization q % 16 ≠ 0 ∧
      Odd ((1 + q ^ n.factorization q).factorization 17)) →
    padicValNat 2 n ≤ A

/-- A second copy from the seed forces another repeated prime and further
powers of 17 in the two-adic exponent force new repeated primes. -/
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    ¬ 3 ∣ n → padicValNat 2 n % 2 = 0 → 125 ≤ padicValNat 2 n →
    (∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1) →
    (∀ q ∈ n.primeFactors, q % 3 = 2 → n.factorization q % 2 = 0) →
    (∃ z ∈ S, z % 3 = 2 ∧ z ∣ 2 ^ padicValNat 2 n + 1) →
    n.primeFactors.card % 2 = 1 →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ z ∧ z ∣ 1 + q ^ n.factorization q) →
    padicValNat 2 n % 8 = 4 → 17 ∈ S →
    17 ∣ padicValNat 2 n → 354689 ^ 2 ∣ n →
    padicValNat 17 (padicValNat 2 n) + 1 ≤ (S.filter (fun q => q % 3 = 2)).card →
    (∀ j : ℕ, j + 1 ≤ padicValNat 17 (padicValNat 2 n) →
      ∃ q ∈ S, q % 3 = 2 ∧ 17 ^ (j + 1) ∣ q - 1 ∧ ¬ q ∣ 16 ^ (17 ^ j) + 1) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H4_R1.H2 := by
  classical
  rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩
  refine ⟨max A (max B C), ?_⟩
  intro n h S hS hlarge hnon h3free hae hamin hsimple hparity hseed hcard hsource ha h17S
  specialize hA n h S hS hlarge hnon h3free hae hamin hsimple hparity hseed hcard hsource ha h17S
  specialize hB n h S hS hlarge hnon h3free hae hamin hsimple hparity hseed hcard hsource ha h17S
  specialize hC n h S hS hlarge hnon h3free hae hamin hsimple hparity hseed hcard hsource ha h17S
  by_cases h17 : 17 ∣ padicValNat 2 n
  · have hSq := forced_354689_square h ha h17 hsimple
    have hpow : 17 ^ padicValNat 17 (padicValNat 2 n) ∣ padicValNat 2 n :=
      pow_padicValNat_dvd
    have hcount := repeated_count_of_seventeen_pow h hS ha hpow hsimple
    have hstage (j : ℕ) (hj : j + 1 ≤ padicValNat 17 (padicValNat 2 n)) :
        ∃ q ∈ S, q % 3 = 2 ∧ 17 ^ (j + 1) ∣ q - 1 ∧ ¬ q ∣ 16 ^ (17 ^ j) + 1 :=
      repeated_primitive_stage h hS ha ((pow_dvd_pow 17 hj).trans hpow) hsimple
    have hb := hC h17 hSq hcount hstage
    omega
  · by_cases hs : ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ 17 ∧ n.factorization q = 1 ∧
      Odd ((1 + q ^ n.factorization q).factorization 17)
    · obtain ⟨q, hq⟩ := hs
      obtain ⟨hqf, hq2, hq17, hqe, hOdd⟩ := hq
      have hres := simple_supplier_residue hqf hq2 hqe (hsimple q hqf hq2 hqe) hOdd
      have hb := hA h17 ⟨q, hqf, hres, hqe, hOdd⟩
      omega
    · obtain ⟨hp17, _, hd17⟩ := (hS 17).mp h17S
      have hn17 : 17 ∣ n := (dvd_pow_self 17 (by decide : (2 : ℕ) ≠ 0)).trans hd17
      have hf17 : 17 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp17, hn17, h.2.ne'⟩
      have heven := hparity 17 hf17 (by decide)
      obtain ⟨q, hqf, hq2, hq17, hOdd⟩ := exists_odd_external_17_supplier h ha h17 heven
      have hq1 : n.factorization q ≠ 1 := fun hq1 => hs ⟨q, hqf, hq2, hq17, hq1, hOdd⟩
      have hqp := Nat.prime_of_mem_primeFactors hqf
      have hpos := hqp.factorization_pos_of_dvd h.2.ne' (Nat.dvd_of_mem_primeFactors hqf)
      have hqSq := (hqp.pow_dvd_iff_le_factorization h.2.ne' (k := 2)).mpr (by omega)
      have hqS := (hS q).mpr ⟨hqp, hq2, hqSq⟩
      have hexp := supplier_exponent_not_divisible_by_sixteen hqf hq17 hOdd
      have hb := hB h17 hs ⟨q, hqS, hq17, hexp, hOdd⟩
      omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H4_R1_H2_R1
