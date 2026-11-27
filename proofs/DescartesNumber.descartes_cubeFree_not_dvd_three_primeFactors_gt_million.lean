import FormalConjectures.Wikipedia.DescartesNumber

/-!
# Cube-free Descartes numbers coprime to three

Chapter 8 of C. Wesley Nevans's dissertation, On the Theory of Integer
Sequences, gives the prime restrictions used here. For the numerical bound,
we group admissible primes by residue classes and certify the finite sums via
kernel reduction of natural-number arithmetic.
-/

namespace OMA.Descartes

open scoped ArithmeticFunction.sigma
open Finset

private theorem divisor_sum_square {s : ℕ} (hs : Squarefree s) :
    σ 1 (s ^ 2) = ∏ p ∈ s.primeFactors, (p ^ 2 + p + 1) := by
  have hs0 : s ≠ 0 := hs.ne_zero
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
    (pow_ne_zero _ hs0), Nat.primeFactors_pow _ (by decide : 2 ≠ 0)]
  refine prod_congr rfl fun p hp => ?_
  have hpos : s.factorization p ≠ 0 := by
    exact Finsupp.mem_support_iff.mp (s.support_factorization.symm ▸ hp)
  have hexp := (Nat.squarefree_iff_factorization_le_one hs0).mp hs p
  have h : s.factorization p = 1 := by omega
  simp [Nat.factorization_pow, h, Finset.sum_range_succ]
  omega

private theorem cyclotomic_prime_mod_three {p q : ℕ} (hq : q.Prime)
    (h : q ∣ p ^ 2 + p + 1) : q = 3 ∨ q % 3 = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hz : (p : ZMod q) ^ 2 + p + 1 = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ q).mpr h
  by_cases h1 : (p : ZMod q) = 1
  · left
    have hz3 : (3 : ZMod q) = 0 := by norm_num [h1] at hz ⊢; exact hz
    have hd := (ZMod.natCast_eq_zero_iff 3 q).mp (by exact_mod_cast hz3)
    exact (Nat.prime_three.eq_one_or_self_of_dvd q hd).resolve_left hq.ne_one
  · right
    have hpow : (p : ZMod q) ^ 3 = 1 := by
      linear_combination ((p : ZMod q) - 1) * hz
    have hp0 : (p : ZMod q) ≠ 0 := by
      intro hz0
      simp [hz0] at hz
    have ho := orderOf_dvd_of_pow_eq_one hpow
    have ho3 := (Nat.prime_three.eq_one_or_self_of_dvd _ ho).resolve_left
      (orderOf_eq_one_iff.not.mpr h1)
    have hd := ZMod.orderOf_dvd_card_sub_one hp0
    rw [ho3] at hd
    rw [Nat.dvd_iff_mod_eq_zero] at hd
    have hq2 := hq.two_le
    omega

private theorem square_of_odd_divisor_sum {m w : ℕ} (hodd : Odd m)
    (hσodd : Odd (σ 1 m)) (hcf : Powerfree 3 (m * w)) :
    ∃ s : ℕ, Squarefree s ∧ m = s ^ 2 := by
  have hm0 : m ≠ 0 := fun h => by simp [h] at hodd
  have hfac : ∀ p ∈ m.primeFactors, m.factorization p = 2 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    have hpodd : Odd p := by
      obtain ⟨a, ha⟩ := hpdvd
      rw [ha] at hodd
      exact (Nat.odd_mul.mp hodd).1
    have hpos : m.factorization p ≠ 0 := by
      exact Finsupp.mem_support_iff.mp (m.support_factorization.symm ▸ hp)
    have hle : ¬3 ≤ m.factorization p := by
      intro h3
      have hmp := (hprime.pow_dvd_iff_le_factorization hm0).mpr h3
      exact hprime.ne_one (Nat.isUnit_iff.mp (hcf (hmp.trans (Nat.dvd_mul_right _ _))))
    suffices m.factorization p ≠ 1 by omega
    intro h1
    have hdiv : p + 1 ∣ σ 1 m := by
      rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0]
      have hsum : (∑ i ∈ range (m.factorization p + 1), p ^ (i * 1)) = p + 1 := by
        simp [h1, sum_range_succ, Nat.add_comm]
      rw [← hsum]
      exact dvd_prod_of_mem (fun q => ∑ i ∈ range (m.factorization q + 1), q ^ (i * 1)) hp
    have htwo : 2 ∣ p + 1 := by
      rw [Nat.odd_iff] at hpodd
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rw [Nat.odd_iff] at hσodd
    exact (by rw [Nat.dvd_iff_mod_eq_zero]; omega : ¬ 2 ∣ σ 1 m) (htwo.trans hdiv)
  let s := ∏ p ∈ m.primeFactors, p
  have hm : m = s ^ 2 := by
    calc
      m = ∏ p ∈ m.primeFactors, p ^ m.factorization p :=
        Nat.prod_primeFactors_pow_factorization hm0
      _ = ∏ p ∈ m.primeFactors, p ^ 2 := prod_congr rfl fun p hp => by rw [hfac p hp]
      _ = s ^ 2 := by rw [Finset.prod_pow]
  refine ⟨s, Nat.squarefree_iff_prime_squarefree.mpr fun p hp h => ?_, hm⟩
  have hp4 : p ^ 4 ∣ m := by
    rw [hm, show 4 = 2 * 2 by decide, pow_mul]
    exact pow_dvd_pow_of_dvd (by simpa [pow_two] using h) 2
  have hp3 : p ^ 3 ∣ p ^ 4 := pow_dvd_pow p (by decide)
  exact hp.ne_one (Nat.isUnit_iff.mp (hcf (hp3.trans (hp4.trans (Nat.dvd_mul_right _ _)))))

private theorem mod_eight_of_prime_divisors {n : ℕ} (hn : n ≠ 0)
    (h : ∀ q, q.Prime → q ∣ n → q % 8 = 1 ∨ q % 8 = 7) :
    n % 8 = 1 ∨ n % 8 = 7 := by
  have hlist : ∀ q ∈ n.primeFactorsList, q % 8 = 1 ∨ q % 8 = 7 := by
    intro q hq
    exact h q (Nat.prime_of_mem_primeFactorsList hq) (Nat.dvd_of_mem_primeFactorsList hq)
  rw [← Nat.prod_primeFactorsList hn]
  generalize n.primeFactorsList = l at hlist ⊢
  induction l with
  | nil => simp
  | cons q l ih =>
    have hq := hlist q (by simp)
    have hl := ih (fun p hp => hlist p (by simp [hp]))
    rw [List.prod_cons, Nat.mul_mod]
    rcases hq with hq | hq <;> rcases hl with hl | hl <;> simp [hq, hl]

private theorem quadratic_prime_mod_eight {s q : ℕ} (hq : q.Prime)
    (hw : q ∣ 2 * s ^ 2 - 1) (hs : 0 < s) : q % 8 = 1 ∨ q % 8 = 7 := by
  let : Fact q.Prime := ⟨hq⟩
  have hnat : 2 * s ^ 2 - 1 + 1 = 2 * s ^ 2 := by
    have hp : 0 < s ^ 2 := by positivity
    omega
  have hcast : ((2 * s ^ 2 - 1 : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hw
  have htwo : (2 : ZMod q) * (s : ZMod q) ^ 2 = 1 := by
    have h := congrArg (fun x : ℕ => (x : ZMod q)) hnat
    simpa [hcast] using h.symm
  have hq2 : q ≠ 2 := by
    intro hh
    subst q
    rw [Nat.dvd_iff_mod_eq_zero] at hw
    have hs2 : 0 < s ^ 2 := by positivity
    omega
  refine (ZMod.exists_sq_eq_two_iff hq2).mp ?_
  refine ⟨(2 : ZMod q) * s, ?_⟩
  calc
    (2 : ZMod q) = 2 * 1 := by ring
    _ = 2 * (2 * (s : ZMod q) ^ 2) := by rw [htwo]
    _ = (2 * (s : ZMod q)) * (2 * (s : ZMod q)) := by ring

private theorem factor_structure {m w : ℕ} (hf : DescartesNumber.IsDescartesFactorization m w)
    (hcf : Powerfree 3 (m * w)) (h3 : ¬3 ∣ m * w) :
    ∃ s : ℕ, 1 < s ∧ Squarefree s ∧ m = s ^ 2 ∧ σ 1 (s ^ 2) = 2 * s ^ 2 - 1 ∧
      (∀ p ∈ s.primeFactors,
        (p % 24 = 5 ∨ p % 24 = 23) ∧
        ∀ q : ℕ, q.Prime → q ∣ p ^ 2 + p + 1 → q % 8 = 1 ∨ q % 8 = 7) := by
  rcases hf with ⟨hwcomp, hodd, _, heq⟩
  have hw1 := hwcomp.1
  have hm1 : 1 < m := by
    have hm0 : m ≠ 0 := fun h => by simp [h] at hodd
    have hmne : m ≠ 1 := by
      intro h
      simp [h] at heq
      omega
    omega
  have hm_odd := (Nat.odd_mul.mp hodd).1
  have hw_odd := (Nat.odd_mul.mp hodd).2
  obtain ⟨u, hu⟩ := hw_odd
  have hu' : w + 1 = 2 * (u + 1) := by omega
  have hhalf : σ 1 m * (u + 1) = m * w := by
    have heq' : 2 * (σ 1 m * (u + 1)) = 2 * (m * w) := by
      calc
        2 * (σ 1 m * (u + 1)) = σ 1 m * (w + 1) := by rw [hu']; ring
        _ = 2 * (m * w) := by rw [heq]; ring
    omega
  have hσodd : Odd (σ 1 m) := (Nat.odd_mul.mp (hhalf ▸ hodd)).1
  obtain ⟨s, hs, hm⟩ := square_of_odd_divisor_sum hm_odd hσodd hcf
  have hs1 : 1 < s := by
    by_contra! h
    interval_cases s <;> simp_all
  have hwm : w.Coprime (w + 1) :=
    (Nat.coprime_self_add_left.mpr (Nat.coprime_one_left w)).symm
  have hwσ : w ∣ σ 1 m := hwm.dvd_of_dvd_mul_right (by rw [heq]; exact Nat.dvd_mul_left _ _)
  obtain ⟨d, hd⟩ := hwσ
  have hcancel : d * (w + 1) = 2 * m := by
    apply Nat.eq_of_mul_eq_mul_right (m := w) (by omega)
    calc
      d * (w + 1) * w = σ 1 m * (w + 1) := by rw [hd]; ring
      _ = 2 * m * w := heq
  have hd_odd : Odd d := (Nat.odd_mul.mp (hd ▸ hσodd)).2
  have hd_coprime : d.Coprime 2 := by
    apply Nat.Coprime.symm
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    rw [Nat.dvd_iff_mod_eq_zero, Nat.odd_iff.mp hd_odd]
    decide
  have hdm : d ∣ m := hd_coprime.dvd_of_dvd_mul_left (by rw [← hcancel]; exact Nat.dvd_mul_right _ _)
  have hσ3 : ¬3 ∣ σ 1 m := by
    rw [hd, Nat.prime_three.dvd_mul]
    exact fun h => h.elim
      (fun hw3 => h3 (hw3.trans (Nat.dvd_mul_left _ _)))
      (fun hd3 => h3 (hd3.trans (hdm.trans (Nat.dvd_mul_right _ _))))
  have hprod : σ 1 m = ∏ p ∈ s.primeFactors, (p ^ 2 + p + 1) := by
    rw [hm, divisor_sum_square hs]
  have hφdvd : ∀ p ∈ s.primeFactors, p ^ 2 + p + 1 ∣ σ 1 m := by
    intro p hp
    rw [hprod]
    exact dvd_prod_of_mem (fun z => z ^ 2 + z + 1) hp
  have hsp₁ : ∀ p ∈ s.primeFactors, p % 3 ≠ 1 := by
    intro p hp hmod
    have hbase : p ≡ 1 [MOD 3] := by simpa [Nat.ModEq] using hmod
    have hzero : p ^ 2 + p + 1 ≡ 0 [MOD 3] :=
      (((hbase.pow 2).add hbase).add (Nat.ModEq.refl 1)).trans (by decide)
    exact hσ3 ((Nat.modEq_zero_iff_dvd.mp hzero).trans (hφdvd p hp))
  have hd1 : d = 1 := by
    by_contra h
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd h
    have hqσ : q ∣ σ 1 m := by rw [hd]; exact hqd.trans (Nat.dvd_mul_left _ _)
    have hqs : q ∣ s := hq.dvd_of_dvd_pow (by simpa [hm] using hqd.trans hdm)
    have hqm : q ∈ s.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqs, hs.ne_zero⟩
    rw [hprod] at hqσ
    obtain ⟨p, hp, hqp⟩ :=
      (hq.prime.dvd_finsetProd_iff (fun p : ℕ => p ^ 2 + p + 1)).mp hqσ
    rcases cyclotomic_prime_mod_three hq hqp with hq3 | hq3
    · subst q
      exact h3 (hqd.trans (hdm.trans (Nat.dvd_mul_right _ _)))
    · exact hsp₁ q hqm hq3
  have hσeq : σ 1 (s ^ 2) = 2 * s ^ 2 - 1 := by
    have hw : w + 1 = 2 * m := by simpa [hd1] using hcancel
    rw [← hm, hd, hd1]
    omega
  refine ⟨s, hs1, hs, hm, hσeq, ?_⟩
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hq8 : ∀ q : ℕ, q.Prime → q ∣ p ^ 2 + p + 1 → q % 8 = 1 ∨ q % 8 = 7 := by
    intro q hq hqp
    have hqσ := hqp.trans (hφdvd p hp)
    rw [hm, hσeq] at hqσ
    exact quadratic_prime_mod_eight hq hqσ (by omega)
  refine ⟨?_, hq8⟩
  have hφ8 := mod_eight_of_prime_divisors (n := p ^ 2 + p + 1) (by positivity) hq8
  have hpodd : Odd p := by
    obtain ⟨k, hk⟩ := hpd
    have h := hm_odd
    rw [hm, hk, pow_two] at h
    exact (Nat.odd_mul.mp (Nat.odd_mul.mp h).1).1
  have hpmod8 : p % 8 = 5 ∨ p % 8 = 7 := by
    have hmod : p ≡ p % 8 [MOD 8] := by simp [Nat.ModEq]
    have hφmod := ((hmod.pow 2).add hmod).add (Nat.ModEq.refl 1)
    change (p ^ 2 + p + 1) % 8 = ((p % 8) ^ 2 + p % 8 + 1) % 8 at hφmod
    rw [hφmod] at hφ8
    have hlt := Nat.mod_lt p (by decide : 0 < 8)
    have hpos : p % 8 % 2 = 1 := by have := Nat.odd_iff.mp hpodd; omega
    generalize p % 8 = r at *
    interval_cases r <;> norm_num at *
  have hpnd3 : ¬3 ∣ p := fun h =>
    h3 ((h.trans (hpd.trans (dvd_pow_self s (by decide : 2 ≠ 0)))).trans
      (by rw [← hm]; exact Nat.dvd_mul_right _ _))
  have hpmod3 : p % 3 = 2 := by
    rw [Nat.dvd_iff_mod_eq_zero] at hpnd3
    have := hsp₁ p hp
    omega
  omega

end OMA.Descartes

namespace OMA.DescartesEstimate

open Finset

private def scale : ℕ := 1000000000
private def period : ℕ := 207480
private def slots : ℕ := 8645
private def capacity : ℕ := 7680
private def lastBlock : ℕ := 131

private def weight (p : ℕ) : ℕ :=
  (scale * (p + 1) + p ^ 2 - 1) / p ^ 2

private noncomputable def score (p : ℕ) : ℝ :=
  1 / (p : ℝ) + 1 / (p : ℝ) ^ 2

private theorem score_le_weight {p : ℕ} (hp : 0 < p) :
    score p ≤ (weight p : ℝ) / scale := by
  have hp2 : 0 < p ^ 2 := by positivity
  have hquot := Nat.mod_add_div (scale * (p + 1) + p ^ 2 - 1) (p ^ 2)
  have hrem := Nat.mod_lt (scale * (p + 1) + p ^ 2 - 1) hp2
  have hmain : scale * (p + 1) ≤ p ^ 2 * weight p := by unfold weight; omega
  have hpreal : (0 : ℝ) < p := by exact_mod_cast hp
  have hcast : (scale : ℝ) * ((p : ℝ) + 1) ≤ (p : ℝ) ^ 2 * (weight p : ℝ) := by
    exact_mod_cast hmain
  have hrewrite : score p = ((p : ℝ) + 1) / (p : ℝ) ^ 2 := by
    unfold score
    field_simp [hpreal.ne']
  rw [hrewrite, div_le_div_iff₀ (by positivity) (by norm_num [scale])]
  nlinarith only [hcast]

private theorem score_antitone {p q : ℕ} (hp : 0 < p) (h : p ≤ q) :
    score q ≤ score p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h' : (p : ℝ) ≤ q := by exact_mod_cast h
  apply add_le_add
  · exact one_div_le_one_div_of_le hp' h'
  · exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp'.le h' _)

private def smallPrimeTests : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

private def cyclotomicTests : List ℕ := [13, 19, 37, 43, 61, 67]

private theorem smallPrimeTests_prime : ∀ q ∈ smallPrimeTests, Nat.Prime q := by
  intro q hq
  simp [smallPrimeTests] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem cyclotomicTests_spec :
    ∀ q ∈ cyclotomicTests, q.Prime ∧ q % 8 ≠ 1 ∧ q % 8 ≠ 7 := by
  intro q hq
  simp [cyclotomicTests] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def passesSmallTests (p : ℕ) : Bool :=
  (if p ≤ 97 then smallPrimeTests.all fun q => decide (p = q ∨ p % q ≠ 0)
    else decide (p.Coprime smallPrimeTests.prod)) &&
    decide ((p ^ 2 + p + 1).Coprime cyclotomicTests.prod)

private def passesWheel (p : ℕ) : Bool :=
  decide (p % 5 ≠ 0 ∧ p % 7 ≠ 0 ∧ p % 13 ≠ 0 ∧ p % 19 ≠ 0 ∧
    (p ^ 2 + p + 1) % 13 ≠ 0 ∧ (p ^ 2 + p + 1) % 19 ≠ 0)

private theorem passesSmallTests_iff (p : ℕ) :
    passesSmallTests p = true ↔
      (∀ q ∈ smallPrimeTests, p = q ∨ p % q ≠ 0) ∧
      (∀ q ∈ cyclotomicTests, (p ^ 2 + p + 1) % q ≠ 0) := by
  simp only [passesSmallTests, Bool.and_eq_true, decide_eq_true_eq,
    Nat.coprime_list_prod_right_iff]
  apply and_congr
  · split_ifs with h
    · simp [List.all_eq_true]
    · simp only [decide_eq_true_eq]
      apply forall_congr'
      intro q
      apply imp_congr_right
      intro hq
      have hq97 : q ≤ 97 := by
        simp [smallPrimeTests] at hq
        omega
      have hne : p ≠ q := by omega
      rw [or_iff_right hne, Nat.coprime_comm,
        (smallPrimeTests_prime q hq).coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]
  · apply forall_congr'
    intro q
    apply imp_congr_right
    intro hq
    rw [Nat.coprime_comm,
      (cyclotomicTests_spec q hq).1.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]

private theorem small_tests_of_prime {p : ℕ} (hp : p.Prime)
    (h : ∀ q : ℕ, q.Prime → q ∣ p ^ 2 + p + 1 → q % 8 = 1 ∨ q % 8 = 7) :
    passesSmallTests p = true := by
  apply (passesSmallTests_iff p).mpr
  constructor
  · intro q hq
    by_cases hdiv : q ∣ p
    · exact Or.inl ((hp.eq_one_or_self_of_dvd _ hdiv).resolve_left
        (smallPrimeTests_prime q hq).ne_one).symm
    · exact Or.inr (mt Nat.dvd_of_mod_eq_zero hdiv)
  · intro q hq hzero
    obtain ⟨hqp, hq1, hq7⟩ := cyclotomicTests_spec q hq
    exact (h q hqp (Nat.dvd_of_mod_eq_zero hzero)).elim hq1 hq7

private def binarySum (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, a => f a
  | n + 1, a => binarySum f n a + binarySum f n (a + 2 ^ n)

private theorem binarySum_eq (f : ℕ → ℕ) (n a : ℕ) :
    binarySum f n a = ∑ i ∈ range (2 ^ n), f (a + i) := by
  induction n generalizing a with
  | zero => simp [binarySum]
  | succ n ih =>
    rw [binarySum, ih, ih, pow_succ, Nat.mul_two, Finset.sum_range_add]
    simp only [Nat.add_assoc]

-- Enumerate the two residue classes modulo 24 directly. Beyond the first
-- period the term is zero, which lets the certificate use a binary sum.
private def prefixTerm (test : ℕ → Bool) (quantity : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k < slots then
    (if test (24 * k + 5) then quantity (24 * k + 5) else 0) +
    (if test (24 * k + 23) then quantity (24 * k + 23) else 0)
  else 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem prefix_chunk_0 :
    binarySum (prefixTerm passesSmallTests weight) 11 0 = 454853986 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem prefix_chunk_1 :
    binarySum (prefixTerm passesSmallTests weight) 11 2048 = 12771892 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem prefix_chunk_2 :
    binarySum (prefixTerm passesSmallTests weight) 11 4096 = 7594513 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem prefix_chunk_3 :
    binarySum (prefixTerm passesSmallTests weight) 11 6144 = 5496719 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem prefix_chunk_4 :
    binarySum (prefixTerm passesSmallTests weight) 11 8192 = 1010106 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem prefix_chunk_5 :
    binarySum (prefixTerm passesSmallTests weight) 11 10240 = 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem prefix_chunk_6 :
    binarySum (prefixTerm passesSmallTests weight) 11 12288 = 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem prefix_chunk_7 :
    binarySum (prefixTerm passesSmallTests weight) 11 14336 = 0 := by
  decide +kernel

private theorem prefix_sum_12_0 :
    binarySum (prefixTerm passesSmallTests weight) 12 0 = 467625878 := by
  rw [binarySum, show 0 + 2 ^ 11 = 2048 by decide, prefix_chunk_0, prefix_chunk_1]

private theorem prefix_sum_12_4096 :
    binarySum (prefixTerm passesSmallTests weight) 12 4096 = 13091232 := by
  rw [binarySum, show 4096 + 2 ^ 11 = 6144 by decide, prefix_chunk_2, prefix_chunk_3]

private theorem prefix_sum_13_0 :
    binarySum (prefixTerm passesSmallTests weight) 13 0 = 480717110 := by
  rw [binarySum, show 0 + 2 ^ 12 = 4096 by decide, prefix_sum_12_0, prefix_sum_12_4096]

private theorem prefix_sum_12_8192 :
    binarySum (prefixTerm passesSmallTests weight) 12 8192 = 1010106 := by
  rw [binarySum, show 8192 + 2 ^ 11 = 10240 by decide, prefix_chunk_4, prefix_chunk_5]

private theorem prefix_sum_12_12288 :
    binarySum (prefixTerm passesSmallTests weight) 12 12288 = 0 := by
  rw [binarySum, show 12288 + 2 ^ 11 = 14336 by decide, prefix_chunk_6, prefix_chunk_7]

private theorem prefix_sum_13_8192 :
    binarySum (prefixTerm passesSmallTests weight) 13 8192 = 1010106 := by
  rw [binarySum, show 8192 + 2 ^ 12 = 12288 by decide, prefix_sum_12_8192, prefix_sum_12_12288]

private theorem prefix_certificate :
    binarySum (prefixTerm passesSmallTests weight) 14 0 = 481727216 := by
  rw [binarySum, show 0 + 2 ^ 13 = 8192 by decide, prefix_sum_13_0, prefix_sum_13_8192]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem wheel_chunk_0 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 11 0 = 1816 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem wheel_chunk_1 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 11 2048 = 1820 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem wheel_chunk_2 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 11 4096 = 1821 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem wheel_chunk_3 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 11 6144 = 1821 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem wheel_chunk_4 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 11 8192 = 402 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem wheel_chunk_5 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 11 10240 = 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem wheel_chunk_6 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 11 12288 = 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem wheel_chunk_7 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 11 14336 = 0 := by
  decide +kernel

private theorem wheel_sum_12_0 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 12 0 = 3636 := by
  rw [binarySum, show 0 + 2 ^ 11 = 2048 by decide, wheel_chunk_0, wheel_chunk_1]

private theorem wheel_sum_12_4096 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 12 4096 = 3642 := by
  rw [binarySum, show 4096 + 2 ^ 11 = 6144 by decide, wheel_chunk_2, wheel_chunk_3]

private theorem wheel_sum_13_0 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 13 0 = 7278 := by
  rw [binarySum, show 0 + 2 ^ 12 = 4096 by decide, wheel_sum_12_0, wheel_sum_12_4096]

private theorem wheel_sum_12_8192 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 12 8192 = 402 := by
  rw [binarySum, show 8192 + 2 ^ 11 = 10240 by decide, wheel_chunk_4, wheel_chunk_5]

private theorem wheel_sum_12_12288 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 12 12288 = 0 := by
  rw [binarySum, show 12288 + 2 ^ 11 = 14336 by decide, wheel_chunk_6, wheel_chunk_7]

private theorem wheel_sum_13_8192 :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 13 8192 = 402 := by
  rw [binarySum, show 8192 + 2 ^ 12 = 12288 by decide, wheel_sum_12_8192, wheel_sum_12_12288]

private theorem wheel_certificate :
    binarySum (prefixTerm passesWheel (fun _ => 1)) 14 0 = capacity := by
  rw [binarySum, show 0 + 2 ^ 13 = 8192 by decide, wheel_sum_13_0, wheel_sum_13_8192]
  decide

private theorem tail_certificate :
    10 ^ 6 * weight (period * lastBlock) +
      capacity * binarySum (fun i => weight (period * i) - weight (period * lastBlock)) 8 1 =
      202235200 := by
  decide +kernel


private def candidatesInClass (test : ℕ → Bool) (r : ℕ) : Finset ℕ :=
  ((range slots).filter fun k => test (24 * k + r)).image fun k => 24 * k + r

private def candidates (test : ℕ → Bool) : Finset ℕ :=
  candidatesInClass test 5 ∪ candidatesInClass test 23

private theorem mem_candidates {test : ℕ → Bool} {p : ℕ} :
    p ∈ candidates test ↔ p < period ∧ (p % 24 = 5 ∨ p % 24 = 23) ∧ test p = true := by
  simp only [candidates, candidatesInClass, mem_union, mem_image, mem_filter, mem_range]
  unfold slots period
  constructor
  · rintro (⟨k, ⟨hk, ht⟩, rfl⟩ | ⟨k, ⟨hk, ht⟩, rfl⟩) <;>
      exact ⟨by omega, by omega, ht⟩
  · rintro ⟨hp, hr | hr, ht⟩
    · left
      exact ⟨p / 24, ⟨by omega, by rwa [show 24 * (p / 24) + 5 = p by omega]⟩, by omega⟩
    · right
      exact ⟨p / 24, ⟨by omega, by rwa [show 24 * (p / 24) + 23 = p by omega]⟩, by omega⟩

private theorem sum_candidates (test : ℕ → Bool) (quantity : ℕ → ℕ) :
    (∑ p ∈ candidates test, quantity p) = binarySum (prefixTerm test quantity) 14 0 := by
  have hdis : Disjoint (candidatesInClass test 5) (candidatesInClass test 23) := by
    rw [Finset.disjoint_left]
    intro p h5 h23
    simp only [candidatesInClass, mem_image, mem_filter, mem_range] at h5 h23
    obtain ⟨i, _, hi⟩ := h5
    obtain ⟨j, _, hj⟩ := h23
    omega
  rw [candidates, sum_union hdis, binarySum_eq]
  have hclass (r : ℕ) :
      (∑ p ∈ candidatesInClass test r, quantity p) =
        ∑ k ∈ range slots, if test (24 * k + r) then quantity (24 * k + r) else 0 := by
    rw [candidatesInClass, sum_image (fun _ _ _ _ => by omega), sum_filter]
  rw [hclass, hclass, ← sum_add_distrib]
  simp only [zero_add]
  calc
    _ = ∑ k ∈ range slots, prefixTerm test quantity k := by
      apply sum_congr rfl
      intro k hk
      simp [prefixTerm, mem_range.mp hk]
    _ = ∑ k ∈ range (2 ^ 14), prefixTerm test quantity k := by
      apply sum_subset (range_mono (by decide))
      intro k _ hk
      rw [prefixTerm, if_neg (mt mem_range.mpr hk)]

private theorem wheel_of_large {p : ℕ} (hp : period ≤ p)
    (hsmall : passesSmallTests p = true) : passesWheel p = true := by
  have hsmall := (passesSmallTests_iff p).mp hsmall
  have h5 : p % 5 ≠ 0 :=
    (hsmall.1 5 (by decide)).resolve_left (by unfold period at hp; omega)
  have h7 : p % 7 ≠ 0 :=
    (hsmall.1 7 (by decide)).resolve_left (by unfold period at hp; omega)
  have h13 : p % 13 ≠ 0 :=
    (hsmall.1 13 (by decide)).resolve_left (by unfold period at hp; omega)
  have h19 : p % 19 ≠ 0 :=
    (hsmall.1 19 (by decide)).resolve_left (by unfold period at hp; omega)
  exact decide_eq_true ⟨h5, h7, h13, h19, hsmall.2 13 (by decide), hsmall.2 19 (by decide)⟩

private theorem wheel_remainder {p : ℕ} (hr : p % 24 = 5 ∨ p % 24 = 23)
    (h : passesWheel p = true) : p % period ∈ candidates passesWheel := by
  have hmod (d : ℕ) (hd : d ∣ period) : p % period ≡ p [MOD d] :=
    Nat.ModEq.of_dvd hd (by simp [Nat.ModEq])
  have hφmod (d : ℕ) (hd : d ∣ period) :
      (p % period) ^ 2 + p % period + 1 ≡ p ^ 2 + p + 1 [MOD d] := by
    exact (((hmod d hd).pow 2).add (hmod d hd)).add (Nat.ModEq.refl 1)
  have hz5 := hmod 5 (by decide)
  have hz7 := hmod 7 (by decide)
  have hz13 := hmod 13 (by decide)
  have hz19 := hmod 19 (by decide)
  have hz24 := hmod 24 (by decide)
  have hφ13 := hφmod 13 (by decide)
  have hφ19 := hφmod 19 (by decide)
  simp only [Nat.ModEq] at hz5 hz7 hz13 hz19 hz24 hφ13 hφ19
  rw [mem_candidates]
  refine ⟨Nat.mod_lt _ (by decide), by simpa [hz24] using hr, ?_⟩
  simpa [passesWheel, hz5, hz7, hz13, hz19, hφ13, hφ19] using h

set_option maxRecDepth 4096 in
private theorem capacity_bound (L : Finset ℕ) (j : ℕ)
    (hL : ∀ p ∈ L, period ≤ p ∧ (p % 24 = 5 ∨ p % 24 = 23) ∧ passesSmallTests p = true) :
    (L.filter fun p => p / period = j).card ≤ capacity := by
  have hcard : (candidates passesWheel).card = capacity := by
    exact (card_eq_sum_ones (candidates passesWheel)).trans
      ((sum_candidates passesWheel (fun _ => 1)).trans wheel_certificate)
  refine (card_le_card_of_injOn (fun p => p % period) ?_ ?_).trans_eq hcard
  · intro p hp
    obtain ⟨hp', _⟩ := mem_filter.mp hp
    obtain ⟨hpL, hr, ht⟩ := hL p hp'
    exact wheel_remainder hr (wheel_of_large hpL ht)
  · intro p hp q hq heq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    have hnp := Nat.mod_add_div p period
    have hnq := Nat.mod_add_div q period
    rw [hp'] at hnp
    rw [hq'] at hnq
    change p % period = q % period at heq
    exact hnp.symm.trans (heq ▸ hnq)


-- Charge each prime the weight at the last block, and add the difference
-- for any earlier block. Each block contains at most `capacity` candidates.
private def tailWeight (p : ℕ) : ℕ :=
  weight (period * lastBlock) +
    ∑ k ∈ range (2 ^ 8), if p / period = k + 1 then
      weight (period * (k + 1)) - weight (period * lastBlock) else 0

private theorem score_le_tailWeight (p : ℕ) (hp : period ≤ p) :
    score p ≤ (tailWeight p : ℝ) / scale := by
  have hperiod : 0 < period := by decide
  have hi : 0 < p / period := by
    have := (Nat.le_div_iff_mul_le hperiod).mpr (by simpa using hp : 1 * period ≤ p)
    omega
  have hform : period * (p / period) ≤ p := by simpa [Nat.mul_comm] using Nat.div_mul_le_self p period
  rw [tailWeight]
  have hbound : ∃ m : ℕ, 0 < m ∧ m ≤ p ∧
      weight m ≤ weight (period * lastBlock) +
        ∑ k ∈ range (2 ^ 8), if p / period = k + 1 then
          weight (period * (k + 1)) - weight (period * lastBlock) else 0 := by
    by_cases hcut : p / period < lastBlock
    · let k := p / period - 1
      have hk : k + 1 = p / period := by dsimp [k]; omega
      have hkr : k ∈ range (2 ^ 8) := by
        unfold lastBlock at hcut
        rw [mem_range]
        change p / period - 1 < 256
        omega
      have hs : weight (period * (p / period)) - weight (period * lastBlock) ≤
          ∑ k ∈ range (2 ^ 8), if p / period = k + 1 then
            weight (period * (k + 1)) - weight (period * lastBlock) else 0 := by
        calc
          _ = (if p / period = k + 1 then
              weight (period * (k + 1)) - weight (period * lastBlock) else 0) := by simp only [hk, ↓reduceIte]
          _ ≤ _ := single_le_sum
            (f := fun j : ℕ => if p / period = j + 1 then
              weight (period * (j + 1)) - weight (period * lastBlock) else 0)
            (fun _ _ => Nat.zero_le _) hkr
      exact ⟨period * (p / period), Nat.mul_pos hperiod hi, hform, by omega⟩
    · have hpos : 0 < period * lastBlock := by decide
      refine ⟨period * lastBlock, hpos, ?_, by omega⟩
      exact (Nat.mul_le_mul_left _ (Nat.le_of_not_gt hcut)).trans hform
  obtain ⟨m, hm, hmp, hw⟩ := hbound
  refine (score_antitone hm hmp).trans ((score_le_weight hm).trans ?_)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hw) (by norm_num [scale])

private theorem tail_sum_bound (L : Finset ℕ) (hcard : L.card ≤ 10 ^ 6)
    (hL : ∀ p ∈ L, period ≤ p ∧ (p % 24 = 5 ∨ p % 24 = 23) ∧ passesSmallTests p = true) :
    (∑ p ∈ L, score p) ≤ (202235200 : ℝ) / scale := by
  have hnat : (∑ p ∈ L, tailWeight p) ≤ 202235200 := by
    rw [← tail_certificate]
    simp only [tailWeight, sum_add_distrib, sum_const, nsmul_eq_mul, binarySum_eq, mul_sum,
      Nat.add_comm 1]
    rw [sum_comm (s := L) (t := range (2 ^ 8))]
    refine add_le_add (Nat.mul_le_mul_right _ hcard) (sum_le_sum fun k _ => ?_)
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    exact Nat.mul_le_mul_right _ (capacity_bound L (k + 1) hL)
  calc
    _ ≤ ∑ p ∈ L, (tailWeight p : ℝ) / scale :=
      sum_le_sum fun p hp => score_le_tailWeight p (hL p hp).1
    _ = ((∑ p ∈ L, tailWeight p : ℕ) : ℝ) / scale := by rw [← sum_div]; push_cast; rfl
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hnat) (by norm_num [scale])

private theorem prefix_sum_bound (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ (p % 24 = 5 ∨ p % 24 = 23) ∧ passesSmallTests p = true) :
    (∑ p ∈ S.filter (· < period), score p) ≤ (481727216 : ℝ) / scale := by
  have hsubset : S.filter (· < period) ⊆ candidates passesSmallTests := by
    intro p hp
    obtain ⟨hs, hlt⟩ := mem_filter.mp hp
    exact mem_candidates.mpr ⟨hlt, (hS p hs).2⟩
  have hnat : (∑ p ∈ S.filter (· < period), weight p) ≤ 481727216 := by
    rw [← prefix_certificate, ← sum_candidates]
    exact sum_le_sum_of_subset hsubset
  calc
    _ ≤ ∑ p ∈ S.filter (· < period), (weight p : ℝ) / scale := by
      refine sum_le_sum fun p hp => score_le_weight ((hS p (mem_filter.mp hp).1).1.pos)
    _ = ((∑ p ∈ S.filter (· < period), weight p : ℕ) : ℝ) / scale := by rw [← sum_div]; push_cast; rfl
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hnat) (by norm_num [scale])

private theorem exp_score_bound : Real.exp ((684 : ℝ) / 1000) < (199 : ℝ) / 100 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num)).mp
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 200 / 199 by norm_num)
  have hinv : Real.log ((199 : ℝ) / 200) = -Real.log (200 / 199) := by
    rw [← Real.log_inv, show ((200 : ℝ) / 199)⁻¹ = 199 / 200 by norm_num]
  have hsplit : Real.log ((199 : ℝ) / 100) = Real.log 2 + Real.log (199 / 200) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [hsplit, hinv]
  linarith [Real.log_two_gt_d9]

private theorem product_bound (S : Finset ℕ) (hcard : S.card ≤ 10 ^ 6)
    (hS : ∀ p ∈ S, p.Prime ∧ (p % 24 = 5 ∨ p % 24 = 23) ∧
      ∀ q : ℕ, q.Prime → q ∣ p ^ 2 + p + 1 → q % 8 = 1 ∨ q % 8 = 7) :
    (∏ p ∈ S, (((p : ℝ) ^ 2 + p + 1) / (p : ℝ) ^ 2)) < (199 : ℝ) / 100 := by
  have ht : ∀ p ∈ S, p.Prime ∧ (p % 24 = 5 ∨ p % 24 = 23) ∧ passesSmallTests p = true :=
    fun p hp => ⟨(hS p hp).1, (hS p hp).2.1, small_tests_of_prime (hS p hp).1 (hS p hp).2.2⟩
  have hpre := prefix_sum_bound S ht
  have htail := tail_sum_bound (S.filter (fun p => ¬p < period))
    ((card_filter_le _ _).trans hcard)
    (fun p hp => ⟨Nat.le_of_not_gt (mem_filter.mp hp).2, (ht p (mem_filter.mp hp).1).2⟩)
  have hsum : (∑ p ∈ S, score p) ≤ (684 : ℝ) / 1000 := by
    rw [← sum_filter_add_sum_filter_not S (· < period) score]
    unfold scale at hpre htail
    linarith
  have hfactor : ∀ p ∈ S,
      ((p : ℝ) ^ 2 + p + 1) / (p : ℝ) ^ 2 = 1 + score p := by
    intro p hp
    have hpos : (0 : ℝ) < p := by exact_mod_cast (ht p hp).1.pos
    unfold score
    field_simp [hpos.ne']
    ring
  calc
    _ = ∏ p ∈ S, (1 + score p) := prod_congr rfl hfactor
    _ ≤ ∏ p ∈ S, Real.exp (score p) :=
      prod_le_prod (f := fun p => 1 + score p) (fun p _ => by unfold score; positivity)
        (fun p _ => by simpa [add_comm] using Real.add_one_le_exp (score p))
    _ = Real.exp (∑ p ∈ S, score p) := (Real.exp_sum S score).symm
    _ ≤ Real.exp ((684 : ℝ) / 1000) := Real.exp_le_exp.mpr hsum
    _ < _ := exp_score_bound

end OMA.DescartesEstimate

namespace OMA.Descartes

open scoped ArithmeticFunction.sigma
open Finset

private theorem root_ge_twenty_three {s : ℕ} (hs1 : 1 < s) (hs : Squarefree s)
    (hap : σ 1 (s ^ 2) = 2 * s ^ 2 - 1)
    (hres : ∀ p ∈ s.primeFactors, p % 24 = 5 ∨ p % 24 = 23) : 23 ≤ s := by
  by_contra! h
  have h5 : s.primeFactors ⊆ {5} := by
    intro p hp
    have hle := Nat.le_of_dvd (by omega : 0 < s) (Nat.dvd_of_mem_primeFactors hp)
    have hr := hres p hp
    simp only [mem_singleton]
    omega
  obtain ⟨p, hprime, hps⟩ := Nat.exists_prime_and_dvd (by omega : s ≠ 1)
  have hpS := Nat.mem_primeFactors.mpr ⟨hprime, hps, hs.ne_zero⟩
  have hp5 : p = 5 := mem_singleton.mp (h5 hpS)
  have heq : s.primeFactors = {5} := Subset.antisymm h5 (singleton_subset_iff.mpr (hp5 ▸ hpS))
  have hs5 : s = 5 := by
    rw [← Nat.prod_primeFactors_of_squarefree hs, heq, prod_singleton]
  rw [divisor_sum_square hs, heq, prod_singleton, hs5] at hap
  norm_num at hap

end OMA.Descartes

open scoped ArithmeticFunction.sigma in
theorem OMA.solution : type_of% @DescartesNumber.descartes_cubeFree_not_dvd_three_primeFactors_gt_million := by
  intro n hd hcf h3
  rcases hd with ⟨m, w, rfl, hf⟩
  obtain ⟨s, hs1, hsf, hm, hap, hres⟩ := OMA.Descartes.factor_structure hf hcf h3
  have hs23 := OMA.Descartes.root_ge_twenty_three hs1 hsf hap (fun p hp => (hres p hp).1)
  have hn0 : m * w ≠ 0 := by
    have hodd := Nat.odd_iff.mp hf.2.1
    omega
  have hmd : s ^ 2 ∣ m * w := by rw [← hm]; exact Nat.dvd_mul_right _ _
  have hsub : s.primeFactors ⊆ (m * w).primeFactors :=
    Nat.primeFactors_mono ((dvd_pow_self s (by decide : 2 ≠ 0)).trans hmd) hn0
  by_contra! hsmall
  have hcard : s.primeFactors.card ≤ 10 ^ 6 :=
    (Finset.card_le_card hsub).trans hsmall
  have hprod := OMA.DescartesEstimate.product_bound s.primeFactors hcard
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hres p hp⟩)
  rw [Finset.prod_div_distrib] at hprod
  have hnum : (∏ p ∈ s.primeFactors, ((p : ℝ) ^ 2 + p + 1)) = (σ 1 (s ^ 2) : ℝ) := by
    rw [OMA.Descartes.divisor_sum_square hsf]
    push_cast
    rfl
  have hden : (∏ p ∈ s.primeFactors, (p : ℝ) ^ 2) = (s : ℝ) ^ 2 := by
    rw [Finset.prod_pow, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf]
  rw [hnum, hden] at hprod
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hineq := (div_lt_iff₀ (by positivity : 0 < (s : ℝ) ^ 2)).mp hprod
  have hσadd : (σ 1 (s ^ 2) : ℝ) + 1 = 2 * (s : ℝ) ^ 2 := by
    have h : σ 1 (s ^ 2) + 1 = 2 * s ^ 2 := by
      have hpow : 0 < s ^ 2 := by positivity
      omega
    exact_mod_cast h
  have hsq : (23 : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hs23) _
  linarith
