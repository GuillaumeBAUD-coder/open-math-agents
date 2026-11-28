import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.PrimeFin
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Positivity

-- Credit: @jacklarmer (Codex)
-- Use the parity of a = v₂(n) to separate two open uniform-boundedness problems.
-- In both cases every prime shared by a and 2^a+1 must be 3. For odd a, write W(a)
-- for the number of prime factors congruent to 2 modulo 3 counted with multiplicity.
-- For e = v₃(n) equal to 11, 13, 19 respectively, v₃(a)+W(a) is at most 7, 8, 13.
--
-- The valuation argument uses the unitary-divisor balance proved by @adammcarter.
-- The e-specific simple-prime chains used for the fixed costs were identified in the
-- earlier reductions. This proof charges each repeated prime factor of a individually.
-- For example, when e=11, 401^8 passes the distinct-prime count but has W=8.
-- For the even case e=11, a=2*409*1637 meets the sieve through 400: its only divisor
-- in [2,400] is 2. But 2^818 = -1 modulo 1637. Thus 1637 divides a and 2^a+1.
-- All its odd multiples are likewise ruled out by the gcd condition.


namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R2

/-!
# Counting prime-factor multiplicities in the odd exponent of two

This file works from the unitary-divisor balance identity. The forced-prime
sets for exponents 11, 13, and 19 and the earlier bounds counting distinct
prime factors are from the Left to Solve reductions of @adammcarter and
@Dugongue for Erdős problem 1052. The theorem `bounded_weight_of_balance`
counts repeated prime factors and includes the 3-adic valuation of the exponent.
-/

namespace UnitaryMultiplicity

private theorem oddPowModThree {x n : ℕ} (hx : x % 3 = 2) (hn : Odd n) :
    x ^ n % 3 = 2 := by
  obtain ⟨t, rfl⟩ := hn
  induction t with
  | zero => simpa using hx
  | succ t ih =>
      have he : 2 * (t + 1) + 1 = (2*t + 1) + 2 := by omega
      have hs : x^2 % 3 = 1 := by rw [pow_two, Nat.mul_mod, hx]
      rw [he, pow_add, Nat.mul_mod, ih, hs]

theorem twoPowOddModThree {b : ℕ} (hb : Odd b) : 2 ^ b % 3 = 2 :=
  oddPowModThree (by decide) hb

/-- Appending an odd multiplier to an exponent gives an integral quotient.
For a base congruent to minus one modulo three, the quotient has the same
residue as the multiplier. -/
theorem oddPowerPlusOneFactor {x k : ℕ} (hx : x % 3 = 2) (hk : Odd k) :
    ∃ q : ℕ, x ^ k + 1 = (x + 1) * q ∧ q % 3 = k % 3 := by
  obtain ⟨t, rfl⟩ := hk
  induction t with
  | zero =>
      exact ⟨1, by simp, by decide⟩
  | succ t ih =>
      obtain ⟨q, hq, hm⟩ := ih
      have hxpos : 1 ≤ x := by omega
      have hxm : (x-1) % 3 = 1 := by omega
      have ho : Odd (2*t+1) := ⟨t, rfl⟩
      have hp := oddPowModThree hx ho
      have he : 2 * (t + 1) + 1 = (2*t + 1) + 2 := by omega
      refine ⟨q+(x-1)*x^(2*t+1), ?_, ?_⟩
      · rw [he, pow_add, mul_add, ← hq]
        have hd := Nat.sub_add_cancel hxpos
        nlinarith only [congrArg (fun z : ℕ => z * ((x+1)*x^(2*t+1))) hd]
      · rw [Nat.add_mod, Nat.mul_mod, hxm, hp, hm, he, Nat.add_mod (2*t+1) 2]

end UnitaryMultiplicity

namespace UnitaryMultiplicity

theorem omegaTwo_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (((a*b) : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length = ((a : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length + ((b : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length := by
  have h := (Nat.perm_primeFactorsList_mul ha hb).filter (fun p => p % 3 == 2)
  simpa using h.length_eq

private theorem factor_of_prod_mod {l : List ℕ} (h : l.prod % 3 = 2) :
    ∃ q ∈ l, q % 3 = 2 := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    by_cases hp : p % 3 = 2
    · exact ⟨p, by simp, hp⟩
    by_cases hl : l.prod % 3 = 2
    · obtain ⟨q, hq, hqm⟩ := ih hl
      exact ⟨q, List.mem_cons_of_mem _ hq, hqm⟩
    rw [List.prod_cons, Nat.mul_mod] at h
    have hp' : p % 3 = 0 ∨ p % 3 = 1 := by omega
    have hl' : l.prod % 3 = 0 ∨ l.prod % 3 = 1 := by omega
    rcases hp' with hp' | hp' <;> rcases hl' with hl' | hl' <;> simp [hp', hl'] at h

theorem omegaTwo_pos_of_mod {n : ℕ} (hn : n % 3 = 2) : 0 < ((n : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length := by
  have hprod : n.primeFactorsList.prod % 3 = 2 := by
    rw [Nat.prod_primeFactorsList (by omega : n ≠ 0)]
    exact hn
  obtain ⟨q, hq, hqm⟩ := factor_of_prod_mod hprod
  have hm : q ∈ n.primeFactorsList.filter (fun p => p % 3 == 2) := by
    exact List.mem_filter.mpr ⟨hq, by simpa using hqm⟩
  exact List.length_pos_of_mem hm

theorem omegaTwo_le_of_odd_core
    (factorStep : ∀ {b p : ℕ}, Odd b → Odd p →
      ∃ q : ℕ, 2^(b*p)+1 = (2^b+1)*q ∧ q % 3 = p % 3)
    {a : ℕ} (ha : Odd a) : ((a : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length ≤ (((2^a+1) : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases ha₁ : a = 1
    · subst a
      simp
    obtain ⟨p, hp, b, hab⟩ := Nat.exists_prime_and_dvd ha₁
    subst a
    obtain ⟨hop, hob⟩ := Nat.odd_mul.mp ha
    have hb : 0 < b := by obtain ⟨k, hk⟩ := hob; omega
    have hlt : b < p*b := by simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hb
    have hrec := ih b hlt hob
    obtain ⟨q, hq, hqm⟩ := factorStep hob hop
    have hq₀ : q ≠ 0 := by intro h; simp [h] at hq
    rw [mul_comm b p] at hq
    rw [hq, omegaTwo_mul hp.ne_zero hb.ne', omegaTwo_mul (by positivity) hq₀]
    by_cases hpm : p % 3 = 2
    · have hpos := omegaTwo_pos_of_mod (hqm.trans hpm)
      have hpω : ((p : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length = 1 := by simp [Nat.primeFactorsList_prime hp, hpm]
      omega
    · have hpω : ((p : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length = 0 := by simp [Nat.primeFactorsList_prime hp, hpm]
      omega

end UnitaryMultiplicity

namespace UnitaryMultiplicity

/-- Every odd exponent contributes at least its own multiplicity of primes
congruent to two modulo three to the corresponding generalized Fermat number. -/
theorem omegaTwo_le_two_pow_add_one {a : ℕ} (ha : Odd a) :
    ((a : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length ≤ (((2 ^ a + 1) : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length := by
  apply omegaTwo_le_of_odd_core _ ha
  intro b p hb hp
  rw [pow_mul]
  exact oddPowerPlusOneFactor (twoPowOddModThree hb) hp

end UnitaryMultiplicity

namespace UnitaryMultiplicity

/-- Counting the prime factors in the residue class two modulo three gives
the cardinality of their support when none of those primes occurs twice. -/
theorem omegaTwo_eq_card_of_no_square {n : ℕ} (hn : n ≠ 0)
    (hsq : ∀ p, p.Prime → p % 3 = 2 → ¬ p ^ 2 ∣ n) :
    ((n : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length = (n.primeFactors.filter (fun p => p % 3 = 2)).card := by
  let L := n.primeFactorsList.filter (fun p => p % 3 == 2)
  have hnodup : L.Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro p
    by_cases hm : p ∈ L
    · obtain ⟨hp, hr⟩ := List.mem_filter.mp hm
      have hprime := Nat.prime_of_mem_primeFactorsList hp
      have hres : p % 3 = 2 := by simpa using hr
      have h := (hprime.pow_dvd_iff_le_factorization hn).not.mp (hsq p hprime hres)
      have heq : L.count p = n.factorization p := by
        simp [L, List.count_filter, hres, Nat.primeFactorsList_count_eq]
      omega
    · simp [List.count_eq_zero_of_not_mem hm]
  have hset : L.toFinset = n.primeFactors.filter (fun p => p % 3 = 2) := by
    ext p
    simp only [L, Nat.primeFactors, List.mem_toFinset, List.mem_filter,
      Finset.mem_filter, beq_iff_eq]
  rw [← hset, List.toFinset_card_of_nodup hnodup]

end UnitaryMultiplicity

namespace UnitaryMultiplicity

/-- The power-sum factor itself consumes one more factor of three than the odd exponent. -/
theorem threeValTexp {a : ℕ} (ha : Odd a) :
    padicValNat 3 (2 ^ a + 1) = 1 + padicValNat 3 a := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1)
    (by decide : Odd 3) (by decide) (by decide) ha
  simpa only [one_pow, show padicValNat 3 (2+1) = 1 from padicValNat.self (by decide)] using h


end UnitaryMultiplicity

namespace UnitaryMultiplicity

/-- The product of distinct primes contains no prime outside its index set. -/
private theorem not_dvd_prime_product {q : ℕ} {P : Finset ℕ}
    (hq : q.Prime) (hp : ∀ p ∈ P, p.Prime) (h : q ∉ P) :
    ¬ q ∣ ∏ p ∈ P, p := by
  intro hd
  obtain ⟨p, hmem, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hd
  exact h ((Nat.prime_dvd_prime_iff_eq hq (hp p hmem)).mp hqp ▸ hmem)

/-- The distinct-prime product on the right forces every prime other than
two and three on the left to occur exactly once. -/
theorem simple_prime_of_balance {m e F G q : ℕ} {P : Finset ℕ}
    (hp : ∀ p ∈ P, p.Prime) (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3)
    (E : F * G = 2 ^ (m+1) * 3 ^ e * ∏ p ∈ P, p) (hd : q ∣ F) :
    q ∈ P ∧ ¬ q ^ 2 ∣ F := by
  have hblock : ¬ q ∣ 2^(m+1) * 3^e := by
    intro h
    rcases hq.dvd_mul.mp h with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h))
  have hmem : q ∈ P := by
    by_contra hn
    have hr : q ∣ F * G := hd.mul_right _
    rw [E] at hr
    exact (hq.dvd_mul.mp hr).elim hblock (not_dvd_prime_product hq hp hn)
  refine ⟨hmem, ?_⟩
  intro hsq
  have hr := hsq.mul_right G
  rw [E, pow_two, ← Finset.mul_prod_erase P (fun t => t) hmem, mul_left_comm] at hr
  have hd' := Nat.dvd_of_mul_dvd_mul_left hq.pos hr
  exact (hq.dvd_mul.mp hd').elim hblock (not_dvd_prime_product hq
    (fun p ht => hp p (Finset.mem_of_mem_erase ht)) (Finset.notMem_erase _ _))

/-- A simple prime coming from an old source cannot also divide the
distinguished factor two to the power m plus one. -/
theorem forced_mem_not_dvd {m e q : ℕ} {P : Finset ℕ}
    (hp : ∀ p ∈ P, p.Prime)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3)
    (h : q ∣ (1+3^e) * ∏ p ∈ P, (p+1)) : q ∈ P ∧ ¬ q ∣ 2^m+1 := by
  let R := (1+3^e) * ∏ p ∈ P, (p+1)
  have e' : ((2^m+1)*R)*1 = 2^(m+1) * 3^e * ∏ p ∈ P, p := by
    simpa only [R, mul_one, mul_assoc] using E
  obtain ⟨hmem, hsq⟩ := simple_prime_of_balance hp hq h2 h3 e' (h.mul_left (2^m+1))
  exact ⟨hmem, fun hf => hsq (by simpa only [pow_two, R] using mul_dvd_mul hf h)⟩

/-- The 3-adic contribution of the first factor, each new simple prime
congruent to two modulo three, and the disjoint forced set X all add. -/
theorem budget_of_balance {m e j : ℕ} {P X : Finset ℕ}
    (hm : m ≠ 0) (hp : ∀ p ∈ P, p.Prime) (h3P : 3 ∉ P)
    (E : (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(m+1) * 3^e * ∏ p ∈ P, p)
    (hX : X ⊆ P) (hXr : ∀ x ∈ X, ¬ x ∣ 2^m+1) (hj : 3^j ∣ ∏ x ∈ X, (x+1)) :
    padicValNat 3 (2^m+1) + ((2^m+1).primeFactors.filter (fun p => p % 3 = 2)).card + j ≤ e := by
  classical
  let Q := (2^m+1).primeFactors.filter (fun p => p % 3 = 2)
  change padicValNat 3 (2^m+1) + Q.card + j ≤ e
  have hQ (q) (hq : q ∈ Q) : q.Prime ∧ q ∣ 2^m+1 ∧ q % 3 = 2 := by
    obtain ⟨hmq, hmod⟩ := Finset.mem_filter.mp hq
    exact ⟨(Nat.mem_primeFactors.mp hmq).1, (Nat.mem_primeFactors.mp hmq).2.1, hmod⟩
  have hQP : Q ⊆ P := by
    intro q hq
    obtain ⟨hprime, hd, hmod⟩ := hQ q hq
    have h2 : q ≠ 2 := by
      rintro rfl
      have := (Nat.dvd_add_right (dvd_pow_self 2 hm)).mp hd
      omega
    exact (simple_prime_of_balance hp hprime h2 (by omega) (by simpa [mul_assoc] using E) hd).1
  have hdj : Disjoint Q X := by
    rw [Finset.disjoint_left]
    exact fun q hq hx => hXr q hx (hQ q hq).2.1
  have hqpow : 3^Q.card ∣ ∏ q ∈ Q, (q+1) := by
    rw [← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun q hq => by have := (hQ q hq).2.2; omega)
  have hv : 3 ^ padicValNat 3 (2^m+1) ∣ 2^m+1 :=
    (padicValNat_dvd_iff_le (by positivity)).mpr le_rfl
  have hbound : 3 ^ (padicValNat 3 (2^m+1) + Q.card + j) ∣ (2^m+1) * ∏ q ∈ Q ∪ X, (q+1) := by
    rw [pow_add, pow_add, Finset.prod_union hdj, mul_assoc]
    exact mul_dvd_mul hv (mul_dvd_mul hqpow hj)
  have hprod := Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p+1) (Finset.union_subset hQP hX)
  have hfull : (2^m+1) * ∏ q ∈ Q ∪ X, (q+1) ∣ (2^m+1) * (1+3^e) * ∏ p ∈ P, (p+1) :=
    (mul_dvd_mul_left (2^m+1) hprod).trans ⟨1+3^e, by ring⟩
  by_contra hn
  have hal := ((pow_dvd_pow 3 (by omega : e+1 ≤ _)).trans hbound).trans hfull
  rw [E, pow_succ, show 2^(m+1)*3^e*(∏ p ∈ P,p) = 3^e*(2^(m+1)*(∏ p ∈ P,p)) by ring] at hal
  have hh := Nat.dvd_of_mul_dvd_mul_left (by positivity : 0 < 3^e) hal
  rcases Nat.prime_three.dvd_mul.mp hh with hh | hh
  · have := Nat.prime_three.dvd_of_dvd_pow hh
    omega
  · exact not_dvd_prime_product Nat.prime_three hp h3P hh

end UnitaryMultiplicity

namespace UnitaryMultiplicity

set_option maxRecDepth 8192 in
theorem forcedLedger11 {F : ℕ} {P : Finset ℕ} (h : (∀ q : ℕ, q.Prime → 3 < q → (q ∣ 1+3^11 ∨ ∃ r ∈ P, q ∣ r+1) → q ∈ P ∧ ¬ q ∣ F)) :
    (∀ q ∈ ({17, 83} : Finset ℕ), q ∈ P ∧ ¬ q ∣ F) ∧
      3 ^ 3 ∣ ∏ q ∈ ({17, 83} : Finset ℕ), (q+1) := by
  have h67 := h 67 (by decide +kernel) (by decide) (Or.inl (by decide +kernel))
  have h661 := h 661 (by decide +kernel) (by decide) (Or.inl (by decide +kernel))
  have h17 := h 17 (by decide +kernel) (by decide) (Or.inr ⟨67, h67.1, by decide +kernel⟩)
  have h331 := h 331 (by decide +kernel) (by decide) (Or.inr ⟨661, h661.1, by decide +kernel⟩)
  have h83 := h 83 (by decide +kernel) (by decide) (Or.inr ⟨331, h331.1, by decide +kernel⟩)
  refine ⟨?_, by decide +kernel⟩
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact h17
  · exact h83

set_option maxRecDepth 8192 in
theorem forcedLedger13 {F : ℕ} {P : Finset ℕ} (h : (∀ q : ℕ, q.Prime → 3 < q → (q ∣ 1+3^13 ∨ ∃ r ∈ P, q ∣ r+1) → q ∈ P ∧ ¬ q ∣ F)) :
    (∀ q ∈ ({17, 617, 5} : Finset ℕ), q ∈ P ∧ ¬ q ∣ F) ∧
      3 ^ 4 ∣ ∏ q ∈ ({17, 617, 5} : Finset ℕ), (q+1) := by
  have h398581 := h 398581 (by norm_num1) (by decide) (Or.inl (by decide +kernel))
  have h17 := h 17 (by decide +kernel) (by decide) (Or.inr ⟨398581, h398581.1, by decide +kernel⟩)
  have h617 := h 617 (by decide +kernel) (by decide) (Or.inr ⟨398581, h398581.1, by decide +kernel⟩)
  have h19 := h 19 (by decide +kernel) (by decide) (Or.inr ⟨398581, h398581.1, by decide +kernel⟩)
  have h5 := h 5 (by decide +kernel) (by decide) (Or.inr ⟨19, h19.1, by decide +kernel⟩)
  refine ⟨?_, by decide +kernel⟩
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact h17
  · exact h617
  · exact h5

set_option maxRecDepth 8192 in
theorem forcedLedger19 {F : ℕ} {P : Finset ℕ} (h : (∀ q : ℕ, q.Prime → 3 < q → (q ∣ 1+3^19 ∨ ∃ r ∈ P, q ∣ r+1) → q ∈ P ∧ ¬ q ∣ F)) :
    (∀ q ∈ ({23, 131, 389, 11, 5} : Finset ℕ), q ∈ P ∧ ¬ q ∣ F) ∧
      3 ^ 5 ∣ ∏ q ∈ ({23, 131, 389, 11, 5} : Finset ℕ), (q+1) := by
  have h2851 := h 2851 (by norm_num1) (by decide) (Or.inl (by decide +kernel))
  have h101917 := h 101917 (by norm_num1) (by decide) (Or.inl (by decide +kernel))
  have h23 := h 23 (by decide +kernel) (by decide) (Or.inr ⟨2851, h2851.1, by decide +kernel⟩)
  have h131 := h 131 (by decide +kernel) (by decide) (Or.inr ⟨101917, h101917.1, by decide +kernel⟩)
  have h389 := h 389 (by decide +kernel) (by decide) (Or.inr ⟨101917, h101917.1, by decide +kernel⟩)
  have h11 := h 11 (by decide +kernel) (by decide) (Or.inr ⟨131, h131.1, by decide +kernel⟩)
  have h5 := h 5 (by decide +kernel) (by decide) (Or.inr ⟨389, h389.1, by decide +kernel⟩)
  refine ⟨?_, by decide +kernel⟩
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact h23
  · exact h131
  · exact h389
  · exact h11
  · exact h5

end UnitaryMultiplicity


namespace UnitaryMultiplicity

theorem forced_ledger {a e : ℕ} {P : Finset ℕ}
    (hp : ∀ p ∈ P, p.Prime)
    (E : (2^a+1)*(1+3^e)*(∏ p ∈ P, (p+1)) = 2^(a+1)*3^e*(∏ p ∈ P, p))
    (he : e=11 ∨ e=13 ∨ e=19) :
    ∃ X : Finset ℕ, X ⊆ P ∧ (∀ x ∈ X, ¬ x ∣ 2^a+1) ∧
      3 ^ (if e=11 then 3 else if e=13 then 4 else 5) ∣ ∏ x ∈ X, (x+1) := by
  have source : (∀ q : ℕ, q.Prime → 3 < q → (q ∣ 1+3^e ∨ ∃ r ∈ P, q ∣ r+1) → q ∈ P ∧ ¬ q ∣ (2^a+1)) := by
    intro q hq hgt hsource
    apply forced_mem_not_dvd hp E hq (by omega) (by omega)
    rcases hsource with hs | ⟨r, hr, hd⟩
    · exact hs.mul_right _
    · exact (hd.trans (Finset.dvd_prod_of_mem (fun p : ℕ => p+1) hr)).mul_left _
  rcases he with rfl | rfl | rfl
  · obtain ⟨hall, hcost⟩ := forcedLedger11 source
    exact ⟨{17, 83}, fun q hq => (hall q hq).1, fun q hq => (hall q hq).2, hcost⟩
  · obtain ⟨hall, hcost⟩ := forcedLedger13 source
    exact ⟨{17, 617, 5}, fun q hq => (hall q hq).1, fun q hq => (hall q hq).2, hcost⟩
  · obtain ⟨hall, hcost⟩ := forcedLedger19 source
    exact ⟨{23, 131, 389, 11, 5}, fun q hq => (hall q hq).1, fun q hq => (hall q hq).2, hcost⟩


end UnitaryMultiplicity

namespace UnitaryMultiplicity

/-- Each prime factor of an odd exponent congruent to two mod three,
including repetitions, costs a separate factor of three in the balance. -/
theorem weighted_budget_of_balance {a e j : ℕ} {P X : Finset ℕ}
    (ha : Odd a) (hp : ∀ p ∈ P, p.Prime) (h3P : 3 ∉ P)
    (E : (2^a+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(a+1) * 3^e * ∏ p ∈ P, p)
    (hX : X ⊆ P) (hXr : ∀ x ∈ X, ¬ x ∣ 2^a+1) (hj : 3^j ∣ ∏ x ∈ X, (x+1)) :
    1 + padicValNat 3 a + ((a : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length + j ≤ e := by
  have ha0 : a ≠ 0 := by obtain ⟨k, hk⟩ := ha; omega
  have hsq (q : ℕ) (hprime : q.Prime) (hmod : q % 3 = 2) : ¬ q^2 ∣ 2^a+1 := by
    intro hd
    have hq : q ∣ 2^a+1 := (dvd_pow_self q (by decide : 2 ≠ 0)).trans hd
    have h2 : q ≠ 2 := by
      rintro rfl
      have := (Nat.dvd_add_right (dvd_pow_self 2 ha0)).mp hq
      omega
    exact (simple_prime_of_balance hp hprime h2 (by omega) (by simpa [mul_assoc] using E) hq).2 hd
  have hb := budget_of_balance ha0 hp h3P E hX hXr hj
  rw [threeValTexp ha, ← omegaTwo_eq_card_of_no_square (by positivity) hsq] at hb
  have hΩ := omegaTwo_le_two_pow_add_one ha
  omega

/-- The unitary-perfect balance in the three remaining odd-exponent cases
restricts the total prime-factor multiplicity of the exponent of two. -/
theorem bounded_weight_of_balance {a e : ℕ} {P : Finset ℕ}
    (ha : Odd a) (hp : ∀ p ∈ P, p.Prime) (h3P : 3 ∉ P)
    (E : (2^a+1) * (1+3^e) * ∏ p ∈ P, (p+1) = 2^(a+1) * 3^e * ∏ p ∈ P, p)
    (he : e = 11 ∨ e = 13 ∨ e = 19) :
    padicValNat 3 a + ((a : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length ≤ (if e=11 then 7 else if e=13 then 8 else 13) := by
  obtain ⟨X, hX, hXr, hj⟩ := forced_ledger hp E he
  have h := weighted_budget_of_balance ha hp h3P E hX hXr hj
  rcases he with rfl | rfl | rfl <;> norm_num at h ⊢ <;> omega

end UnitaryMultiplicity

namespace UnitaryMultiplicity

/-- The odd two-adic exponent of a unitary perfect number with unique repeated
odd prime 3 satisfies a multiplicity bound in each of the three specified
cases for the exponent of 3. -/
theorem unitaryPerfect_odd_multiplicity {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (unique_three : ∀ p, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p = 3)
    (he : n.factorization 3 = 11 ∨ n.factorization 3 = 13 ∨ n.factorization 3 = 19)
    (ha : Odd (padicValNat 2 n)) :
    padicValNat 3 (padicValNat 2 n) + (((padicValNat 2 n) : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length ≤
      if n.factorization 3 = 11 then 7 else if n.factorization 3 = 13 then 8 else 13 := by
  have hn0 : n ≠ 0 := hn.2.ne'
  have hsimple : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have hlt : ¬ 2 ≤ n.factorization r := by
      intro h
      exact hr3 ((unique_three r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr h⟩)
    omega
  have h3 : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_three, Nat.dvd_of_factorization_pos (by omega), hn0⟩
  obtain ⟨hP, balance⟩ :=
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.kernel_balance_one hn h3 (by decide) hsimple
  rw [Nat.factorization_def n Nat.prime_two] at balance
  exact bounded_weight_of_balance ha (fun p hp => (hP p hp).1) (by simp) balance he

end UnitaryMultiplicity

namespace UnitaryExponent

/-- A prime shared by the exponent and the value of a positive-sign power
appears at least twice in the value, provided the prime is odd. -/
theorem common_prime_square {p b a : ℕ} (hp : p.Prime) (ho : Odd p)
    (ha : p ∣ a) (hv : p ∣ b^a + 1) : p^2 ∣ b^a + 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, rfl⟩ := ha
  rw [Nat.mul_comm p k, pow_mul] at hv ⊢
  let x := b^k
  change p ∣ x^p + 1 at hv
  change p^2 ∣ x^p + 1
  have hzero := (ZMod.natCast_eq_zero_iff (x^p + 1) p).mpr hv
  push_cast at hzero
  have hfermat : (x : ZMod p)^p = x := by
    simpa only [ZMod.card] using FiniteField.pow_card (x : ZMod p)
  rw [hfermat] at hzero
  have hx : p ∣ x + 1 := (ZMod.natCast_eq_zero_iff (x+1) p).mp (by push_cast; exact hzero)
  have hnx : ¬ p ∣ x := by
    intro h
    have h1 : p ∣ 1 := (Nat.dvd_add_iff_right h).mpr hx
    exact hp.not_dvd_one h1
  have hval := padicValNat.pow_add_pow (x := x) (y := 1) ho hx hnx ho
  simp only [one_pow] at hval
  apply (Nat.pow_dvd_iff_le_padicValNat hp.ne_one (by positivity : x^p + 1 ≠ 0)).mpr
  have hpos := one_le_padicValNat_of_dvd (by positivity : x + 1 ≠ 0) hx
  have hpp := one_le_padicValNat_of_dvd hp.ne_zero (dvd_refl p)
  omega

/-- Lift a common prime through the standard unitary-perfect balance. -/
theorem square_dvd_number {n a b p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hbalance : b^a + 1 ∣ 2*n) (hcommon : p ∣ Nat.gcd a (b^a+1)) : p^2 ∣ n := by
  obtain ⟨ha, hv⟩ := Nat.dvd_gcd_iff.mp hcommon
  have hco : (p^2).Coprime 2 := ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_left 2
  exact hco.dvd_of_dvd_mul_left ((common_prime_square hp (hp.odd_of_ne_two hp2) ha hv).trans hbalance)

/-- Application to any prime-power component in the unitary-divisor product.
For a unitary perfect number the product identity is the established
`prod_eq_two_mul` lemma of the Erdős 1052 reduction. -/
theorem square_dvd_of_unitary_product {n p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q ∈ n.primeFactors)
    (hbalance : ∏ z ∈ n.primeFactors, (1 + z ^ n.factorization z) = 2*n)
    (hcommon : p ∣ Nat.gcd (n.factorization q) (q^(n.factorization q)+1)) : p^2 ∣ n := by
  apply square_dvd_number hp hp2 _ hcommon
  rw [← hbalance, Nat.add_comm]
  exact Finset.dvd_prod_of_mem (fun z => 1 + z ^ n.factorization z) hq

end UnitaryExponent

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    (n.factorization 3 = 11 ∨ n.factorization 3 = 13 ∨ n.factorization 3 = 19) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (n.factorization 3 = 11 → ∀ d ∈ ({4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (n.factorization 3 = 13 → ∀ d ∈ ({2, 4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (n.factorization 3 = 19 → ∀ d ∈ ({2, 8, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    Even (padicValNat 2 n) →
    (∀ p : ℕ, p.Prime → p ∣ Nat.gcd (padicValNat 2 n) (2^(padicValNat 2 n)+1) → p = 3) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    (n.factorization 3 = 11 ∨ n.factorization 3 = 13 ∨ n.factorization 3 = 19) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (n.factorization 3 = 11 → ∀ d ∈ ({4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (n.factorization 3 = 13 → ∀ d ∈ ({2, 4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (n.factorization 3 = 19 → ∀ d ∈ ({2, 8, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    Odd (padicValNat 2 n) →
    (∀ p : ℕ, p.Prime → p ∣ Nat.gcd (padicValNat 2 n) (2^(padicValNat 2 n)+1) → p = 3) →
    padicValNat 3 (padicValNat 2 n) + (((padicValNat 2 n) : ℕ).primeFactorsList.filter (fun p => p % 3 == 2)).length ≤
      (if n.factorization 3 = 11 then 7 else if n.factorization 3 = 13 then 8 else 13) →
    padicValNat 2 n ≤ A

theorem prime_in_gcd {n p : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (unique_three : ∀ q, q.Prime ∧ q ≠ 2 ∧ q^2 ∣ n ↔ q = 3)
    (hp : p.Prime) (hd : p ∣ Nat.gcd (padicValNat 2 n) (2^(padicValNat 2 n)+1)) : p = 3 := by
  have h2 : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.two_dvd_of_isUnitaryPerfect hn,
      hn.2.ne'⟩
  have ha : padicValNat 2 n ≠ 0 := by
    have h := Nat.prime_two.factorization_pos_of_dvd hn.2.ne' (Nat.dvd_of_mem_primeFactors h2)
    rw [Nat.factorization_def n Nat.prime_two] at h
    omega
  by_cases hp2 : p = 2
  · subst p
    exact (Nat.prime_two.not_dvd_one ((Nat.dvd_add_iff_right (dvd_pow_self 2 ha)).mpr
      (Nat.dvd_gcd_iff.mp hd).2)).elim
  · apply (unique_three p).mp
    refine ⟨hp, hp2, ?_⟩
    apply UnitaryExponent.square_dvd_of_unitary_product hp hp2 h2
      (OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.prod_eq_two_mul hn)
    simpa only [Nat.factorization_def n Nat.prime_two] using hd

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1.H2 := by
  rintro ⟨A, evenBound⟩ ⟨B, oddBound⟩
  refine ⟨max A B, ?_⟩
  intro n hn unique_three he common case11 case13 case19
  have hg := fun p hp hd => prime_in_gcd (n := n) (p := p) hn unique_three hp hd
  rcases Nat.even_or_odd (padicValNat 2 n) with h | h
  · exact (evenBound n hn unique_three he common case11 case13 case19 h hg).trans
      (Nat.le_max_left _ _)
  · exact (oddBound n hn unique_three he common case11 case13 case19 h hg
      (UnitaryMultiplicity.unitaryPerfect_odd_multiplicity hn unique_three he h)).trans
      (Nat.le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R2
