import FormalConjectures.ErdosProblems.«470»

/-!
Choose a least nondeficient divisor. A perfect divisor is immediately
pseudoperfect. Otherwise the divisor is primitive abundant, so the
classification and subset-sum checks of Liddy and Riedl apply.
Pseudoperfectness passes to positive multiples by scaling the subset.

For the large numerical bound, use a search by increasing primes and
split on a finite exponent when the product of the limiting geometric
factors reaches 2. In a terminal branch with primes bounded by 3^B and
fixed exponents bounded by K, the denominator of the limiting product
is bounded by 3^(B*(5*K+5)). Raising all free exponents to
B*(5*K+5)+4 leaves a smaller total geometric tail than that gap.
This gives a finite search without scanning the integers up to the bound.
-/

-- Credit: @dk8827

open Finset
open scoped BigOperators

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1

private theorem pseudoperfect_of_dvd {m n : ℕ} (hn : 0 < n) (h : m ∣ n)
    (hm : m.Pseudoperfect) : n.Pseudoperfect := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨hm₀, s, hs, hsum⟩ := hm
  have ha : 0 < a := by
    by_contra! h
    have ha0 : a = 0 := by omega
    simp [ha0] at hn
  let scale : ℕ ↪ ℕ :=
    ⟨fun d => d * a, fun _ _ h => Nat.eq_of_mul_eq_mul_right ha h⟩
  refine ⟨hn, s.map scale, ?_, ?_⟩
  · intro d hd
    obtain ⟨e, he, rfl⟩ := mem_map.1 hd
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.1 (hs he)
    exact Nat.mem_properDivisors.2
      ⟨Nat.mul_dvd_mul_right hdvd a, Nat.mul_lt_mul_of_pos_right hlt ha⟩
  · rw [sum_map]
    change (∑ d ∈ s, d * a) = m * a
    rw [← sum_mul, hsum]

/-- The bound from enumerating odd primitive abundant numbers with at most five prime factors. -/
def H1 : Prop :=
  ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
    (∀ d ∈ m.properDivisors, d.Deficient) →
    m ≤ 10 ^ 540879392320 ∧ ∀ p ∈ m.primeFactors, p ≤ 36550417

/-- The subset-sum check on the bounded primitive abundant numbers. -/
def H2 : Prop :=
  ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
    (∀ d ∈ m.properDivisors, d.Deficient) → m ≤ 10 ^ 540879392320 →
    (∀ p ∈ m.primeFactors, p ≤ 36550417) → m.Pseudoperfect

theorem main : H1 → H2 → type_of% @Erdos470.erdos_470.variants.odd_weird_prime_div := by
  classical
  intro bound verify n hon hwn
  have hn : 0 < n := hon.pos
  have hn0 := Nat.ne_of_gt hn
  have hs : {q : ℕ | q ∈ n.divisors ∧ q.Prime} = (n.primeFactors : Set ℕ) := by
    ext q
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Nat.mem_primeFactors, Nat.mem_divisors]
    tauto
  rw [hs, Set.ncard_coe_finset]
  by_contra! hsmall
  have hndef : ¬ n.Deficient := by
    intro h
    exact (not_lt_of_gt hwn.1) h
  have hex : ∃ m : ℕ, m ∣ n ∧ ¬ m.Deficient := ⟨n, dvd_rfl, hndef⟩
  let m := Nat.find hex
  have hmn : m ∣ n := (Nat.find_spec hex).1
  have hmndef : ¬ m.Deficient := (Nat.find_spec hex).2
  have hmodd : Odd m := hon.of_dvd_nat hmn
  have hm0 : 0 ≠ m := (Nat.ne_of_gt hmodd.pos).symm
  have hmproper (d : ℕ) (hd : d ∈ m.properDivisors) : d.Deficient := by
    have ⟨hdd, hdm⟩ := Nat.mem_properDivisors.1 hd
    by_contra hnot
    exact (not_le_of_gt hdm) (Nat.find_min' hex ⟨hdd.trans hmn, hnot⟩)
  have hmpp : m.Pseudoperfect := by
    by_cases ha : m.Abundant
    · have hc := card_le_card (Nat.primeFactors_mono hmn hn0)
      have hcl : m.primeFactors.card ≤ 5 := by omega
      obtain ⟨hmmax, hpmax⟩ := bound m hmodd ha hcl hmproper
      exact verify m hmodd ha hcl hmproper hmmax hpmax
    · exact ((Nat.perfect_iff_not_abundant_and_not_deficient hm0).2 ⟨ha, hmndef⟩).pseudoperfect
  exact hwn.2 (pseudoperfect_of_dvd hn hmn hmpp)

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1
