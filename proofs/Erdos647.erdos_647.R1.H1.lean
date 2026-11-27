import OMAReductions.R_Erdos647_erdos_647_R1
import Mathlib

-- Step Erdos647.erdos_647.R1.H1: hypothesis H1 of reduction Erdos647.erdos_647.R1
-- Credit: @ivillar
--
-- tau(m)^6 / m is multiplicative: it is the product over p^e || m of (e+1)^6 / p^e. For each prime
-- p this factor is at most (a+1)^6 / p^a for an explicit exponent a = ex p (the maximiser), and it
-- is at most 1 for p >= 64. The product of the 18 maximal factors (primes below 64) is about
-- 138.3^6, below 139^6. All comparisons are done in N by cross-multiplication.

namespace OMA.Erdos647H1

open Finset

/-- The maximising exponent of (e+1)^6 / p^e (0 for primes p >= 64). -/
def ex : ℕ → ℕ
  | 2 => 8
  | 3 => 4
  | 5 => 3
  | 7 => 2
  | 11 => 2
  | 13 => 1
  | 17 => 1
  | 19 => 1
  | 23 => 1
  | 29 => 1
  | 31 => 1
  | 37 => 1
  | 41 => 1
  | 43 => 1
  | 47 => 1
  | 53 => 1
  | 59 => 1
  | 61 => 1
  | _ => 0

/-- The primes below 64. -/
def T : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61}

lemma fz {m p : ℕ} (h : p ∉ m.primeFactors) : m.factorization p = 0 :=
  Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])

lemma ex_eq_zero {p : ℕ} (hp : p ∉ T) : ex p = 0 := by
  unfold T at hp
  simp only [mem_insert, mem_singleton, not_or] at hp
  unfold ex
  split <;> simp_all

lemma ge_64 {p : ℕ} (hp : p.Prime) (hT : p ∉ T) : 64 ≤ p := by
  by_contra h
  push Not at h
  unfold T at hT
  simp only [mem_insert, mem_singleton, not_or] at hT
  interval_cases p <;> first | (norm_num at hp; done) | (simp at hT; done)

/-- Beyond the maximiser the ratio keeps decreasing. -/
lemma key (p a : ℕ) (hstep : (a + 2) ^ 6 ≤ p * (a + 1) ^ 6)
    (hsmall : ∀ e ≤ a, (e + 1) ^ 6 * p ^ a ≤ (a + 1) ^ 6 * p ^ e) :
    ∀ e, (e + 1) ^ 6 * p ^ a ≤ (a + 1) ^ 6 * p ^ e := by
  intro e
  rcases le_or_gt e a with h | h
  · exact hsmall e h
  obtain ⟨d, rfl⟩ : ∃ d, e = a + d := ⟨e - a, by omega⟩
  clear h
  induction d with
  | zero => exact hsmall a le_rfl
  | succ d ih =>
    have hmono : (a + d + 2) * (a + 1) ≤ (a + 2) * (a + d + 1) := by nlinarith
    have hmono6 : ((a + d + 2) * (a + 1)) ^ 6 ≤ ((a + 2) * (a + d + 1)) ^ 6 :=
      Nat.pow_le_pow_left hmono 6
    have hratio : (a + d + 2) ^ 6 ≤ p * (a + d + 1) ^ 6 := by
      rw [mul_pow, mul_pow] at hmono6
      have h1 : (a + d + 2) ^ 6 * (a + 1) ^ 6 ≤ (p * (a + d + 1) ^ 6) * (a + 1) ^ 6 := by
        calc (a + d + 2) ^ 6 * (a + 1) ^ 6 ≤ (a + 2) ^ 6 * (a + d + 1) ^ 6 := hmono6
          _ ≤ (p * (a + 1) ^ 6) * (a + d + 1) ^ 6 := Nat.mul_le_mul_right _ hstep
          _ = (p * (a + d + 1) ^ 6) * (a + 1) ^ 6 := by ring
      exact Nat.le_of_mul_le_mul_right h1 (by positivity)
    calc (a + (d + 1) + 1) ^ 6 * p ^ a = (a + d + 2) ^ 6 * p ^ a := by ring_nf
      _ ≤ (p * (a + d + 1) ^ 6) * p ^ a := Nat.mul_le_mul_right _ hratio
      _ = p * ((a + d + 1) ^ 6 * p ^ a) := by ring
      _ ≤ p * ((a + 1) ^ 6 * p ^ (a + d)) := Nat.mul_le_mul_left _ ih
      _ = (a + 1) ^ 6 * p ^ (a + (d + 1)) := by ring

lemma large (p e : ℕ) (hp : 64 ≤ p) : (e + 1) ^ 6 ≤ p ^ e := by
  have h1 : e + 1 ≤ 2 ^ e := Nat.lt_two_pow_self
  calc (e + 1) ^ 6 ≤ (2 ^ e) ^ 6 := Nat.pow_le_pow_left h1 6
    _ = 64 ^ e := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    _ ≤ p ^ e := Nat.pow_le_pow_left hp e

lemma local_bound (p e : ℕ) (hp : p.Prime) :
    (e + 1) ^ 6 * p ^ ex p ≤ (ex p + 1) ^ 6 * p ^ e := by
  by_cases hT : p ∈ T
  · unfold T at hT
    simp only [mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
    exact key _ _ (by norm_num [ex]) (by simp only [ex]; decide) e
  · rw [ex_eq_zero hT]
    simpa using large p e (ge_64 hp hT)

lemma prod_T : (∏ p ∈ T, (ex p + 1) ^ 6) ≤ 139 ^ 6 * ∏ p ∈ T, p ^ ex p := by
  unfold T
  simp only [ex]
  decide

end OMA.Erdos647H1

open OMA.Erdos647H1 Finset in
theorem OMA.solution : OMA.R_Erdos647_erdos_647_R1.H1 := by
  unfold OMA.R_Erdos647_erdos_647_R1.H1
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm0 : m ≠ 0 := hm.ne'
  rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hm0]
  set S := m.primeFactors
  set U := S ∪ T
  have hτ : ∏ p ∈ S, (m.factorization p + 1) = ∏ p ∈ U, (m.factorization p + 1) := by
    apply prod_subset subset_union_left
    intro p _ hpS
    simp [fz hpS]
  have hmprod : m = ∏ p ∈ U, p ^ m.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm0]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    apply prod_subset subset_union_left
    intro p _ hpS
    simp [fz hpS]
  have hD : ∏ p ∈ U, p ^ ex p = ∏ p ∈ T, p ^ ex p := by
    symm
    apply prod_subset subset_union_right
    intro p _ hpT
    simp [ex_eq_zero hpT]
  have hN : ∏ p ∈ U, (ex p + 1) ^ 6 = ∏ p ∈ T, (ex p + 1) ^ 6 := by
    symm
    apply prod_subset subset_union_right
    intro p _ hpT
    simp [ex_eq_zero hpT]
  have hUprime : ∀ p ∈ U, p.Prime ∨ m.factorization p = 0 := by
    intro p hp
    by_cases hpS : p ∈ S
    · exact Or.inl (Nat.prime_of_mem_primeFactors hpS)
    · exact Or.inr (fz hpS)
  have hlocal : ∀ p ∈ U, (m.factorization p + 1) ^ 6 * p ^ ex p ≤
      (ex p + 1) ^ 6 * p ^ m.factorization p := by
    intro p hp
    rcases hUprime p hp with hpr | h0
    · exact local_bound p _ hpr
    · rw [h0]
      by_cases hpT : p ∈ T
      · unfold T at hpT
        simp only [mem_insert, mem_singleton] at hpT
        rcases hpT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [ex]
      · simp [ex_eq_zero hpT]
  have hprod := prod_le_prod' hlocal
  rw [prod_mul_distrib, prod_mul_distrib, hD, hN, ← hmprod] at hprod
  rw [hτ, ← prod_pow]
  have hDpos : 0 < ∏ p ∈ T, p ^ ex p := by
    apply prod_pos
    intro p hp
    unfold T at hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> norm_num
  have h2 := prod_T
  have h3 : (∏ p ∈ U, (m.factorization p + 1) ^ 6) * ∏ p ∈ T, p ^ ex p ≤
      (139 ^ 6 * m) * ∏ p ∈ T, p ^ ex p := by
    calc (∏ p ∈ U, (m.factorization p + 1) ^ 6) * ∏ p ∈ T, p ^ ex p
        ≤ (∏ p ∈ T, (ex p + 1) ^ 6) * m := hprod
      _ ≤ (139 ^ 6 * ∏ p ∈ T, p ^ ex p) * m := Nat.mul_le_mul_right _ h2
      _ = (139 ^ 6 * m) * ∏ p ∈ T, p ^ ex p := by ring
  exact Nat.le_of_mul_le_mul_right h3 hDpos
