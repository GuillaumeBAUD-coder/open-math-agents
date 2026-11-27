import OMAReductions.R_Erdos647_erdos_647_R1

-- Credit: @yves-pires

namespace Erdos647DivisorBound

open ArithmeticFunction.sigma
open scoped BigOperators

-- Exponents maximizing the local ratio (a+1)^6 / p^a.
def peakExponent (p : ℕ) : ℕ :=
  if p.Prime ∧ p < 64 then
    if p = 2 then 8 else if p = 3 then 4 else if p = 5 then 3
    else if p = 7 ∨ p = 11 then 2 else 1
  else 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
lemma smallPrimePowers : ∀ p : Fin 64, ∀ a : Fin 9, p.val.Prime →
    (a.val + 1) ^ 6 * p.val ^ peakExponent p.val ≤
      (peakExponent p.val + 1) ^ 6 * p.val ^ a.val := by
  decide

lemma growth (a : ℕ) (ha : 8 ≤ a) : (a + 2) ^ 6 ≤ 2 * (a + 1) ^ 6 := by
  have h : (a + 2) * 9 ≤ (a + 1) * 10 := by omega
  have hp := Nat.pow_le_pow_left h 6
  rw [mul_pow, mul_pow] at hp
  change (a + 2) ^ 6 * 531441 ≤ (a + 1) ^ 6 * 1000000 at hp
  omega

lemma atPrime (p : ℕ) (hp : p.Prime) (a : ℕ) :
    (a + 1) ^ 6 * p ^ peakExponent p ≤ (peakExponent p + 1) ^ 6 * p ^ a := by
  by_cases hbig : 64 ≤ p
  · have he : peakExponent p = 0 := by simp [peakExponent, show ¬ p < 64 by omega]
    simp only [he, pow_zero, mul_one, Nat.zero_add, one_pow, one_mul]
    calc
      (a + 1) ^ 6 ≤ (2 ^ a) ^ 6 := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := a)) 6
      _ = 64 ^ a := by rw [← pow_mul, Nat.mul_comm a 6, pow_mul, show (2 : ℕ)^6 = 64 by decide]
      _ ≤ p ^ a := Nat.pow_le_pow_left hbig a
  · have hp64 : p < 64 := by omega
    induction a with
    | zero => exact smallPrimePowers ⟨p, hp64⟩ ⟨0, by decide⟩ hp
    | succ a ih =>
      by_cases ha : a + 1 < 9
      · exact smallPrimePowers ⟨p, hp64⟩ ⟨a + 1, ha⟩ hp
      · have hstep : (a + 2) ^ 6 ≤ p * (a + 1) ^ 6 :=
          (growth a (by omega)).trans (Nat.mul_le_mul_right _ hp.two_le)
        calc
          (a + 2) ^ 6 * p ^ peakExponent p ≤ (p * (a + 1) ^ 6) * p ^ peakExponent p :=
            Nat.mul_le_mul_right _ hstep
          _ = p * ((a + 1) ^ 6 * p ^ peakExponent p) := Nat.mul_assoc _ _ _
          _ ≤ p * ((peakExponent p + 1) ^ 6 * p ^ a) := Nat.mul_le_mul_left _ ih
          _ = (peakExponent p + 1) ^ 6 * p ^ (a + 1) := by rw [pow_succ p a]; ac_rfl

set_option maxRecDepth 4096 in
lemma peakProduct :
    (∏ p ∈ Finset.range 64, (peakExponent p + 1) ^ 6) ≤
      139 ^ 6 * (∏ p ∈ Finset.range 64, p ^ peakExponent p) := by decide

set_option maxRecDepth 4096 in
lemma denominatorPos : 0 < (∏ p ∈ Finset.range 64, p ^ peakExponent p) := by decide

theorem divisorBound (m : ℕ) : (σ 0 m) ^ 6 ≤ 139 ^ 6 * m := by
  by_cases hm : m = 0
  · subst m; simp
  let S := Finset.range 64 ∪ m.primeFactors
  have hr : Finset.range 64 ⊆ S := Finset.subset_union_left
  have hf : m.primeFactors ⊆ S := Finset.subset_union_right
  have hout {p : ℕ} (h : p ∉ m.primeFactors) : m.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp h
  have heout {p : ℕ} (h : p ∉ Finset.range 64) : peakExponent p = 0 := by
    simp [peakExponent, show ¬ p < 64 from fun hp => h (Finset.mem_range.mpr hp)]
  have hden : (∏ p ∈ S, p ^ peakExponent p) =
      ∏ p ∈ Finset.range 64, p ^ peakExponent p :=
    (Finset.prod_subset hr (fun p _ h => by simp [heout h])).symm
  have hnum : (∏ p ∈ S, (peakExponent p + 1) ^ 6) =
      ∏ p ∈ Finset.range 64, (peakExponent p + 1) ^ 6 :=
    (Finset.prod_subset hr (fun p _ h => by simp [heout h])).symm
  have hvalue : (∏ p ∈ S, p ^ m.factorization p) = m := by
    calc
      _ = ∏ p ∈ m.primeFactors, p ^ m.factorization p :=
        (Finset.prod_subset hf (fun p _ h => by simp [hout h])).symm
      _ = m := (Nat.prod_primeFactors_pow_factorization hm).symm
  have hcount : (∏ p ∈ S, (m.factorization p + 1)) = σ 0 m := by
    calc
      _ = ∏ p ∈ m.primeFactors, (m.factorization p + 1) :=
        (Finset.prod_subset hf (fun p _ h => by simp [hout h])).symm
      _ = σ 0 m := by
        simpa using
          (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
            (k := 0) hm).symm
  have hprod : (∏ p ∈ S, (m.factorization p + 1) ^ 6 * p ^ peakExponent p) ≤
      ∏ p ∈ S, (peakExponent p + 1) ^ 6 * p ^ m.factorization p := by
    apply Finset.prod_le_prod'
    intro p _
    by_cases hp : p.Prime
    · exact atPrime p hp _
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp, peakExponent, hp]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hden, hnum, hvalue,
    Finset.prod_pow, hcount] at hprod
  have h := hprod.trans (Nat.mul_le_mul_right m peakProduct)
  rw [mul_right_comm (139 ^ 6)] at h
  exact Nat.le_of_mul_le_mul_right h denominatorPos

end Erdos647DivisorBound

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R1.H1 :=
  Erdos647DivisorBound.divisorBound
