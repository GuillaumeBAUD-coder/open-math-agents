import OMAReductions.R_oeis_a300984_R1
import Mathlib

namespace OMA.DivisorSums

open Finset ArithmeticFunction OMA.S_oeis_a300984

private theorem squarefreeProduct (n : ℕ) (hn : n ≠ 0) :
    squarefreeSum n = ∏ p ∈ n.primeFactors, (1 + p) := by
  rw [Finset.prod_one_add, squarefreeSum, Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq]
  exact Finset.sum_congr rfl fun subset _ => Finset.prod_val subset

theorem formula : OMA.R_oeis_a300984_R1.H1 := by
  intro p i j hp hne hj
  change squarefreeSum (2^i * p^j) = (if i = 0 then 1 else 3) * (1 + p) ∧
    nonsquarefreeSum (2^i * p^j) =
      (∑ a ∈ range (i + 1), 2^a) * (∑ b ∈ range (j + 1), p^b) -
        (if i = 0 then 1 else 3) * (1 + p)
  have hpj : (p^j).primeFactors = {p} := Nat.primeFactors_prime_pow hj.ne' hp
  have hSquarefree :
      squarefreeSum (2^i * p^j) = (if i = 0 then 1 else 3) * (1 + p) := by
    cases i with
    | zero => simp [squarefreeProduct, hp.ne_zero, hpj]
    | succ i =>
      rw [squarefreeProduct _ (mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ hp.ne_zero)),
        Nat.primeFactors_mul (pow_ne_zero _ (by decide)) (pow_ne_zero _ hp.ne_zero),
        Nat.primeFactors_prime_pow (Nat.succ_ne_zero i) Nat.prime_two, hpj]
      simp [hne.symm]
  have hTotal : ∑ d ∈ (2^i * p^j).divisors, d =
      (∑ a ∈ range (i + 1), 2^a) * (∑ b ∈ range (j + 1), p^b) := by
    rw [← sigma_one_apply,
      isMultiplicative_sigma.map_mul_of_coprime (Nat.coprime_pow_primes i j Nat.prime_two hp hne.symm)]
    simp only [sigma_apply_prime_pow Nat.prime_two, sigma_apply_prime_pow hp, mul_one]
  have hPartition : squarefreeSum (2^i * p^j) + nonsquarefreeSum (2^i * p^j) =
      ∑ d ∈ (2^i * p^j).divisors, d :=
    Finset.sum_filter_add_sum_filter_not _ Squarefree id
  exact ⟨hSquarefree, by omega⟩

end OMA.DivisorSums

theorem OMA.solution : OMA.R_oeis_a300984_R1.H1 := OMA.DivisorSums.formula