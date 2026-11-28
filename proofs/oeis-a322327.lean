import OMAStatements.S_oeis_a322327
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: for coprime m, n the prime factors of m*n are the disjoint union of those of m and n,
-- the exponent of a prime of m in m*n is its exponent in m, and omega is additive, so both factors
-- of a_k are multiplicative. For p^e (e > 0) the only prime factor is p with exponent e and
-- omega = 1, giving e * k. No computer search.

namespace OMA.A322327Proof

open OMA.S_oeis_a322327

theorem not_dvd_of_coprime {m n p : ℕ} (h : Nat.Coprime m n) (hp : p ∈ m.primeFactors) :
    ¬ p ∣ n := by
  intro hpn
  have h1 := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hpn
  rw [Nat.Coprime.gcd_eq_one h] at h1
  exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one h1

theorem prod_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    (∏ p ∈ (m * n).primeFactors, ((m * n).factorization p : ℤ)) =
      (∏ p ∈ m.primeFactors, (m.factorization p : ℤ)) *
        (∏ p ∈ n.primeFactors, (n.factorization p : ℤ)) := by
  rw [Nat.primeFactors_mul hm.ne' hn.ne', Finset.prod_union h.disjoint_primeFactors]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_mul_apply_of_coprime h,
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_coprime h hp), add_zero]
  · apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_mul_apply_of_coprime h,
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_coprime h.symm hp), zero_add]

theorem result : ∀ k : ℤ,
    a k 1 = 1 ∧
    (∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → a k (m * n) = a k m * a k n) ∧
    ∀ p e : ℕ, p.Prime → 0 < e → a k (p ^ e) = k * e := by
  intro k
  refine ⟨?_, ?_, ?_⟩
  · simp [a]
  · intro m n hm hn h
    unfold a
    rw [prod_mul hm hn h, ArithmeticFunction.cardDistinctFactors_mul h, pow_add]
    ring
  · intro p e hp he
    unfold a
    rw [Nat.primeFactors_prime_pow he.ne' hp, Finset.prod_singleton,
      ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp he.ne']
    simp [Nat.factorization_pow, hp.factorization_self]
    ring

end OMA.A322327Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a322327.main := OMA.A322327Proof.result
