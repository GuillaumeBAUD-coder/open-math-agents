import OMAStatements.S_oeis_a055231
import Mathlib

/-! Proof for OEIS A055231: the valuation of `a(n)` at a prime `p` is `1` if `v_p(n) = 1` and `0` otherwise; comparing
valuations of `a(nm) · gcd(n, a(m)) · gcd(m, a(n))` and `a(n) a(m)` at every prime reduces the
identity to a case check on `v_p(n)` and `v_p(m)`.
Credit: Sudharsan Rajendiran -/

namespace OMA.P055231
open OMA.S_oeis_a055231

lemma a_ne_zero (n : ℕ) : a n ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).ne_zero

lemma fa (n p : ℕ) : (a n).factorization p = if n.factorization p = 1 then 1 else 0 := by
  unfold a
  rw [Nat.factorization_prod fun q hq =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1).ne_zero]
  rw [Finset.sum_apply']
  rw [Finset.sum_congr rfl fun q hq => by
    rw [(Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1).factorization,
      Finsupp.single_apply]]
  rw [Finset.sum_ite_eq']
  by_cases h : n.factorization p = 1
  · have hp : p ∈ n.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
    simp [h, hp]
  · simp [h]

end OMA.P055231

theorem OMA.solution : type_of% @OMA.S_oeis_a055231.main := by
  intro n m hn hm
  have h1 := OMA.P055231.a_ne_zero n
  have h2 := OMA.P055231.a_ne_zero m
  have h3 := OMA.P055231.a_ne_zero (n * m)
  have g1 : Nat.gcd n (OMA.S_oeis_a055231.a m) ≠ 0 := (Nat.gcd_pos_of_pos_left _ hn).ne'
  have g2 : Nat.gcd m (OMA.S_oeis_a055231.a n) ≠ 0 := (Nat.gcd_pos_of_pos_left _ hm).ne'
  symm
  apply Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero (Nat.mul_ne_zero g1 g2))
  symm
  apply Nat.eq_of_factorization_eq (Nat.mul_ne_zero h3 (Nat.mul_ne_zero g1 g2)) (Nat.mul_ne_zero h1 h2)
  intro p
  rw [Nat.factorization_mul h3 (Nat.mul_ne_zero g1 g2), Nat.factorization_mul g1 g2,
    Nat.factorization_gcd (by omega) h2, Nat.factorization_gcd (by omega) h1,
    Nat.factorization_mul h1 h2]
  simp only [Finsupp.add_apply, Finsupp.inf_apply, OMA.P055231.fa]
  rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply]
  split_ifs <;> omega
