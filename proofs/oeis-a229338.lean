import OMAStatements.S_oeis_a229338
import Mathlib

-- Problem: A229338, product of products of elements of subsets of divisors of n.
-- Upstream: formal-conjectures statements/oeis-a229338.lean (declaration OMA.S_oeis_a229338.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: each element of a finite set S lies in 2^(|S|-1) of its subsets, so the product equals
-- (prod of S)^(2^(|S|-1)); and (prod_{d | n} d)^2 = n^tau(n) by pairing d with n/d.

namespace OMA.P_oeis_a229338

open OMA.S_oeis_a229338

theorem prod_powerset_prod (S : Finset ℕ) :
    ∏ s ∈ S.powerset, ∏ d ∈ s, d = (∏ d ∈ S, d) ^ (2 ^ (S.card - 1)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_powerset_insert ha, ih, Finset.card_insert_of_notMem ha, Finset.prod_insert ha]
    have h2 : ∏ t ∈ S.powerset, ∏ d ∈ insert a t, d = a ^ (2 ^ S.card) * ∏ t ∈ S.powerset, ∏ d ∈ t, d := by
      rw [← Finset.card_powerset S, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro t ht
      have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
      rw [Finset.prod_insert hat]
    rw [h2, ih]
    rcases Nat.eq_zero_or_pos S.card with h | h
    · rw [Finset.card_eq_zero.mp h]
      simp
    · rw [show S.card + 1 - 1 = S.card by omega, mul_pow]
      have e : 2 ^ S.card = 2 ^ (S.card - 1) + 2 ^ (S.card - 1) := by
        rw [← two_mul, ← pow_succ', Nat.sub_add_cancel h]
      rw [e, pow_add, pow_add]
      ring

theorem prod_divisors_sq (n : ℕ) : (∏ d ∈ n.divisors, d) ^ 2 = n ^ n.divisors.card := by
  rw [sq]
  nth_rewrite 1 [← Nat.prod_div_divisors n (fun d => d)]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro d hd
  exact Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)

theorem main' : ∀ n : ℕ, 1 ≤ n → a n = n ^ (n.divisors.card * 2 ^ (n.divisors.card - 2)) := by
  intro n hn
  unfold a
  rw [prod_powerset_prod]
  rcases Nat.lt_or_ge n.divisors.card 2 with h | h
  · -- only n = 1
    have h1 : n = 1 := by
      by_contra hc
      have : ({1, n} : Finset ℕ) ⊆ n.divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [Nat.mem_divisors] <;> omega
      have := Finset.card_le_card this
      rw [Finset.card_pair (Ne.symm hc)] at this
      omega
    subst h1
    simp
  · rw [show n.divisors.card - 1 = (n.divisors.card - 2) + 1 by omega, pow_succ,
      mul_comm (2 ^ (n.divisors.card - 2)) 2, pow_mul, prod_divisors_sq, ← pow_mul]

end OMA.P_oeis_a229338

theorem OMA.solution : type_of% @OMA.S_oeis_a229338.main := OMA.P_oeis_a229338.main'
