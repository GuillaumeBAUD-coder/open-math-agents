import OMAStatements.S_oeis_a229338
import Mathlib

/-!
For a finite set `s`, squaring the product over subsets gives `(∏ s)^(2^|s|)` (induction on `s`:
each element lies in half of the subsets). For the divisors of `n`, pairing `d` with `n / d`
gives `(∏ d)^2 = n^tau`. So `a(n)^2 = n^(tau * 2^(tau-1)) = (n^(tau * 2^(tau-2)))^2` when
`tau >= 2`, and squaring is injective on `ℕ`. The case `n = 1` is direct.
-/

namespace R229338
open OMA.S_oeis_a229338

theorem pow_prod (s : Finset ℕ) :
    (∏ t ∈ s.powerset, ∏ d ∈ t, d) ^ 2 = (∏ d ∈ s, d) ^ (2 ^ s.card) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_powerset_insert ha, Finset.card_insert_of_notMem ha, Finset.prod_insert ha]
    have h2 : ∏ t ∈ s.powerset, ∏ d ∈ insert a t, d = ∏ t ∈ s.powerset, (a * ∏ d ∈ t, d) := by
      apply Finset.prod_congr rfl
      intro t ht
      rw [Finset.mem_powerset] at ht
      exact Finset.prod_insert (fun h => ha (ht h))
    rw [h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_powerset, pow_succ 2 s.card]
    generalize ∏ t ∈ s.powerset, ∏ d ∈ t, d = P at ih ⊢
    generalize ∏ d ∈ s, d = S at ih ⊢
    generalize 2 ^ s.card = m at ih ⊢
    calc (P * (a ^ m * P)) ^ 2 = (P ^ 2) ^ 2 * (a ^ m) ^ 2 := by ring
      _ = (S ^ m) ^ 2 * (a ^ m) ^ 2 := by rw [ih]
      _ = (a * S) ^ (m * 2) := by ring

theorem prod_div_sq (n : ℕ) : (∏ d ∈ n.divisors, d) ^ 2 = n ^ n.divisors.card := by
  rw [sq]
  nth_rewrite 2 [← Nat.prod_div_divisors n (fun d => d)]
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (fun d hd => Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd))]
  simp

theorem two_le_card (n : ℕ) (hn : 2 ≤ n) : 2 ≤ n.divisors.card := by
  have h : 1 < n.divisors.card := by
    rw [Finset.one_lt_card]
    exact ⟨1, Nat.one_mem_divisors.mpr (by omega), n, Nat.mem_divisors_self n (by omega),
      by omega⟩
  omega

theorem a_one : a 1 = 1 := by
  show ∏ s ∈ (Nat.divisors 1).powerset, ∏ d ∈ s, d = 1
  rw [Nat.divisors_one]
  decide

end R229338

theorem OMA.solution : type_of% @OMA.S_oeis_a229338.main := by
  intro n hn
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [R229338.a_one]
    simp
  · have h1 := R229338.pow_prod n.divisors
    have h2 := R229338.prod_div_sq n
    obtain ⟨k, hk⟩ : ∃ k, n.divisors.card = k + 2 :=
      ⟨n.divisors.card - 2, by have := R229338.two_le_card n h; omega⟩
    apply Nat.pow_left_injective two_ne_zero
    show (OMA.S_oeis_a229338.a n) ^ 2 = (n ^ (n.divisors.card * 2 ^ (n.divisors.card - 2))) ^ 2
    unfold OMA.S_oeis_a229338.a
    rw [h1, hk, Nat.add_sub_cancel]
    rw [hk] at h2
    generalize ∏ d ∈ n.divisors, d = D at h2 ⊢
    calc D ^ 2 ^ (k + 2) = (D ^ 2) ^ (2 ^ (k + 1)) := by ring
      _ = (n ^ (k + 2)) ^ (2 ^ (k + 1)) := by rw [h2]
      _ = (n ^ ((k + 2) * 2 ^ k)) ^ 2 := by ring
