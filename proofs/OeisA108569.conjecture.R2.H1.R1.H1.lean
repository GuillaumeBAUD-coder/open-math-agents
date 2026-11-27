import OMAReductions.R_OeisA108569_conjecture_R2_H1_R1
import Mathlib

/-! Step OeisA108569.conjecture.R2.H1.R1.H1. Credit: @ivillar (original proof). With m = 2p - 1, a collision means
2 phi(m) + 1 = m. Since phi(m) * prod q = m * prod (q - 1) over the prime factors of m, and for at
most two distinct odd primes prod q <= 2 prod (q - 1), this is impossible. -/

namespace OMA108569

open Finset

lemma prod_le (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime ∧ q % 2 = 1) (hc : S.card ≤ 2) :
    ∏ q ∈ S, q ≤ 2 * ∏ q ∈ S, (q - 1) := by
  have h3 : ∀ q ∈ S, 3 ≤ q := fun q hq => by
    have := (hS q hq).1.two_le; have := (hS q hq).2; omega
  rcases Nat.lt_or_ge S.card 2 with h | h
  · rcases Nat.lt_or_ge S.card 1 with h0 | h1
    · have : S = ∅ := Finset.card_eq_zero.mp (show S.card = 0 by omega)
      subst this; simp
    · obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
      simp only [prod_singleton]
      have := h3 q (mem_singleton_self q)
      omega
  · obtain ⟨q, r, hqr, rfl⟩ := Finset.card_eq_two.mp (show S.card = 2 by omega)
    rw [prod_pair hqr, prod_pair hqr]
    have hq3 := h3 q (by simp)
    have hr3 := h3 r (by simp)
    have hqo := (hS q (by simp)).2
    have hro := (hS r (by simp)).2
    have key : 2 ≤ (q - 2) * (r - 2) := by
      rcases Nat.lt_or_gt_of_ne hqr with hlt | hlt
      · have : 5 ≤ r := by omega
        have : 1 ≤ q - 2 := by omega
        have : 3 ≤ r - 2 := by omega
        nlinarith
      · have : 5 ≤ q := by omega
        have : 3 ≤ q - 2 := by omega
        have : 1 ≤ r - 2 := by omega
        nlinarith
    obtain ⟨a, rfl⟩ : ∃ a, q = a + 3 := ⟨q - 3, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, r = b + 3 := ⟨r - 3, by omega⟩
    simp only [show a + 3 - 2 = a + 1 by omega, show b + 3 - 2 = b + 1 by omega] at key
    simp only [show a + 3 - 1 = a + 2 by omega, show b + 3 - 1 = b + 2 by omega]
    nlinarith

theorem main_H1 : OMA.R_OeisA108569_conjecture_R2_H1_R1.H1 := by
  intro p hp hodd hcard heq
  rw [Nat.totient_prime hp] at heq hcard
  set m := p + (p - 1) with hm
  have hp3 : 3 ≤ p := by have := hp.two_le; obtain ⟨k, hk⟩ := hodd; omega
  have hmodd : m % 2 = 1 := by omega
  have hS : ∀ q ∈ m.primeFactors, q.Prime ∧ q % 2 = 1 := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    refine ⟨hqp, ?_⟩
    rcases hqp.eq_two_or_odd with h2 | h2
    · exfalso
      have := Nat.dvd_of_mem_primeFactors hq
      rw [h2] at this
      omega
    · exact h2
  have hP := prod_le m.primeFactors hS hcard
  have hQpos : 0 < ∏ q ∈ m.primeFactors, (q - 1) :=
    Finset.prod_pos fun q hq => by have := (hS q hq).1.two_le; omega
  have hT := Nat.totient_mul_prod_primeFactors m
  rw [← heq] at hT
  set P := ∏ q ∈ m.primeFactors, q with hPdef
  set Q := ∏ q ∈ m.primeFactors, (q - 1) with hQdef
  have hm2 : m = 2 * (p - 1) + 1 := by omega
  rw [hm2] at hT
  have h1 : (p - 1) * P ≤ (p - 1) * (2 * Q) := Nat.mul_le_mul_left _ hP
  nlinarith

end OMA108569

theorem OMA.solution : OMA.R_OeisA108569_conjecture_R2_H1_R1.H1 := OMA108569.main_H1
