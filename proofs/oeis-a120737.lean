import OMAStatements.S_oeis_a120737
import Mathlib

/-
A120737: if the number of divisors d(k) divides the radical rad(k), then rad(k) / d(k) = 1.

main070 shows rad(k) = d(k) in that case, by counting prime factors with multiplicity: d(k) is
the product of the e_p + 1 over the primes p dividing k, each factor at least 2, so it has at
least as many prime factors (with multiplicity) as rad(k) has, while it divides rad(k).
The radical of Mathlib is the product of the prime factors.
-/

namespace OMA.P120737
open ArithmeticFunction

lemma omega_prod {ι : Type*} (s : Finset ι) (g : ι → ℕ) (hg : ∀ i ∈ s, g i ≠ 0) :
    cardFactors (∏ i ∈ s, g i) = ∑ i ∈ s, cardFactors (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      cardFactors_mul (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

lemma omega_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ cardFactors n := by
  rw [cardFactors_apply]
  rcases h : n.primeFactorsList with _ | ⟨x, l⟩
  · rcases (Nat.primeFactorsList_eq_nil n).1 h with h | h <;> omega
  · simp

lemma main070 : ∀ k : ℕ, 1 ≤ k → k.divisors.card ∣ ∏ p ∈ k.primeFactors, p →
    ∏ p ∈ k.primeFactors, p = k.divisors.card := by
  intro k hk hdvd
  rw [Nat.card_divisors (by omega)] at hdvd ⊢
  obtain ⟨c, hc⟩ := hdvd
  have hP0 : ∏ p ∈ k.primeFactors, p ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hT0 : ∏ p ∈ k.primeFactors, (k.factorization p + 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p _ => Nat.succ_ne_zero _
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hP0 (by simpa using hc)
  have h1 : cardFactors (∏ p ∈ k.primeFactors, p) = k.primeFactors.card := by
    rw [omega_prod _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero,
      Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun p hp =>
      cardFactors_apply_prime (Nat.prime_of_mem_primeFactors hp)
  have h2 : k.primeFactors.card ≤
      cardFactors (∏ p ∈ k.primeFactors, (k.factorization p + 1)) := by
    rw [omega_prod _ _ fun p _ => Nat.succ_ne_zero _, Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun p hp => omega_pos ?_
    have := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd (by omega)
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  have h3 := congrArg cardFactors hc
  rw [cardFactors_mul hT0 hc0, h1] at h3
  have hc1 : c = 1 := by
    by_contra hne
    have := omega_pos (n := c) (by omega)
    omega
  rw [hc, hc1, mul_one]

lemma main' :
    ∀ k : ℕ, 0 < k → k.divisors.card ∣ UniqueFactorizationMonoid.radical k →
      UniqueFactorizationMonoid.radical k / k.divisors.card = 1 := by
  intro k hk h
  rw [Nat.radical_eq_prod_primeFactors] at h ⊢
  rw [main070 k hk h]
  exact Nat.div_self (Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 hk.ne'⟩)

end OMA.P120737

theorem OMA.solution : type_of% @OMA.S_oeis_a120737.main := OMA.P120737.main'
