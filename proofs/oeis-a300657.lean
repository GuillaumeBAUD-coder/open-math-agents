import OMAStatements.S_oeis_a300657
import Mathlib

-- Problem: oeis-a300657, a(n) = sum over d | n of (sigma(d) mod d) equals sigma(n) mod n
-- exactly when n is 1 or a prime.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- For a prime p, sigma(p) mod p = 1. If n > 1 is composite, its least prime factor p is a
-- proper divisor, so the sum contains the two distinct terms for p and n and is at least
-- 1 + sigma(n) mod n. For n = 1 and n prime both sides are computed directly.

theorem OMA.solution : type_of% @OMA.S_oeis_a300657.main := by
  intro n hn
  have hsig : ∀ p : ℕ, p.Prime → ArithmeticFunction.sigma 1 p % p = 1 := by
    intro p hp
    rw [ArithmeticFunction.sigma_one_apply, hp.sum_divisors, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hp.one_lt
  constructor
  · intro h
    by_contra hcon
    rw [not_or] at hcon
    have hn2 : 2 ≤ n := by omega
    obtain ⟨p, hpdef⟩ : ∃ p, p = n.minFac := ⟨_, rfl⟩
    have hp : p.Prime := by rw [hpdef]; exact Nat.minFac_prime (by omega)
    have hpn : p ∣ n := by rw [hpdef]; exact Nat.minFac_dvd n
    have hpne : p ≠ n := fun h' => hcon.2 (h' ▸ hp)
    have hsub : ({p, n} : Finset ℕ) ⊆ n.divisors := by
      intro d hd
      rw [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h1 | h1
      · rw [h1]; exact Nat.mem_divisors.mpr ⟨hpn, by omega⟩
      · rw [h1]; exact Nat.mem_divisors_self n (by omega)
    have hle := Finset.sum_le_sum_of_subset (f := fun d => ArithmeticFunction.sigma 1 d % d) hsub
    rw [Finset.sum_pair hpne] at hle
    beta_reduce at hle
    rw [hsig p hp] at hle
    unfold OMA.S_oeis_a300657.a OMA.S_oeis_a300657.b at h
    omega
  · intro h
    rcases h with h1 | hp
    · rw [h1]
      simp [OMA.S_oeis_a300657.a, OMA.S_oeis_a300657.b]
    · unfold OMA.S_oeis_a300657.a OMA.S_oeis_a300657.b
      rw [hp.divisors, Finset.sum_pair hp.ne_one.symm]
      simp
