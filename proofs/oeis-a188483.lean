import OMAStatements.S_oeis_a188483
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Tactic

-- Problem: A188483: Kravitz conjecture (no n has abundance sigma(n) - 2n a positive odd square).
-- Upstream: formal-conjectures statements/oeis-a188483.lean
-- Credit: @LordDavidDev (the owner of the agent is credited as the solver)
--
-- The conjecture is false. The smallest counterexample is
--   n = 550564 = 742^2 = 2^2 * 7^2 * 53^2,
-- with sigma(n) = 7 * 57 * 2863 = 1142337 = 2 * 550564 + 41209 and
-- 41209 = 203^2 = (2 * 101 + 1)^2, so the abundance of 550564 is the positive odd square 203^2.
-- (The OEIS entry A188483 collects the numbers whose squares have an odd square abundance, and
-- starts with 742; 742^2 = 550564 is the smallest counterexample.)
-- sigma is computed from its multiplicativity (`Nat.Coprime.divisors_mul`) and
-- `Nat.divisors_prime_pow`, so no large `Nat.divisors` has to be evaluated in the kernel.

open OMA.S_oeis_a188483

private lemma sigma_prime_sq (p : ℕ) (hp : p.Prime) : sigma (p ^ 2) = 1 + p + p ^ 2 := by
  rw [sigma, Nat.divisors_prime_pow hp 2, Finset.sum_map]
  simp [Finset.sum_range_succ, pow_succ]

private lemma sigma_mul_coprime {m n : ℕ} (h : m.Coprime n) :
    sigma (m * n) = sigma m * sigma n := by
  rw [sigma, sigma, sigma, Nat.divisors_mul, Finset.mul_def, Finset.sum_image]
  · rw [Finset.sum_product, Finset.sum_mul_sum]
  · intro x hx y hy hxy
    exact h.mul_injOn_divisors hx hy hxy

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a188483.main) := by
  intro h
  have h1 : sigma 550564 = 2 * 550564 + (2 * 101 + 1) ^ 2 := by
    have hfac : 550564 = 2 ^ 2 * (7 ^ 2 * 53 ^ 2) := by norm_num
    rw [hfac, sigma_mul_coprime (by norm_num), sigma_mul_coprime (by norm_num),
      sigma_prime_sq 2 (by norm_num), sigma_prime_sq 7 (by norm_num),
      sigma_prime_sq 53 (by norm_num)]
    norm_num
  exact h 550564 (by norm_num) ⟨101, h1⟩
