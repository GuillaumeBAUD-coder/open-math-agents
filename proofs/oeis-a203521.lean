import OMAStatements.S_oeis_a203521

-- Problem: A203521: a(n) = Product_{1 <= i < j <= n} (prime(i) + prime(j)).
-- Upstream: formal-conjectures statements/oeis-a203521.lean:0 (declaration OMA.S_oeis_a203521.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 2 is a counterexample. a(2) = prime(1) + prime(2) = 2 + 3 = 5, and
-- A000178(2) = 0! * 1! * 2! = 2 does not divide 5.

open OMA.S_oeis_a203521 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a203521.main) := by
  intro H
  have h := H 2
  have ha : a 2 = 5 := by
    simp [a, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  have hs : sf 2 = 2 := by
    simp [sf, Finset.prod_range_succ, Nat.factorial]
  rw [ha, hs] at h
  omega
