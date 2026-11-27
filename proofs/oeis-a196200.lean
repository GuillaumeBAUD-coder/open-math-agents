import OMAStatements.S_oeis_a196200
import Mathlib

-- Problem: A196200: Numbers k such that Euler phi(Dedekind psi(k)) > k.
-- Upstream: formal-conjectures statements/oeis-a196200.lean:0 (declaration OMA.S_oeis_a196200.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- The inequality phi(psi(n)) <= n fails at n = 39270 = 2 * 3 * 5 * 7 * 11 * 17, the counterexample
-- of L. Toth recorded in Sandor's paper: psi(39270) = 3 * 4 * 6 * 8 * 12 * 18 = 124416 = 2^9 * 3^5
-- and phi(124416) = 41472 > 39270.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a196200.main) := by
  intro h
  have h1 := h 39270 (by norm_num)
  have hpf : (39270 : ℕ).primeFactors = {2, 3, 5, 7, 11, 17} := by
    have e : (39270 : ℕ) = 2 * (3 * (5 * (7 * (11 * 17)))) := by norm_num
    rw [e, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
    rfl
  have hpsi : OMA.S_oeis_a196200.psi 39270 = 124416 := by
    unfold OMA.S_oeis_a196200.psi
    rw [hpf]
    decide
  have htot : Nat.totient 124416 = 41472 := by
    have e : (124416 : ℕ) = 2 ^ 9 * 3 ^ 5 := by norm_num
    rw [e, Nat.totient_mul (by norm_num), Nat.totient_prime_pow (by norm_num) (by norm_num),
      Nat.totient_prime_pow (by norm_num) (by norm_num)]
    norm_num
  rw [hpsi, htot] at h1
  norm_num at h1
