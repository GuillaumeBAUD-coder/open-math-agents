import OMAStatements.S_mo_418419
import Mathlib

-- Problem mo-418419: the statement claims that if R is a subring of a domain S and R is integrally closed in S,
-- then for every prime ideal P of R the extended ideal P S is prime.
-- Upstream: statements/mo-418419.lean (declaration OMA.S_mo_418419.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: take R = Z, S = Q and P = (2). Z is integrally closed in its fraction field Q and (2) is prime,
-- but 2 is a unit of Q, so the extended ideal is all of Q, which is not a prime ideal.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_418419.main) := by
  intro h
  have hic : IsIntegrallyClosedIn ℤ ℚ := (isIntegrallyClosed_iff_isIntegrallyClosedIn ℚ).mp inferInstance
  have hP : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
  have hmap := h ℤ ℚ (algebraMap ℤ ℚ).injective_int hic (Ideal.span {(2 : ℤ)}) hP
  apply hmap.ne_top
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self 2))
  rw [isUnit_iff_ne_zero]
  norm_num
