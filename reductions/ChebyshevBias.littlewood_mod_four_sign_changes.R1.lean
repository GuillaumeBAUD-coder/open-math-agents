import FormalConjectures.Wikipedia.ChebyshevBias

-- Reduction ChebyshevBias.littlewood_mod_four_sign_changes.R1 of Chebyshev's bias — littlewood mod
-- four sign changes
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is a conjunction of two independent oscillation statements, one per direction in
-- which the count of primes 3 mod 4 leads the count of primes 1 mod 4. Each direction is a
-- separate theorem, so each is its own attackable step.

namespace OMA.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1

/-- The direction `π(n; 4, 3) > π(n; 4, 1)` happens for infinitely many `n`, i.e. the set of
arguments on which the `3 mod 4` primes lead is infinite. -/
def H1 : Prop := ChebyshevBias.chebyshevModFourLeadSet.Infinite

/-- The opposite direction `π(n; 4, 1) > π(n; 4, 3)` happens for infinitely many `n`. -/
def H2 : Prop := {n : ℕ | n.primeCountingMod 4 3 < n.primeCountingMod 4 1}.Infinite

theorem main : H1 → H2 → type_of% @ChebyshevBias.littlewood_mod_four_sign_changes := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1
