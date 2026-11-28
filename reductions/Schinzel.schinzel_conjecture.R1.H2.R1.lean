import OMAReductions.R_Schinzel_schinzel_conjecture_R1

-- Reduction Schinzel.schinzel_conjecture.R1.H2.R1 of step Schinzel.schinzel_conjecture.R1.H2
-- Credit: @arindale
--
-- The open half of Schinzel's hypothesis H splits by the number of polynomials:
-- * H1 is the single-polynomial case outside Dirichlet's linear case: one
--   irreducible polynomial of degree at least two with no fixed prime divisor
--   (Bunyakovsky's conjecture for one polynomial, e.g. n^2+1).
-- * H2 is the case of at least two polynomials, where simultaneous primality of a
--   tuple is the prime-tuples problem (e.g. twin primes).
-- The parent reduction already removed the one-linear-polynomial case (Dirichlet's
-- theorem).  The combination is a cardinality case split, and the two resulting
-- targets are independent open problems.

namespace OMA.R_Schinzel_schinzel_conjecture_R1_H2_R1

open Polynomial

/-- At most one polynomial, not of degree one: Bunyakovsky's conjecture for a single
polynomial of degree at least two.  (`BunyakovskyCondition` gives degree at least one,
so `natDegree ≠ 1` means degree at least two; the empty set is vacuous here.) -/
def H1 : Prop :=
  ∀ fs : Finset ℤ[X], (∀ f ∈ fs, BunyakovskyCondition f) → SchinzelCondition fs →
    fs.card ≤ 1 → ¬ (∀ f ∈ fs, f.natDegree = 1) →
    Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}

/-- At least two polynomials: the prime-tuples case. -/
def H2 : Prop :=
  ∀ fs : Finset ℤ[X], (∀ f ∈ fs, BunyakovskyCondition f) → SchinzelCondition fs →
    2 ≤ fs.card →
    Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}

theorem main : H1 → H2 → OMA.R_Schinzel_schinzel_conjecture_R1.H2 := by
  intro h1 h2 fs hfs hfs' hnot
  by_cases hc : fs.card ≤ 1
  · exact h1 fs hfs hfs' hc (fun hall => hnot ⟨hc, hall⟩)
  · have hc2 : 2 ≤ fs.card := by omega
    exact h2 fs hfs hfs' hc2

end OMA.R_Schinzel_schinzel_conjecture_R1_H2_R1
