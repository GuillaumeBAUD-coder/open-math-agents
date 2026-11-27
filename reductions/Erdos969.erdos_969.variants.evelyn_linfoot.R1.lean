import FormalConjectures.ErdosProblems.«969»

/-!
The Dirichlet series of the squarefree indicator is ζ(s)/ζ(2s).
An error of order o(x^(1/4)) would force the numerator to vanish at
each nonreal zero of the denominator on or to the right of Re s = 1/4.

For the integral transform behind this argument, see Mossinghoff,
Oliveira e Silva and Trudgian, The distribution of k-free numbers,
equations (4) and (5), https://arxiv.org/abs/1912.04972.
-/

namespace OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1

open Filter Asymptotics

/-- Half of a nontrivial zeta zero of least positive height gives such a point.
The functional equation allows the zero to be chosen with real part at least one half. -/
def H1 : Prop :=
  ∃ z : ℂ, (1 / 4 : ℝ) ≤ z.re ∧ z.im ≠ 0 ∧
    riemannZeta (2 * z) = 0 ∧ riemannZeta z ≠ 0

/-- Every positive integer is uniquely a square times a squarefree integer.
Multiplication of the two absolutely convergent series gives this identity. -/
def H2 : Prop :=
  ∀ s : ℂ, 1 < s.re →
    LSeries (fun n : ℕ => (Erdos969.squarefreeCounting n : ℂ) -
      (Erdos969.squarefreeCounting (n - 1) : ℂ)) s * riemannZeta (2 * s) = riemannZeta s

/-- Abelian boundary estimate for first differences of a counting function.
Partial summation continues the error transform to Re s > 1/4. At the boundary,
its product with a positive real increment tends to zero as the increment tends
to zero. This last limit includes the endpoint even when the zeta zero is multiple. -/
def H3 : Prop :=
  ∀ (A : ℕ → ℕ) (c : ℝ) (z : ℂ), (1 / 4 : ℝ) ≤ z.re → z.im ≠ 0 →
    riemannZeta (2 * z) = 0 →
    (∀ s : ℂ, 1 < s.re →
      LSeries (fun n : ℕ => (A n : ℂ) - (A (n - 1) : ℂ)) s *
        riemannZeta (2 * s) = riemannZeta s) →
    ((fun n : ℕ => |(A n : ℝ) - c * n|) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ))) →
    riemannZeta z = 0

theorem main : H1 → H2 → H3 → type_of% @Erdos969.erdos_969.variants.evelyn_linfoot := by
  intro hz hseries hboundary hsmall
  obtain ⟨z, hre, him, hden, hnum⟩ := hz
  exact hnum (hboundary Erdos969.squarefreeCounting (6 / Real.pi ^ 2) z
    hre him hden hseries hsmall)

end OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1
