import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace OMA.S_mo_263756

/-- Coefficients of the denominator after canceling the factor `X^k`
in the root-of-unity-filtered exponential from the question. -/
noncomputable def denominator (N k : ℕ) (ω : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun r =>
    ((k.factorial : ℂ) / ((k+r).factorial : ℂ)) *
      (1 / (N : ℂ))^r *
      ((∑ j ∈ Finset.range N, ω^(j*r)) / (N : ℂ))

noncomputable def generating (N k : ℕ) (ω z : ℂ) : PowerSeries ℂ :=
  PowerSeries.rescale (z + ω^k / (N : ℂ)) (PowerSeries.exp ℂ) *
    (denominator N k ω)⁻¹

/-- The generalized Bernoulli polynomial evaluated at `z`. -/
noncomputable def polynomialValue (N k n : ℕ) (ω z : ℂ) : ℂ :=
  (n.factorial : ℂ) * PowerSeries.coeff n (generating N k ω z)

noncomputable def affinityShift (N k : ℕ) (ω : ℂ) : ℂ :=
  ((ω^k)^2 - ω^k) / (N : ℂ)

/-- The affine symmetry with an explicit shift for each allowed pair `(N,k)`. -/
theorem main :
    ∀ N k : ℕ, 0 < N → k < N → ∀ ω : ℂ, IsPrimitiveRoot ω N →
      ∀ (z : ℂ) (n : ℕ),
        polynomialValue N k n ω (affinityShift N k ω + ω^k*z) =
          (ω^k)^n * polynomialValue N k n ω z := by
  sorry

end OMA.S_mo_263756
