import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Banach's problem – is there an ergodic system with simple Lebesgue spectrum?

Source: https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Dynamical_systems
See Ryzhikov, Unsolved problems on joinings, multiple mixing, spectrum, and rank,
Q2 (https://arxiv.org/abs/2405.03641), for the probability-space formulation.
Credit: @ArjunCodess

We use the probability-preserving automorphism formulation. On a standard Borel space,
vanishing measure on singletons expresses nonatomicity. The Koopman operator has simple
Lebesgue spectrum on mean-zero complex L² exactly when it acts as the bilateral shift on
a Hilbert basis indexed by the integers. The character basis on the circle identifies
this shift with multiplication by the coordinate function for normalized Lebesgue measure.
-/

namespace OMA.S_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum

open MeasureTheory

/-- The orthogonal complement of the constant functions in complex L². -/
noncomputable def meanZeroL2 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] : Submodule ℂ (Lp ℂ 2 μ) :=
  (Submodule.span ℂ {Lp.const 2 μ (1 : ℂ)}).orthogonal

theorem main :
    ∃ (X : Type) (m : MeasurableSpace X),
      letI : MeasurableSpace X := m
      StandardBorelSpace X ∧
        ∃ (μ : Measure X) (hμ : IsProbabilityMeasure μ),
          letI : IsProbabilityMeasure μ := hμ
          NullSingletonClass μ ∧
            ∃ (T : X ≃ᵐ X) (hT : Ergodic T μ) (b : HilbertBasis ℤ ℂ (meanZeroL2 μ)),
              ∀ n : ℤ, Lp.compMeasurePreserving T hT.toMeasurePreserving
                (b n : Lp ℂ 2 μ) = (b (n + 1) : Lp ℂ 2 μ) := by
  sorry

end OMA.S_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum
