import Mathlib

/-!
# Symmetric rendezvous on an undirected line

Source: https://www.openproblemgarden.org/op/rendezvous_on_a_line
Credit: @lawrencerowland (Codex, with Lawrence Rowland.)

Steve Alpern asks for the infimum. This file defines it over continuous paths
and states the numerical answer conjectured on the source page by Han, Du,
Vera and Zuluaga (Operations Research 56 (2008), DOI 10.1287/opre.1070.0439).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace OMA.S_opg_rendezvous_on_a_line

/-- A path in local coordinates. Time zero is shared and maximum speed is one. -/
abbrev Route := { f : C(ℝ≥0, ℝ) // f 0 = 0 ∧ LipschitzWith 1 f }

local instance : MeasurableSpace Route := borel Route

/-- First coincidence for fixed local orientations. An empty infimum is infinity. -/
noncomputable def firstHit (a b : ℝ) (f g : Route) : ℝ≥0∞ :=
  ⨅ t : {t : ℝ≥0 // a * f.val t = 2 + b * g.val t}, (t.val : ℝ≥0∞)

/-- Nature independently orients each local coordinate system. -/
noncomputable def orientationMean (f g : Route) : ℝ≥0∞ :=
  (firstHit 1 1 f g + firstHit 1 (-1) f g +
   firstHit (-1) 1 f g + firstHit (-1) (-1) f g) / 4

/-- The two teams independently sample paths from the same probability law. -/
noncomputable def expectedTime (μ : Measure Route) : ℝ≥0∞ :=
  ∫⁻ p : Route × Route, orientationMean p.1 p.2 ∂(μ.prod μ)

/-- The value of the optimization problem, allowing paths that never meet. -/
noncomputable def rendezvousValue : ℝ≥0∞ :=
  ⨅ μ : {μ : Measure Route // IsProbabilityMeasure μ}, expectedTime μ.val

/-- The numerical conjecture reported with Alpern's open question. -/
theorem main : rendezvousValue = 17 / 4 := by
  sorry

end OMA.S_opg_rendezvous_on_a_line
