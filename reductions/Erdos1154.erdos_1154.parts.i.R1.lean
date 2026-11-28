import FormalConjectures.ErdosProblems.«1154»

-- Reduction Erdos1154.erdos_1154.parts.i.R1 of Erdős Problem 1154 — i
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Erdős Problem 1154 (part i): for every `a ∈ [0,1]` there is a subring of `ℝ` whose carrier has
Hausdorff dimension `a`.

The two endpoints of the interval are settled by explicit witnesses, so they are isolated as
*positive* hypotheses rather than being hidden inside the open core:

* `H1` -- `a = 0`: witnessed by the zero subring `⊥ : Subring ℝ`, whose carrier is `{0}`, and
  `dimH {0} = 0`.
* `H2` -- `a = 1`: witnessed by the whole ring `⊤ : Subring ℝ`, whose carrier is `univ`, and
  `dimH univ = 1`.
* `H3` -- the genuinely open core: `0 < a < 1`, i.e. a fractal subring for a strictly intermediate
  dimension.

`main` is the case split on `a = 0`, `a = 1` and the remainder.
-/

namespace OMA.R_Erdos1154_erdos_1154_parts_i_R1

open Set MeasureTheory
open scoped ENNReal

/-- The endpoint `a = 0`: the zero subring has carrier `{0}` and Hausdorff dimension `0`. -/
def H1 : Prop :=
  ∀ a ∈ Icc (0 : ℝ≥0∞) 1, a = 0 → ∃ R : Subring ℝ, dimH (R : Set ℝ) = a

/-- The endpoint `a = 1`: the whole ring has carrier `ℝ` and Hausdorff dimension `1`. -/
def H2 : Prop :=
  ∀ a ∈ Icc (0 : ℝ≥0∞) 1, a = 1 → ∃ R : Subring ℝ, dimH (R : Set ℝ) = a

/-- The open core: every strictly intermediate dimension `0 < a < 1`. -/
def H3 : Prop :=
  ∀ a ∈ Icc (0 : ℝ≥0∞) 1, a ≠ 0 → a ≠ 1 → ∃ R : Subring ℝ, dimH (R : Set ℝ) = a

theorem main : H1 → H2 → H3 → type_of% @Erdos1154.erdos_1154.parts.i := by
  intro h1 h2 h3 a ha
  by_cases h0 : a = 0
  · exact h1 a ha h0
  · by_cases h1' : a = 1
    · exact h2 a ha h1'
    · exact h3 a ha h0 h1'

end OMA.R_Erdos1154_erdos_1154_parts_i_R1
