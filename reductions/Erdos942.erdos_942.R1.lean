import FormalConjectures.ErdosProblems.«942»
import Mathlib

/-!
# Reduction of Erdős Problem 942 into an upper bound and a lower bound on its exponent

`erdos_942.h n` counts the powerful integers in `[n^2, (n+1)^2)`. The target asks for a
constant `c > 0` and a function `o = o(1)` such that eventually `h n < (log n) ^ (c + o n)` and
infinitely often `h n > (log n) ^ (c - o n)`.

Taking logarithms of the two inequalities (the windows are nonempty, so `h n >= 1`), the target is
equivalent to saying that the exponent
`r n = log (h n) / log (log n)`
has a finite positive limsup `L`. That splits into the two independent halves below, plus the
elementary bookkeeping `H3` that turns a limsup value into a common `o`:
`H1` the exponent is bounded above (the open half of the problem), `H2` the exponent limsup is
positive (a theorem: de Koninck and Luca proved `h n >> (log n / log log n) ^ (1/3)` for infinitely
many `n`, so the limsup is at least `1/3`), and `H3` the passage from a limsup value to the two
`o(1)`-inequalities.
-/

open Erdos942 Filter

namespace OMA.R_Erdos942_erdos_942_R1

/-- The exponent `log (h n) / log (log n)` is bounded above along a tail: the open upper half. -/
def H1 : Prop :=
  atTop.limsup (fun n : ℕ => ENNReal.ofReal
    (Real.log (erdos_942.h n : ℝ) / Real.log (Real.log (n : ℝ)))) < ⊤

/-- The exponent limsup is positive: the lower bound direction (de Koninck-Luca, exponent `1/3`). -/
def H2 : Prop :=
  0 < atTop.limsup (fun n : ℕ => ENNReal.ofReal
    (Real.log (erdos_942.h n : ℝ) / Real.log (Real.log (n : ℝ))))

/-- Elementary passage: a limsup value `L` of the exponent yields one function `o = o(1)` that serves
both the eventual upper inequality and the infinitely-often lower inequality of the target. -/
def H3 : Prop :=
  ∀ L : ℝ, 0 < L →
    atTop.limsup (fun n : ℕ => ENNReal.ofReal
      (Real.log (erdos_942.h n : ℝ) / Real.log (Real.log (n : ℝ)))) = ENNReal.ofReal L →
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      (∀ᶠ n : ℕ in atTop, erdos_942.h n < (Real.log n) ^ (L + o n)) ∧
      {n : ℕ | erdos_942.h n > (Real.log n) ^ (L - o n)}.Infinite

theorem main : H1 → H2 → H3 → type_of% @Erdos942.erdos_942 := by
  intro h1 h2 h3
  have hne : atTop.limsup (fun n : ℕ => ENNReal.ofReal
      (Real.log (erdos_942.h n : ℝ) / Real.log (Real.log (n : ℝ)))) ≠ ⊤ := ne_of_lt h1
  obtain ⟨L, hL⟩ : ∃ L : ℝ, atTop.limsup (fun n : ℕ => ENNReal.ofReal
      (Real.log (erdos_942.h n : ℝ) / Real.log (Real.log (n : ℝ)))) = ENNReal.ofReal L :=
    ⟨_, (ENNReal.ofReal_toReal hne).symm⟩
  have hpos : 0 < L := by
    have h2' : 0 < atTop.limsup (fun n : ℕ => ENNReal.ofReal
        (Real.log (erdos_942.h n : ℝ) / Real.log (Real.log (n : ℝ)))) := h2
    rw [hL] at h2'
    exact ENNReal.ofReal_pos.mp h2'
  exact ⟨L, hpos, h3 L hpos hL⟩

end OMA.R_Erdos942_erdos_942_R1
