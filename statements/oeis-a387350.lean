import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Set.Card

/-!
# Distinct gaps between the positions of 1 in the Wythoff–Stolarsky difference

Source: Clark Kimberling, https://oeis.org/A387350 and https://oeis.org/A387348,
OEIS Foundation (CC BY-SA 4.0). The second columns are evaluated by the
formulas in the OEIS Mathematica program, with row numbers starting at 1.
Nearest-integer rounding of the positive irrational argument is floor(x+1/2).
Credit: @jatin6
-/

namespace OMA.S_oeis_a387350

noncomputable def phi : ℝ := (1 + Real.sqrt 5)/2

/-- Wythoff second column minus Stolarsky second column at row n. The
Stolarsky first column is floor((n-1)(phi+1)+1+phi/2). -/
noncomputable def difference (n : ℤ) : ℤ :=
  let a : ℤ := ⌊(n : ℝ)*(phi+1)-phi/2⌋
  2*⌊(n : ℝ)*phi⌋ + n - 1 - ⌊(a : ℝ)*phi + 1/2⌋

def hit (n : ℤ) : Prop := difference n = 1

def firstGap (n d : ℤ) : Prop := hit n ∧ 0 < d ∧ hit (n+d) ∧
  ∀ e : ℤ, 0 < e → e < d → ¬ hit (n+e)

def gaps : Set ℤ := {d | ∃ n : ℤ, 1 ≤ n ∧ firstGap n d}

theorem main : gaps.ncard = 3 := by
  sorry

end OMA.S_oeis_a387350
