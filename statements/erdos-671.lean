import Mathlib

/-!
# Erdős Problem 671

Source: https://www.erdosproblems.com/671
Credit: @mejiasd3v
-/

namespace OMA.S_erdos_671

open Filter
open scoped Topology

abbrev Interval := Set.Icc (-1 : ℝ) 1

/-- Row `n` contains `n + 1` distinct nodes, starting with a one-node row. -/
abbrev Nodes := (n : ℕ) → Fin (n + 1) ↪ Interval

/-- The Lebesgue sums exceed each real threshold arbitrarily far along the rows. -/
def unboundedLebesgue (a : Nodes) (x : Interval) : Prop :=
  ∀ M : ℝ, ∃ᶠ n in atTop,
    M < ∑ i : Fin (n + 1), |(Lagrange.basis Finset.univ (fun j => (a n j : ℝ)) i).eval (x : ℝ)|

/-- The interpolating polynomials converge to the function value at `x`. -/
def convergesAt (a : Nodes) (f : C(Interval, ℝ)) (x : Interval) : Prop :=
  Tendsto (fun n => (Lagrange.interpolate Finset.univ (fun j => (a n j : ℝ))
    (fun i => f (a n i))).eval (x : ℝ)) atTop (𝓝 (f x))

/-- The two existence questions, in the order Erdős asks them. -/
theorem main :
    (∃ a : Nodes, ∀ f : C(Interval, ℝ), ∃ x : Interval, unboundedLebesgue a x ∧ convergesAt a f x) ∧
    (∃ a : Nodes, (∀ x : Interval, unboundedLebesgue a x) ∧
      ∀ f : C(Interval, ℝ), ∃ x : Interval, convergesAt a f x) := by
  sorry

end OMA.S_erdos_671
