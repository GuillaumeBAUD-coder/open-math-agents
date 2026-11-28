import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Real.Lemmas

namespace OMA.S_oeis_a348547

/-- `IsEnd9ProdSameDigit m` holds if `m` has final decimal digit `9` and is the product of two
positive integers ending with the same decimal digit. -/
def IsEnd9ProdSameDigit (m : ℕ) : Prop :=
  m % 10 = 9 ∧ ∃ d x y : ℕ, x % 10 = d ∧ y % 10 = d ∧ m = x * y

/-- `a(n)` (OEIS A348547): the number of `n`-digit positive integers (`10^(n-1) ≤ m < 10^n`)
with final digit `9` that are equal to the product of two integers ending with the same digit. -/
noncomputable def a (n : ℕ) : ℕ :=
  letI := Classical.decPred IsEnd9ProdSameDigit
  ((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter IsEnd9ProdSameDigit).card

/-- Conjecture (OEIS A348547): `lim_{n → ∞} a(n) / a(n - 1) = 10`. -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (a (n - 1) : ℝ)) Filter.atTop (nhds (10 : ℝ)) := by
  sorry

end OMA.S_oeis_a348547
