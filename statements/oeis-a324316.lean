import Mathlib

/-!
# OEIS A324316: Primary Carmichael numbers.

Source: https://oeis.org/A324316
Credit: @unserus

OEIS: "Dickson's conjecture implies that the sequence is infinite, see Kellner 2019."
The open statement is that the sequence is infinite. Definition (OEIS): squarefree integers
`m > 1` such that for every prime `p` dividing `m`, the sum of the base-`p` digits of `m` equals
`p` (e.g. `1729 = 7 * 13 * 19`: `5020₇`, `a30₁₃`, `4f0₁₉` have digit sums `7`, `13`, `19`).
-/

namespace OMA.S_oeis_a324316

/-- `m` is a primary Carmichael number. -/
def IsPrimaryCarmichael (m : ℕ) : Prop :=
  1 < m ∧ Squarefree m ∧ ∀ p ∈ m.primeFactors, (Nat.digits p m).sum = p

/-- The terms of A324316. -/
def a324316Set : Set ℕ := {m : ℕ | IsPrimaryCarmichael m}

/-- A324316 is infinite. -/
theorem main : a324316Set.Infinite := by
  sorry

end OMA.S_oeis_a324316
