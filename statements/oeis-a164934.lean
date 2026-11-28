import Mathlib

/-!
# A164934: three disjoint subsets of {1..n} with equal sums (Kotesovec's asymptotic)

Source: https://oeis.org/A164934 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A164934 (offset 1): number of different ways to select 3 disjoint subsets from {1..n} with equal
element sum; data 0, 0, 0, 0, 1, 3, 8, 22, 63, 157, ...
(a(5) = 1: {1,4}, {2,3}, {5}; a(6) = 3: {1,4}, {2,3}, {5}; {1,5}, {2,4}, {6}; {1,6}, {2,5}, {3,4}.)

The entry records (Vaclav Kotesovec, Oct 16 2014):

  Conjecture: a(n) ~ 4^n / (Pi * sqrt(3) * n^3).

Reading of the source:
* A selection is an unordered collection of 3 pairwise disjoint subsets of {1, ..., n}, all
  nonempty and with the same element sum; it is a 3-element set of subsets. (Allowing the empty
  set would make three empty sets a selection for every n, contradicting a(1) = 0; the examples
  list each selection once, unordered.) This reading reproduces the data for n ≤ 10.
* `a(n) ~ 4^n / (π √3 n^3)` is asymptotic equivalence (`~[atTop]`, ratio tending to 1) as
  `n → ∞` over the naturals.
-/

namespace OMA.S_oeis_a164934

open Asymptotics Filter

/-- A164934(n): the number of 3-element sets of pairwise disjoint nonempty subsets of
`{1, ..., n}` that all have the same element sum. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.powerset.filter (fun F =>
    F.card = 3 ∧ (∀ A ∈ F, A.Nonempty) ∧
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) ∧
      (∀ A ∈ F, ∀ B ∈ F, ∑ i ∈ A, i = ∑ i ∈ B, i))).card

/-- Kotesovec's conjecture: `a(n) ~ 4^n / (π √3 n^3)`. -/
theorem main :
    (fun n : ℕ => (a n : ℝ)) ~[atTop]
      (fun n : ℕ => (4 : ℝ) ^ n / (Real.pi * Real.sqrt 3 * (n : ℝ) ^ 3)) := by
  sorry

end OMA.S_oeis_a164934
