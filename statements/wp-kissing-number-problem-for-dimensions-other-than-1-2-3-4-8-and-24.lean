import Mathlib

/-!
# Kissing number problem in dimensions other than 1, 2, 3, 4, 8, and 24

Source: https://en.wikipedia.org/wiki/Kissing_number_problem
-- Credit: @mbilenko03 (agent: antigravity, model grok-4.7)

The kissing number `τ(d)` is the greatest number of pairwise non-overlapping unit balls in
Euclidean space `ℝ^d` that can each touch a central unit ball. The same number is the greatest
`m` for which some `m` points of the sphere of radius `2` are pairwise at distance at least `2`.

The problem asks for `τ(d)` for every `d ∉ {1, 2, 3, 4, 8, 24}`. The six solved dimensions are
`τ(1) = 2`, `τ(2) = 6`, `τ(3) = 12`, `τ(4) = 24`, `τ(8) = 240`, and `τ(24) = 196560`.

For the first three open dimensions, the root lattices `D₅`, `E₆`, and `E₇` realize
configurations of sizes `40`, `72`, and `126`. These are the standard conjectured exact values
(the source lists them as the best known lower bounds, with upper bounds `44`, `77`, and `134`
still strictly larger). `main` states those three conjectures.

`kissingNumber d` is `sSup` of the set of sizes that `IsKissingConfig` allows. The set is
nonempty for every `d`: `IsKissingConfig d 0 Fin.elim0` holds, because both quantifiers over
`Fin 0` are vacuous, so `0` belongs to the set. It is bounded above. The centers lie on the
compact sphere of radius `2` and are separated by distance `2`, so only finitely many fit. A
volume bound makes the same fact explicit: the open unit balls about the centers are pairwise
disjoint and contained in the ball of radius `3`, hence `m ≤ 3 ^ d` for `d ≥ 1`, while `d = 0`
admits only the empty configuration. `Nat.sSup` of a nonempty bounded subset of `ℕ` is its
greatest element (`Nat.sSup_mem`), so `kissingNumber d = τ(d)`. It is not the junk value `0`
that `Nat.sSup` returns on an unbounded set of naturals.
-/

namespace OMA.S_wp_kissing_number_problem_for_dimensions_other_than_1_2_3_4_8_and_24

/-- `m` centers of congruent unit balls that touch the central unit ball at `0` and have
pairwise disjoint interiors: each center lies on the sphere of radius `2`, and any two centers
are at distance at least `2`. -/
def IsKissingConfig (d m : ℕ) (c : Fin m → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ i, ‖c i‖ = 2) ∧ (∀ i j, i ≠ j → 2 ≤ dist (c i) (c j))

/-- The Euclidean kissing number `τ(d)`. -/
noncomputable def kissingNumber (d : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ c : Fin m → EuclideanSpace ℝ (Fin d), IsKissingConfig d m c }

/-- The conjectured kissing numbers in dimensions `5`, `6`, and `7`. -/
theorem main : kissingNumber 5 = 40 ∧ kissingNumber 6 = 72 ∧ kissingNumber 7 = 126 := by
  sorry

end OMA.S_wp_kissing_number_problem_for_dimensions_other_than_1_2_3_4_8_and_24
