import Mathlib

/-!
# A conjecture on iterated circumcentres

Source: https://www.openproblemgarden.org/op/a_conjecture_on_iterated_circumcentres
Credit: @ishaanzee

**Conjecture** (L. Goddyn). Let `p₁, p₂, p₃, …` be a sequence of points in `ℝ^d` with the property
that for every `i ≥ d + 2`, the points `p_{i-1}, p_{i-2}, …, p_{i-d-1}` are distinct, lie on a
unique sphere, and further, `pᵢ` is the center of this sphere. If this sequence is periodic, must
its period be `2d + 4`?

(Goddyn proved this for `d ≤ 5`.) We state the affirmative answer.

Formalization:
* Points are in `EuclideanSpace ℝ (Fin d)` with `d ≥ 1`; the sequence is indexed from `0`, so the
  condition is imposed for every `i ≥ d + 1` on the `d + 1` points `p j`, `i - d - 1 ≤ j < i`.
* "Lie on a unique sphere": there is exactly one `EuclideanGeometry.Sphere` containing them, and
  `pᵢ` is its center.
* "Its period is `2d + 4`": `2d + 4` is the least positive period, i.e. `p (n + 2d + 4) = p n` for
  all `n`, and no smaller positive `q` is a period.
-/

namespace OMA.S_opg_a_conjecture_on_iterated_circumcentres

/-- The sequence `p` satisfies Goddyn's circumcentre recursion in `ℝ^d`. -/
def IsCircumcentreSequence (d : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ i : ℕ, d + 1 ≤ i →
    (∀ j ∈ Finset.Ico (i - d - 1) i, ∀ j' ∈ Finset.Ico (i - d - 1) i, j ≠ j' → p j ≠ p j') ∧
    ∃ s : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin d)),
      (∀ j ∈ Finset.Ico (i - d - 1) i, p j ∈ s) ∧
      (∀ s' : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin d)),
        (∀ j ∈ Finset.Ico (i - d - 1) i, p j ∈ s') → s' = s) ∧
      p i = s.center

/-- **Goddyn's conjecture**: a periodic circumcentre sequence in `ℝ^d` has least period `2d + 4`. -/
theorem main : ∀ (d : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin d)), 1 ≤ d → IsCircumcentreSequence d p →
    (∃ q : ℕ, 0 < q ∧ Function.Periodic p q) →
      Function.Periodic p (2 * d + 4) ∧ ∀ q : ℕ, 0 < q → Function.Periodic p q → 2 * d + 4 ≤ q := by
  sorry

end OMA.S_opg_a_conjecture_on_iterated_circumcentres
