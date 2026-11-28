import Mathlib

/-!
# Erdős Problem 956

Source: https://www.erdosproblems.com/956
Credit: Sudharsan Rajendiran

For `C, D ⊆ ℝ²` let `δ(C, D) = inf_{c ∈ C, d ∈ D} ‖c - d‖`. Let `h(n)` be the maximal `m` such
that there are a compact convex set `C ⊂ ℝ²` and a set `X ⊂ ℝ²` of size `n` such that the
translates `(C + x)_{x ∈ X}` are pairwise disjoint and there are `m` pairs `x_1, x_2 ∈ X` with
`δ(C + x_1, C + x_2) = 1`. Determine `h(n)`; in particular, prove that there is a constant
`c > 0` with `h(n) > n^{1 + c}` for all large `n`.

We formalize the second part, which the page asks to prove: there is `c > 0` with
`h(n) > n^{1 + c}` for all sufficiently large `n`. It is open; a disproof is the negation of
`main`. (Determining `h(n)` exactly is not formalized here.)

Conventions:
- `ℝ²` is `EuclideanSpace ℝ (Fin 2)`. `C` is nonempty, compact and convex.
- Pairs are unordered pairs of distinct points of `X`, i.e. two-element subsets of `X`.
- `h(n)` is a supremum of a set of natural numbers bounded by `n.choose 2`; for `n ≥ 1` the set
  is nonempty (`m = 0` is attained), so it is a true maximum.
-/

namespace OMA.S_erdos_956

open Filter Pointwise

/-- `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `δ(C, D) = inf_{c ∈ C, d ∈ D} ‖c - d‖`. -/
noncomputable def δ (C D : Set Plane) : ℝ :=
  sInf {r : ℝ | ∃ c ∈ C, ∃ d ∈ D, r = ‖c - d‖}

open Classical in
/-- The number of pairs `{x₁, x₂} ⊆ X` with `δ(C + x₁, C + x₂) = 1`. -/
noncomputable def touchingPairs (C : Set Plane) (X : Finset Plane) : ℕ :=
  ((X.powersetCard 2).filter (fun s =>
    ∃ x₁ ∈ s, ∃ x₂ ∈ s, x₁ ≠ x₂ ∧ δ (x₁ +ᵥ C) (x₂ +ᵥ C) = 1)).card

/-- `h(n)`. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ C : Set Plane, C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
    ∃ X : Finset Plane, X.card = n ∧
      (∀ x₁ ∈ X, ∀ x₂ ∈ X, x₁ ≠ x₂ → Disjoint (x₁ +ᵥ C) (x₂ +ᵥ C)) ∧
      m = touchingPairs C X}

/-- Erdős Problem 956, the part to be proved: `h(n) > n^{1 + c}` for some `c > 0` and all
large `n`. -/
theorem main : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < h n := by
  sorry

end OMA.S_erdos_956
