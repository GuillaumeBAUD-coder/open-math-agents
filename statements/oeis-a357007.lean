import Mathlib

/-!
# A357007: Number of vertices in an equilateral triangle when n internal equilateral triangles are drawn between the 3n points that divide each side into n+1 equal parts.

Source: https://oeis.org/A357007 (OEIS Foundation, CC BY-SA 4.0)
Credit: @marcusbuffett

Entry (Scott R. Shannon, Sep 08 2022), offset 0. Data:
  3, 6, 15, 30, 51, 66, 111, 150, 171, 246, 303, 312, 435, 510, 543, 678, 771, 765, 975, ...
The formula section states:
  Conjecture: a(n) = 3*n^2 + 3 for equilateral triangles that only contain simple vertices when
  cut by n internal equilateral triangles. This is never the case if (n + 1) mod 3 = 0 for n > 3.
(A356984 counts the regions and A357008 the edges; a vertex where exactly two segments cross is
a "simple" vertex.)

Conventions:
* The triangle has corners `A = (0, 0)`, `B = (1, 0)`, `C = (1/2, √3/2)` in `ℝ × ℝ`; corner `i`
  (`i = 0, 1, 2`) is `A`, `B`, `C`, and side `i` runs from corner `i` to corner `i + 1`
  (indices mod 3).
* `divPt n i k` is the point of side `i` at distance `k/(n+1)` of its length from corner `i`;
  for `k = 1, ..., n` these are the `3n` points dividing the sides into `n + 1` equal parts.
* The `k`-th internal triangle (`1 ≤ k ≤ n`) has corners `divPt n 0 k`, `divPt n 1 k`,
  `divPt n 2 k`; it is equilateral by the rotational symmetry of the figure.
* The drawn segments are indexed by `(i, k)` with `k ≤ n`: for `k = 0` the side `i` of the big
  triangle, for `1 ≤ k ≤ n` the side of the `k`-th internal triangle from `divPt n i k` to
  `divPt n (i+1) k`.
* The vertices of the figure are the endpoints of the drawn segments and the points common to two
  different drawn segments.
* The triangle "only contains simple vertices" when no point off the sides of the big triangle
  lies on three different drawn segments (every interior vertex is a crossing of exactly two
  segments).
* `Set.ncard` counts the vertices (the set is finite).
-/

namespace OMA.S_oeis_a357007

/-- The corners `A`, `B`, `C` of the equilateral triangle. -/
noncomputable def corner (i : Fin 3) : ℝ × ℝ :=
  if i = 0 then (0, 0) else if i = 1 then (1, 0) else (1 / 2, Real.sqrt 3 / 2)

/-- The point of side `i` (from corner `i` to corner `i + 1`) at fraction `k / (n + 1)`. -/
noncomputable def divPt (n : ℕ) (i : Fin 3) (k : ℕ) : ℝ × ℝ :=
  corner i + ((k : ℝ) / (n + 1)) • (corner (i + 1) - corner i)

/-- Endpoints of the drawn segment `(i, k)`: side `i` of the big triangle for `k = 0`, side `i`
of the `k`-th internal triangle for `1 ≤ k ≤ n`. -/
noncomputable def ends (n : ℕ) (σ : Fin 3 × ℕ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  if σ.2 = 0 then (corner σ.1, corner (σ.1 + 1)) else (divPt n σ.1 σ.2, divPt n (σ.1 + 1) σ.2)

/-- The drawn segments: `3` sides and `3n` sides of internal triangles. -/
def Seg (n : ℕ) : Type := {σ : Fin 3 × ℕ // σ.2 ≤ n}

/-- The points of a drawn segment. -/
noncomputable def pts (n : ℕ) (σ : Seg n) : Set (ℝ × ℝ) :=
  segment ℝ (ends n σ.1).1 (ends n σ.1).2

/-- Vertices: endpoints of drawn segments and points common to two different drawn segments. -/
def vertices (n : ℕ) : Set (ℝ × ℝ) :=
  {p | ∃ σ : Seg n, p = (ends n σ.1).1 ∨ p = (ends n σ.1).2} ∪
    {p | ∃ σ τ : Seg n, σ ≠ τ ∧ p ∈ pts n σ ∧ p ∈ pts n τ}

/-- Only simple vertices: no point off the sides of the big triangle lies on three different
drawn segments. -/
def OnlySimple (n : ℕ) : Prop :=
  ∀ p : ℝ × ℝ, (∀ i : Fin 3, p ∉ segment ℝ (corner i) (corner (i + 1))) →
    ¬ ∃ σ₁ σ₂ σ₃ : Seg n, σ₁ ≠ σ₂ ∧ σ₁ ≠ σ₃ ∧ σ₂ ≠ σ₃ ∧
      p ∈ pts n σ₁ ∧ p ∈ pts n σ₂ ∧ p ∈ pts n σ₃

/-- The conjecture of OEIS A357007: with only simple vertices there are `3 n^2 + 3` vertices. -/
theorem main : ∀ n : ℕ, OnlySimple n → (vertices n).ncard = 3 * n ^ 2 + 3 := by
  sorry

end OMA.S_oeis_a357007
