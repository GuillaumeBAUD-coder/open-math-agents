import Mathlib

namespace OMA.S_oeis_a324018

open scoped Classical

/-- Standard embedding of the vertices `{0, 1}^n` of the `n`-cube into `ℝ^n`. -/
def cubeEmbed {n : ℕ} (v : Fin n → Bool) : Fin n → ℝ :=
  fun i => if v i then 1 else 0

/-- An undirected edge of the complete graph on the `2^n` vertices of the `n`-cube. -/
abbrev Edge (n : ℕ) := { e : Finset (Fin n → Bool) // e.card = 2 }

/-- A subset `S` of vertices of the `n`-cube is coplanar if its embedded image lies in
a 2-dimensional affine subspace of `ℝ^n`. -/
def IsCoplanar (n : ℕ) (S : Finset (Fin n → Bool)) : Prop :=
  ∃ p v w : Fin n → ℝ, ∀ x ∈ S, ∃ s t : ℝ, cubeEmbed x = p + s • v + t • w

/-- `S` forms a monochromatic planar `K_4` subgraph under edge 2-coloring `c`. -/
def IsMonoPlanarK4 (n : ℕ) (c : Edge n → Bool) (S : Finset (Fin n → Bool)) : Prop :=
  S.card = 4 ∧ IsCoplanar n S ∧ ∃ b : Bool, ∀ e : Edge n, e.val ⊆ S → c e = b

/-- OEIS A324018(`n`): number of 2-colorings of the edges of the complete graph on the
`2^n` vertices of an `n`-cube that contain no monochromatic planar `K_4` subgraph. -/
noncomputable def a324018 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Edge n → Bool)).filter
    (fun c => ∀ S : Finset (Fin n → Bool), ¬ IsMonoPlanarK4 n c S)).card

/-- OEIS A324018 Conjecture: For all `n ≥ 3`,
`a(n) < 31 * (2^(binomial(2^n, 2) - 5) - 2^(binomial(2^n, 2) - 10))`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      a324018 n < 31 * (2 ^ ((2 ^ n).choose 2 - 5) - 2 ^ ((2 ^ n).choose 2 - 10)) := by
  sorry

end OMA.S_oeis_a324018
