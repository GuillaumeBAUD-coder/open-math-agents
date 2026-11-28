import Mathlib

namespace OMA.S_mo_495937

open scoped BigOperators

/-- An ordered family of `n+1` vertices of the binary `n`-cube. -/
abbrev CubeFamily (n : ℕ) := Fin (n + 1) → Fin n → Bool

/-- Nonzero determinant of the difference vectors based at vertex zero. -/
def FullDimensional {n : ℕ} (x : CubeFamily n) : Prop :=
  (Matrix.of fun i j : Fin n =>
    (if x i.succ j then (1 : ℤ) else 0) -
      (if x 0 j then (1 : ℤ) else 0)).det ≠ 0

/-- Squared Euclidean distance on binary vertices, which is their Hamming distance. -/
def squareDistance {n : ℕ} (x : CubeFamily n) (i j : Fin (n + 1)) : ℕ :=
  ∑ k : Fin n, if x i k = x j k then 0 else 1

/-- Congruence of the simplices means equality of distance matrices after relabeling. -/
def EuclideanEquivalent {n : ℕ} (x y : CubeFamily n) : Prop :=
  ∃ p : Equiv.Perm (Fin (n + 1)), ∀ i j, squareDistance x (p i) (p j) = squareDistance y i j

/-- Equivalence under the symmetries of the cube and a relabeling of the vertices. -/
def CubeEquivalent {n : ℕ} (x y : CubeFamily n) : Prop :=
  ∃ (p : Equiv.Perm (Fin (n + 1))) (q : Equiv.Perm (Fin n)) (flip : Fin n → Bool),
    ∀ i j, y i j = if flip j then !(x (p i) (q j)) else x (p i) (q j)

noncomputable def fullDimensionalFamilies (n : ℕ) : Finset (CubeFamily n) := by
  classical
  exact Finset.univ.filter FullDimensional

/-- The congruence classes of full-dimensional simplices in the cube. -/
noncomputable def euclideanTypes (n : ℕ) : Finset (Set (CubeFamily n)) := by
  classical
  exact (fullDimensionalFamilies n).image fun x => {y | EuclideanEquivalent x y}

/-- The cube-symmetry basis orbits counted by A126776. -/
noncomputable def cubeBasisOrbits (n : ℕ) : Finset (Set (CubeFamily n)) := by
  classical
  exact (fullDimensionalFamilies n).image fun x => {y | CubeEquivalent x y}

/-- In dimension five two different cube-symmetry basis orbits already
give congruent simplices, and the Euclidean count is strictly smaller. -/
theorem main :
    (∃ x y : CubeFamily 5, FullDimensional x ∧ FullDimensional y ∧
      EuclideanEquivalent x y ∧ ¬ CubeEquivalent x y) ∧
    (euclideanTypes 5).card < (cubeBasisOrbits 5).card := by
  sorry

end OMA.S_mo_495937
