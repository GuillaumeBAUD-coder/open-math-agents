import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Sym

/-!
# Erdős Problem 132

See https://www.erdosproblems.com/132. The first question uses the range
`n ≥ 5` specified in the remarks and in Conjecture 1.1 of Clemen, Dumitrescu,
and Liu (arXiv:2505.04283). The second question asks for growth uniformly
over all point sets of a given size.
-/

namespace OMA.S_erdos_132

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def pairDistance : Sym2 Point → ℝ :=
  Sym2.lift ⟨dist, dist_comm⟩

noncomputable def distinctPairs (A : Finset Point) : Finset (Sym2 Point) := by
  classical
  exact A.sym2.filter fun pair => ¬ pair.IsDiag

/-- The number of unordered pairs of distinct points of `A` separated by `d`. -/
noncomputable def multiplicity (A : Finset Point) (d : ℝ) : ℕ := by
  classical
  exact ((distinctPairs A).filter fun pair => pairDistance pair = d).card

/-- The realized distances whose multiplicity is at most the number of points. -/
noncomputable def rareDistances (A : Finset Point) : Finset ℝ := by
  classical
  exact ((distinctPairs A).image pairDistance).filter fun d => multiplicity A d ≤ A.card

theorem main :
    (∀ A : Finset Point, 5 ≤ A.card → 2 ≤ (rareDistances A).card) ∧
    (∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset Point, N ≤ A.card → k ≤ (rareDistances A).card) := by
  sorry

end OMA.S_erdos_132
