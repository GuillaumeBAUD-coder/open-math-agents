import FormalConjectures.GreensOpenProblems.«70»

/-!
Theorem 1 and the convex-layer argument of Abel et al.
Every large point set contains many collinear points or an empty pentagon.
arXiv:0904.0262
-/

namespace OMA.R_Green70_green_70_variants_empty_pentagon_R1

open Green70

/-- The Erdős–Szekeres theorem for possibly collinear planar sets. -/
def H1 : Prop :=
  ∀ m : ℕ, ∃ N : ℕ, ∀ P : Finset (ℝ × ℝ), N ≤ P.card →
    ∃ S : Finset (ℝ × ℝ), S ⊆ P ∧ m ≤ S.card ∧
      (S : Set (ℝ × ℝ)) ⊆ frontier (convexHull ℝ (S : Set (ℝ × ℝ)))

/-- The convex-layer bound for sets with neither a long line nor an empty pentagon. -/
def H2 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ m : ℕ, ∀ P S : Finset (ℝ × ℝ), S ⊆ P →
    (S : Set (ℝ × ℝ)) ⊆ frontier (convexHull ℝ (S : Set (ℝ × ℝ))) →
    ¬ HasCollinear k P → ¬ HasEmptyPentagon P → S.card < m

theorem main : H1 → H2 → type_of% @Green70.green_70.variants.empty_pentagon := by
  classical
  intro findBoundary boundBoundary k hk
  by_cases hk2 : k = 2
  · subst k
    refine ⟨2, fun P hP => Or.inl ?_⟩
    obtain ⟨S, hSP, hS⟩ := Finset.exists_subset_card_eq hP
    obtain ⟨x, y, _, rfl⟩ := Finset.card_eq_two.mp hS
    exact ⟨{x, y}, hSP, hS, by simpa only [Finset.coe_insert, Finset.coe_singleton] using
      (collinear_pair ℝ x y)⟩
  · obtain ⟨m, hm⟩ := boundBoundary k (by omega)
    obtain ⟨N, hN⟩ := findBoundary m
    refine ⟨N, fun P hP => ?_⟩
    by_contra! h
    obtain ⟨S, hSP, hcard, hfrontier⟩ := hN P hP
    exact (hm P S hSP hfrontier h.1 h.2).not_ge hcard

end OMA.R_Green70_green_70_variants_empty_pentagon_R1
