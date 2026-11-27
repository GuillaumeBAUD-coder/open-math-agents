import FormalConjectures.ErdosProblems.«103»
import Mathlib

-- Reduction Erdos103.erdos_103.variants.two_le.R2 of Erdős Problem 103 (two minimisers).
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- R1 splits the claim into existence of minimisers plus one conditional boundary statement.
-- This second reduction uses a different axis: the case analysis on tightness, with the two
-- cases exposed as independent steps. Either case alone yields two incongruent minimisers, and
-- every minimiser falls in exactly one of them, so the two steps are genuinely separate lines of
-- attack: the tight case is combinatorial, while the case with a movable point is a perturbation
-- argument.

namespace OMA.R_Erdos103_erdos_103_variants_two_le_R2

open EuclideanGeometry Filter Finset
open Erdos103
open scoped Classical ENNReal

/-- Minimisers exist for all large `n`. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ A : Finset ℝ², IsMinimiser n A

/-- The tight case: if in every minimiser every point is at distance exactly `1` or exactly the
diameter from some other point, then two incongruent minimisers exist. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (∀ A : Finset ℝ², IsMinimiser n A → ∀ p ∈ A,
      ∃ q ∈ A.erase p, dist p q = 1 ∨ dist p q = Metric.diam (A : Set ℝ²)) →
    ∃ A B : Finset ℝ², IsMinimiser n A ∧ IsMinimiser n B ∧ ¬ Congruent A B

/-- The movable case: if some minimiser has a point that is strictly farther than `1` from, and
strictly closer than the diameter to, every other point, then two incongruent minimisers exist. -/
def H3 : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (∃ A : Finset ℝ², IsMinimiser n A ∧ ∃ p ∈ A,
      ∀ q ∈ A.erase p, 1 < dist p q ∧ dist p q < Metric.diam (A : Set ℝ²)) →
    ∃ A B : Finset ℝ², IsMinimiser n A ∧ IsMinimiser n B ∧ ¬ Congruent A B

/-- Congruence of finite point sets is symmetric. -/
lemma congruent_comm {A B : Finset ℝ²} (h : Congruent A B) : Congruent B A := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [← he, Set.image_image]
  simp

/-- Two incongruent minimisers already give `2 ≤ h n`. -/
lemma two_le_of_pair {n : ℕ} {A B : Finset ℝ²} (hA : IsMinimiser n A)
    (hB : IsMinimiser n B) (hc : ¬ Congruent A B) : 2 ≤ Erdos103.h n := by
  have hne : A ≠ B := by
    intro h
    subst h
    refine hc ⟨IsometryEquiv.refl _, ?_⟩
    change id '' (A : Set ℝ²) = A
    exact Set.image_id _
  let S : Finset (Finset ℝ²) := {A, B}
  have hBoth : (∀ X ∈ S, IsMinimiser n X) ∧ ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → ¬ Congruent X Y := by
    constructor
    · intro X hX
      rcases (show X = A ∨ X = B from by simpa [S] using hX) with rfl | rfl
      · exact hA
      · exact hB
    · intro X hX Y hY hXY
      have hX' : X = A ∨ X = B := by simpa [S] using hX
      have hY' : Y = A ∨ Y = B := by simpa [S] using hY
      rcases hX' with hx | hx <;> rcases hY' with hy | hy <;> subst X <;> subst Y
      · exact (hXY rfl).elim
      · exact hc
      · exact fun hh => hc (congruent_comm hh)
      · exact (hXY rfl).elim
  have hcard : (S.card : ℕ∞) = 2 := by simp [S, Finset.card_pair hne]
  rw [← hcard]
  exact le_iSup_of_le S (le_iSup_of_le hBoth le_rfl)

theorem main : H1 → H2 → H3 → type_of% @Erdos103.erdos_103.variants.two_le := by
  intro hExist hTight hMoved
  filter_upwards [hExist, hTight, hMoved,
    (eventually_ge_atTop 2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n)] with n hE hT hM hn2
  by_cases hBoundary : ∀ A : Finset ℝ², IsMinimiser n A → ∀ p ∈ A,
      ∃ q ∈ A.erase p, dist p q = 1 ∨ dist p q = Metric.diam (A : Set ℝ²)
  · obtain ⟨A, B, hA, hB, hN⟩ := hT hBoundary
    exact two_le_of_pair hA hB hN
  · push Not at hBoundary
    obtain ⟨A, hA, p, hp, hFree⟩ := hBoundary
    have hmove : ∃ A : Finset ℝ², IsMinimiser n A ∧ ∃ p ∈ A,
        ∀ q ∈ A.erase p, 1 < dist p q ∧ dist p q < Metric.diam (A : Set ℝ²) := by
      refine ⟨A, hA, p, hp, ?_⟩
      intro q hq
      have hqA := (mem_erase.mp hq).2
      have hne := (mem_erase.mp hq).1
      have hLow := hA.1.2 hp hqA hne.symm
      change (1 : ℝ≥0∞) ≤ edist p q at hLow
      rw [edist_dist, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hLow
      have hHigh := Metric.dist_le_diam_of_mem A.finite_toSet.isBounded hp hqA
      exact ⟨lt_of_le_of_ne hLow (hFree q hq).1.symm, lt_of_le_of_ne hHigh (hFree q hq).2⟩
    obtain ⟨A', B', hA', hB', hN'⟩ := hM hmove
    exact two_le_of_pair hA' hB' hN'

end OMA.R_Erdos103_erdos_103_variants_two_le_R2
