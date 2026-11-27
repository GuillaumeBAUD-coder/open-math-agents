import OMAReductions.R_LatinSquare_numTransversalsZn_R1
import Mathlib

-- Step LatinSquare.numTransversalsZn.R1.H3: hypothesis H3 of reduction LatinSquare.numTransversalsZn.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
A sequence in the open unit interval converging to an interior point stays in a closed
subinterval: eventually it lies in `[x / 2, (x + 1) / 2]`, and the finitely many earlier terms have
a positive minimum and a maximum below `1`.
-/

namespace LatinSquareStepH3

open Filter Set
open scoped Topology

theorem bounded_away (u : ℕ → ℝ) (x : ℝ) (hu : Tendsto u atTop (𝓝 x)) (hx : x ∈ Ioo (0 : ℝ) 1)
    (h : ∀ n ≥ 1, u n ∈ Ioo (0 : ℝ) 1) :
    ∃ a b : ℝ, 0 < a ∧ b < 1 ∧ a < b ∧ ∀ n ≥ 1, u n ∈ Icc a b := by
  obtain ⟨hx0, hx1⟩ := hx
  have h1 : ∀ᶠ n in atTop, x / 2 < u n := (tendsto_order.1 hu).1 (x / 2) (by linarith)
  have h2 : ∀ᶠ n in atTop, u n < (x + 1) / 2 := (tendsto_order.1 hu).2 ((x + 1) / 2) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h1.and h2)
  have hne : (Finset.Icc 1 (N + 1)).Nonempty := ⟨1, by simp⟩
  obtain ⟨i, hi, himin⟩ := Finset.exists_min_image (Finset.Icc 1 (N + 1)) u hne
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (Finset.Icc 1 (N + 1)) u hne
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  refine ⟨min (x / 2) (u i), max ((x + 1) / 2) (u j), lt_min (by linarith) (h i hi1).1,
    max_lt (by linarith) (h j hj1).2, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le (by linarith) (le_max_left _ _))
  · intro n hn
    by_cases hnN : N ≤ n
    · obtain ⟨ha, hb⟩ := hN n hnN
      exact ⟨le_trans (min_le_left _ _) ha.le, le_trans hb.le (le_max_left _ _)⟩
    · have hmem : n ∈ Finset.Icc 1 (N + 1) := Finset.mem_Icc.2 ⟨hn, by omega⟩
      exact ⟨le_trans (min_le_right _ _) (himin n hmem), le_trans (hjmax n hmem) (le_max_right _ _)⟩

end LatinSquareStepH3

theorem OMA.solution : OMA.R_LatinSquare_numTransversalsZn_R1.H3 :=
  fun u x hu hx h => LatinSquareStepH3.bounded_away u x hu hx h
