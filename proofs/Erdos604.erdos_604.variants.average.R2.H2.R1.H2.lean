import OMAReductions.R_Erdos604_erdos_604_variants_average_R2_H2_R1
import Mathlib

-- Step Erdos604.erdos_604.variants.average.R2.H2.R1.H2: hypothesis H2 of reduction Erdos604.erdos_604.variants.average.R2.H2.R1
-- Credit: @ivillar

/-!
Two distinct centres determine a point of the plane up to at most two choices from its two
distances (Mathlib's `eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`), so every fibre of
`p ↦ (dist p u, dist p v)` has at most two points.
-/
open Finset
open scoped EuclideanGeometry
open scoped Classical

namespace F2E604

theorem fiber : ∀ (A : Finset ℝ²) (u v : ℝ²), u ≠ v →
    A.card ≤ 2 * (A.image fun p => (dist p u, dist p v)).card := by
  intro A u v huv
  apply Finset.card_le_mul_card_image
  intro b hb
  by_contra hcon
  have h3 : 2 < (A.filter (fun p => (dist p u, dist p v) = b)).card := not_le.mp hcon
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.mp h3
  have ep := (Finset.mem_filter.mp hp).2
  have eq' := (Finset.mem_filter.mp hq).2
  have er := (Finset.mem_filter.mp hr).2
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd huv hpq
    (congrArg Prod.fst ep) (congrArg Prod.fst eq') (congrArg Prod.fst er)
    (congrArg Prod.snd ep) (congrArg Prod.snd eq') (congrArg Prod.snd er) with h | h
  · exact hpr h.symm
  · exact hqr h.symm

end F2E604

theorem OMA.solution : OMA.R_Erdos604_erdos_604_variants_average_R2_H2_R1.H2 :=
  F2E604.fiber
