import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2
import Mathlib

/-!
Popular translate by double counting. Fix the left offset N. For every x in
[1,N] the right offsets t below 2N with x+N in A+t are exactly x+N-y for y in A,
so there are |A| of them. Summing over x gives |U||A| incidences spread over 2N
offsets, hence one offset t covers at least |U||A|/(2N) points of U; the rest
of U is the leftover set V.
-/

namespace OMA.Helpers

open Finset

/-- For a point x of [1,N], the number of offsets t below 2N with x+N in A+t
equals the size of A (the offsets are x+N-y for y in A). -/
theorem e142ps_offsets_card (N x : ℕ) (hx : x ∈ Icc 1 N) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N) :
    ((range (2*N)).filter (fun t => ∃ y ∈ A, x + N = y + t)).card = A.card := by
  classical
  have hxr := mem_Icc.mp hx
  have himg : (range (2*N)).filter (fun t => ∃ y ∈ A, x + N = y + t)
      = A.image (fun y => x + N - y) := by
    ext t
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨-, y, hy, h⟩
      exact ⟨y, hy, by omega⟩
    · rintro ⟨y, hy, rfl⟩
      have hyr := mem_Icc.mp (hA hy)
      exact ⟨by omega, y, hy, by omega⟩
  rw [himg, card_image_of_injOn]
  intro a ha b hb hab
  have har := mem_Icc.mp (hA ha)
  have hbr := mem_Icc.mp (hA hb)
  simp only at hab
  omega

/-- Total incidence count between U and the translates of A. -/
theorem e142ps_incidences (N : ℕ) (A U : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hU : U ⊆ Icc 1 N) :
    ∑ t ∈ range (2*N), (U.filter (fun x => ∃ y ∈ A, x + N = y + t)).card
      = U.card * A.card := by
  classical
  simp_rw [card_filter]
  rw [sum_comm]
  calc ∑ x ∈ U, ∑ t ∈ range (2*N), (if ∃ y ∈ A, x + N = y + t then 1 else 0)
      = ∑ _x ∈ U, A.card := by
        apply sum_congr rfl
        intro x hx
        rw [← card_filter]
        exact e142ps_offsets_card N x (hU hx) A hA
    _ = U.card * A.card := by rw [sum_const, smul_eq_mul]

/-- Some offset t below 2N carries at least the average number of incidences. -/
theorem e142ps_popular (N : ℕ) (hN : 2 ≤ N) (A U : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hU : U ⊆ Icc 1 N) :
    ∃ t : ℕ, U.card * A.card ≤
      2 * N * (U.filter (fun x => ∃ y ∈ A, x + N = y + t)).card := by
  classical
  by_contra hno
  simp only [not_exists, not_le] at hno
  have hlt : ∑ t ∈ range (2*N), 2 * N * (U.filter (fun x => ∃ y ∈ A, x + N = y + t)).card <
      ∑ _t ∈ range (2*N), U.card * A.card := by
    apply sum_lt_sum_of_nonempty ⟨0, mem_range.mpr (by omega)⟩
    intro t _
    exact hno t
  have hL : ∑ t ∈ range (2*N), 2 * N * (U.filter (fun x => ∃ y ∈ A, x + N = y + t)).card
      = 2 * N * (U.card * A.card) := by
    rw [← mul_sum, e142ps_incidences N A U hA hU]
  have hR : ∑ _t ∈ range (2*N), U.card * A.card = 2 * N * (U.card * A.card) := by
    rw [sum_const, card_range, smul_eq_mul]
  rw [hL, hR] at hlt
  exact lt_irrefl _ hlt

end OMA.Helpers

open OMA.Helpers Finset in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2.H2 := by
  classical
  intro N hN A U hA hU
  obtain ⟨t, ht⟩ := e142ps_popular N hN A U hA hU
  refine ⟨N, t, U.filter (fun x => ¬ ∃ y ∈ A, x + N = y + t), filter_subset _ _, ?_, ?_⟩
  · have hsplit := card_filter_add_card_filter_not (s := U)
      (fun x => ∃ y ∈ A, x + N = y + t)
    have hNr : (0:ℝ) < 2 * N := by
      have : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      linarith
    have h1 : ((U.filter (fun x => ¬ ∃ y ∈ A, x + N = y + t)).card : ℝ)
        = U.card - (U.filter (fun x => ∃ y ∈ A, x + N = y + t)).card := by
      rw [← hsplit]
      push_cast
      ring
    have h2 : (U.card : ℝ) * A.card ≤
        2 * N * (U.filter (fun x => ∃ y ∈ A, x + N = y + t)).card := by
      exact_mod_cast ht
    have h3 : (A.card : ℝ) / (2 * N) * U.card ≤
        (U.filter (fun x => ∃ y ∈ A, x + N = y + t)).card := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hNr]
      linarith
    rw [h1, sub_mul, one_mul]
    linarith
  · intro x hx hxV
    by_contra hno
    exact hxV (mem_filter.mpr ⟨hx, hno⟩)
