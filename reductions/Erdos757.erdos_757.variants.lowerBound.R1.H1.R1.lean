import OMAReductions.R_Erdos757_erdos_757_variants_lowerBound_R1

/-! The arithmetic-progression hypergraph of a (4,5)-set, following Gyárfás and Lehel.
The original proof bounds the transversal number of a sparse triple system.
Ma and Tang, arXiv:2602.23282, sharpen the resulting fraction to 9/17 using
Henning and Yeo. Either transversal estimate suffices in the second step. -/

namespace OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1
open Finset
open scoped Pointwise Classical

/-- All proper progressions are covered by a sparse, linear, F₇-free triple system. -/
def H1 : Prop := ∀ A : Finset ℝ,
    (∀ B ⊆ (A : Set ℝ), B.ncard = 4 → 11 ≤ (B - B).ncard) →
    ∃ E : Finset (Finset ℝ), E.card ≤ A.card ∧
      (∀ e ∈ E, e ⊆ A ∧ e.card = 3) ∧
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) ∧
      (∀ u : Fin 7 → ℝ, Function.Injective u →
        ¬ ({u 0,u 1,u 2} ∈ E ∧ {u 0,u 3,u 4} ∈ E ∧ {u 0,u 5,u 6} ∈ E ∧
          {u 1,u 3,u 5} ∈ E ∧ {u 2,u 4,u 6} ∈ E)) ∧
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + z = 2*y → x ≠ z → {x,y,z} ∈ E

/-- A transversal saving, uniform in the size of the sparse linear triple system. -/
def H2 : Prop := ∃ r : ℝ, r < 1/2 ∧ ∀ (A : Finset ℝ) (E : Finset (Finset ℝ)), E.card ≤ A.card →
    (∀ e ∈ E, e ⊆ A ∧ e.card = 3) →
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) →
    (∀ u : Fin 7 → ℝ, Function.Injective u →
      ¬ ({u 0,u 1,u 2} ∈ E ∧ {u 0,u 3,u 4} ∈ E ∧ {u 0,u 5,u 6} ∈ E ∧
        {u 1,u 3,u 5} ∈ E ∧ {u 2,u 4,u 6} ∈ E)) →
    ∃ T ⊆ A, (∀ e ∈ E, ∃ x ∈ e, x ∈ T) ∧ (T.card : ℝ) ≤ r*A.card

theorem main : H1 → H2 → OMA.R_Erdos757_erdos_757_variants_lowerBound_R1.H1 := by
  rintro geometry ⟨r,hr,cover⟩
  refine ⟨1-r, by linarith, ?_⟩
  intro A hA _hZ hfour
  let V := hA.toFinset
  have hV : (V : Set ℝ) = A := hA.coe_toFinset
  obtain ⟨E,small,triple,linear,free,progress⟩ := geometry V (by simpa [hV] using hfour)
  obtain ⟨T,sub,hit,cost⟩ := cover V E small triple linear free
  refine ⟨(↑(V \ T) : Set ℝ),?_,?_,?_⟩
  · exact hV ▸ (show ((V \ T : Finset ℝ) : Set ℝ) ⊆ (V : Set ℝ) from
      fun _ hx => (mem_sdiff.mp hx).1)
  · intro x hx y hy z hz hsum
    by_contra hne
    obtain ⟨w,hw,hwT⟩ := hit _ (progress x (mem_sdiff.mp hx).1 y (mem_sdiff.mp hy).1 z
      (mem_sdiff.mp hz).1 hsum hne)
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl|rfl|rfl
    · exact (mem_sdiff.mp hx).2 hwT
    · exact (mem_sdiff.mp hy).2 hwT
    · exact (mem_sdiff.mp hz).2 hwT
  · have total : ((V \ T).card : ℝ) + T.card = V.card := by
      exact_mod_cast card_sdiff_add_card_eq_card sub
    have cardA : A.ncard = V.card := by rw [← hV, Set.ncard_coe_finset]
    rw [cardA,Set.ncard_coe_finset]
    linarith

end OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1
