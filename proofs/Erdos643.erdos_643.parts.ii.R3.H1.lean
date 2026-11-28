import OMAReductions.R_Erdos643_erdos_643_parts_ii_R3
import Mathlib

-- Step H1 of reduction Erdos643.erdos_643.parts.ii.R3: the star lower bound.
-- Credit: @Salofe

namespace OMA.Helpers

/-- The star at vertex `v`: all `t`-sets of `Fin n` through `v`, built from `(t-1)`-subsets of
the other vertices. -/
def erdos643Star (n t : ℕ) (v : Fin n) : Finset (Finset (Fin n)) :=
  ((Finset.univ.erase v).powersetCard (t - 1)).image (insert v)

lemma erdos643Star_mem {n t : ℕ} {v : Fin n} {A : Finset (Fin n)}
    (hA : A ∈ erdos643Star n t v) : v ∈ A := by
  unfold erdos643Star at hA
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hA
  exact Finset.mem_insert_self v s

lemma erdos643Star_card_mem {n t : ℕ} (ht : 1 ≤ t) {v : Fin n} {A : Finset (Fin n)}
    (hA : A ∈ erdos643Star n t v) : A.card = t := by
  unfold erdos643Star at hA
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hA
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.1 hs
  have hv : v ∉ s := fun h => by simpa using hsub h
  rw [Finset.card_insert_of_notMem hv]
  omega

lemma erdos643Star_card (n t : ℕ) (v : Fin n) :
    (erdos643Star n t v).card = (n - 1).choose (t - 1) := by
  unfold erdos643Star
  rw [Finset.card_image_of_injOn, Finset.card_powersetCard, Finset.card_erase_of_mem
    (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
  intro s hs s' hs' heq
  have hv : v ∉ s := fun h => by
    simpa using (Finset.mem_powersetCard.1 (Finset.mem_coe.1 hs)).1 h
  have hv' : v ∉ s' := fun h => by
    simpa using (Finset.mem_powersetCard.1 (Finset.mem_coe.1 hs')).1 h
  have := congrArg (fun A => Finset.erase A v) heq
  simpa [Finset.erase_insert hv, Finset.erase_insert hv'] using this

lemma erdos643Star_noRepeat (n t : ℕ) (v : Fin n) :
    ¬ (erdos643Star n t v).HasRepeatedDisjointUnion := by
  rintro ⟨A, hA, B, hB, C, _, D, _, hAB, _⟩
  exact Finset.disjoint_left.1 hAB (erdos643Star_mem hA) (erdos643Star_mem hB)

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos643_erdos_643_parts_ii_R3.H1 := by
  intro t n ht htn
  have hn : 0 < n := by omega
  let v : Fin n := ⟨0, hn⟩
  rw [← erdos643Star_card n t v]
  unfold Hypergraph.extremalNumber
  apply Finset.le_sup (f := Finset.card)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, erdos643Star_noRepeat n t v⟩
  intro A hA
  exact Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, erdos643Star_card_mem ht hA⟩
