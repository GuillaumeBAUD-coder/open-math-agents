import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Data.Fin.Embedding

namespace OMA.R_RamseyNumbers_ramsey_number_three_nine_R1

open RamseyNumbers SimpleGraph

-- Kalbfleisch's circulant on 35 vertices supplies the lower witness.
def H1 : Prop := ∃ G : SimpleGraph (Fin 35), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 9

-- The Goedgebeur--Radziszowski classification implies this minimum-degree bound.
def H2 : Prop :=
  ∀ (G : SimpleGraph (Fin 35)) [DecidableRel G.Adj],
    G.CliqueFree 3 → Gᶜ.CliqueFree 9 → ∀ v, 8 ≤ G.degree v

theorem main : H1 → H2 → type_of% @RamseyNumbers.ramsey_number_three_nine := by
  classical
  intro witness minimum
  have upper : IsGraphRamsey 36 3 9 := by
    rintro G ⟨ht, hi⟩
    have maxdeg (v : Fin 36) : G.degree v < 9 := by
      by_contra! h
      apply hi.mono h (G.neighborFinset v)
      refine ⟨?_, rfl⟩
      rw [G.coe_neighborFinset, G.isClique_compl]
      exact G.isIndepSet_neighborSet_of_triangleFree ht v
    have lower (v : Fin 36) (w : Fin 35) :
        8 ≤ (G.comap v.succAboveEmb).degree w := by
      let e := SimpleGraph.Embedding.comap v.succAboveEmb G
      exact minimum _ (CliqueFree.comap e.isContained ht)
        (CliqueFree.comap (SimpleGraph.Embedding.complEquiv e).isContained hi) w
    have noEdge (u v : Fin 36) (huv : G.Adj u v) : False := by
      obtain ⟨w, rfl⟩ := Fin.exists_succAbove_eq huv.ne
      let f := v.succAboveEmb
      let H := G.comap f
      have incl : ((H.neighborFinset w).map f) ⊂ G.neighborFinset (f w) := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro z hz
          obtain ⟨i, hi', rfl⟩ := Finset.mem_map.mp hz
          exact (G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp hi')
        · intro he
          have mem : v ∈ (H.neighborFinset w).map f := he ▸ (G.mem_neighborFinset _ _).mpr huv
          obtain ⟨i, _, eq⟩ := Finset.mem_map.mp mem
          exact Fin.succAbove_ne v i eq
      have less := Finset.card_lt_card incl
      rw [Finset.card_map] at less
      change H.degree w < G.degree (f w) at less
      have lo : 8 ≤ H.degree w := lower v w
      have up := maxdeg (f w)
      omega
    apply hi.mono (show 9 ≤ 36 by decide) Finset.univ
    refine ⟨?_, by simp⟩
    intro u _ v _ huv
    exact ⟨huv, noEdge u v⟩
  rw [classicalRamsey_eq_sInf]
  apply IsLeast.csInf_eq
  refine ⟨upper, ?_⟩
  intro n hn
  by_contra! hlt
  have mono : Monotone (fun m => IsGraphRamsey m 3 9) :=
    monotone_nat_of_le_succ fun m => IsGraphRamsey.succ m 3 9
  obtain ⟨G, ht, hi⟩ := witness
  exact mono (show n ≤ 35 by omega) hn G ⟨ht, hi⟩

end OMA.R_RamseyNumbers_ramsey_number_three_nine_R1
