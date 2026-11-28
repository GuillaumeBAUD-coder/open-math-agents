import OMAReductions.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1
import Mathlib

/-!
Reduction of `Arxiv.2605.02731.dean_conjecture.variants.six_le.R1.H2` (odd case `k >= 7` of
Dean's conjecture, proved by Luo-Ma-Zhao 2026) to two concrete 2-connected end-block theorems
on `Fin n`:
1. `H1`: 2-connected bipartite graphs on `Fin n` (`n >= k + 1`) with at most one vertex `r`
   of degree `< k` contain a cycle of length divisible by `2 * k`.
2. `H2`: 2-connected non-bipartite graphs on `Fin n` (`n >= k + 1`) containing an odd cycle,
   with at most one vertex `r` of degree `< k`, contain a cycle of length divisible by `k`.

In `main`, we prove from scratch:
- the 2-connected end-block extraction theorem for finite connected graphs with `minDegree >= k`,
- canonical transport from arbitrary finite `V : Type` to `Fin n` preserving 2-connectedness,
  degrees, bipartiteness, and cycle lengths,
- the parity characterization of bipartite graphs (every cycle in a bipartite graph has even
  length, and every connected non-bipartite finite graph contains an odd cycle via BFS
  distance-parity coloring and minimal-length odd closed walk extraction).
-/

open SimpleGraph

namespace OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H2_R1

/- Bipartite 2-connected end-block case for odd k >= 7 (Luo-Ma-Zhao 2026):
every 2-connected bipartite graph on Fin n (n >= k + 1) with at most one vertex of degree < k
contains a cycle of length divisible by 2 * k. -/
def H1 : Prop :=
  ∀ {n k : ℕ}, 7 ≤ k → Odd k → k + 1 ≤ n →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.IsBipartite →
      (∀ v : Fin n, (G.induce {u : Fin n | u ≠ v}).Connected) →
      (∃ r : Fin n, ∀ v : Fin n, v ≠ r → k ≤ G.degree v) →
      ∃ m ∈ G.cycleLengths, 2 * k ∣ m

/- Non-bipartite 2-connected end-block case for odd k >= 7 (Luo-Ma-Zhao 2026):
every 2-connected non-bipartite graph on Fin n (n >= k + 1) containing an odd cycle,
with at most one vertex of degree < k, contains a cycle of length divisible by k. -/
def H2 : Prop :=
  ∀ {n k : ℕ}, 7 ≤ k → Odd k → k + 1 ≤ n →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ¬ G.IsBipartite →
      (∃ m₀ ∈ G.cycleLengths, Odd m₀) →
      (∀ v : Fin n, (G.induce {u : Fin n | u ≠ v}).Connected) →
      (∃ r : Fin n, ∀ v : Fin n, v ≠ r → k ≤ G.degree v) →
      ∃ m ∈ G.cycleLengths, k ∣ m

/- Any graph homomorphism that is injective maps cycleLengths into the codomain. -/
lemma cycleLengths_subset_of_hom_inj {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) :
    G.cycleLengths ⊆ H.cycleLengths := by
  intro m hm
  rcases hm with ⟨v, p, hp, rfl⟩
  exact ⟨f v, p.map f, hp.map hf, by simp⟩

/- A graph isomorphism preserves vertex degrees. -/
lemma iso_degree_eq {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (v : V) :
    H.degree (e v) = G.degree v := by
  rw [← H.card_neighborSet_eq_degree, ← G.card_neighborSet_eq_degree]
  refine Fintype.card_congr ?_
  exact
    { toFun := fun w => ⟨e.symm w.1, by
        have h : H.Adj (e v) w.1 := w.2
        have h' : H.Adj (e v) (e (e.symm w.1)) := by simpa using h
        exact (e.map_rel_iff).mp h'⟩
      invFun := fun u => ⟨e u.1, (e.map_rel_iff).mpr u.2⟩
      left_inv := fun w => Subtype.ext (e.apply_symm_apply w.1)
      right_inv := fun u => Subtype.ext (e.symm_apply_apply u.1) }

/- A graph isomorphism preserves 2-connectedness (connectedness after deleting any vertex). -/
lemma iso_two_connected {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H)
    (hG : ∀ x : V, (G.induce {u : V | u ≠ x}).Connected) :
    ∀ y : W, (H.induce {u : W | u ≠ y}).Connected := by
  intro y
  let f : G.induce {u : V | u ≠ e.symm y} →g H.induce {u : W | u ≠ y} :=
    { toFun := fun x => ⟨e x.1, fun h => x.2 (by simpa using congrArg e.symm h)⟩
      map_rel' := fun {_ _} hadj => e.map_rel_iff.mpr hadj }
  have hsurj : Function.Surjective f := by
    intro w
    refine ⟨⟨e.symm w.1, fun h => w.2 (by simpa using congrArg e h)⟩, ?_⟩
    exact Subtype.ext (e.apply_symm_apply w.1)
  exact (hG (e.symm y)).map f hsurj

/- Any 2-connected graph on at least 3 vertices is connected. -/
lemma connected_of_two_connected {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (h2conn : ∀ x : V, (G.induce {u : V | u ≠ x}).Connected) :
    G.Connected := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine SimpleGraph.Connected.mk fun a b => ?_
  have hex : ∃ c : V, c ≠ a ∧ c ≠ b := by
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ : Finset V) ⊆ {a, b} := by
      intro x _
      by_cases hxa : x = a
      · simp [hxa]
      · simp [hno x hxa]
    have hle : Fintype.card V ≤ ({a, b} : Finset V).card := by
      simpa using Finset.card_le_card hsub
    have hle2 : ({a, b} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨c, hca, hcb⟩ := hex
  have hreach := (h2conn c) ⟨a, hca.symm⟩ ⟨b, hcb.symm⟩
  exact hreach.map (SimpleGraph.Embedding.induce {u : V | u ≠ c}).toHom

/- Cardinality lower bound from a vertex of degree at least k. -/
lemma card_ge_succ_of_degree_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (v : V) (hv : k ≤ G.degree v) :
    k + 1 ≤ Fintype.card V := by
  rw [← G.card_neighborFinset_eq_degree] at hv
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro w hw
    have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    exact Finset.mem_erase.mpr ⟨hadj.ne.symm, Finset.mem_univ w⟩
  have hle : (G.neighborFinset v).card ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
  have herase : (Finset.univ.erase v).card + 1 = Fintype.card V := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    omega
  omega

/- Walk lifting into an induced subgraph when every support vertex belongs to the subset. -/
lemma reachable_induce_of_walk_support {V : Type*} (G : SimpleGraph V) (S : Set V)
    {x y : V} (w : G.Walk x y) (hsupp : ∀ z ∈ w.support, z ∈ S) :
    (G.induce S).Reachable ⟨x, hsupp x w.start_mem_support⟩ ⟨y, hsupp y w.end_mem_support⟩ := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hab p ih =>
    rename_i a b c
    have ha : a ∈ S := hsupp a (by simp)
    have hb : b ∈ S := hsupp b (by simp)
    have hpsupp : ∀ z ∈ p.support, z ∈ S := fun z hz => hsupp z (by simp [hz])
    have hadj : (G.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ := hab
    exact hadj.reachable.trans (ih hpsupp)

/- End-block extraction theorem: every finite connected simple graph with minDegree >= k (k >= 2)
contains an induced 2-connected subgraph on at least k + 1 vertices in which every vertex except
possibly one cut-vertex r has degree at least k. -/
lemma exists_two_connected_end_block {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 2 ≤ k)
    (hconn : G.Connected) (hdeg : k ≤ G.minDegree) :
    ∃ (S : Finset V) (r : (S : Set V)),
      k + 1 ≤ S.card ∧
      (∀ x : (S : Set V), ((G.induce (S : Set V)).induce {y : (S : Set V) | y ≠ x}).Connected) ∧
      (∀ y : (S : Set V), y ≠ r → k ≤ (G.induce (S : Set V)).degree y) := by
  classical
  have hneV : Nonempty V := hconn.nonempty
  obtain ⟨v₀⟩ := hneV
  have hcardV : k + 1 ≤ Fintype.card V :=
    card_ge_succ_of_degree_ge G v₀ (le_trans hdeg (G.minDegree_le_degree v₀))
  by_cases h2G : ∀ x : V, (G.induce {u : V | u ≠ x}).Connected
  · refine ⟨Finset.univ, ⟨v₀, Finset.mem_coe.mpr (Finset.mem_univ v₀)⟩, ?_, ?_, ?_⟩
    · rw [Finset.card_univ]; exact hcardV
    · intro x
      let e : G.induce {u : V | u ≠ x.1} ≃g
          (G.induce ((Finset.univ : Finset V) : Set V)).induce {y : ((Finset.univ : Finset V) : Set V) | y ≠ x} :=
        { toFun := fun u => ⟨⟨u.1, Finset.mem_coe.mpr (Finset.mem_univ u.1)⟩,
            fun h => u.2 (congrArg Subtype.val h)⟩
          invFun := fun y => ⟨y.1.1, fun h => y.2 (Subtype.ext h)⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
          map_rel_iff' := Iff.rfl }
      exact (h2G x.1).map e.toHom e.surjective
    · intro y _
      let e : G ≃g G.induce ((Finset.univ : Finset V) : Set V) :=
        { toFun := fun u => ⟨u, Finset.mem_coe.mpr (Finset.mem_univ u)⟩
          invFun := fun u => u.1
          left_inv := fun _ => rfl
          right_inv := fun _ => Subtype.ext rfl
          map_rel_iff' := Iff.rfl }
      have hdeq : (G.induce ((Finset.univ : Finset V) : Set V)).degree y = G.degree y.1 := by
        have h := iso_degree_eq e y.1
        have he : e y.1 = y := Subtype.ext rfl
        rwa [he] at h
      rw [hdeq]
      exact le_trans hdeg (G.minDegree_le_degree y.1)
  · let IsSepComp : V → Finset V → Prop := fun r C =>
      C.Nonempty ∧ r ∉ C ∧
      (G.induce (C : Set V)).Connected ∧
      (∀ u ∈ C, ∀ w : V, G.Adj u w → w ∈ C ∨ w = r) ∧
      (∃ z : V, z ≠ r ∧ z ∉ C)
    have hex_sep : ∃ m : ℕ, ∃ (r : V) (C : Finset V), IsSepComp r C ∧ C.card = m := by
      push Not at h2G
      obtain ⟨r, hnot⟩ := h2G
      have hne_del : Nonempty {u : V | u ≠ r} := by
        have hpos : 0 < (Finset.univ.erase r).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ]
          omega
        obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
        exact ⟨⟨u, (Finset.mem_erase.mp hu).1⟩⟩
      obtain ⟨a, b, hnab⟩ : ∃ a b : {u : V | u ≠ r}, ¬ (G.induce {u : V | u ≠ r}).Reachable a b := by
        by_contra hall
        push Not at hall
        exact hnot (SimpleGraph.Connected.mk hall)
      let C : Finset V := Finset.univ.filter fun w : V =>
        ∃ hw : w ≠ r, (G.induce {u : V | u ≠ r}).Reachable a ⟨w, hw⟩
      have hmemC : ∀ (w : V), w ∈ C ↔ ∃ hw : w ≠ r, (G.induce {u : V | u ≠ r}).Reachable a ⟨w, hw⟩ := by
        intro w
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨C.card, r, C, ⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
      · exact ⟨a.1, (hmemC a.1).mpr ⟨a.2, SimpleGraph.Reachable.refl a⟩⟩
      · intro hr
        obtain ⟨hrr, _⟩ := (hmemC r).mp hr
        exact hrr rfl
      · have hneC : Nonempty (C : Set V) := ⟨⟨a.1, (hmemC a.1).mpr ⟨a.2, SimpleGraph.Reachable.refl a⟩⟩⟩
        refine SimpleGraph.Connected.mk fun x y => ?_
        obtain ⟨hx_ne, hax⟩ := (hmemC x.1).mp x.2
        obtain ⟨hy_ne, hay⟩ := (hmemC y.1).mp y.2
        obtain ⟨w⟩ := hax.symm.trans hay
        have hw_supp : ∀ z ∈ (w.map (SimpleGraph.Embedding.induce {u : V | u ≠ r}).toHom).support, z ∈ (C : Set V) := by
          intro z hz
          rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
          obtain ⟨z', hz', rfl⟩ := hz
          have hxz' : (G.induce {u : V | u ≠ r}).Reachable ⟨x.1, hx_ne⟩ z' :=
            ⟨w.takeUntil z' hz'⟩
          exact (hmemC z'.1).mpr ⟨z'.2, hax.trans hxz'⟩
        exact reachable_induce_of_walk_support G (C : Set V)
          (w.map (SimpleGraph.Embedding.induce {u : V | u ≠ r}).toHom) hw_supp
      · intro u hu w hadj
        by_cases hwr : w = r
        · exact Or.inr hwr
        · left
          obtain ⟨hu_ne, hau⟩ := (hmemC u).mp hu
          have hadj' : (G.induce {u : V | u ≠ r}).Adj ⟨u, hu_ne⟩ ⟨w, hwr⟩ := hadj
          exact (hmemC w).mpr ⟨hwr, hau.trans hadj'.reachable⟩
      · refine ⟨b.1, b.2, fun hb => ?_⟩
        obtain ⟨_, hab⟩ := (hmemC b.1).mp hb
        exact hnab hab
    let m₀ := Nat.find hex_sep
    obtain ⟨r, C, hC, hC_card⟩ := Nat.find_spec hex_sep
    have hmin : ∀ r' C', IsSepComp r' C' → C.card ≤ C'.card := by
      intro r' C' hC'
      rw [hC_card]
      exact Nat.find_min' hex_sep ⟨r', C', hC', rfl⟩
    let S : Finset V := insert r C
    have hrS : r ∈ (S : Set V) := Finset.mem_coe.mpr (Finset.mem_insert_self r C)
    have hmemS : ∀ w : V, w ∈ (S : Set V) ↔ w = r ∨ w ∈ C := by
      intro w
      simp only [S, Finset.mem_coe, Finset.mem_insert]
    have hdeg_in_C : ∀ (u : V) (hu : u ∈ C),
        k ≤ (G.induce (S : Set V)).degree ⟨u, (hmemS u).mpr (Or.inr hu)⟩ := by
      intro u hu
      have hGu : k ≤ G.degree u := le_trans hdeg (G.minDegree_le_degree u)
      refine le_trans hGu ?_
      rw [← G.card_neighborSet_eq_degree, ← (G.induce (S : Set V)).card_neighborSet_eq_degree]
      let f : G.neighborSet u → (G.induce (S : Set V)).neighborSet ⟨u, (hmemS u).mpr (Or.inr hu)⟩ :=
        fun w => ⟨⟨w.1, (hmemS w.1).mpr (Or.symm (hC.2.2.2.1 u hu w.1 w.2))⟩, w.2⟩
      have hf : Function.Injective f := fun w₁ w₂ h => Subtype.ext (congrArg (fun t => t.1.1) h)
      exact Fintype.card_le_of_injective f hf
    obtain ⟨u₀, hu₀⟩ := hC.1
    have hcardS : k + 1 ≤ S.card := by
      have h := card_ge_succ_of_degree_ge (G.induce (S : Set V))
        ⟨u₀, (hmemS u₀).mpr (Or.inr hu₀)⟩ (hdeg_in_C u₀ hu₀)
      have heq : Fintype.card (S : Set V) = S.card := by
        rw [← Fintype.card_coe S]
        exact Fintype.card_congr
          { toFun := fun x => ⟨x.1, Finset.mem_coe.mp x.2⟩
            invFun := fun x => ⟨x.1, Finset.mem_coe.mpr x.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      omega
    refine ⟨S, ⟨r, hrS⟩, hcardS, ?_, ?_⟩
    · intro x
      by_cases hxr : x.1 = r
      · let e : G.induce (C : Set V) ≃g (G.induce (S : Set V)).induce {y : (S : Set V) | y ≠ x} :=
          { toFun := fun u => ⟨⟨u.1, (hmemS u.1).mpr (Or.inr u.2)⟩, fun h => hC.2.1 (by
              have hux : u.1 = x.1 := congrArg Subtype.val h
              rw [hxr] at hux
              exact hux ▸ u.2)⟩
            invFun := fun y => ⟨y.1.1, by
              rcases (hmemS y.1.1).mp y.1.2 with hyr | hyC
              · exfalso
                apply y.2
                exact Subtype.ext (by rw [hyr, hxr])
              · exact hyC⟩
            left_inv := fun _ => Subtype.ext rfl
            right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
            map_rel_iff' := Iff.rfl }
        exact hC.2.2.1.map e.toHom e.surjective
      · have hxC : x.1 ∈ C := by
          rcases (hmemS x.1).mp x.2 with h | h
          · exact absurd h hxr
          · exact h
        by_contra hnot
        let T : Set (S : Set V) := {y : (S : Set V) | y ≠ x}
        let rS : T := ⟨⟨r, hrS⟩, fun h => hxr (congrArg Subtype.val h).symm⟩
        have hneT : Nonempty T := ⟨rS⟩
        have hex_a : ∃ a : T, ¬ ((G.induce (S : Set V)).induce T).Reachable rS a := by
          by_contra hall
          push Not at hall
          have hconnT : ((G.induce (S : Set V)).induce T).Connected :=
            SimpleGraph.Connected.mk fun u v => (hall u).symm.trans (hall v)
          exact hnot hconnT
        obtain ⟨a, hna⟩ := hex_a
        let C' : Finset V := Finset.univ.filter fun w : V =>
          ∃ (hw : w ∈ (S : Set V)) (hwx : (⟨w, hw⟩ : (S : Set V)) ≠ x),
            ((G.induce (S : Set V)).induce T).Reachable a ⟨⟨w, hw⟩, hwx⟩
        have hmemC' : ∀ w : V, w ∈ C' ↔
            ∃ (hw : w ∈ (S : Set V)) (hwx : (⟨w, hw⟩ : (S : Set V)) ≠ x),
              ((G.induce (S : Set V)).induce T).Reachable a ⟨⟨w, hw⟩, hwx⟩ := by
          intro w
          simp only [C', Finset.mem_filter, Finset.mem_univ, true_and]
        have hr_not_C' : r ∉ C' := by
          intro hr'
          obtain ⟨hw, hwx, har⟩ := (hmemC' r).mp hr'
          have heq : (⟨⟨r, hw⟩, hwx⟩ : T) = rS := Subtype.ext (Subtype.ext rfl)
          rw [heq] at har
          exact hna har.symm
        have hC'_sub : C' ⊆ C.erase x.1 := by
          intro w hw
          obtain ⟨hwS, hwx, _⟩ := (hmemC' w).mp hw
          have hwx' : w ≠ x.1 := fun h => hwx (Subtype.ext h)
          have hwC : w ∈ C := by
            rcases (hmemS w).mp hwS with hwr | h
            · exact absurd (hwr ▸ hw) hr_not_C'
            · exact h
          exact Finset.mem_erase.mpr ⟨hwx', hwC⟩
        have hlt : C'.card < C.card := by
          have hle : C'.card ≤ (C.erase x.1).card := Finset.card_le_card hC'_sub
          have her : (C.erase x.1).card < C.card := Finset.card_erase_lt_of_mem hxC
          exact lt_of_le_of_lt hle her
        have hsep' : IsSepComp x.1 C' := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · exact ⟨a.1.1, (hmemC' a.1.1).mpr ⟨a.1.2, a.2, SimpleGraph.Reachable.refl a⟩⟩
          · intro hx'
            obtain ⟨_, hxx, _⟩ := (hmemC' x.1).mp hx'
            exact hxx (Subtype.ext rfl)
          · have hneC' : Nonempty (C' : Set V) :=
              ⟨⟨a.1.1, (hmemC' a.1.1).mpr ⟨a.1.2, a.2, SimpleGraph.Reachable.refl a⟩⟩⟩
            refine SimpleGraph.Connected.mk fun y₁ y₂ => ?_
            obtain ⟨h1S, h1x, ha1⟩ := (hmemC' y₁.1).mp y₁.2
            obtain ⟨h2S, h2x, ha2⟩ := (hmemC' y₂.1).mp y₂.2
            obtain ⟨w⟩ := ha1.symm.trans ha2
            let emb : (G.induce (S : Set V)).induce T →g G :=
              (SimpleGraph.Embedding.induce (S : Set V)).toHom.comp (SimpleGraph.Embedding.induce T).toHom
            have hsupp : ∀ z ∈ (w.map emb).support, z ∈ (C' : Set V) := by
              intro z hz
              rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
              obtain ⟨z', hz', rfl⟩ := hz
              have h1z' : ((G.induce (S : Set V)).induce T).Reachable ⟨⟨y₁.1, h1S⟩, h1x⟩ z' :=
                ⟨w.takeUntil z' hz'⟩
              exact (hmemC' z'.1.1).mpr ⟨z'.1.2, z'.2, ha1.trans h1z'⟩
            exact reachable_induce_of_walk_support G (C' : Set V) (w.map emb) hsupp
          · intro u hu w hadj
            by_cases hwx : w = x.1
            · exact Or.inr hwx
            · left
              have huC : u ∈ C := (Finset.mem_erase.mp (hC'_sub hu)).2
              have hwS : w ∈ (S : Set V) := (hmemS w).mpr (Or.symm (hC.2.2.2.1 u huC w hadj))
              obtain ⟨huS, hux, hau⟩ := (hmemC' u).mp hu
              have hwxS : (⟨w, hwS⟩ : (S : Set V)) ≠ x := fun h => hwx (congrArg Subtype.val h)
              have hadjT : ((G.induce (S : Set V)).induce T).Adj ⟨⟨u, huS⟩, hux⟩ ⟨⟨w, hwS⟩, hwxS⟩ := hadj
              exact (hmemC' w).mpr ⟨hwS, hwxS, hau.trans hadjT.reachable⟩
          · exact ⟨r, Ne.symm hxr, hr_not_C'⟩
        have hge : C.card ≤ C'.card := hmin x.1 C' hsep'
        omega
    · intro y hy
      have hyC : y.1 ∈ C := by
        rcases (hmemS y.1).mp y.2 with hyr | h
        · exfalso
          exact hy (Subtype.ext hyr)
        · exact h
      have hy_eq : (⟨y.1, (hmemS y.1).mpr (Or.inr hyC)⟩ : (S : Set V)) = y := Subtype.ext rfl
      rw [← hy_eq]
      exact hdeg_in_C y.1 hyC

/- In any bipartite graph, a walk's length is even iff its endpoints receive the same 2-color. -/
lemma coloring_two_eq_iff_even_length {V : Type*} {G : SimpleGraph V}
    (c : G.Coloring (Fin 2)) {u v : V} (w : G.Walk u v) :
    c u = c v ↔ Even w.length := by
  induction w with
  | nil =>
    simp
  | cons hab p ih =>
    rename_i a b d
    have hne : c a ≠ c b := c.valid hab
    have hpar : (c a = c d) ↔ (c b ≠ c d) := by
      have ha := (c a).isLt
      have hb := (c b).isLt
      have hd := (c d).isLt
      constructor
      · intro h1 h2
        exact hne (h1.trans h2.symm)
      · intro h2
        apply Fin.ext
        have hne' : (c a).val ≠ (c b).val := fun h => hne (Fin.ext h)
        have h2' : (c b).val ≠ (c d).val := fun h => h2 (Fin.ext h)
        omega
    rw [hpar, SimpleGraph.Walk.length_cons, Nat.even_add_one]
    exact ih.not

/- Every cycle in a bipartite graph has even length. -/
lemma even_of_mem_cycleLengths_of_isBipartite {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite) {m : ℕ} (hm : m ∈ G.cycleLengths) : Even m := by
  obtain ⟨c⟩ := hbip
  rcases hm with ⟨v, w, _, rfl⟩
  exact (coloring_two_eq_iff_even_length c w).mp rfl

/- Every walk that is not a path decomposes into prefix, nontrivial closed walk, and suffix. -/
lemma exists_split_of_not_isPath {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {x y : V} (p : G.Walk x y) (hnp : ¬ p.IsPath) :
    ∃ (z : V) (p₁ : G.Walk x z) (c : G.Walk z z) (p₂ : G.Walk z y),
      0 < c.length ∧ p₁.length + c.length + p₂.length = p.length := by
  induction p with
  | nil =>
    exact absurd SimpleGraph.Walk.IsPath.nil hnp
  | cons hab q ih =>
    rename_i a b d
    by_cases ha : a ∈ q.support
    · refine ⟨a, SimpleGraph.Walk.nil, SimpleGraph.Walk.cons hab (q.takeUntil a ha),
        q.dropUntil a ha, ?_, ?_⟩
      · simp
      · have hlen := congrArg SimpleGraph.Walk.length (q.take_spec ha)
        rw [SimpleGraph.Walk.length_append] at hlen
        simp only [SimpleGraph.Walk.length_nil, SimpleGraph.Walk.length_cons, zero_add]
        omega
    · have hnq : ¬ q.IsPath := by
        intro hq
        apply hnp
        rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons, List.nodup_cons]
        exact ⟨ha, hq.support_nodup⟩
      obtain ⟨z, q₁, c, p₂, hcpos, hlen⟩ := ih hnq
      refine ⟨z, SimpleGraph.Walk.cons hab q₁, c, p₂, hcpos, ?_⟩
      simp only [SimpleGraph.Walk.length_cons]
      omega

/- Any odd closed walk yields an odd cycle (by taking a minimal-length odd closed walk). -/
lemma exists_odd_cycle_of_odd_closed_walk {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hex : ∃ (a : V) (w : G.Walk a a), Odd w.length) :
    ∃ m ∈ G.cycleLengths, Odd m := by
  classical
  have hexn : ∃ n : ℕ, ∃ (a : V) (w : G.Walk a a), Odd w.length ∧ w.length = n := by
    obtain ⟨a, w, hodd⟩ := hex
    exact ⟨w.length, a, w, hodd, rfl⟩
  let n₀ := Nat.find hexn
  obtain ⟨a, w, hodd, hwlen⟩ := Nat.find_spec hexn
  have hmin : ∀ (b : V) (p : G.Walk b b), Odd p.length → w.length ≤ p.length := by
    intro b p hp
    rw [hwlen]
    exact Nat.find_min' hexn ⟨b, p, hp, rfl⟩
  have hlen3 : 3 ≤ w.length := by
    cases w with
    | nil =>
      rcases hodd with ⟨t, ht⟩
      simp only [SimpleGraph.Walk.length_nil] at ht
      omega
    | cons hab p =>
      cases p with
      | nil => exact absurd rfl (G.ne_of_adj hab)
      | cons hbc q =>
        cases q with
        | nil =>
          rcases hodd with ⟨t, ht⟩
          simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at ht
          omega
        | cons _ _ =>
          simp only [SimpleGraph.Walk.length_cons]
          omega
  have htail_path : w.tail.IsPath := by
    cases w with
    | nil =>
      simp only [SimpleGraph.Walk.length_nil] at hlen3
      omega
    | cons hab p =>
      have hp : p.IsPath := by
        by_contra hnp
        obtain ⟨z, p₁, c, p₂, hcpos, hsplit⟩ := exists_split_of_not_isPath p hnp
        let w' : G.Walk a a := SimpleGraph.Walk.cons hab (p₁.append p₂)
        have hw'_len : w'.length = 1 + p₁.length + p₂.length := by
          simp only [w', SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_append]
          omega
        have hsum : c.length + w'.length = (SimpleGraph.Walk.cons hab p).length := by
          rw [hw'_len, SimpleGraph.Walk.length_cons]
          omega
        have hlt_c : c.length < (SimpleGraph.Walk.cons hab p).length := by
          rw [SimpleGraph.Walk.length_cons]
          omega
        have hlt_w' : w'.length < (SimpleGraph.Walk.cons hab p).length := by
          omega
        rcases Nat.even_or_odd c.length with hec | hoc
        · have how' : Odd w'.length := by
            rcases hec with ⟨r, hr⟩
            rcases hodd with ⟨s, hs⟩
            exact ⟨s - r, by omega⟩
          have hle := hmin a w' how'
          omega
        · have hle := hmin z c hoc
          omega
      cases p with
      | nil => exact hp
      | cons _ _ => exact hp
  have hcyc : w.IsCycle :=
    SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨htail_path, hlen3⟩
  exact ⟨w.length, ⟨a, w, hcyc, rfl⟩, hodd⟩

/- Every connected non-bipartite graph contains an odd cycle (via BFS distance-parity coloring). -/
lemma exists_odd_cycle_of_connected_not_isBipartite {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (hnb : ¬ G.IsBipartite) :
    ∃ m ∈ G.cycleLengths, Odd m := by
  classical
  obtain ⟨v₀⟩ := hconn.nonempty
  let f : V → Fin 2 := fun v => ⟨(G.edist v₀ v).toNat % 2, Nat.mod_lt _ (by omega)⟩
  have hbad : ∃ u w : V, G.Adj u w ∧ f u = f w := by
    by_contra hall
    push Not at hall
    exact hnb ⟨SimpleGraph.Coloring.mk f (fun hadj => hall _ _ hadj)⟩
  obtain ⟨u, w, hadj, hfeq⟩ := hbad
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_edist v₀ u
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_edist v₀ w
  have hmod : p.length % 2 = q.length % 2 := by
    have hv := congrArg Fin.val hfeq
    simp only [f] at hv
    rw [← hp, ← hq, ENat.toNat_natCast, ENat.toNat_natCast] at hv
    exact hv
  let W : G.Walk v₀ v₀ := p.append (SimpleGraph.Walk.cons hadj q.reverse)
  have hW_odd : Odd W.length := by
    have hlen : W.length = p.length + (q.length + 1) := by
      simp [W]
    rw [hlen]
    exact ⟨p.length / 2 + q.length / 2 + p.length % 2, by omega⟩
  exact exists_odd_cycle_of_odd_closed_walk G ⟨v₀, W, hW_odd⟩

theorem main : H1 → H2 →
    OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1.H2 := by
  classical
  intro hH1 hH2 V _ _ k hk hodd G _ hconn hdeg
  obtain ⟨S, r, hcardS, h2connS, hdegS⟩ :=
    exists_two_connected_end_block G (by omega) hconn hdeg
  let n : ℕ := Fintype.card (S : Set V)
  let eqv : (S : Set V) ≃ Fin n := Fintype.equivFin (S : Set V)
  let H : SimpleGraph (S : Set V) := G.induce (S : Set V)
  let H' : SimpleGraph (Fin n) := H.comap eqv.symm
  let iso : H ≃g H' :=
    { toEquiv := eqv
      map_rel_iff' := by
        intro a b
        change H.Adj (eqv.symm (eqv a)) (eqv.symm (eqv b)) ↔ H.Adj a b
        simp }
  have hn : k + 1 ≤ n := by
    have heq : Fintype.card (S : Set V) = S.card := by
      rw [← Fintype.card_coe S]
      exact Fintype.card_congr
        { toFun := fun x => ⟨x.1, Finset.mem_coe.mp x.2⟩
          invFun := fun x => ⟨x.1, Finset.mem_coe.mpr x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    change k + 1 ≤ Fintype.card (S : Set V)
    omega
  have h2conn' : ∀ v : Fin n, (H'.induce {u : Fin n | u ≠ v}).Connected :=
    iso_two_connected iso h2connS
  have hdeg' : ∀ v : Fin n, v ≠ eqv r → k ≤ H'.degree v := by
    intro v hv
    have hsymm : eqv.symm v ≠ r := fun h => hv (by simpa using congrArg eqv h)
    have hdeq : H'.degree v = H.degree (eqv.symm v) := by
      have h := iso_degree_eq iso (eqv.symm v)
      have he : iso (eqv.symm v) = v := eqv.apply_symm_apply v
      rwa [he] at h
    rw [hdeq]
    exact hdegS (eqv.symm v) hsymm
  have hlift : H'.cycleLengths ⊆ G.cycleLengths := by
    let embS : H ↪g G := SimpleGraph.Embedding.induce (S : Set V)
    refine Set.Subset.trans ?_ (cycleLengths_subset_of_hom_inj embS.toHom embS.injective)
    exact cycleLengths_subset_of_hom_inj iso.symm.toHom iso.symm.injective
  by_cases hbip : H'.IsBipartite
  · obtain ⟨m, hm, hdvd⟩ := hH1 hk hodd hn H' hbip h2conn' ⟨eqv r, hdeg'⟩
    exact ⟨m, hlift hm, dvd_trans (dvd_mul_left k 2) hdvd⟩
  · have hconn' : H'.Connected :=
      connected_of_two_connected H' (by rw [Fintype.card_fin]; omega) h2conn'
    obtain ⟨m₀, hm₀, hm₀_odd⟩ := exists_odd_cycle_of_connected_not_isBipartite H' hconn' hbip
    obtain ⟨m, hm, hdvd⟩ := hH2 hk hodd hn H' hbip ⟨m₀, hm₀, hm₀_odd⟩ h2conn' ⟨eqv r, hdeg'⟩
    exact ⟨m, hlift hm, hdvd⟩

end OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H2_R1
