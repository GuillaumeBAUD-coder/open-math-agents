import OMAReductions.R_RamseyNumbers_ramsey_number_three_nine_R2
import Mathlib

/-!
# Small extensions of the seventeen-vertex Ramsey graphs

An anti-neighborhood at a degree-three vertex leaves a seventeen-vertex
Ramsey(3,6) graph and three independent attachment sets. At a vertex of
smaller degree, an eighteen-vertex anti-neighborhood can instead be viewed
as a single-vertex extension of a seventeen-vertex graph.

The seven graph rows are adjacency masks decoded from Brendan McKay's
[Ramsey catalogue](https://users.cecs.anu.edu.au/~bdm/data/r36_17.g6)
([CC BY 4.0](https://users.cecs.anu.edu.au/~bdm/data/)). The attachment
method follows Goedgebeur and Radziszowski,
[New Computational Upper Bounds for Ramsey Numbers R(3,k)](https://arxiv.org/abs/1210.5826),
Section 3.
-/

namespace OMA.Ramsey39Degree

open Finset SimpleGraph

/-- The three neighbors of a degree-three vertex give the attachment sets of
the induced graph on its seventeen nonneighbors. -/
theorem extract_degree_three (G : SimpleGraph (Fin 21)) [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) (hind : Gᶜ.CliqueFree 7)
    (hE : G.edgeFinset.card = 52) (hmin : ∀ x, 3 ≤ G.degree x)
    (w : Fin 21) (hw : G.degree w = 3) :
    ∃ (H : SimpleGraph (Fin 17)) (_ : DecidableRel H.Adj) (B : Fin 3 → Finset (Fin 17)),
      H.CliqueFree 3 ∧ Hᶜ.CliqueFree 6 ∧
      (∀ j, Hᶜ.IsClique (B j : Set (Fin 17))) ∧ (∀ j, 2 ≤ (B j).card) ∧
      H.edgeFinset.card + (∑ j, (B j).card) = 49 ∧
      (∀ i j, i ≠ j → ∀ T : Finset (Fin 17), Hᶜ.IsNClique 5 T →
        ¬ Disjoint T (B i ∪ B j)) := by
  classical
  let N := G.neighborFinset w
  let U := Gᶜ.neighborFinset w
  let D := G.induce (U : Set (Fin 21))
  let A (i : N) := (univ : Finset U).filter (fun x => G.Adj i.val x.val)
  have hN : Fintype.card N = 3 := by
    rw [Fintype.card_coe, G.card_neighborFinset_eq_degree, hw]
  have hU : Fintype.card U = 17 := by
    rw [Fintype.card_coe, Gᶜ.card_neighborFinset_eq_degree, G.degree_compl, hw]
    simp
  let a := (Fintype.equivFinOfCardEq hN).symm
  let e := (Fintype.equivFinOfCardEq hU).symm
  let x : Fin 3 ↪ Fin 21 := a.toEmbedding.trans (Function.Embedding.subtype _)
  let y : Fin 17 ↪ Fin 21 := e.toEmbedding.trans (Function.Embedding.subtype _)
  let H := D.comap e
  let B (j : Fin 3) := (A (a j)).map e.symm.toEmbedding
  have hB (i : Fin 3) (j : Fin 17) : j ∈ B i ↔ G.Adj (x i) (y j) := by
    simp [B, A, x, y, Finset.mem_map_equiv]
  have hNA (i : Fin 3) : G.Adj w (x i) := (G.mem_neighborFinset ..).mp (a i).property
  have hUA (j : Fin 17) : Gᶜ.Adj w (y j) := (Gᶜ.mem_neighborFinset ..).mp (e j).property
  have hNU (i : Fin 3) (j : Fin 17) : x i ≠ y j := fun he => (hUA j).2 (he ▸ hNA i)
  have hNN (i j : Fin 3) (hij : x i ≠ x j) : ¬ G.Adj (x i) (x j) :=
    G.isIndepSet_neighborSet_of_triangleFree htri w (hNA i) (hNA j) hij
  have hrow (i : Fin 3) : (B i).card + 1 = G.degree (x i) := by
    rw [show (B i).card = (A (a i)).card from Finset.card_map _]
    exact RamseyDeficiency.row_card G htri w (a i)
  have hDS := RamseyDeficiency.removed_eq G htri w
  change D.edgeFinset.card + (∑ i ∈ N, G.degree i) = G.edgeFinset.card at hDS
  have hsum : (∑ j : Fin 3, (B j).card) + 3 = ∑ j ∈ N, G.degree j := by
    calc
      (∑ j : Fin 3, (B j).card) + 3 = ∑ j : Fin 3, ((B j).card + 1) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ j : Fin 3, G.degree (x j) := Finset.sum_congr rfl (fun j _ => hrow j)
      _ = ∑ j : N, G.degree j.val := a.sum_comp (fun j => G.degree j.val)
      _ = ∑ j ∈ N, G.degree j := Finset.sum_coe_sort N (fun j : Fin 21 => G.degree j)
  let iso : H ≃g D := SimpleGraph.Iso.comap e D
  have hHD := Fintype.card_congr iso.mapEdgeSet
  rw [H.card_edgeSet, D.card_edgeSet] at hHD
  let em : H ↪g G := SimpleGraph.Embedding.comap y G
  have lift (T : Finset (Fin 17)) (hT : Hᶜ.IsClique (T : Set (Fin 17))) :
      Gᶜ.IsClique (T.map y : Set (Fin 21)) := by
    intro v hv z hz hvz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hz
    exact ⟨hvz, (hT hi hj (fun he => hvz (congrArg y he))).2⟩
  refine ⟨H, inferInstance, B, CliqueFree.comap em.isContained htri, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT
    have hTm : Gᶜ.IsNClique 6 (T.map y) := ⟨lift T hT.isClique, by simpa using hT.card_eq⟩
    apply hind _ (hTm.insert (a := w) ?_)
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact hUA i
  · intro i a ha b hb hab
    exact ⟨hab, G.isIndepSet_neighborSet_of_triangleFree htri (x i)
      ((hB i a).mp ha) ((hB i b).mp hb) (y.injective.ne hab)⟩
  · intro i
    have hm := hmin (x i)
    have he := hrow i
    omega
  · omega
  · intro i j hij T hT hdis
    let J : Finset (Fin 3) := {i,j}
    have hJi : J.card = 2 := by simp [J, hij]
    let X := J.map x
    let Y := T.map y
    have hXY : Disjoint X Y := by
      apply Finset.disjoint_left.mpr
      intro z hzX hzY
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hzX
      obtain ⟨b, _, he⟩ := Finset.mem_map.mp hzY
      exact hNU a b he.symm
    have hX : Gᶜ.IsClique (X : Set (Fin 21)) := by
      intro z hz v hv h
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hv
      exact ⟨h, hNN a b h⟩
    have hY : Gᶜ.IsClique (Y : Set (Fin 21)) := lift T hT.isClique
    have cross (z v : Fin 21) (hz : z ∈ X) (hv : v ∈ Y) : Gᶜ.Adj z v := by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
      refine ⟨hNU a b, fun h => Finset.disjoint_left.mp hdis hb ?_⟩
      have hba := (hB a b).mpr h
      simp only [J, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Finset.mem_union_left _ hba
      · exact Finset.mem_union_right _ hba
    have full : Gᶜ.IsClique (↑(X ∪ Y) : Set (Fin 21)) := by
      intro z hz v hv h
      rcases Finset.mem_union.mp hz with hz | hz <;> rcases Finset.mem_union.mp hv with hv | hv
      · exact hX hz hv h
      · exact cross _ _ hz hv
      · exact (cross _ _ hv hz).symm
      · exact hY hz hv h
    apply hind (X ∪ Y)
    refine ⟨full, ?_⟩
    rw [Finset.card_union_of_disjoint hXY]
    simp [X, Y, hJi, hT.card_eq]

end OMA.Ramsey39Degree

namespace OMA.Ramsey39Degree

open Finset SimpleGraph

theorem relabel_attachments {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) (B : Fin 3 → Finset V)
    (hc : ∀ j, Gᶜ.IsClique (B j : Set V)) (hs : ∀ j, 2 ≤ (B j).card)
    (he : G.edgeFinset.card + (∑ j, (B j).card) = 49)
    (hp : ∀ i j, i ≠ j → ∀ T : Finset V, Gᶜ.IsNClique 5 T →
      ¬ Disjoint T (B i ∪ B j)) :
    ∃ B' : Fin 3 → Finset W, (∀ j, Hᶜ.IsClique (B' j : Set W)) ∧
      (∀ j, 2 ≤ (B' j).card) ∧ H.edgeFinset.card + (∑ j, (B' j).card) = 49 ∧
      (∀ i j, i ≠ j → ∀ T : Finset W, Hᶜ.IsNClique 5 T →
        ¬ Disjoint T (B' i ∪ B' j)) := by
  let F := e.toEquiv.toEmbedding
  let R := e.symm.toEquiv.toEmbedding
  let B' (j : Fin 3) := (B j).map F
  have hE := Fintype.card_congr e.mapEdgeSet
  rw [G.card_edgeSet, H.card_edgeSet] at hE
  refine ⟨B', ?_, fun j => by simpa only [B', card_map] using hs j, ?_, ?_⟩
  · intro j x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
    exact ⟨hxy, fun h => (hc j ha hb (fun hab => hxy (congrArg F hab))).2
      (e.map_adj_iff.mp h)⟩
  · simpa only [B', card_map, ← hE] using he
  · intro i j hij T hT hdis
    let S := T.map R
    have hS : Gᶜ.IsNClique 5 S := by
      refine ⟨?_, (card_map _).trans hT.card_eq⟩
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
      exact ⟨hxy, fun h => (hT.isClique ha hb (fun hab => hxy (congrArg R hab))).2
        (e.symm.map_adj_iff.mp h)⟩
    apply hp i j hij S hS
    apply Finset.disjoint_left.mpr
    intro a ha hab
    have hfa : F a ∈ T := by
      obtain ⟨b, hb, rfl⟩ := mem_map.mp ha
      simpa [F, R] using hb
    apply Finset.disjoint_left.mp hdis hfa
    rw [show B' i ∪ B' j = (B i ∪ B j).map F from (map_union _ _).symm]
    exact mem_map.mpr ⟨a, hab, rfl⟩

end OMA.Ramsey39Degree

open SimpleGraph Finset
open scoped BigOperators

namespace OMA.R_RamseyNumbers_ramsey_number_three_nine_R2_H3_R1

open OMA.Ramsey39Degree

private theorem no_avoid18
    {rows : Fin 7 → Fin 17 → ℕ}
    (hCat : ∀ (G : SimpleGraph (Fin 17)), G.CliqueFree 3 → Gᶜ.CliqueFree 6 →
      ∃ (k : Fin 7) (e : Fin 17 ≃ Fin 17), ∀ i j,
        G.Adj (e i) (e j) ↔ i ≠ j ∧ (rows k (min i j)).testBit (max i j).val = true)
    (hOne : ∀ (k : Fin 7) (G : SimpleGraph (Fin 17)),
      (∀ i j, G.Adj i j ↔ i ≠ j ∧ (rows k (min i j)).testBit (max i j).val = true) →
      ∀ (B : Finset (Fin 17)), Gᶜ.IsClique (B : Set (Fin 17)) → B.card ≤ 5 →
      (∀ T : Finset (Fin 17), Gᶜ.IsNClique 5 T → ¬ Disjoint T B) → False)
    (K : SimpleGraph (Fin 18))
    [DecidableRel K.Adj] (hT : K.CliqueFree 3) (hI : Kᶜ.CliqueFree 6) : False := by
  classical
  let e : Fin 17 ↪ Fin 18 := Fin.castSuccEmb
  let J := K.comap e
  let emb : J ↪g K := SimpleGraph.Embedding.comap e K
  have hJT : J.CliqueFree 3 := CliqueFree.comap emb.isContained hT
  have hJI : Jᶜ.CliqueFree 6 :=
    CliqueFree.comap (SimpleGraph.Embedding.complEquiv emb).isContained hI
  obtain ⟨k,f,hRows⟩ := hCat J hJT hJI
  let C := J.comap f
  let em : C ↪g K := (SimpleGraph.Iso.comap f J).toEmbedding.trans emb
  let v : Fin 18 := Fin.last 17
  let B := univ.filter (fun i => K.Adj v (em i))
  have hB (i : Fin 17) : i∈B ↔ K.Adj v (em i) := by simp [B]
  have hBI : Cᶜ.IsClique (B : Set (Fin 17)) := by
    intro x hx y hy hxy
    refine ⟨hxy,?_⟩
    intro hadj
    exact K.isIndepSet_neighborSet_of_triangleFree hT v ((hB x).mp hx) ((hB y).mp hy)
      (fun he => hxy (em.injective he)) (em.map_adj_iff.mpr hadj)
  have hSize : B.card ≤ 5 := by
    by_contra! hLarge
    obtain ⟨T, hTB,hCard⟩ := Finset.exists_subset_card_eq (show 6 ≤ B.card by omega)
    apply CliqueFree.comap (SimpleGraph.Embedding.complEquiv em).isContained hI T
    exact ⟨hBI.subset hTB,hCard⟩
  apply hOne k C hRows B hBI hSize
  intro S hS hDisj
  have hMap : Kᶜ.IsNClique 5 (S.map em.toEmbedding) := by
    refine ⟨?_,(Finset.card_map _).trans hS.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hy
    exact (SimpleGraph.Embedding.complEquiv em).map_adj_iff.mpr
      (hS.isClique ha hb (fun he => hxy (congrArg em he)))
  apply hI _ (hMap.insert (a:=v) ?_)
  intro x hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
  refine ⟨(Fin.castSucc_ne_last (f i)).symm,?_⟩
  intro he
  exact Finset.disjoint_left.mp hDisj hi ((hB i).mpr he)

/-- Completeness of McKay's seven isomorphism types on 17 vertices. -/
def H1 : Prop :=
  let rows : Fin 7 → Fin 17 → ℕ := ![
    ![0x1c200, 0x12880, 0x9500, 0x1a140, 0x150a0, 0x2e10, 0x5c08, 0x8612, 0x4a0c, 0x11a1, 0x100e4, 0x8162, 0x2254, 0x502a, 0x2151, 0x88d, 0x41b],
    ![0x18600, 0x15080, 0xa900, 0x12890, 0xd108, 0x16240, 0x9c20, 0x830a, 0x10494, 0x18a1, 0x6141, 0x424c, 0x2252, 0x142c, 0xc32, 0xd5, 0x12b],
    ![0x10310, 0x8490, 0x14808, 0xb004, 0x63, 0xaa10, 0x15410, 0x17002, 0xe801, 0x5421, 0x2a42, 0x1524, 0xac8, 0x5a8, 0x3c4, 0x1012a, 0x80c5],
    ![0x780, 0x14804, 0xb002, 0x1c220, 0x1a140, 0x2d08, 0x5610, 0x7801, 0x5031, 0x2849, 0x18061, 0x82a2, 0x101c4, 0x2b4, 0x1ca, 0xc1c, 0x141a],
    ![0x1e000, 0x2224, 0x11102, 0x8890, 0x4448, 0x4582, 0x2390, 0x11068, 0x8864, 0x18842, 0x13030, 0x6308, 0xc484, 0xc43, 0x1831, 0x1309, 0x685],
    ![0x1e, 0x6061, 0x15801, 0x18601, 0xa181, 0x10a82, 0x11502, 0x5430, 0x4a50, 0x3128, 0x28c8, 0x8524, 0x82c4, 0x10612, 0x8186, 0x5818, 0x206c],
    ![0x1e, 0x6061, 0x14c01, 0x18281, 0xb101, 0x11902, 0x11602, 0x3c08, 0x4630, 0x2948, 0x81c4, 0x82a4, 0x40f0, 0x10292, 0x9106, 0x4c18, 0x206c]
  ]
  ∀ (G : SimpleGraph (Fin 17)), G.CliqueFree 3 → Gᶜ.CliqueFree 6 →
    ∃ (k : Fin 7) (e : Fin 17 ≃ Fin 17), ∀ i j,
      G.Adj (e i) (e j) ↔ i ≠ j ∧ (rows k (min i j)).testBit (max i j).val = true

/-- A single independent attachment set of size at most five cannot meet
every independent five-set in any of the seven base graphs. -/
def H2 : Prop :=
  let rows : Fin 7 → Fin 17 → ℕ := ![
    ![0x1c200, 0x12880, 0x9500, 0x1a140, 0x150a0, 0x2e10, 0x5c08, 0x8612, 0x4a0c, 0x11a1, 0x100e4, 0x8162, 0x2254, 0x502a, 0x2151, 0x88d, 0x41b],
    ![0x18600, 0x15080, 0xa900, 0x12890, 0xd108, 0x16240, 0x9c20, 0x830a, 0x10494, 0x18a1, 0x6141, 0x424c, 0x2252, 0x142c, 0xc32, 0xd5, 0x12b],
    ![0x10310, 0x8490, 0x14808, 0xb004, 0x63, 0xaa10, 0x15410, 0x17002, 0xe801, 0x5421, 0x2a42, 0x1524, 0xac8, 0x5a8, 0x3c4, 0x1012a, 0x80c5],
    ![0x780, 0x14804, 0xb002, 0x1c220, 0x1a140, 0x2d08, 0x5610, 0x7801, 0x5031, 0x2849, 0x18061, 0x82a2, 0x101c4, 0x2b4, 0x1ca, 0xc1c, 0x141a],
    ![0x1e000, 0x2224, 0x11102, 0x8890, 0x4448, 0x4582, 0x2390, 0x11068, 0x8864, 0x18842, 0x13030, 0x6308, 0xc484, 0xc43, 0x1831, 0x1309, 0x685],
    ![0x1e, 0x6061, 0x15801, 0x18601, 0xa181, 0x10a82, 0x11502, 0x5430, 0x4a50, 0x3128, 0x28c8, 0x8524, 0x82c4, 0x10612, 0x8186, 0x5818, 0x206c],
    ![0x1e, 0x6061, 0x14c01, 0x18281, 0xb101, 0x11902, 0x11602, 0x3c08, 0x4630, 0x2948, 0x81c4, 0x82a4, 0x40f0, 0x10292, 0x9106, 0x4c18, 0x206c]
  ]
  ∀ (k : Fin 7) (G : SimpleGraph (Fin 17)),
    (∀ i j, G.Adj i j ↔ i ≠ j ∧ (rows k (min i j)).testBit (max i j).val = true) →
    ∀ (B : Finset (Fin 17)), Gᶜ.IsClique (B : Set (Fin 17)) → B.card ≤ 5 →
    (∀ T : Finset (Fin 17), Gᶜ.IsNClique 5 T → ¬ Disjoint T B) → False

/-- The degree-three extension cannot satisfy all pairwise attachment tests
within the 52-edge budget. -/
def H3 : Prop :=
  let rows : Fin 7 → Fin 17 → ℕ := ![
    ![0x1c200, 0x12880, 0x9500, 0x1a140, 0x150a0, 0x2e10, 0x5c08, 0x8612, 0x4a0c, 0x11a1, 0x100e4, 0x8162, 0x2254, 0x502a, 0x2151, 0x88d, 0x41b],
    ![0x18600, 0x15080, 0xa900, 0x12890, 0xd108, 0x16240, 0x9c20, 0x830a, 0x10494, 0x18a1, 0x6141, 0x424c, 0x2252, 0x142c, 0xc32, 0xd5, 0x12b],
    ![0x10310, 0x8490, 0x14808, 0xb004, 0x63, 0xaa10, 0x15410, 0x17002, 0xe801, 0x5421, 0x2a42, 0x1524, 0xac8, 0x5a8, 0x3c4, 0x1012a, 0x80c5],
    ![0x780, 0x14804, 0xb002, 0x1c220, 0x1a140, 0x2d08, 0x5610, 0x7801, 0x5031, 0x2849, 0x18061, 0x82a2, 0x101c4, 0x2b4, 0x1ca, 0xc1c, 0x141a],
    ![0x1e000, 0x2224, 0x11102, 0x8890, 0x4448, 0x4582, 0x2390, 0x11068, 0x8864, 0x18842, 0x13030, 0x6308, 0xc484, 0xc43, 0x1831, 0x1309, 0x685],
    ![0x1e, 0x6061, 0x15801, 0x18601, 0xa181, 0x10a82, 0x11502, 0x5430, 0x4a50, 0x3128, 0x28c8, 0x8524, 0x82c4, 0x10612, 0x8186, 0x5818, 0x206c],
    ![0x1e, 0x6061, 0x14c01, 0x18281, 0xb101, 0x11902, 0x11602, 0x3c08, 0x4630, 0x2948, 0x81c4, 0x82a4, 0x40f0, 0x10292, 0x9106, 0x4c18, 0x206c]
  ]
  ∀ (k : Fin 7) (G : SimpleGraph (Fin 17)) [DecidableRel G.Adj],
    (∀ i j, G.Adj i j ↔ i ≠ j ∧ (rows k (min i j)).testBit (max i j).val = true) →
    ∀ (B : Fin 3 → Finset (Fin 17)),
    (∀ i, Gᶜ.IsClique (B i : Set (Fin 17))) →
    (∀ i, 2 ≤ (B i).card) →
    G.edgeFinset.card + (∑ i, (B i).card) = 49 →
    (∀ i j, i ≠ j → ∀ S : Finset (Fin 17), Gᶜ.IsNClique 5 S →
      ¬ Disjoint S (B i ∪ B j)) → False

theorem main : H1 → H2 → H3 → OMA.R_RamseyNumbers_ramsey_number_three_nine_R2.H3 := by
  intro hCat hSingle hTriple V _ _ G _ hCard hT hI hEdges w
  classical
  let e : Fin 21 ≃ V :=
    Fintype.equivOfCardEq (by simpa using hCard.symm)
  let K := G.comap e
  let f : K ≃g G := SimpleGraph.Iso.comap e G
  have hKT : K.CliqueFree 3 := CliqueFree.comap f.toEmbedding.isContained hT
  have hKI : Kᶜ.CliqueFree 7 :=
    CliqueFree.comap (SimpleGraph.Embedding.complEquiv f.toEmbedding).isContained hI
  have hE : K.edgeFinset.card=52 := f.card_edgeFinset_eq.trans hEdges
  have hMin (x : Fin 21) : 3 ≤ K.degree x := by
    by_contra! h
    have hN : 18 ≤ Kᶜ.degree x := by
      rw [K.degree_compl,Fintype.card_fin]
      omega
    obtain ⟨J,_,hJT,hJI,_⟩ := RamseyDeficiency.extract_anti (k:=6) K hKT hKI x hN
    exact no_avoid18 hCat hSingle J hJT hJI
  let x := e.symm w
  have hDeg : G.degree w = K.degree x := by
    have h := f.degree_eq x
    change G.degree (e (e.symm w)) = K.degree x at h
    rwa [e.apply_symm_apply] at h
  rw [hDeg]
  by_contra! hSmall
  have hx : K.degree x=3 := by have h := hMin x; omega
  obtain ⟨J,_,B,hJT,hJI,hB,hSizes,hSum,hPairs⟩ :=
    extract_degree_three K hKT hKI hE hMin x hx
  obtain ⟨k,z,hRows⟩ := hCat J hJT hJI
  let C := J.comap z
  let eqv : J ≃g C := (SimpleGraph.Iso.comap z J).symm
  obtain ⟨B',hB',hSizes',hSum',hPairs'⟩ := relabel_attachments eqv B hB hSizes hSum hPairs
  exact hTriple k C hRows B' hB' hSizes' hSum' hPairs'

end OMA.R_RamseyNumbers_ramsey_number_three_nine_R2_H3_R1
