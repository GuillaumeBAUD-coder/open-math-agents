import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.Embedding

open RamseyNumbers SimpleGraph

namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R1

-- A clique search branches on its least vertex, retaining only larger neighbours.
lemma exclude_search {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (cert : (Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
      (fun j rec vs => if vs.length < j+1 then false else vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
      k (List.finRange n)) = false) : G.CliqueFree k := by
  let search := Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
    (fun j rec vs => if vs.length < j+1 then false else vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
  have found (j : ℕ) (vs : List (Fin n)) (s : Finset (Fin n)) (hs : G.IsNClique j s)
      (hsub : ∀ x ∈ s, x ∈ vs) : search j vs = true := by
    induction j generalizing vs s with
    | zero => rfl
    | succ j ih =>
      have hne : s.Nonempty := Finset.card_pos.mp (by rw [hs.card_eq]; omega)
      let v := s.min' hne
      have hv : v ∈ s := s.min'_mem hne
      have hlen : s.card ≤ vs.length :=
        (Finset.card_le_card (show s ⊆ vs.toFinset from fun x hx => List.mem_toFinset.mpr (hsub x hx))).trans
          (List.toFinset_card_le vs)
      have enough : ¬ vs.length < j+1 := by rw [hs.card_eq] at hlen; omega
      change (if vs.length < j+1 then false else vs.any _) = true
      rw [if_neg enough]
      apply List.any_eq_true.mpr
      refine ⟨v, hsub v hv, ih _ (s.erase v) (hs.erase_of_mem hv) ?_⟩
      intro w hw
      obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
      exact List.mem_filter.mpr ⟨hsub w hw, decide_eq_true
        ⟨lt_of_le_of_ne (s.min'_le _ hw) hne.symm, hs.isClique hv hw hne.symm⟩⟩
  intro s hs
  have yes := found k (List.finRange n) s hs (by simp)
  change search k (List.finRange n) = false at cert
  simp_all

-- Data from McKay's combinatorial data collection (CC BY 4.0), r45_24.g6,
-- first graph of the McKay--Angeltveit collection, recoded as binary masks.
-- The size pruning and mask representation follow VinnyMo's proof in PR 1435.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
lemma twentyfour_fails : ¬ IsGraphRamsey 24 4 5 := by
  let rows : Array ℕ := #[0xd3ac00, 0xec5300, 0xe2e2c0, 0x39f030, 0x86dc28, 0xcd2518, 0x599684, 0xe7944, 0xbca0a2, 0xab1846, 0x616871, 0xb21691, 0x142ada, 0x2095ad, 0xad049e, 0x9a215d, 0x964669, 0x4d8a95, 0x5351b2, 0x42c3ea, 0x659949, 0x506f0e, 0x3e0467, 0x1cb37]
  let G : SimpleGraph (Fin 24) :=
    { Adj := fun u v => u ≠ v ∧ rows[min u.val v.val]!.testBit (max u.val v.val) = true
      symm := ⟨fun {u v} h => ⟨h.1.symm, by simpa only [min_comm v.val u.val, max_comm v.val u.val] using h.2⟩⟩
      loopless := ⟨fun u h => h.1 rfl⟩ }
  let : DecidableRel G.Adj := fun u v => inferInstanceAs
    (Decidable (u ≠ v ∧ rows[min u.val v.val]!.testBit (max u.val v.val) = true))
  intro h
  exact h G ⟨exclude_search G 4 (by dsimp +zetaDelta only; decide +kernel), exclude_search Gᶜ 5 (by dsimp +zetaDelta only; decide +kernel)⟩

-- With no triangle and no independent k-set, each vertex has fewer than k neighbours.
lemma degree_lt {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree k) (v : Fin n) : G.degree v < k := by
  by_contra! h
  apply hc.mono h (G.neighborFinset v)
  refine ⟨?_, rfl⟩
  rw [G.coe_neighborFinset, G.isClique_compl]
  exact G.isIndepSet_neighborSet_of_triangleFree hG v

-- An independent k-set among non-neighbours extends to an independent (k+1)-set.
lemma nonneighbors_lt {n k m r : ℕ} (hr : IsGraphRamsey m r k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.CliqueFree r)
    (hc : Gᶜ.CliqueFree (k + 1)) (v : Fin n) : Gᶜ.degree v < m := by
  classical
  by_contra! h
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin m) (s := Gᶜ.neighborFinset v) (by simpa using h)
  have hv (i : Fin m) : Gᶜ.Adj v (f i) :=
    (Gᶜ.mem_neighborFinset v (f i)).mp (hf ⟨i, rfl⟩)
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  apply hr H
  refine ⟨CliqueFree.comap e.isContained hG, ?_⟩
  intro t ht
  have hs : Gᶜ.IsNClique k (t.map f) := by
    refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => hxy (congrArg f he)))
  apply hc _ (hs.insert (a := v) ?_)
  intro w hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
  exact hv i

lemma six_works : IsGraphRamsey 6 3 3 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := degree_lt Gᶜ hc (by simpa using hG : Gᶜᶜ.CliqueFree 3) 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

lemma nine_works : IsGraphRamsey 9 3 4 := by
  classical
  rintro G ⟨hG, hc⟩
  have hdegree (v : Fin 9) : G.degree v = 3 := by
    have hd := degree_lt G hG hc v
    have hdc := nonneighbors_lt six_works G hG hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp [hdegree] at hsum
  omega

lemma fourteen_works : IsGraphRamsey 14 3 5 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := nonneighbors_lt nine_works G hG hc 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

lemma eighteen_works : IsGraphRamsey 18 4 4 := by
  classical
  rintro G ⟨ht, hi⟩
  have nine := (IsGraphRamsey.symm 9 3 4).mp nine_works
  have lo := nonneighbors_lt nine G ht hi 0
  have hi' := nonneighbors_lt nine Gᶜ hi (by simpa using ht : Gᶜᶜ.CliqueFree 4) 0
  rw [G.degree_compl, Fintype.card_fin] at lo
  rw [Gᶜ.degree_compl, G.degree_compl, Fintype.card_fin] at hi'
  omega

lemma map_clique {n m k : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (e : G ↪g H) {S : Finset (Fin n)} (hs : G.IsNClique k S) :
    H.IsNClique k (S.map e.toEmbedding) := by
  refine ⟨?_, (Finset.card_map _).trans hs.card_eq⟩
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
  exact e.map_adj_iff.mpr (hs.isClique hi hj (fun h => hxy (congrArg e h)))

-- The three degree cases follow Section 3 of Gauthier and Brown, A Formal Proof
-- of R(4,5)=25 (ITP 2024, DOI 10.4230/LIPIcs.ITP.2024.16).
-- Each test rules out a possible neighbourhood of the deleted even-degree vertex.
def H1 : Prop :=
  ∀ (H : SimpleGraph (Fin 24)), H.CliqueFree 4 → Hᶜ.CliqueFree 5 →
    ∀ T : Finset (Fin 24), T.card = 8 →
    (∃ S ⊆ T, H.IsNClique 3 S) ∨ (∃ S : Finset (Fin 24), Disjoint S T ∧ Hᶜ.IsNClique 4 S)

def H2 : Prop :=
  ∀ (H : SimpleGraph (Fin 24)), H.CliqueFree 4 → Hᶜ.CliqueFree 5 →
    ∀ T : Finset (Fin 24), T.card = 10 →
    (∃ S ⊆ T, H.IsNClique 3 S) ∨ (∃ S : Finset (Fin 24), Disjoint S T ∧ Hᶜ.IsNClique 4 S)

def H3 : Prop :=
  ∀ (H : SimpleGraph (Fin 24)), H.CliqueFree 4 → Hᶜ.CliqueFree 5 →
    ∀ T : Finset (Fin 24), T.card = 12 →
    (∃ S ⊆ T, H.IsNClique 3 S) ∨ (∃ S : Finset (Fin 24), Disjoint S T ∧ Hᶜ.IsNClique 4 S)


theorem main : H1 → H2 → H3 → type_of% @RamseyNumbers.ramsey_number_four_five := by
  classical
  intro eight ten twelve
  have upper : IsGraphRamsey 25 4 5 := by
    rintro G ⟨ht, hi⟩
    have ex : ∃ v, Even (G.degree v) := by
      by_contra! h
      have allOdd (v : Fin 25) : Odd (G.degree v) := Nat.not_even_iff_odd.mp (h v)
      have par := G.even_card_odd_degree_vertices
      simp [allOdd] at par
      obtain ⟨k, hk⟩ := par
      omega
    obtain ⟨v, hv⟩ := ex
    have low := nonneighbors_lt eighteen_works G ht hi v
    have high := nonneighbors_lt ((IsGraphRamsey.symm 14 3 5).mp fourteen_works)
      Gᶜ hi (by simpa using ht : Gᶜᶜ.CliqueFree 4) v
    rw [G.degree_compl, Fintype.card_fin] at low
    rw [Gᶜ.degree_compl, G.degree_compl, Fintype.card_fin] at high
    let f := v.succAboveEmb
    let H := G.comap f
    let e := SimpleGraph.Embedding.comap f G
    let ec := SimpleGraph.Embedding.complEquiv e
    let T := Finset.univ.filter fun i : Fin 24 => G.Adj v (f i)
    have mem (i : Fin 24) : i ∈ T ↔ G.Adj v (f i) := by simp [T]
    have imageT : T.map f = G.neighborFinset v := by
      ext z
      constructor
      · intro hz
        obtain ⟨i, hi', rfl⟩ := Finset.mem_map.mp hz
        exact (G.mem_neighborFinset _ _).mpr ((mem i).mp hi')
      · intro hz
        have ha := (G.mem_neighborFinset _ _).mp hz
        obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq ha.ne.symm
        exact Finset.mem_map.mpr ⟨i, (mem i).mpr ha, rfl⟩
    have size : T.card = G.degree v := by rw [← Finset.card_map (f := f), imageT]; rfl
    have ok : H.CliqueFree 4 := CliqueFree.comap e.isContained ht
    have okc : Hᶜ.CliqueFree 5 := CliqueFree.comap ec.isContained hi
    have cases : T.card = 8 ∨ T.card = 10 ∨ T.card = 12 := by obtain ⟨k,hk⟩ := hv; omega
    have obstruction : (∃ S ⊆ T, H.IsNClique 3 S) ∨
        (∃ S : Finset (Fin 24), Disjoint S T ∧ Hᶜ.IsNClique 4 S) := by
      rcases cases with h | h | h
      · exact eight H ok okc T h
      · exact ten H ok okc T h
      · exact twelve H ok okc T h
    rcases obstruction with ⟨S, hsub, hs⟩ | ⟨S, hdis, hs⟩
    · apply ht _ ((map_clique e hs).insert (a := v) ?_)
      intro z hz
      obtain ⟨i, hi', rfl⟩ := Finset.mem_map.mp hz
      exact (mem i).mp (hsub hi')
    · apply hi _ ((map_clique ec hs).insert (a := v) ?_)
      intro z hz
      obtain ⟨i, hi', rfl⟩ := Finset.mem_map.mp hz
      exact ⟨(Fin.succAbove_ne v i).symm, fun ha => Finset.disjoint_left.mp hdis hi' ((mem i).mpr ha)⟩
  rw [classicalRamsey_eq_sInf]
  apply IsLeast.csInf_eq
  refine ⟨upper, ?_⟩
  intro n hn
  by_contra! hlt
  have mono : Monotone (fun m => IsGraphRamsey m 4 5) :=
    monotone_nat_of_le_succ fun m => IsGraphRamsey.succ m 4 5
  exact twentyfour_fails (mono (show n ≤ 24 by omega) hn)

end OMA.R_RamseyNumbers_ramsey_number_four_five_R1
