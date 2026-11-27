import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases

open RamseyNumbers SimpleGraph

namespace OMA.R_RamseyNumbers_ramsey_number_three_eight_R1

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

-- Data from McKay's combinatorial data collection (CC BY 4.0), r38_27.g6.gz,
-- first graph of the Brinkmann--Goedgebeur enumeration, recoded as binary masks.
-- The size pruning and mask representation follow VinnyMo's proof in PR 1435.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
lemma twentyseven_fails : ¬ IsGraphRamsey 27 3 8 := by
  let rows : Array ℕ := #[0x4486410, 0x31494, 0x48e042, 0x9094a0, 0x208923, 0x464058, 0x4101524, 0x604090a, 0xc100d0, 0x442d800, 0x204084b, 0x1082690, 0x208224a, 0x231805, 0x2210225, 0x205021c, 0x110e102, 0x2902222, 0x12884a0, 0x941805, 0x6b0048, 0x4946010, 0x1100325, 0x12a0108, 0x6c50800, 0x102d480, 0x12002c1]
  let G : SimpleGraph (Fin 27) :=
    { Adj := fun u v => u ≠ v ∧ rows[min u.val v.val]!.testBit (max u.val v.val) = true
      symm := ⟨fun {u v} h => ⟨h.1.symm, by simpa only [min_comm v.val u.val, max_comm v.val u.val] using h.2⟩⟩
      loopless := ⟨fun u h => h.1 rfl⟩ }
  let : DecidableRel G.Adj := fun u v => inferInstanceAs
    (Decidable (u ≠ v ∧ rows[min u.val v.val]!.testBit (max u.val v.val) = true))
  intro h
  exact h G ⟨exclude_search G 3 (by dsimp +zetaDelta only; decide +kernel), exclude_search Gᶜ 8 (by dsimp +zetaDelta only; decide +kernel)⟩

-- With no triangle and no independent k-set, each vertex has fewer than k neighbours.
lemma degree_lt {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree k) (v : Fin n) : G.degree v < k := by
  by_contra! h
  apply hc.mono h (G.neighborFinset v)
  refine ⟨?_, rfl⟩
  rw [G.coe_neighborFinset, G.isClique_compl]
  exact G.isIndepSet_neighborSet_of_triangleFree hG v

-- An independent k-set among non-neighbours extends to an independent (k+1)-set.
lemma nonneighbors_lt {n k m : ℕ} (hr : IsGraphRamsey m 3 k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
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

-- The smaller Ramsey bound forces a candidate neighbourhood to have size at least five.
def H1 : Prop := IsGraphRamsey 23 3 7

-- On 27 vertices no independent set of size five through seven meets every independent seven-set.
def H2 : Prop :=
  ∀ (H : SimpleGraph (Fin 27)), H.CliqueFree 3 → Hᶜ.CliqueFree 8 →
    ∀ T : Finset (Fin 27), Hᶜ.IsClique T → 5 ≤ T.card → T.card ≤ 7 →
    ∃ S : Finset (Fin 27), Hᶜ.IsNClique 7 S ∧ Disjoint S T

theorem main : H1 → H2 → type_of% @RamseyNumbers.ramsey_number_three_eight := by
  classical
  intro small obstruction
  have upper : IsGraphRamsey 28 3 8 := by
    rintro G ⟨ht, hi⟩
    let v := Fin.last 27
    let f : Fin 27 ↪ Fin 28 := Fin.castSuccEmb
    let H := G.comap f
    let e : H ↪g G := SimpleGraph.Embedding.comap f G
    let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
    let T := Finset.univ.filter fun i : Fin 27 => G.Adj v (f i)
    have mem (i : Fin 27) : i ∈ T ↔ G.Adj v (f i) := by simp [T]
    have imageT : T.map f = G.neighborFinset v := by
      ext z
      constructor
      · intro hz
        obtain ⟨i, hi', rfl⟩ := Finset.mem_map.mp hz
        exact (G.mem_neighborFinset _ _).mpr ((mem i).mp hi')
      · intro hz
        have ha := (G.mem_neighborFinset _ _).mp hz
        obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last ha.ne.symm
        exact Finset.mem_map.mpr ⟨i, (mem i).mpr ha, rfl⟩
    have size : T.card = G.degree v := by
      rw [← Finset.card_map (f := f), imageT]
      rfl
    have low := nonneighbors_lt small G ht hi v
    rw [G.degree_compl, Fintype.card_fin] at low
    have high := degree_lt G ht hi v
    have independent : Hᶜ.IsClique T := by
      intro i hI j hJ hij
      apply ec.map_adj_iff.mp
      exact ⟨f.injective.ne hij, G.isIndepSet_neighborSet_of_triangleFree ht v
        ((mem i).mp hI) ((mem j).mp hJ) (f.injective.ne hij)⟩
    obtain ⟨S, hs, hdis⟩ := obstruction H (CliqueFree.comap e.isContained ht)
      (CliqueFree.comap ec.isContained hi) T independent (by omega) (by omega)
    have mapped : Gᶜ.IsNClique 7 (S.map f) := by
      refine ⟨?_, (Finset.card_map _).trans hs.card_eq⟩
      intro x hx y hy hxy
      obtain ⟨i, hi', rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨j, hj', rfl⟩ := Finset.mem_map.mp hy
      exact ec.map_adj_iff.mpr (hs.isClique hi' hj' (fun h => hxy (congrArg f h)))
    apply hi _ (mapped.insert (a := v) ?_)
    intro z hz
    obtain ⟨i, hi', rfl⟩ := Finset.mem_map.mp hz
    exact ⟨(Fin.castSucc_ne_last i).symm, fun ha => Finset.disjoint_left.mp hdis hi' ((mem i).mpr ha)⟩
  rw [classicalRamsey_eq_sInf]
  apply IsLeast.csInf_eq
  refine ⟨upper, ?_⟩
  intro n hn
  by_contra! hlt
  have mono : Monotone (fun m => IsGraphRamsey m 3 8) :=
    monotone_nat_of_le_succ fun m => IsGraphRamsey.succ m 3 8
  exact twentyseven_fails (mono (show n ≤ 27 by omega) hn)

end OMA.R_RamseyNumbers_ramsey_number_three_eight_R1
