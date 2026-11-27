import OMAReductions.R_RamseyNumbers_ramsey_number_three_nine_R1

/-! The 27-vertex edge bound forces regularity in a 35-vertex Ramsey graph. -/
open SimpleGraph RamseyNumbers
namespace OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1

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

-- The smaller Ramsey bound forces degrees seven and eight.
def H1 : Prop := IsGraphRamsey 28 3 8

-- The extremal edge bound e(3,8,27) ≥ 85, computed by Goedgebeur and Radziszowski.
def H2 : Prop :=
  ∀ (H : SimpleGraph (Fin 27)) [DecidableRel H.Adj],
    H.CliqueFree 3 → Hᶜ.CliqueFree 8 → 85 ≤ H.edgeFinset.card

theorem main : H1 → H2 → OMA.R_RamseyNumbers_ramsey_number_three_nine_R1.H2 := by
  classical
  intro small density G inst ht hi
  have degrees (v : Fin 35) : G.degree v = 7 ∨ G.degree v = 8 := by
    have lo := nonneighbors_lt small G ht hi v
    have up := degree_lt G ht hi v
    rw [G.degree_compl, Fintype.card_fin] at lo
    omega
  let U : Finset (Fin 35) := Finset.univ
  let L := U.filter fun i => G.degree i = 7
  let low (S : Finset (Fin 35)) := S.filter fun i => G.degree i = 7
  -- Each vertex of degree seven contributes one unit below the maximum degree.
  have deficit (S : Finset (Fin 35)) :
      (∑ i ∈ S, G.degree i) + (low S).card = 8 * S.card := by
    have one (i : Fin 35) : G.degree i + (if G.degree i = 7 then 1 else 0) = 8 := by
      rcases degrees i with h | h <;> simp [h]
    have eq := Finset.sum_congr (s₁ := S) (s₂ := S) rfl (fun i _ => one i)
    simpa [Finset.sum_add_distrib, low, Nat.mul_comm] using eq
  let W (S T : Finset (Fin 35)) := ∑ i ∈ S, ∑ j ∈ T, (if G.Adj i j then 1 else 0 : ℕ)
  have sym (S T) : W S T = W T S := by
    unfold W
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have split (S T) : W S T + W Sᶜ T = W U T := by
    exact Finset.sum_add_sum_compl S _
  have total (S) : W S U = ∑ i ∈ S, G.degree i := by
    unfold W U
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  -- Counting the edges among the 27 non-neighbours forces a strict majority.
  have majority (v : Fin 35) (hv : G.degree v = 7) :
      L.card < 2 * (low (G.neighborFinset v)).card := by
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    have bcard : B.card = 27 := by
      change Gᶜ.degree v = 27
      rw [G.degree_compl, Fintype.card_fin, hv]
    have lower : 170 ≤ W B B := by
      obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
        (α := Fin 27) (s := B) (by simp [bcard])
      have im : (Finset.univ.map f) = B := by
        apply Finset.eq_of_subset_of_card_le
        · intro w hw
          obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
          exact hf ⟨i, rfl⟩
        · simp [bcard]
      let H := G.comap f
      let e : H ↪g G := SimpleGraph.Embedding.comap f G
      let ec := SimpleGraph.Embedding.complEquiv e
      have free : Hᶜ.CliqueFree 8 := by
        intro S hs
        have mapped : Gᶜ.IsNClique 8 (S.map f) := by
          refine ⟨?_, (Finset.card_map _).trans hs.card_eq⟩
          intro x hx y hy hxy
          obtain ⟨i, hi', rfl⟩ := Finset.mem_map.mp hx
          obtain ⟨j, hj', rfl⟩ := Finset.mem_map.mp hy
          exact ec.map_adj_iff.mpr (hs.isClique hi' hj' (fun h => hxy (congrArg f h)))
        apply hi _ (mapped.insert (a := v) ?_)
        intro w hw
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
        exact (Gᶜ.mem_neighborFinset _ _).mp (hf ⟨i, rfl⟩)
      have bound := density H (CliqueFree.comap e.isContained ht) free
      have sumdeg := H.sum_degrees_eq_twice_card_edges
      have count : W B B = ∑ i, H.degree i := by
        unfold W
        rw [← im]
        simp only [Finset.sum_map]
        change (∑ i : Fin 27, ∑ j : Fin 27, (if H.Adj i j then 1 else 0 : ℕ)) = _
        apply Finset.sum_congr rfl
        intro i _
        rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
        exact Finset.sum_boole (R := ℕ) (H.Adj i) Finset.univ
      omega
    have bsub : B ⊆ Nᶜ := by
      intro i h
      exact Finset.mem_compl.mpr fun hn => ((Gᶜ.mem_neighborFinset _ _).mp h).2
        ((G.mem_neighborFinset _ _).mp hn)
    have inc (S T V : Finset (Fin 35)) (h : S ⊆ T) : W S V ≤ W T V :=
      Finset.sum_le_sum_of_subset_of_nonneg h (by intros; omega)
    have hsub : W B B ≤ W Nᶜ Nᶜ :=
      (inc B Nᶜ B bsub).trans ((sym Nᶜ B) ▸ inc B Nᶜ Nᶜ bsub)
    have zero : W N N = 0 := by
      apply Finset.sum_eq_zero
      intro i hI
      apply Finset.sum_eq_zero
      intro j hJ
      have hh : ¬ G.Adj i j := by
        intro ha
        exact G.isIndepSet_neighborSet_of_triangleFree ht v
          ((G.mem_neighborFinset _ _).mp hI) ((G.mem_neighborFinset _ _).mp hJ) ha.ne ha
      simp [hh]
    have a := split N U
    have b := split N N
    have c := split N Nᶜ
    have s1 := sym Nᶜ U
    have s2 := sym N U
    have s3 := sym Nᶜ N
    have dd := deficit N
    have allD := deficit U
    have nc : N.card = 7 := hv
    have uc : U.card = 35 := by simp [U]
    change (∑ i ∈ U, G.degree i) + L.card = 8 * U.card at allD
    have t1 := total U
    have t2 := total N
    change L.card < 2 * (low N).card
    omega
  intro v
  rcases degrees v with h | h
  · exfalso
    let A := low (G.neighborFinset v)
    have ma : L.card < 2 * A.card := majority v h
    have pos : 0 < A.card := by omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp pos
    obtain ⟨hvn, hw7⟩ := Finset.mem_filter.mp hw
    have adj := (G.mem_neighborFinset _ _).mp hvn
    let D := low (G.neighborFinset w)
    have md : L.card < 2 * D.card := majority w hw7
    -- Adjacent vertices in a triangle-free graph have disjoint neighbourhoods.
    have dis : Disjoint A D := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      have vz := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hz).1
      have wz := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hz').1
      exact G.isIndepSet_neighborSet_of_triangleFree ht v adj vz wz.ne wz
    have sub : A ∪ D ⊆ L := by
      intro z hz
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hz with hz | hz <;> exact (Finset.mem_filter.mp hz).2
    have bound := Finset.card_le_card sub
    rw [Finset.card_union_of_disjoint dis] at bound
    omega
  · omega

end OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1
