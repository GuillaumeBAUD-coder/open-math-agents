import OMAStatements.S_mo_263706
import Mathlib

/-!
The graph: 18 vertices, the hamiltonian cycle `0 - 1 - ... - 17 - 0` plus the perfect matching
`chordN`. It arises from a non-bipartite cubic 10-vertex graph by replacing two vertices with
copies of `K_{2,3}` (whose 3-side carries the outside edges). By parity inside the bipartite
gadgets it has no 17-cycle; here this is checked by an exhaustive kernel search over simple
paths.
-/

namespace OMA.MO263706

def chordN (i : ℕ) : ℕ := [15, 16, 17, 11, 7, 8, 14, 4, 5, 12, 13, 3, 9, 10, 6, 0, 1, 2].getD i 0

def nbN (i : ℕ) : List ℕ := [(i + 1) % 18, (i + 17) % 18, chordN i]

def G : SimpleGraph (Fin 18) where
  Adj i j := j.val ∈ nbN i.val
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (j.val ∈ nbN i.val))

def R (a b : ℕ) : Prop := b ∈ nbN a

def noCyc (s : ℕ) : ℕ → List ℕ → ℕ → Bool
  | 0, _, cur => !((nbN cur).contains s)
  | k + 1, vis, cur => (nbN cur).all (fun w => vis.contains w || noCyc s k (w :: vis) w)

theorem noCyc_spec (s : ℕ) : ∀ (k : ℕ) (vis : List ℕ) (cur : ℕ) (ys : List ℕ),
    noCyc s k vis cur = true → ys.length = k →
    List.IsChain R (cur :: (ys ++ [s])) → (∀ y ∈ ys, y ∉ vis) → ys.Nodup → False := by
  intro k
  induction k with
  | zero =>
    intro vis cur ys h hl hc _ _
    rw [List.length_eq_zero_iff] at hl
    subst hl
    simp only [List.nil_append, List.isChain_cons_cons, List.isChain_singleton, and_true] at hc
    simp only [noCyc] at h
    rw [List.contains_iff_mem.mpr hc] at h
    exact absurd h (by decide)
  | succ k ih =>
    intro vis cur ys h hl hc hv hn
    match ys, hl with
    | y :: ys', hl =>
      simp only [List.cons_append, List.isChain_cons_cons] at hc
      simp only [noCyc, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem] at h
      rcases h y hc.1 with h1 | h1
      · exact hv y (by simp) h1
      · rw [List.nodup_cons] at hn
        refine ih (y :: vis) y ys' h1 (by simpa using hl) hc.2 ?_ hn.2
        intro z hz hz'
        rcases List.mem_cons.mp hz' with rfl | hz'
        · exact hn.1 hz
        · exact hv z (by simp [hz]) hz'

theorem noCyc_all : ∀ v < 2, noCyc v 16 [v] v = true := by decide +kernel

theorem no_long_cycle_aux (v : Fin 18) (hv2 : v.val < 2) (p : G.Walk v v) (hp : p.IsCycle)
    (hlen : p.length = 17) : False := by
  have hsupp : p.support = v :: p.support.tail := p.cons_tail_support.symm
  have htl : p.support.tail.length = 17 := by
    have := p.length_support
    rw [hsupp] at this
    simp only [List.length_cons] at this
    omega
  have hne : p.support.tail ≠ [] := by
    intro h; rw [h] at htl; simp at htl
  have hlast : p.support.tail.getLast hne = v := by
    rw [List.getLast_tail]
    exact p.getLast_support
  have hnd0 : p.support.tail.Nodup := hp.support_nodup
  have hch0 := p.isChain_adj_support
  set t := p.support.tail with ht
  have ht' : t = t.dropLast ++ [v] := by
    rw [← hlast]; exact (List.dropLast_append_getLast hne).symm
  rw [hsupp, ht'] at hch0
  rw [ht'] at hnd0
  have hch : List.IsChain R (v.val :: ((t.dropLast.map Fin.val) ++ [v.val])) := by
    have := (List.isChain_map (R := R) Fin.val).mpr hch0
    simpa [List.map_append] using this
  have hnd : ((t.dropLast.map Fin.val) ++ [v.val]).Nodup := by
    have := hnd0.map Fin.val_injective
    simpa [List.map_append] using this
  rw [List.nodup_append] at hnd
  refine noCyc_spec v.val 16 [v.val] v.val (t.dropLast.map Fin.val) (noCyc_all v.val hv2)
    ?_ hch ?_ hnd.1
  · rw [List.length_map, List.length_dropLast]; omega
  · intro y hy hy'
    exact hnd.2.2 y hy y hy' rfl

theorem no_long_cycle (v : Fin 18) (p : G.Walk v v) (hp : p.IsCycle) : p.length ≠ 17 := by
  intro hlen
  have hex : ∃ u ∈ p.support, u.val < 2 := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have hnd : p.support.tail.Nodup := hp.support_nodup
    have htl : p.support.tail.length = 17 := by
      have h1 := p.length_support
      rw [← p.cons_tail_support] at h1
      simp only [List.length_cons] at h1
      omega
    have hsub : p.support.tail.toFinset ⊆ Finset.univ.filter (fun x : Fin 18 => 2 ≤ x.val) := by
      intro x hx
      rw [List.mem_toFinset] at hx
      have := hcon x (List.mem_of_mem_tail hx)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hc1 := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, htl] at hc1
    have hc2 : (Finset.univ.filter (fun x : Fin 18 => 2 ≤ x.val)).card = 16 := by decide
    omega
  obtain ⟨u, hu, hu2⟩ := hex
  exact no_long_cycle_aux u hu2 (p.rotate u hu) (hp.rotate hu) (by simpa using hlen)

def hc : G.Walk 0 0 := (SimpleGraph.Walk.cons (show G.Adj 0 1 by decide) (SimpleGraph.Walk.cons (show G.Adj 1 2 by decide) (SimpleGraph.Walk.cons (show G.Adj 2 3 by decide) (SimpleGraph.Walk.cons (show G.Adj 3 4 by decide) (SimpleGraph.Walk.cons (show G.Adj 4 5 by decide) (SimpleGraph.Walk.cons (show G.Adj 5 6 by decide) (SimpleGraph.Walk.cons (show G.Adj 6 7 by decide) (SimpleGraph.Walk.cons (show G.Adj 7 8 by decide) (SimpleGraph.Walk.cons (show G.Adj 8 9 by decide) (SimpleGraph.Walk.cons (show G.Adj 9 10 by decide) (SimpleGraph.Walk.cons (show G.Adj 10 11 by decide) (SimpleGraph.Walk.cons (show G.Adj 11 12 by decide) (SimpleGraph.Walk.cons (show G.Adj 12 13 by decide) (SimpleGraph.Walk.cons (show G.Adj 13 14 by decide) (SimpleGraph.Walk.cons (show G.Adj 14 15 by decide) (SimpleGraph.Walk.cons (show G.Adj 15 16 by decide) (SimpleGraph.Walk.cons (show G.Adj 16 17 by decide) (SimpleGraph.Walk.cons (show G.Adj 17 0 by decide) SimpleGraph.Walk.nil))))))))))))))))))

theorem hc_cycle : hc.IsHamiltonianCycle := by
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_, by decide⟩
  unfold hc
  rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
  constructor <;> decide

theorem deg (v : Fin 18) : (G.neighborSet v).ncard = 3 := by
  rw [← G.coe_neighborFinset, Set.ncard_coe_finset, G.card_neighborFinset_eq_degree]
  revert v
  decide

theorem fin2_aux : ∀ x y z : Fin 2, x ≠ y → y ≠ z → x = z := by decide

theorem odd_cycle_aux (a b c d e f g h i : Fin 2)
    (h1 : a ≠ b) (h2 : b ≠ c) (h3 : c ≠ d) (h4 : d ≠ e) (h5 : e ≠ f) (h6 : f ≠ g) (h7 : g ≠ h)
    (h8 : h ≠ i) (h9 : i ≠ a) : False := by
  have e1 := fin2_aux _ _ _ h1 h2
  have e2 := fin2_aux _ _ _ h3 h4
  have e3 := fin2_aux _ _ _ h5 h6
  have e4 := fin2_aux _ _ _ h7 h8
  exact h9 (e4.symm.trans (e3.symm.trans (e2.symm.trans e1.symm)))

theorem not_bip : ¬ G.IsBipartite := by
  rintro ⟨C⟩
  have hv : ∀ i j : Fin 18, G.Adj i j → C i ≠ C j := fun i j h => C.valid h
  exact odd_cycle_aux (C 3) (C 4) (C 5) (C 6) (C 7) (C 8) (C 9) (C 10) (C 11)
    (hv _ _ (by decide)) (hv _ _ (by decide)) (hv _ _ (by decide)) (hv _ _ (by decide))
    (hv _ _ (by decide)) (hv _ _ (by decide)) (hv _ _ (by decide)) (hv _ _ (by decide))
    (hv _ _ (by decide))

end OMA.MO263706

theorem OMA.solution : type_of% @OMA.S_mo_263706.main :=
  ⟨18, OMA.MO263706.G, OMA.MO263706.deg,
    fun _ => ⟨0, OMA.MO263706.hc, OMA.MO263706.hc_cycle⟩,
    fun v p hp => OMA.MO263706.no_long_cycle v p hp, OMA.MO263706.not_bip⟩
