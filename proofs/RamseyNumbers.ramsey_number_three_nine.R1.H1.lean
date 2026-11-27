import OMAReductions.R_RamseyNumbers_ramsey_number_three_nine_R1

/-! Kalbfleisch’s 35-vertex graph, from Brendan McKay’s combinatorial data
collection, https://users.cecs.anu.edu.au/~bdm/data/r39_35.g6 (CC BY 4.0).
The graph6 adjacency data is recoded as 35 neighborhood masks. The clique
search adapts the verifier in open-math-agents reduction #660 for R(3,6),
with an additional bound on the number of remaining vertices. -/
open SimpleGraph
namespace OMA.Ramsey35

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
      have hslen : s.card ≤ vs.length :=
        (Finset.card_le_card (show s ⊆ vs.toFinset from fun x hx => List.mem_toFinset.mpr (hsub x hx))).trans
          (List.toFinset_card_le vs)
      have hh : ¬ vs.length < j+1 := by rw [hs.card_eq] at hslen; omega
      change (if vs.length < j+1 then false else vs.any _) = true
      rw [if_neg hh]
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


def rows : Array ℕ := #[0x1fe, 0x2c5080201, 0x4a2c04001, 0x532101001, 0x2a4820401, 0x349200801, 0x558042001, 0x320330001, 0x4c04c8001, 0x20868c02, 0x402614210, 0x84192220, 0x48076008, 0x201609840, 0x110189404, 0xe016300, 0x11809c80, 0x413001290, 0x207001340, 0x2a804902, 0x49804888, 0x948024a0, 0x11c002504, 0x100390214, 0x20172022, 0x400e840c, 0x400648812, 0x80589060, 0x200634048, 0x4108029c, 0x22101162, 0x108200916, 0x80c040e8, 0x4100420b2, 0x20402054c]

def graph : SimpleGraph (Fin 35) where
  Adj u v := u ≠ v ∧ rows[min u.val v.val]!.testBit (max u.val v.val) = true
  symm := ⟨fun {u v} h => ⟨h.1.symm, by simpa only [min_comm v.val u.val,max_comm v.val u.val] using h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs
  (Decidable (u ≠ v ∧ rows[min u.val v.val]!.testBit (max u.val v.val) = true))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem red : graph.CliqueFree 3 := exclude_search graph 3 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem blue : graphᶜ.CliqueFree 9 := exclude_search graphᶜ 9 (by decide +kernel)

end OMA.Ramsey35

theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_three_nine_R1.H1 :=
  ⟨OMA.Ramsey35.graph, OMA.Ramsey35.red, OMA.Ramsey35.blue⟩
