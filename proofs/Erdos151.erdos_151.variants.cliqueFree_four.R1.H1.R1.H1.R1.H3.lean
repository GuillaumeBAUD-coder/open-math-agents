import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1

/-! Ramsey lower bounds R(3,9) >= 36 and R(3,10) >= 40 by explicit graphs.
The clique search lemma, the 35-vertex Kalbfleisch graph and its two checks are
adapted from the merged proof by @VinnyMo (open-math-agents #1435,
RamseyNumbers.ramsey_number_three_nine.R1.H1), whose graph data comes from
Brendan McKay, https://users.cecs.anu.edu.au/~bdm/data/r39_35.g6 (CC BY 4.0).
The 39-vertex triangle-free graph with no independent set of ten vertices is
Exoo's construction (G. Exoo, SIAM J. Discrete Math. 2 (1989) 488-490), taken
in graph6 form from the leaps-in-bounds certificate ramsey-3-10-lower-40
(github.com/daniel-munro/leaps-in-bounds, MIT) and recoded as upper-triangle
neighbourhood masks. -/
open SimpleGraph
namespace OMA.Erdos151Ramsey

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


def rows35 : Array ℕ := #[0x1fe, 0x2c5080201, 0x4a2c04001, 0x532101001, 0x2a4820401, 0x349200801, 0x558042001, 0x320330001, 0x4c04c8001, 0x20868c02, 0x402614210, 0x84192220, 0x48076008, 0x201609840, 0x110189404, 0xe016300, 0x11809c80, 0x413001290, 0x207001340, 0x2a804902, 0x49804888, 0x948024a0, 0x11c002504, 0x100390214, 0x20172022, 0x400e840c, 0x400648812, 0x80589060, 0x200634048, 0x4108029c, 0x22101162, 0x108200916, 0x80c040e8, 0x4100420b2, 0x20402054c]

def graph35 : SimpleGraph (Fin 35) where
  Adj u v := u ≠ v ∧ rows35[min u.val v.val]!.testBit (max u.val v.val) = true
  symm := ⟨fun {u v} h => ⟨h.1.symm, by simpa only [min_comm v.val u.val,max_comm v.val u.val] using h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

instance : DecidableRel graph35.Adj := fun u v => inferInstanceAs
  (Decidable (u ≠ v ∧ rows35[min u.val v.val]!.testBit (max u.val v.val) = true))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem red35 : graph35.CliqueFree 3 := exclude_search graph35 3 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem blue35 : graph35ᶜ.CliqueFree 9 := exclude_search graph35ᶜ 9 (by decide +kernel)


def rows39 : Array ℕ := #[0x204808452, 0x409010884, 0x2050121108, 0xa0242210, 0x5102084020, 0x420221240, 0x1042442080, 0x84884100, 0x4109008600, 0x2210110800, 0x10a0484800, 0x102809000, 0x4205012000, 0x2408124000, 0x50240000, 0x410290000, 0x1060420000, 0x82840000, 0x4105080000, 0x208100000, 0x4105200000, 0x1208400000, 0x6410800000, 0x1061000000, 0x2082000000, 0x224000000, 0x2408000000, 0x850000000, 0x10a0000000, 0x900000000, 0x4480000000, 0x100000000, 0x2200000000, 0xc00000000, 0x1000000000, 0x7000000000, 0x0, 0x0, 0x0]

def graph39 : SimpleGraph (Fin 39) where
  Adj u v := u ≠ v ∧ rows39[min u.val v.val]!.testBit (max u.val v.val) = true
  symm := ⟨fun {u v} h => ⟨h.1.symm, by simpa only [min_comm v.val u.val,max_comm v.val u.val] using h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

instance : DecidableRel graph39.Adj := fun u v => inferInstanceAs
  (Decidable (u ≠ v ∧ rows39[min u.val v.val]!.testBit (max u.val v.val) = true))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem red39 : graph39.CliqueFree 3 := exclude_search graph39 3 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem blue39 : graph39ᶜ.CliqueFree 10 := exclude_search graph39ᶜ 10 (by decide +kernel)

lemma bound {N K : ℕ} (hK : 1 ≤ K) (G0 : SimpleGraph (Fin N)) (h3 : G0.CliqueFree 3)
    (hc : G0ᶜ.CliqueFree K) : ∀ n, K ≤ Erdos151.H n → N < n := by
  intro n hn
  by_contra hle
  push_neg at hle
  have hS : ∀ k ∈ {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s},
      k ≤ K - 1 := by
    intro k hk
    by_contra hkK
    let f : Fin n ↪ Fin N := Fin.castLEEmb hle
    have hG3 : (G0.comap f).CliqueFree 3 := fun s hs => h3 _ ((hs.map (f := f)).mono (SimpleGraph.map_comap_le f G0))
    obtain ⟨s, hs⟩ := hk (G0.comap f) hG3
    have hcomp : (G0.comap f)ᶜ = G0ᶜ.comap f := by
      ext u v
      simp [f.injective.ne_iff]
    rw [← isNClique_compl, hcomp] at hs
    exact (hc.mono (by omega)) _ ((hs.map (f := f)).mono (SimpleGraph.map_comap_le f G0ᶜ))
  have h := csSup_le' hS
  unfold Erdos151.H at hn
  omega

end OMA.Erdos151Ramsey

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1.H3 :=
  ⟨fun n h => by
    have := OMA.Erdos151Ramsey.bound (by norm_num) _ OMA.Erdos151Ramsey.red35
      OMA.Erdos151Ramsey.blue35 n h
    omega,
   fun n h => by
    have := OMA.Erdos151Ramsey.bound (by norm_num) _ OMA.Erdos151Ramsey.red39
      OMA.Erdos151Ramsey.blue39 n h
    omega⟩
