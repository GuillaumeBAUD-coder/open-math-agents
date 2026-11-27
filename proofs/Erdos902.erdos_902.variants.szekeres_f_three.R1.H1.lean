import OMAReductions.R_Erdos902_erdos_902_variants_szekeres_f_three_R1

open Erdos902 Finset

-- The arc count follows the parent reduction, which credits @luciusacarr.
private theorem two_mul_arcs {α : Type*} [Fintype α] [DecidableEq α] (G : Digraph α) [DecidableRel G.Adj]
    (hG : G.IsTournament) :
    2 * ∑ v : α, (univ.filter (fun x => G.Adj x v)).card = Fintype.card α * Fintype.card α - Fintype.card α := by
  have hT : ∑ v : α, (univ.filter (fun x => G.Adj x v)).card =
      ((univ : Finset (α × α)).filter (fun p => G.Adj p.1 p.2)).card := by
    simp only [card_filter]
    rw [Fintype.sum_prod_type_right]
  have hswap : ((univ : Finset (α × α)).filter (fun p => G.Adj p.2 p.1)).card =
      ((univ : Finset (α × α)).filter (fun p => G.Adj p.1 p.2)).card := by
    apply card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      rw [mem_filter] at hp ⊢
      exact ⟨mem_univ _, hp.2⟩
    · intro p _ q _ h
      rw [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      rw [mem_filter] at hq
      exact ⟨(q.2, q.1), by rw [mem_filter]; exact ⟨mem_univ _, hq.2⟩, rfl⟩
  have hunion : ((univ : Finset (α × α)).filter (fun p => G.Adj p.1 p.2)) ∪
      ((univ : Finset (α × α)).filter (fun p => G.Adj p.2 p.1)) =
      (univ : Finset (α)).offDiag := by
    ext p
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_offDiag]
    constructor
    · rintro (h | h)
      · exact fun e => hG.1 p.1 (by rw [← e] at h; exact h)
      · exact fun e => hG.1 p.1 (by rw [← e] at h; exact h)
    · intro hne
      by_cases h : G.Adj p.1 p.2
      · exact Or.inl h
      · exact Or.inr (by
          by_contra h'
          exact h ((hG.2 p.1 p.2 hne).2 h'))
  have hdisj : Disjoint ((univ : Finset (α × α)).filter (fun p => G.Adj p.1 p.2))
      ((univ : Finset (α × α)).filter (fun p => G.Adj p.2 p.1)) := by
    rw [disjoint_left]
    intro p hp hq
    rw [mem_filter] at hp hq
    have hne : p.1 ≠ p.2 := fun e => hG.1 p.1 (by have := hp.2; rw [← e] at this; exact this)
    exact (hG.2 p.1 p.2 hne).1 hp.2 hq.2
  have hcard := card_union_of_disjoint hdisj
  rw [hunion, offDiag_card, hswap] at hcard
  simp only [card_univ] at hcard
  rw [hT]
  omega

-- The multiplicity argument is due to Szekeres and Szekeres. This form is
-- inspired by Jared Wilder's Erdos902Szekeres.lean in jaredwilder/erdos902.
private theorem nine_le_indegree (G : Digraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.IsTournament) (hS : HasPropertyS G 3) (v : Fin 18) :
    9 ≤ (univ.filter (fun u => G.Adj u v)).card := by
  classical
  have dom (s : Finset (Fin 18)) (hs : s.card ≤ 3) : ∃ w, ∀ a ∈ s, G.Adj w a := by
    obtain ⟨t, hst, _, ht⟩ := exists_subsuperset_card_eq (subset_univ s) hs (by decide)
    obtain ⟨w, _, hw⟩ := hS t ht
    exact ⟨w, fun a ha => hw a (hst ha)⟩
  let N := univ.filter (fun u => G.Adj u v)
  let T : Digraph N := ⟨fun a b => G.Adj a.val b.val⟩
  have hT : T.IsTournament := ⟨fun a => hG.1 _, fun a b hab =>
    hG.2 _ _ (fun e => hab (Subtype.ext e))⟩
  have hfour (a : N) : 4 ≤ (univ.filter (fun u => T.Adj u a)).card := by
    by_contra! hsmall
    let D := univ.filter (fun u => T.Adj u a)
    let f : N ↪ Fin 18 := ⟨Subtype.val, Subtype.val_injective⟩
    obtain ⟨w, hw⟩ := dom (D.map f) (by rw [card_map]; exact Nat.le_of_lt_succ hsmall)
    have hsize : ({v, a.val, w} : Finset _).card ≤ 3 := by
      calc _ ≤ ({a.val, w} : Finset _).card + 1 := card_insert_le _ _
           _ ≤ 3 := by have := card_insert_le a.val {w}; simp only [card_singleton] at this; omega
    obtain ⟨x, hx⟩ := dom {v, a.val, w} hsize
    let z : N := ⟨x, mem_filter.mpr ⟨mem_univ _, hx v (by simp)⟩⟩
    have hz : z ∈ D := mem_filter.mpr ⟨mem_univ _, hx a.val (by simp)⟩
    have hwx : G.Adj w x := hw x (mem_map.mpr ⟨z, hz, rfl⟩)
    have hxw := hx w (by simp)
    have hne : w ≠ x := fun e => hG.1 x (e ▸ hwx)
    exact (hG.2 _ _ hne).1 hwx hxw
  have hsum := sum_le_sum (s := (univ : Finset N)) (fun a _ => hfour a)
  have heq := two_mul_arcs T hT
  simp only [sum_const, card_univ, Fintype.card_coe, smul_eq_mul] at hsum heq
  obtain ⟨w, hw⟩ := dom {v} (by simp)
  have hpos : 0 < N.card := card_pos.mpr ⟨w, mem_filter.mpr ⟨mem_univ _, hw v (by simp)⟩⟩
  change 9 ≤ N.card
  by_contra! hlt
  have := Nat.mul_le_mul_left N.card (show N.card ≤ 8 by omega)
  nlinarith [Nat.sub_add_cancel (show N.card ≤ N.card * N.card by nlinarith)]

theorem OMA.solution : OMA.R_Erdos902_erdos_902_variants_szekeres_f_three_R1.H1 := by
  intro G _ hG v hv hS
  have := nine_le_indegree G hG hS v
  omega

