import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2

-- Step WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H1
-- Credit: @mjsechrest2
-- Proof of the cut-vertex case (2*sigma + 3 <= n) of WOWII Conjecture 189:
--   1. Show G - c has exactly 2 connected components C1, C2, with sigma >= 2, |Ci| <= 2*sigma,
--      and c has at least 2 neighbors in each Ci.
--   2. Show any two vertices in Ci \ {x0} have distance <= 2 in G, yielding the degree lower bound
--      2 * deg_{Ci}(v) >= |Ci| (for dist(x0, v) <= 2) and >= |Ci| - 1 (otherwise).
--   3. Prove Chvatal's Hamiltonian cycle theorem via an edge-maximal counterexample and apply it
--      to obtain Hamiltonian paths ending at a neighbor of c in both C1 and C2, then concatenate at c.

namespace OMA.WOWII189H1

open SimpleGraph
open scoped Classical

section Chvatal

variable {W : Type*} [Fintype W]

def IsHamCycle (H : SimpleGraph W) (l : List W) : Prop :=
  l.Nodup ∧ l.length = Fintype.card W ∧ l.IsChain H.Adj ∧
    ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, H.Adj a b

def HasHamCycle (H : SimpleGraph W) : Prop :=
  ∃ l : List W, IsHamCycle H l

def ChvatalCond (H : SimpleGraph W) : Prop :=
  ∀ k : ℕ, 1 ≤ k → 2 * k < Fintype.card W →
    (Finset.univ.filter (fun v : W => H.degree v ≤ k)).card < k ∨
      k < (Finset.univ.filter (fun v : W => Fintype.card W - k ≤ H.degree v)).card

lemma isHamCycle_rot {H : SimpleGraph W} {l : List W} (hl : IsHamCycle H l) {q : W} (hq : q ∈ l) :
    ∃ l' : List W, IsHamCycle H l' ∧ l'.head? = some q := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hq
  obtain ⟨hnd, hlen, hch, hcl⟩ := hl
  have hperm : ((q :: B) ++ A).Perm (A ++ q :: B) := List.perm_append_comm
  refine ⟨(q :: B) ++ A, ⟨hperm.nodup_iff.mpr hnd, hperm.length_eq.trans hlen, ?_, ?_⟩, by simp⟩
  · rw [List.isChain_append] at hch
    refine List.isChain_append.mpr ⟨hch.2.1, hch.1, ?_⟩
    intro x hx y hy
    apply hcl
    · rw [List.getLast?_append]
      have : (q :: B).getLast? = some x := hx
      simp [this]
    · rw [List.head?_append, hy]
      rfl
  · intro x hx y hy
    simp only [List.head?_append, List.head?_cons, Option.some_or, Option.mem_def,
      Option.some.injEq] at hy
    subst hy
    cases hA : A with
    | nil =>
      rw [hA, List.append_nil] at hx
      apply hcl
      · rw [hA, List.nil_append]; exact hx
      · rw [hA, List.nil_append]; rfl
    | cons a A' =>
      rw [hA] at hx hch
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hx
      rw [List.isChain_append] at hch
      exact hch.2.2 x hx q rfl

lemma hasHamCycle_mono {H H' : SimpleGraph W} (hle : H ≤ H') (h : HasHamCycle H) :
    HasHamCycle H' := by
  obtain ⟨l, hnd, hlen, hch, hcl⟩ := h
  exact ⟨l, hnd, hlen, hch.imp (fun _ _ e => hle e), fun a ha b hb => hle (hcl a ha b hb)⟩

lemma degree_mono_le {H H' : SimpleGraph W} (hle : H ≤ H') (v : W) :
    H.degree v ≤ H'.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  exact Finset.card_le_card (fun u hu => (mem_neighborFinset _ _ _).mpr (hle ((mem_neighborFinset _ _ _).mp hu)))

lemma chvatalCond_mono {H H' : SimpleGraph W} (hle : H ≤ H') (h : ChvatalCond H) :
    ChvatalCond H' := by
  intro k hk1 hkm
  rcases h k hk1 hkm with h1 | h2
  · left
    exact lt_of_le_of_lt (Finset.card_le_card (fun v hv => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact (degree_mono_le hle v).trans hv)) h1
  · right
    exact lt_of_lt_of_le h2 (Finset.card_le_card (fun v hv => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hv.trans (degree_mono_le hle v)))

lemma top_hasHamCycle (hm : 3 ≤ Fintype.card W) : HasHamCycle (⊤ : SimpleGraph W) := by
  let l : List W := Finset.univ.toList
  have hnd : l.Nodup := Finset.nodup_toList _
  have hlen : l.length = Fintype.card W := Finset.length_toList _
  have hch : l.IsChain (⊤ : SimpleGraph W).Adj := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [SimpleGraph.top_adj]
    intro heq
    have := hnd.getElem_inj_iff.mp heq
    omega
  refine ⟨l, hnd, hlen, hch, ?_⟩
  intro a ha b hb
  simp only [SimpleGraph.top_adj]
  have hne : l ≠ [] := by
    intro h0; rw [h0] at hlen; simp at hlen; omega
  rw [List.getLast?_eq_some_getLast hne, Option.mem_def, Option.some.injEq] at ha
  rw [List.head?_eq_some_head hne, Option.mem_def, Option.some.injEq] at hb
  subst ha hb
  rw [List.getLast_eq_getElem, List.head_eq_getElem]
  intro heq
  have := hnd.getElem_inj_iff.mp heq
  omega

lemma mem_of_nodup_card {l : List W} (hnd : l.Nodup) (hlen : l.length = Fintype.card W) (x : W) :
    x ∈ l := by
  have hto : l.toFinset = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [List.toFinset_card_of_nodup hnd, hlen])
  exact List.mem_toFinset.mp (hto ▸ Finset.mem_univ x)

lemma hamPath_of_addEdge {H : SimpleGraph W} (hm : 3 ≤ Fintype.card W) {u v : W}
    (huv : u ≠ v) (hno : ¬ HasHamCycle H)
    (hadd : HasHamCycle (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)})) :
    ∃ l : List W, l.Nodup ∧ l.length = Fintype.card W ∧ l.IsChain H.Adj ∧
      l.head? = some u ∧ l.getLast? = some v := by
  let H' := H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
  obtain ⟨l0, hl0⟩ := hadd
  obtain ⟨l, ⟨hnd, hlen, hch, hcl⟩, hhead⟩ := isHamCycle_rot hl0 (mem_of_nodup_card hl0.1 hl0.2.1 u)
  cases l with
  | nil => simp at hhead
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst a
    have hu_not_t : u ∉ t := (List.nodup_cons.mp hnd).1
    have hnd_t : t.Nodup := (List.nodup_cons.mp hnd).2
    have hch_t : t.IsChain H'.Adj := (List.isChain_cons.mp hch).2
    have htlen2 : 2 ≤ t.length := by simp only [List.length_cons] at hlen; omega
    have htne : t ≠ [] := by intro h0; rw [h0] at htlen2; simp at htlen2
    have hadj_ne : ∀ x y : W, x ∈ t → y ∈ t → H'.Adj x y → H.Adj x y := by
      intro x y hx hy hxy
      rcases hxy with h | h
      · exact h
      · simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at h
        rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd hx hu_not_t
        · exact absurd hy hu_not_t
    have hch_t_H : t.IsChain H.Adj := by
      rw [List.isChain_iff_getElem] at hch_t ⊢
      intro i hi
      exact hadj_ne _ _ (List.getElem_mem _) (List.getElem_mem _) (hch_t i hi)
    have hhd_ne_last : t.head htne ≠ t.getLast htne := by
      rw [List.head_eq_getElem, List.getLast_eq_getElem]
      intro heq
      have := hnd_t.getElem_inj_iff.mp heq
      omega
    by_cases hlast : t.getLast htne = v
    · refine ⟨u :: t, hnd, hlen, ?_, rfl, ?_⟩
      · refine List.isChain_cons.mpr ⟨?_, hch_t_H⟩
        intro y hy
        have hy' := (List.isChain_cons.mp hch).1 y hy
        rcases hy' with h | h
        · exact h
        · simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at h
          rcases h.1 with ⟨-, rfl⟩ | ⟨hvu, -⟩
          · rw [List.head?_eq_some_head htne, Option.mem_def, Option.some.injEq] at hy
            exact absurd (hy.trans hlast.symm) hhd_ne_last
          · exact absurd hvu huv
      · rw [List.getLast?_cons_of_ne_nil htne, List.getLast?_eq_some_getLast htne, hlast]
    · by_cases hhd : t.head htne = v
      · have hperm : (u :: t.reverse).Perm (u :: t) := List.Perm.cons u (List.reverse_perm t)
        have hlast_adj : H'.Adj (t.getLast htne) u := by
          apply hcl
          · rw [List.getLast?_cons_of_ne_nil htne, List.getLast?_eq_some_getLast htne]; rfl
          · rfl
        have hlast_H : H.Adj (t.getLast htne) u := by
          rcases hlast_adj with h | h
          · exact h
          · simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at h
            rcases h.1 with ⟨h1, -⟩ | ⟨h2, -⟩
            · exact absurd (h1 ▸ List.getLast_mem htne) hu_not_t
            · exact absurd h2 hlast
        refine ⟨u :: t.reverse, hperm.nodup_iff.mpr hnd, hperm.length_eq.trans hlen, ?_, rfl, ?_⟩
        · refine List.isChain_cons.mpr ⟨?_, ?_⟩
          · intro y hy
            rw [List.head?_reverse, List.getLast?_eq_some_getLast htne, Option.mem_def,
              Option.some.injEq] at hy
            subst hy
            exact hlast_H.symm
          · rw [List.isChain_reverse]
            exact hch_t_H.imp (fun _ _ e => e.symm)
        · rw [List.getLast?_cons_of_ne_nil (by simpa using htne), List.getLast?_reverse,
            List.head?_eq_some_head htne, hhd]
      · exfalso
        apply hno
        refine ⟨u :: t, hnd, hlen, ?_, ?_⟩
        · refine List.isChain_cons.mpr ⟨?_, hch_t_H⟩
          intro y hy
          have hy' := (List.isChain_cons.mp hch).1 y hy
          rcases hy' with h | h
          · exact h
          · simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at h
            rcases h.1 with ⟨-, rfl⟩ | ⟨hvu, -⟩
            · rw [List.head?_eq_some_head htne, Option.mem_def, Option.some.injEq] at hy
              exact absurd hy hhd
            · exact absurd hvu huv
        · intro a ha b hb
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
          subst hb
          rw [List.getLast?_cons_of_ne_nil htne, List.getLast?_eq_some_getLast htne,
            Option.mem_def, Option.some.injEq] at ha
          subst ha
          have hcl' := hcl (t.getLast htne)
            (by rw [List.getLast?_cons_of_ne_nil htne, List.getLast?_eq_some_getLast htne]; rfl) u rfl
          rcases hcl' with h | h
          · exact h
          · simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at h
            rcases h.1 with ⟨h1, -⟩ | ⟨h2, -⟩
            · exact absurd (h1 ▸ List.getLast_mem htne) hu_not_t
            · exact absurd h2 hlast

lemma no_crossing_chords {H : SimpleGraph W} {l : List W} {u v : W}
    (hnd : l.Nodup) (hlen : l.length = Fintype.card W) (hch : l.IsChain H.Adj)
    (hhead : l.head? = some u) (hlast : l.getLast? = some v) (hno : ¬ HasHamCycle H)
    {j : ℕ} (hj : j + 1 < l.length) :
    ¬ (H.Adj u (l.getD (j + 1) u) ∧ H.Adj (l.getD j u) v) := by
  rintro ⟨hA, hB⟩
  apply hno
  set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
  have hperm : c.Perm l := by
    have := List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1)))
    rwa [List.take_append_drop] at this
  have hj1 : j < l.length := by omega
  have hne : l ≠ [] := by intro h0; rw [h0] at hj; simp at hj
  have e1 : (l.take (j + 1)).getLast? = some (l.getD j u) := by
    rw [List.getLast?_take, List.getD_eq_getElem _ _ hj1]
    simp [List.getElem?_eq_getElem hj1]
  have e2 : (l.drop (j + 1)).reverse.head? = some v := by
    rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega), hlast]
  have e3 : c.getLast? = some (l.getD (j + 1) u) := by
    rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
      List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
    rfl
  have e4 : c.head? = some u := by
    rw [hcdef, List.head?_append, List.head?_take, if_neg (by omega), hhead]
    rfl
  refine ⟨c, hperm.nodup_iff.mpr hnd, hperm.length_eq.trans hlen, ?_, ?_⟩
  · refine List.isChain_append.mpr ⟨hch.take _, ?_, ?_⟩
    · rw [List.isChain_reverse]
      exact (hch.drop _).imp (fun _ _ e => e.symm)
    · intro x hx y hy
      rw [e1, Option.mem_def, Option.some.injEq] at hx
      rw [e2, Option.mem_def, Option.some.injEq] at hy
      subst hx hy
      exact hB
  · intro a ha b hb
    rw [e3, Option.mem_def, Option.some.injEq] at ha
    rw [e4, Option.mem_def, Option.some.injEq] at hb
    subst ha hb
    exact hA.symm

theorem chvatal_cycle (H : SimpleGraph W) (hm : 3 ≤ Fintype.card W) (hC : ChvatalCond H) :
    HasHamCycle H := by
  by_contra hno
  let P : SimpleGraph W → Prop := fun M => ChvatalCond M ∧ ¬ HasHamCycle M
  obtain ⟨M, hHM, hMmax⟩ := Finite.exists_le_maximal (p := P) ⟨hC, hno⟩
  obtain ⟨hMC, hMno⟩ := hMmax.1
  let NonAdj := Finset.univ.filter (fun p : W × W => p.1 ≠ p.2 ∧ ¬ M.Adj p.1 p.2)
  have hNA_ne : NonAdj.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have htop : M = ⊤ := by
      ext x y
      simp only [SimpleGraph.top_adj]
      constructor
      · exact M.ne_of_adj
      · intro hne
        by_contra hna
        have : (x, y) ∈ NonAdj := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hna⟩
        rw [hemp] at this
        exact Finset.notMem_empty _ this
    exact hMno (htop ▸ top_hasHamCycle hm)
  obtain ⟨⟨u0, v0⟩, huv0_mem, huv0_max⟩ :=
    Finset.exists_max_image NonAdj (fun p => M.degree p.1 + M.degree p.2) hNA_ne
  obtain ⟨u, v, huv_mem, huv_max, hduv⟩ :
      ∃ u v : W, (u, v) ∈ NonAdj ∧
        (∀ p ∈ NonAdj, M.degree p.1 + M.degree p.2 ≤ M.degree u + M.degree v) ∧
        M.degree u ≤ M.degree v := by
    by_cases hle : M.degree u0 ≤ M.degree v0
    · exact ⟨u0, v0, huv0_mem, huv0_max, hle⟩
    · have hswap : (v0, u0) ∈ NonAdj := by
        simp only [NonAdj, Finset.mem_filter, Finset.mem_univ, true_and] at huv0_mem ⊢
        exact ⟨huv0_mem.1.symm, fun h => huv0_mem.2 h.symm⟩
      refine ⟨v0, u0, hswap, fun p hp => ?_, by omega⟩
      have := huv0_max p hp
      dsimp only at this
      omega
  obtain ⟨huv_ne, huv_na⟩ := (Finset.mem_filter.mp huv_mem).2
  dsimp only at huv_ne huv_na
  let M' := M ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
  have hM'_ham : HasHamCycle M' := by
    by_contra hM'no
    have hM'C : ChvatalCond M' := chvatalCond_mono le_sup_left hMC
    have hle' : M' ≤ M := hMmax.2 ⟨hM'C, hM'no⟩ le_sup_left
    have : M'.Adj u v := Or.inr ⟨Set.mem_singleton _, huv_ne⟩
    exact huv_na (hle' this)
  obtain ⟨l, hnd, hlen, hch, hhead, hlast⟩ := hamPath_of_addEdge hm huv_ne hMno hM'_ham
  set m := Fintype.card W with hmdef
  have hne : l ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen; omega
  have hl0 : l.getD 0 u = u := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => simp at hhead; exact hhead
  have hllast : l.getD (m - 1) u = v := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    have h1 := List.getLast_eq_getElem hne
    rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hlast
    rw [← hlast, h1]
    congr 1; omega
  let S := (Finset.range (m - 1)).filter (fun j => M.Adj u (l.getD (j + 1) u))
  let T := (Finset.range (m - 1)).filter (fun j => M.Adj (l.getD j u) v)
  have hS_card : M.degree u = S.card := by
    rw [← card_neighborFinset_eq_degree]
    have heq : M.neighborFinset u = S.image (fun j => l.getD (j + 1) u) := by
      ext y
      rw [mem_neighborFinset, Finset.mem_image]
      constructor
      · intro hy
        obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem (mem_of_nodup_card hnd hlen y)
        have hidx0 : idx ≠ 0 := by
          rintro rfl
          have : l[0] = u := by rw [← List.getD_eq_getElem _ _ hidx, hl0]
          exact hy.ne this.symm
        refine ⟨idx - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, ?_⟩
        · rw [show idx - 1 + 1 = idx by omega, List.getD_eq_getElem _ _ hidx]; exact hy
        · rw [show idx - 1 + 1 = idx by omega, List.getD_eq_getElem _ _ hidx]
      · rintro ⟨j, hj, rfl⟩
        exact (Finset.mem_filter.mp hj).2
    rw [heq, Finset.card_image_of_injOn]
    intro i hi j hj hij
    have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    simp only at hij
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hij
    have := hnd.getElem_inj_iff.mp hij
    omega
  have hT_card : M.degree v ≤ T.card := by
    rw [← card_neighborFinset_eq_degree]
    refine (Finset.card_le_card (t := T.image (fun j => l.getD j u)) ?_).trans Finset.card_image_le
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem (mem_of_nodup_card hnd hlen y)
    have hidxm : idx ≠ m - 1 := by
      rintro rfl
      have : l[m - 1] = v := by rw [← List.getD_eq_getElem _ _ hidx, hllast]
      exact hy.ne this.symm
    exact Finset.mem_image.mpr ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by
      rw [List.getD_eq_getElem _ _ hidx]; exact hy.symm⟩, List.getD_eq_getElem _ _ hidx⟩
  have hdisj : Disjoint S T := by
    refine Finset.disjoint_left.mpr (fun j hjS hjT => ?_)
    have hjr := Finset.mem_range.mp (Finset.mem_filter.mp hjS).1
    exact no_crossing_chords hnd hlen hch hhead hlast hMno (by omega)
      ⟨(Finset.mem_filter.mp hjS).2, (Finset.mem_filter.mp hjT).2⟩
  have hsum_le : M.degree u + M.degree v ≤ m - 1 := by
    have hsub : S ∪ T ⊆ Finset.range (m - 1) := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h <;> exact (Finset.mem_filter.mp h).1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_range] at hc
    omega
  set k := M.degree u with hkdef
  have hk1 : 1 ≤ k := by
    have h0S : 0 ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      rw [show 0 + 1 = 1 by rfl, List.getD_eq_getElem _ _ (by omega)]
      have h01 := (List.isChain_iff_getElem.mp hch) 0 (by omega)
      have h0u : l[0]'(by omega) = u := by rw [← List.getD_eq_getElem _ _ (by omega), hl0]
      rwa [h0u] at h01
    have : 0 < S.card := Finset.card_pos.mpr ⟨0, h0S⟩
    omega
  have h2km : 2 * k < m := by omega
  have hlow_ge : k ≤ (Finset.univ.filter (fun w : W => M.degree w ≤ k)).card := by
    have himg : S.image (fun j => l.getD j u) ⊆ Finset.univ.filter (fun w : W => M.degree w ≤ k) := by
      intro w hw
      obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.mp hw
      have hjr := Finset.mem_range.mp (Finset.mem_filter.mp hjS).1
      have hj_na : ¬ M.Adj (l.getD j u) v := fun h =>
        Finset.disjoint_left.mp hdisj hjS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjr, h⟩)
      have hj_ne : l.getD j u ≠ v := by
        intro heq
        rw [← hllast, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at heq
        have := hnd.getElem_inj_iff.mp heq
        omega
      have hmaxj := huv_max (l.getD j u, v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_ne, hj_na⟩)
      dsimp only at hmaxj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hinj : Set.InjOn (fun j => l.getD j u) (S : Set ℕ) := by
      intro i hi j hj hij
      have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      simp only at hij
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hij
      exact hnd.getElem_inj_iff.mp hij
    have hc := Finset.card_le_card himg
    rw [Finset.card_image_of_injOn hinj] at hc
    omega
  have hbig_gt : k < (Finset.univ.filter (fun w : W => m - k ≤ M.degree w)).card := by
    rcases hMC k hk1 h2km with hlt | hgt
    · omega
    · exact hgt
  let Big := Finset.univ.filter (fun w : W => m - k ≤ M.degree w)
  have hnot_sub : ¬ Big ⊆ M.neighborFinset u := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree] at hle
    dsimp only [Big] at hle
    omega
  obtain ⟨w, hwBig, hwnotN⟩ := Finset.not_subset.mp hnot_sub
  have hwdeg : m - k ≤ M.degree w := (Finset.mem_filter.mp hwBig).2
  have hwu_ne : u ≠ w := by
    rintro rfl
    omega
  have hwu_na : ¬ M.Adj u w := by
    rwa [mem_neighborFinset] at hwnotN
  have hmaxw := huv_max (u, w) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwu_ne, hwu_na⟩)
  dsimp only at hmaxw
  omega

end Chvatal

section ComponentPath

variable {W : Type*} [Fintype W]

lemma hamPath_of_cycle {H : SimpleGraph W} {T : Finset W} (hcyc : HasHamCycle H)
    (hT : T.Nonempty) :
    ∃ l : List W, l.Nodup ∧ l.length = Fintype.card W ∧ l.IsChain H.Adj ∧
      ∃ t ∈ T, l.getLast? = some t := by
  obtain ⟨t, ht⟩ := hT
  obtain ⟨l0, hl0⟩ := hcyc
  obtain ⟨l, ⟨hnd, hlen, hch, -⟩, hhead⟩ := isHamCycle_rot hl0 (mem_of_nodup_card hl0.1 hl0.2.1 t)
  refine ⟨l.reverse, List.nodup_reverse.mpr hnd, by simpa using hlen, ?_, t, ht, ?_⟩
  · rw [List.isChain_reverse]
    exact hch.imp (fun _ _ e => e.symm)
  · rw [List.getLast?_reverse, hhead]

lemma dist_le_card_sub_one {H : SimpleGraph W} (hconn : H.Connected) (x y : W) :
    H.dist x y ≤ Fintype.card W - 1 := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
  let q := p.bypass
  have hle : H.dist x y ≤ q.length := SimpleGraph.dist_le q
  have hnd : q.support.Nodup := p.bypass_isPath.support_nodup
  have hcard : q.support.length ≤ Fintype.card W := hnd.length_le_card
  have hsupp : q.support.length = q.length + 1 := SimpleGraph.Walk.length_support q
  omega

lemma chvatal_of_deg_ge_two {H H' : SimpleGraph W} (hm : 4 ≤ Fintype.card W)
    (hle : H ≤ H') (x₀ w : W) (hwx : w ≠ x₀) (hxw : H.Adj x₀ w)
    (hdeg_x0 : 2 ≤ H'.degree x₀)
    (hdeg : ∀ v : W, v ≠ x₀ →
      (H.dist x₀ v ≤ 2 → Fintype.card W ≤ 2 * H.degree v) ∧
      Fintype.card W - 1 ≤ 2 * H.degree v) :
    ChvatalCond H' := by
  set m := Fintype.card W with hmdef
  intro k hk1 h2km
  by_cases hk_one : k = 1
  · subst hk_one
    left
    have hemp : Finset.univ.filter (fun v : W => H'.degree v ≤ 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v _
      by_cases hv : v = x₀
      · subst hv; omega
      · have h1 := (hdeg v hv).2
        have h2 := degree_mono_le hle v
        omega
    simp [hemp]
  · by_cases hsmall : 2 * k + 1 < m
    · left
      have hsub : Finset.univ.filter (fun v : W => H'.degree v ≤ k) ⊆ {x₀} := by
        intro v hv
        rw [Finset.mem_singleton]
        by_contra hne
        have h1 := (hdeg v hne).2
        have h2 := degree_mono_le hle v
        have h3 : H'.degree v ≤ k := (Finset.mem_filter.mp hv).2
        omega
      have hc := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hc
      omega
    · right
      have hmk : m = 2 * k + 1 := by omega
      let S := insert w ((H.neighborFinset w).erase x₀)
      have hSsub : S ⊆ Finset.univ.filter (fun v : W => m - k ≤ H'.degree v) := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hu_ne : u ≠ x₀ := by
          rcases Finset.mem_insert.mp hu with rfl | hu'
          · exact hwx
          · exact (Finset.mem_erase.mp hu').1
        have hdist : H.dist x₀ u ≤ 2 := by
          rcases Finset.mem_insert.mp hu with rfl | hu'
          · exact (SimpleGraph.dist_eq_one_iff_adj.mpr hxw).le.trans (by decide)
          · have hwu : H.Adj w u := (mem_neighborFinset _ _ _).mp (Finset.mem_erase.mp hu').2
            have := SimpleGraph.dist_le (Walk.cons hxw (Walk.cons hwu Walk.nil))
            simpa using this
        have h1 := (hdeg u hu_ne).1 hdist
        have h2 := degree_mono_le hle u
        omega
      have hx0_mem : x₀ ∈ H.neighborFinset w := (mem_neighborFinset _ _ _).mpr hxw.symm
      have hw_not : w ∉ (H.neighborFinset w).erase x₀ := fun h =>
        H.loopless.irrefl w ((mem_neighborFinset _ _ _).mp (Finset.mem_erase.mp h).2)
      have hScard : S.card = H.degree w := by
        rw [Finset.card_insert_of_notMem hw_not, Finset.card_erase_of_mem hx0_mem,
          card_neighborFinset_eq_degree]
        have hpos : 1 ≤ H.degree w := by
          rw [← card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr ⟨x₀, hx0_mem⟩
        omega
      have hdw : Fintype.card W ≤ 2 * H.degree w := (hdeg w hwx).1
        ((SimpleGraph.dist_eq_one_iff_adj.mpr hxw).le.trans (by decide))
      have hc := Finset.card_le_card hSsub
      dsimp only [m] at hc hmk
      omega

lemma ham_path_of_component (H : SimpleGraph W) (hm : 2 ≤ Fintype.card W) (hconn : H.Connected)
    (T : Finset W) (hT : 2 ≤ T.card) (x₀ : W)
    (hdeg : ∀ v : W, v ≠ x₀ →
      (H.dist x₀ v ≤ 2 → Fintype.card W ≤ 2 * H.degree v) ∧
      Fintype.card W - 1 ≤ 2 * H.degree v) :
    ∃ l : List W, l.Nodup ∧ l.length = Fintype.card W ∧ l.IsChain H.Adj ∧
      ∃ t ∈ T, l.getLast? = some t := by
  set m := Fintype.card W with hmdef
  by_cases hm2 : m = 2
  · obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
    have hadj : H.Adj t₁ t₂ := by
      have : Nontrivial W := ⟨⟨t₁, t₂, hne⟩⟩
      obtain ⟨y, hy⟩ := hconn.preconnected.exists_adj_of_nontrivial t₁
      have hyt2 : y = t₂ := by
        have h2 : ({t₁, t₂} : Finset W).card = 2 := Finset.card_pair hne
        have huniv : ({t₁, t₂} : Finset W) = Finset.univ := Finset.eq_univ_of_card _ (by omega)
        have : y ∈ ({t₁, t₂} : Finset W) := huniv ▸ Finset.mem_univ y
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · exact absurd hy (H.loopless.irrefl _)
        · rfl
      exact hyt2 ▸ hy
    refine ⟨[t₁, t₂], by simp [hne], by simp [hm2], by simp [hadj], t₂, ht₂, rfl⟩
  by_cases hm3 : m = 3
  · have htop : H = ⊤ := by
      ext u v
      simp only [SimpleGraph.top_adj]
      constructor
      · exact H.ne_of_adj
      · intro huv
        suffices ∀ a b : W, a ≠ x₀ → a ≠ b → H.Adj a b by
          by_cases hu : u = x₀
          · exact (this v u (hu ▸ huv.symm) huv.symm).symm
          · exact this u v hu huv
        intro a b ha hab
        have hd : H.dist x₀ a ≤ 2 := by
          have := dist_le_card_sub_one hconn x₀ a
          omega
        have hda : 2 ≤ H.degree a := by
          have := (hdeg a ha).1 hd
          omega
        have hsub : H.neighborFinset a ⊆ Finset.univ.erase a := by
          intro z hz
          exact Finset.mem_erase.mpr ⟨((mem_neighborFinset _ _ _).mp hz).ne.symm, Finset.mem_univ _⟩
        have heq : H.neighborFinset a = Finset.univ.erase a := Finset.eq_of_subset_of_card_le hsub (by
          rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, card_neighborFinset_eq_degree]
          omega)
        have hb : b ∈ H.neighborFinset a := heq ▸ Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
        exact (mem_neighborFinset _ _ _).mp hb
    exact hamPath_of_cycle (htop ▸ top_hasHamCycle (by omega)) (Finset.card_pos.mp (by omega))
  have hm4 : 4 ≤ m := by omega
  have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w₀, hw₀⟩ := hconn.preconnected.exists_adj_of_nontrivial x₀
  by_cases hd2 : 2 ≤ H.degree x₀
  · have hC := chvatal_of_deg_ge_two hm4 le_rfl x₀ w₀ hw₀.ne.symm hw₀ hd2 hdeg
    exact hamPath_of_cycle (chvatal_cycle H (by omega) hC) (Finset.card_pos.mp (by omega))
  · have hd1 : H.degree x₀ = 1 := by
      have : 1 ≤ H.degree x₀ := by
        rw [← card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨w₀, (mem_neighborFinset _ _ _).mpr hw₀⟩
      omega
    have huniq : ∀ u : W, H.Adj x₀ u → u = w₀ := by
      intro u hu
      have hle1 : (H.neighborFinset x₀).card ≤ 1 := by rw [card_neighborFinset_eq_degree]; omega
      exact Finset.card_le_one.mp hle1 u ((mem_neighborFinset _ _ _).mpr hu) w₀
        ((mem_neighborFinset _ _ _).mpr hw₀)
    by_cases hx0T : x₀ ∈ T
    · -- Induce on W' = {v : W | v ≠ x₀}
      let W' := {v : W // v ≠ x₀}
      let H' : SimpleGraph W' := H.induce {v : W | v ≠ x₀}
      have hcard' : Fintype.card W' = m - 1 := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      have hdeg' : ∀ v : W',
          (v.1 ≠ w₀ → H'.degree v = H.degree v.1) ∧
          (v.1 = w₀ → H'.degree v + 1 = H.degree v.1) := by
        intro v
        have hbij : (H'.neighborFinset v).card = ((H.neighborFinset v.1).erase x₀).card := by
          refine Finset.card_bij (fun (u : W') _ => u.1) ?_ ?_ ?_
          · intro u hu
            have hu' : H.Adj v.1 u.1 := (H'.mem_neighborFinset v u).mp hu
            exact Finset.mem_erase.mpr ⟨u.2, (H.mem_neighborFinset v.1 u.1).mpr hu'⟩
          · intro u₁ _ u₂ _ h; exact Subtype.ext h
          · intro u hu
            obtain ⟨hux, hua⟩ := Finset.mem_erase.mp hu
            exact ⟨⟨u, hux⟩, (H'.mem_neighborFinset v ⟨u, hux⟩).mpr ((H.mem_neighborFinset v.1 u).mp hua), rfl⟩
        rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, hbij]
        constructor
        · intro hne
          have hnot : x₀ ∉ H.neighborFinset v.1 := fun h =>
            hne (huniq v.1 ((mem_neighborFinset _ _ _).mp h).symm)
          rw [Finset.erase_eq_of_notMem hnot]
        · intro heq
          have hmem : x₀ ∈ H.neighborFinset v.1 := (mem_neighborFinset _ _ _).mpr (heq ▸ hw₀.symm)
          rw [Finset.card_erase_of_mem hmem]
          have hpos : 1 ≤ (H.neighborFinset v.1).card := Finset.card_pos.mpr ⟨x₀, hmem⟩
          omega
      have hC' : ChvatalCond H' := by
        intro k hk1 h2km'
        have hdw0 : Fintype.card W ≤ 2 * H.degree w₀ := (hdeg w₀ hw₀.ne.symm).1
          ((SimpleGraph.dist_eq_one_iff_adj.mpr hw₀).le.trans (by decide))
        by_cases hk2 : 2 ≤ k
        · left
          refine lt_of_le_of_lt (Finset.card_le_card (t := ({⟨w₀, hw₀.ne.symm⟩} : Finset W')) ?_)
            (by rw [Finset.card_singleton]; omega)
          intro v hv
          rw [Finset.mem_singleton]
          by_contra hne
          have hvne : v.1 ≠ w₀ := fun h => hne (Subtype.ext h)
          have h1 := (hdeg' v).1 hvne
          have h2 := (hdeg v.1 v.2).2
          have h3 : H'.degree v ≤ k := by convert (Finset.mem_filter.mp hv).2
          dsimp only [m] at hcard'
          omega
        · have hk_eq : k = 1 := by omega
          subst hk_eq
          by_cases hm5 : 5 ≤ m
          · left
            refine lt_of_le_of_lt (Finset.card_le_card (t := (∅ : Finset W')) ?_) (by simp)
            intro v hv
            exfalso
            have h3 : H'.degree v ≤ 1 := by convert (Finset.mem_filter.mp hv).2
            dsimp only [m] at hm5
            by_cases hv0 : v.1 = w₀
            · have h1 := (hdeg' v).2 hv0
              rw [hv0] at h1
              omega
            · have h1 := (hdeg' v).1 hv0
              have h2 := (hdeg v.1 v.2).2
              omega
          · right
            have hm4' : m = 4 := by omega
            refine lt_of_lt_of_le ?_ (Finset.card_le_card (s := Finset.univ.erase ⟨w₀, hw₀.ne.symm⟩) ?_)
            · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
              omega
            · intro v hv
              have hvne : v.1 ≠ w₀ := fun h => (Finset.mem_erase.mp hv).1 (Subtype.ext h)
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              have h1 := (hdeg' v).1 hvne
              have h2 := (hdeg v.1 v.2).2
              have hle : Fintype.card W' - 1 ≤ H'.degree v := by dsimp only [m] at hcard' hm4'; omega
              convert hle
      obtain ⟨l0, hl0⟩ := chvatal_cycle H' (by omega) hC'
      obtain ⟨l', ⟨hnd', hlen', hch', -⟩, hhead'⟩ :=
        isHamCycle_rot hl0 (mem_of_nodup_card hl0.1 hl0.2.1 ⟨w₀, hw₀.ne.symm⟩)
      let lrev := l'.reverse.map Subtype.val
      have hrev_nd : lrev.Nodup := (List.nodup_reverse.mpr hnd').map Subtype.val_injective
      have hrev_x0 : x₀ ∉ lrev := by
        intro h
        obtain ⟨u, -, hu⟩ := List.mem_map.mp h
        exact u.2 hu
      have hrev_ch : lrev.IsChain H.Adj := by
        have hr : l'.reverse.IsChain H'.Adj := by
          rw [List.isChain_reverse]
          exact hch'.imp (fun _ _ e => e.symm)
        rw [List.isChain_map]
        exact hr
      have hrev_last : lrev.getLast? = some w₀ := by
        rw [List.getLast?_map, List.getLast?_reverse, hhead']
        rfl
      refine ⟨lrev ++ [x₀], ?_, ?_, ?_, x₀, hx0T, by simp⟩
      · rw [List.nodup_append]
        refine ⟨hrev_nd, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        rintro rfl
        exact hrev_x0 ha
      · simp only [List.length_append, List.length_singleton, lrev, List.length_map,
          List.length_reverse, hlen', hcard']
        omega
      · refine List.isChain_append.mpr ⟨hrev_ch, List.isChain_singleton _, ?_⟩
        intro a ha b hb
        rw [hrev_last, Option.mem_def, Option.some.injEq] at ha
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        subst ha hb
        exact hw₀.symm
    · -- x₀ ∉ T: pick t ∈ T with t ≠ w₀, form H* = H ⊔ {x₀, t}
      have hTe : (T.erase w₀).Nonempty := by
        rw [← Finset.card_pos]
        have := Finset.pred_card_le_card_erase (s := T) (a := w₀)
        omega
      obtain ⟨t, ht_er⟩ := hTe
      obtain ⟨htw0, htT⟩ := Finset.mem_erase.mp ht_er
      have htx0 : t ≠ x₀ := fun h => hx0T (h ▸ htT)
      have hna : ¬ H.Adj x₀ t := fun h => htw0 (huniq t h)
      let Hstar := H ⊔ SimpleGraph.fromEdgeSet {s(x₀, t)}
      have hdeg_star : 2 ≤ Hstar.degree x₀ := by
        rw [← card_neighborFinset_eq_degree]
        have hsub : ({w₀, t} : Finset W) ⊆ Hstar.neighborFinset x₀ := by
          intro z hz
          rw [mem_neighborFinset]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Or.inl hw₀
          · exact Or.inr ⟨Set.mem_singleton _, htx0.symm⟩
        have hc := Finset.card_le_card hsub
        rwa [Finset.card_pair htw0.symm] at hc
      have hCstar := chvatal_of_deg_ge_two hm4 le_sup_left x₀ w₀ hw₀.ne.symm hw₀ (by convert hdeg_star) hdeg
      obtain ⟨l0, hl0⟩ := chvatal_cycle Hstar (by omega) hCstar
      obtain ⟨l, ⟨hnd, hlen, hch, hcl⟩, hhead⟩ := isHamCycle_rot hl0 (mem_of_nodup_card hl0.1 hl0.2.1 x₀)
      cases l with
      | nil => simp at hhead
      | cons a rest =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst a
        have hx0_not : x₀ ∉ rest := (List.nodup_cons.mp hnd).1
        have hnd_r : rest.Nodup := (List.nodup_cons.mp hnd).2
        have hch_r : rest.IsChain Hstar.Adj := (List.isChain_cons.mp hch).2
        have hrlen : 3 ≤ rest.length := by simp only [List.length_cons] at hlen; omega
        have hrne : rest ≠ [] := by intro h0; rw [h0] at hrlen; simp at hrlen
        have hadj_r : ∀ x y : W, x ∈ rest → y ∈ rest → Hstar.Adj x y → H.Adj x y := by
          intro x y hx hy hxy
          rcases hxy with h | h
          · exact h
          · simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at h
            rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact absurd hx hx0_not
            · exact absurd hy hx0_not
        have hch_r_H : rest.IsChain H.Adj := by
          rw [List.isChain_iff_getElem] at hch_r ⊢
          intro i hi
          exact hadj_r _ _ (List.getElem_mem _) (List.getElem_mem _) (hch_r i hi)
        have hnbr_star : ∀ y : W, Hstar.Adj x₀ y → y = w₀ ∨ y = t := by
          intro y hy
          rcases hy with h | h
          · exact Or.inl (huniq y h)
          · simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at h
            rcases h.1 with ⟨-, rfl⟩ | ⟨h2, -⟩
            · exact Or.inr rfl
            · exact absurd h2.symm htx0
        have hrh_adj : Hstar.Adj x₀ (rest.head hrne) :=
          (List.isChain_cons.mp hch).1 _ (List.head?_eq_some_head hrne)
        have hrl_adj : Hstar.Adj x₀ (rest.getLast hrne) :=
          (hcl _ (by rw [List.getLast?_cons_of_ne_nil hrne, List.getLast?_eq_some_getLast hrne]; rfl) x₀ rfl).symm
        have hrh_ne_l : rest.head hrne ≠ rest.getLast hrne := by
          rw [List.head_eq_getElem, List.getLast_eq_getElem]
          intro heq
          have := hnd_r.getElem_inj_iff.mp heq
          omega
        rcases hnbr_star _ hrh_adj with hh | hh <;> rcases hnbr_star _ hrl_adj with hl | hl
        · exact absurd (hh.trans hl.symm) hrh_ne_l
        · refine ⟨x₀ :: rest, hnd, hlen, List.isChain_cons.mpr ⟨?_, hch_r_H⟩, t, htT, ?_⟩
          · intro y hy
            rw [List.head?_eq_some_head hrne, Option.mem_def, Option.some.injEq] at hy
            rw [← hy, hh]; exact hw₀
          · rw [List.getLast?_cons_of_ne_nil hrne, List.getLast?_eq_some_getLast hrne, hl]
        · have hperm : (x₀ :: rest.reverse).Perm (x₀ :: rest) :=
            List.Perm.cons x₀ (List.reverse_perm rest)
          refine ⟨x₀ :: rest.reverse, hperm.nodup_iff.mpr hnd, hperm.length_eq.trans hlen,
            List.isChain_cons.mpr ⟨?_, ?_⟩, t, htT, ?_⟩
          · intro y hy
            rw [List.head?_reverse, List.getLast?_eq_some_getLast hrne, Option.mem_def,
              Option.some.injEq] at hy
            rw [← hy, hl]; exact hw₀
          · rw [List.isChain_reverse]
            exact hch_r_H.imp (fun _ _ e => e.symm)
          · rw [List.getLast?_cons_of_ne_nil (by simpa using hrne), List.getLast?_reverse,
              List.head?_eq_some_head hrne, hh]
        · exact absurd (hh.trans hl.symm) hrh_ne_l

end ComponentPath

section CutVertex

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma walk_induce_of_notMem {G : SimpleGraph V} {S : Set V} :
    ∀ {a b : V} (p : G.Walk a b) (hp : ∀ v ∈ p.support, v ∈ S),
      (G.induce S).Reachable ⟨a, hp a (Walk.start_mem_support p)⟩
        ⟨b, hp b (Walk.end_mem_support p)⟩
  | _, _, .nil, _ => Reachable.refl _
  | a, b, .cons h q, hp => by
    have hq : ∀ v ∈ q.support, v ∈ S := fun v hv => hp v (List.mem_cons_of_mem _ hv)
    have hstep : (G.induce S).Adj ⟨a, hp a (List.mem_cons_self)⟩
        ⟨_, hq _ (Walk.start_mem_support q)⟩ := h
    exact (Adj.reachable hstep).trans (walk_induce_of_notMem q hq)

lemma dist_through_cut {G : SimpleGraph V} (hconn : G.Connected) {c : V}
    {x y : V} (hx : x ≠ c) (hy : y ≠ c)
    (hdiff : (G.induce {v | v ≠ c}).connectedComponentMk ⟨x, hx⟩ ≠
      (G.induce {v | v ≠ c}).connectedComponentMk ⟨y, hy⟩) :
    G.dist x y = G.dist x c + G.dist c y := by
  apply le_antisymm (hconn.dist_triangle (u := x) (v := c) (w := y))
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
  have hc_mem : c ∈ p.support := by
    by_contra hnot
    have hall : ∀ v ∈ p.support, v ≠ c := fun v hv hvc => hnot (hvc ▸ hv)
    have hreach := walk_induce_of_notMem (S := {v | v ≠ c}) p hall
    exact hdiff (ConnectedComponent.eq.mpr hreach)
  have h1 := SimpleGraph.dist_le (p.takeUntil c hc_mem)
  have h2 := SimpleGraph.dist_le (p.dropUntil c hc_mem)
  have hlen : (p.takeUntil c hc_mem).length + (p.dropUntil c hc_mem).length = p.length := by
    rw [← Walk.length_append, Walk.take_spec]
  omega

lemma exists_adj_in_comp {G : SimpleGraph V} (hconn : G.Connected) {c : V}
    (K : (G.induce {v | v ≠ c}).ConnectedComponent) :
    ∃ u : {v : V // v ≠ c}, (G.induce {v | v ≠ c}).connectedComponentMk u = K ∧ G.Adj c u.1 := by
  obtain ⟨⟨w0, hw0⟩, hw⟩ := K.exists_rep
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist c w0
  cases p with
  | nil => exact absurd rfl hw0
  | cons hadj q =>
    rename_i u
    have hu_ne : u ≠ c := hadj.ne.symm
    have hc_not_q : c ∉ q.support := by
      intro hmem
      have hle := SimpleGraph.dist_le (q.dropUntil c hmem)
      have hlen : (q.takeUntil c hmem).length + (q.dropUntil c hmem).length = q.length := by
        rw [← Walk.length_append, Walk.take_spec]
      simp only [Walk.length_cons] at hp
      omega
    have hall : ∀ v ∈ q.support, v ≠ c := fun v hv hvc => hc_not_q (hvc ▸ hv)
    have hreach := walk_induce_of_notMem (S := {v | v ≠ c}) q hall
    exact ⟨⟨u, hu_ne⟩, (ConnectedComponent.eq.mpr hreach).trans hw, hadj⟩

lemma dist_eq_succ_of_unique_nbr {G : SimpleGraph V} (hconn : G.Connected) {c u : V}
    (hu : u ≠ c) (hcu : G.Adj c u)
    (huniq : ∀ v : V, (hv : v ≠ c) →
      (G.induce {x | x ≠ c}).connectedComponentMk ⟨v, hv⟩ =
        (G.induce {x | x ≠ c}).connectedComponentMk ⟨u, hu⟩ →
      G.Adj c v → v = u)
    {y : V} (hy : y ≠ c)
    (hyK : (G.induce {x | x ≠ c}).connectedComponentMk ⟨y, hy⟩ =
      (G.induce {x | x ≠ c}).connectedComponentMk ⟨u, hu⟩) :
    G.dist c y = 1 + G.dist u y := by
  apply le_antisymm
  · have h1 := hconn.dist_triangle (u := c) (v := u) (w := y)
    have h2 : G.dist c u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hcu
    omega
  · obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist c y
    cases p with
    | nil => exact absurd rfl hy
    | cons hadj q =>
      rename_i v
      have hv_ne : v ≠ c := hadj.ne.symm
      have hc_not_q : c ∉ q.support := by
        intro hmem
        have hle := SimpleGraph.dist_le (q.dropUntil c hmem)
        have hlen : (q.takeUntil c hmem).length + (q.dropUntil c hmem).length = q.length := by
          rw [← Walk.length_append, Walk.take_spec]
        simp only [Walk.length_cons] at hp
        omega
      have hall : ∀ z ∈ q.support, z ≠ c := fun z hz hzc => hc_not_q (hzc ▸ hz)
      have hreach := walk_induce_of_notMem (S := {x | x ≠ c}) q hall
      have hvK : (G.induce {x | x ≠ c}).connectedComponentMk ⟨v, hv_ne⟩ =
          (G.induce {x | x ≠ c}).connectedComponentMk ⟨u, hu⟩ :=
        (ConnectedComponent.eq.mpr hreach).trans hyK
      have hvu : v = u := huniq v hv_ne hvK hadj
      subst hvu
      have hle := SimpleGraph.dist_le q
      simp only [Walk.length_cons] at hp
      omega

omit [Fintype V] [DecidableEq V] in
lemma dist_induce_ge {G : SimpleGraph V} {S : Set V} (a b : S)
    (hr : (G.induce S).Reachable a b) :
    G.dist a.1 b.1 ≤ (G.induce S).dist a b := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hle := SimpleGraph.dist_le (p.map (Embedding.induce S).toHom)
  rw [Walk.length_map, hp] at hle
  exact hle

end CutVertex

end OMA.WOWII189H1

open SimpleGraph OMA.WOWII189H1
open scoped Classical

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.H1 := by
  intro V _ _ _ G _ hconn hH hn ⟨c, hcut⟩
  set σ := secondSmallestDegree G with hσdef
  let Vc := {x : V // x ≠ c}
  let Gc : SimpleGraph Vc := G.induce {x : V | x ≠ c}
  let Comp := Gc.ConnectedComponent
  haveI : Finite Comp := Finite.of_surjective Gc.connectedComponentMk Quot.exists_rep
  haveI : Fintype Comp := Fintype.ofFinite Comp
  haveI hVc_ne : Nonempty Vc := by
    haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x, hx⟩ := exists_ne c
    exact ⟨⟨x, hx⟩⟩
  haveI : Nonempty {x : V | x ≠ c} := hVc_ne
  have hcomp_two : 2 ≤ Fintype.card Comp := by
    by_contra hlt
    have h1 : Fintype.card Comp = 1 := by
      have : Nonempty Comp := ⟨Gc.connectedComponentMk (Classical.arbitrary Vc)⟩
      have := Fintype.card_pos (α := Comp)
      omega
    apply hcut
    refine ⟨fun x y => ?_⟩
    have hsub : Subsingleton Comp := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact ConnectedComponent.eq.mp (Subsingleton.elim _ _)
  let Vcomp (K : Comp) : Finset V :=
    Finset.univ.filter (fun v => ∃ hv : v ≠ c, Gc.connectedComponentMk ⟨v, hv⟩ = K)
  let O (K : Comp) : Finset V := (Vcomp K).filter (fun v => Odd (G.dist c v))
  let E (K : Comp) : Finset V := (Vcomp K).filter (fun v => Even (G.dist c v))
  have hmem_Vcomp : ∀ (K : Comp) (v : V), v ∈ Vcomp K ↔
      ∃ hv : v ≠ c, Gc.connectedComponentMk ⟨v, hv⟩ = K := by
    intro K v; simp [Vcomp]
  have hdisj_comp : ∀ K₁ K₂ : Comp, K₁ ≠ K₂ → Disjoint (Vcomp K₁) (Vcomp K₂) := by
    intro K₁ K₂ hne
    refine Finset.disjoint_left.mpr (fun v hv1 hv2 => ?_)
    obtain ⟨hv, h1⟩ := (hmem_Vcomp K₁ v).mp hv1
    obtain ⟨_, h2⟩ := (hmem_Vcomp K₂ v).mp hv2
    exact hne (h1.symm.trans h2)
  have hunion_comp : Finset.univ.biUnion Vcomp = Finset.univ.erase c := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_erase, and_true, hmem_Vcomp]
    constructor
    · rintro ⟨_, hv, _⟩; exact hv
    · intro hv; exact ⟨Gc.connectedComponentMk ⟨v, hv⟩, hv, rfl⟩
  have hsum_Vcomp : ∑ K : Comp, (Vcomp K).card = Fintype.card V - 1 := by
    rw [← Finset.card_biUnion (fun K₁ _ K₂ _ h => hdisj_comp K₁ K₂ h), hunion_comp,
      Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]
  have hOE_card : ∀ K : Comp, (O K).card + (E K).card = (Vcomp K).card := by
    intro K
    have hdisj : Disjoint (O K) (E K) := Finset.disjoint_left.mpr (fun v h1 h2 =>
      (Nat.not_even_iff_odd.mpr (Finset.mem_filter.mp h1).2) (Finset.mem_filter.mp h2).2)
    have hun : O K ∪ E K = Vcomp K := by
      ext v
      simp only [Finset.mem_union, O, E, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        rcases Nat.even_or_odd (G.dist c v) with he | ho
        · exact Or.inr ⟨h, he⟩
        · exact Or.inl ⟨h, ho⟩
    rw [← Finset.card_union_of_disjoint hdisj, hun]
  have hsum_E : ∑ K : Comp, (E K).card ≤ σ := by
    have hdisjE : Set.PairwiseDisjoint (Finset.univ : Finset Comp) E := by
      intro K₁ _ K₂ _ hne
      exact (hdisj_comp K₁ K₂ hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hsub : insert c (Finset.univ.biUnion E) ⊆ Finset.univ.filter (fun w => Even (G.dist c w)) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · simp
      · obtain ⟨K, -, hwK⟩ := Finset.mem_biUnion.mp hw'
        exact (Finset.mem_filter.mp hwK).2
    have hc_not : c ∉ Finset.univ.biUnion E := by
      intro h
      obtain ⟨K, -, hcK⟩ := Finset.mem_biUnion.mp h
      obtain ⟨hne, -⟩ := (hmem_Vcomp K c).mp (Finset.mem_filter.mp hcK).1
      exact hne rfl
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hc_not, Finset.card_biUnion hdisjE] at hcard
    have hHc : (Finset.univ.filter (fun w => Even (G.dist c w))).card ≤ 1 + σ := hH c
    omega
  have hsum_O_ge : σ + 2 ≤ ∑ K : Comp, (O K).card := by
    have htot : (∑ K : Comp, (O K).card) + (∑ K : Comp, (E K).card) = Fintype.card V - 1 := by
      rw [← Finset.sum_add_distrib]
      simpa [hOE_card] using hsum_Vcomp
    omega
  have hO_other_le : ∀ K : Comp, ∑ K' ∈ Finset.univ.erase K, (O K').card ≤ σ := by
    intro K
    obtain ⟨u, huK, hcu⟩ := exists_adj_in_comp hconn K
    have hdisjO : Set.PairwiseDisjoint (Finset.univ.erase K) O := by
      intro K₁ _ K₂ _ hne
      exact (hdisj_comp K₁ K₂ hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hsub : insert u.1 ((Finset.univ.erase K).biUnion O) ⊆
        Finset.univ.filter (fun w => Even (G.dist u.1 w)) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · simp
      · obtain ⟨K', hK', hwK'⟩ := Finset.mem_biUnion.mp hw'
        have hne : K ≠ K' := (Finset.mem_erase.mp hK').1.symm
        obtain ⟨hwc, hw_mk⟩ := (hmem_Vcomp K' w).mp (Finset.mem_filter.mp hwK').1
        have hodd : Odd (G.dist c w) := (Finset.mem_filter.mp hwK').2
        have hdt := dist_through_cut hconn u.2 hwc (by
          change Gc.connectedComponentMk u ≠ Gc.connectedComponentMk ⟨w, hwc⟩
          rw [huK, hw_mk]; exact hne)
        have hdu : G.dist u.1 c = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hcu.symm
        rw [hdt, hdu]
        obtain ⟨j, hj⟩ := hodd
        exact ⟨j + 1, by omega⟩
    have hu_not : u.1 ∉ (Finset.univ.erase K).biUnion O := by
      intro h
      obtain ⟨K', hK', huK'⟩ := Finset.mem_biUnion.mp h
      obtain ⟨huc, hmk⟩ := (hmem_Vcomp K' u.1).mp (Finset.mem_filter.mp huK').1
      have hu_eq : (⟨u.1, huc⟩ : Vc) = u := Subtype.ext rfl
      rw [hu_eq, huK] at hmk
      exact (Finset.mem_erase.mp hK').1 hmk.symm
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hu_not, Finset.card_biUnion hdisjO] at hcard
    have hHu : (Finset.univ.filter (fun w => Even (G.dist u.1 w))).card ≤ 1 + σ := hH u.1
    omega
  have hO_ge_two : ∀ K : Comp, 2 ≤ (O K).card := by
    intro K
    have hsplit := Finset.add_sum_erase Finset.univ (fun K' : Comp => (O K').card) (Finset.mem_univ K)
    have := hO_other_le K
    omega
  have hVcomp_ge_sigma : ∀ K : Comp, σ ≤ (Vcomp K).card := by
    intro K
    have hcard2 : 2 ≤ (Vcomp K).card :=
      (hO_ge_two K).trans (Finset.card_le_card (Finset.filter_subset _ _))
    obtain ⟨v₁, hv₁, v₂, hv₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Vcomp K).card)
    obtain ⟨v, hvK, hdegv⟩ : ∃ v ∈ Vcomp K, σ ≤ G.degree v := by
      rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.degree_pair (G := G) v₁ v₂ hne with h | h
      · exact ⟨v₁, hv₁, h⟩
      · exact ⟨v₂, hv₂, h⟩
    have hsub : G.neighborFinset v ⊆ insert c ((Vcomp K).erase v) := by
      intro w hw
      have hadj : G.Adj v w := (mem_neighborFinset _ _ _).mp hw
      by_cases hwc : w = c
      · exact hwc ▸ Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        refine Finset.mem_erase.mpr ⟨hadj.ne.symm, (hmem_Vcomp K w).mpr ⟨hwc, ?_⟩⟩
        obtain ⟨hvc, hvmk⟩ := (hmem_Vcomp K v).mp hvK
        exact (ConnectedComponent.eq.mpr (Adj.reachable (show Gc.Adj ⟨w, hwc⟩ ⟨v, hvc⟩ from hadj.symm))).trans hvmk
    have hc := Finset.card_le_card hsub
    have hc_not : c ∉ (Vcomp K).erase v := fun h =>
      ((hmem_Vcomp K c).mp (Finset.mem_erase.mp h).2).1 rfl
    rw [card_neighborFinset_eq_degree, Finset.card_insert_of_notMem hc_not,
      Finset.card_erase_of_mem hvK] at hc
    omega
  have hcomp_eq_two : Fintype.card Comp = 2 := by
    by_contra hne2
    have hr3 : 3 ≤ Fintype.card Comp := by omega
    have hsum_all : (Fintype.card Comp - 1) * (∑ K : Comp, (O K).card) ≤ Fintype.card Comp * σ := by
      have h1 : ∑ K : Comp, ∑ K' ∈ Finset.univ.erase K, (O K').card ≤ Fintype.card Comp * σ := by
        calc ∑ K : Comp, ∑ K' ∈ Finset.univ.erase K, (O K').card
            ≤ ∑ _K : Comp, σ := Finset.sum_le_sum (fun K _ => hO_other_le K)
          _ = Fintype.card Comp * σ := by simp
      have h2 : ∑ K : Comp, ∑ K' ∈ Finset.univ.erase K, (O K').card =
          (Fintype.card Comp - 1) * ∑ K : Comp, (O K).card := by
        have hstep : ∀ K : Comp, ∑ K' ∈ Finset.univ.erase K, (O K').card =
            (∑ K' : Comp, (O K').card) - (O K).card := by
          intro K
          have := Finset.add_sum_erase Finset.univ (fun K' : Comp => (O K').card) (Finset.mem_univ K)
          omega
        simp only [hstep]
        have hle_each : ∀ K ∈ (Finset.univ : Finset Comp), (O K).card ≤ ∑ K' : Comp, (O K').card :=
          fun K hK => Finset.single_le_sum (f := fun K' : Comp => (O K').card) (fun _ _ => Nat.zero_le _) hK
        have hadd : (∑ K : Comp, ((∑ K' : Comp, (O K').card) - (O K).card)) +
            (∑ K : Comp, (O K).card) = Fintype.card Comp * (∑ K' : Comp, (O K').card) := by
          rw [← Finset.sum_add_distrib]
          calc ∑ K : Comp, ((∑ K' : Comp, (O K').card) - (O K).card + (O K).card)
              = ∑ _K : Comp, (∑ K' : Comp, (O K').card) :=
                Finset.sum_congr rfl (fun K hK => Nat.sub_add_cancel (hle_each K hK))
            _ = Fintype.card Comp * (∑ K' : Comp, (O K').card) := by simp
        have hmul : (Fintype.card Comp - 1) * (∑ K : Comp, (O K).card) + (∑ K : Comp, (O K).card) =
            Fintype.card Comp * (∑ K : Comp, (O K).card) := by
          cases h : Fintype.card Comp with
          | zero => omega
          | succ r => simp [Nat.succ_mul]
        omega
      omega
    have hsum_V_ge : Fintype.card Comp * σ ≤ ∑ K : Comp, (Vcomp K).card := by
      calc Fintype.card Comp * σ = ∑ _K : Comp, σ := by simp
        _ ≤ ∑ K : Comp, (Vcomp K).card := Finset.sum_le_sum (fun K _ => hVcomp_ge_sigma K)
    have hsum_O_ge' : (Fintype.card Comp - 1) * σ ≤ ∑ K : Comp, (O K).card := by
      have htot : (∑ K : Comp, (O K).card) + (∑ K : Comp, (E K).card) = ∑ K : Comp, (Vcomp K).card := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun K _ => hOE_card K)
      have hmul : (Fintype.card Comp - 1) * σ + σ = Fintype.card Comp * σ := by
        cases h : Fintype.card Comp with
        | zero => omega
        | succ r => simp [Nat.succ_mul]
      omega
    have hsq : (Fintype.card Comp - 1) * ((Fintype.card Comp - 1) * σ) ≤ Fintype.card Comp * σ :=
      (Nat.mul_le_mul_left _ hsum_O_ge').trans hsum_all
    by_cases hσ0 : σ = 0
    · obtain ⟨K₁, -, K₂, -, hne⟩ := Finset.one_lt_card.mp (by rw [Finset.card_univ]; omega : 1 < (Finset.univ : Finset Comp).card)
      have hle := hO_other_le K₁
      have hmem : K₂ ∈ Finset.univ.erase K₁ := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
      have h1 := Finset.single_le_sum (f := fun K' : Comp => (O K').card) (fun _ _ => Nat.zero_le _) hmem
      have h2 := hO_ge_two K₂
      omega
    · have hgt : Fintype.card Comp < (Fintype.card Comp - 1) * (Fintype.card Comp - 1) := by
        obtain ⟨r, hr⟩ : ∃ r, Fintype.card Comp = r + 3 := ⟨Fintype.card Comp - 3, by omega⟩
        rw [hr, show r + 3 - 1 = r + 2 by omega]
        nlinarith
      have : Fintype.card Comp * σ < (Fintype.card Comp - 1) * ((Fintype.card Comp - 1) * σ) := by
        rw [← mul_assoc]
        exact Nat.mul_lt_mul_of_pos_right hgt (by omega)
      omega
  obtain ⟨K₁, -, K₂, -, hKne⟩ :=
    Finset.one_lt_card.mp (by rw [Finset.card_univ, hcomp_eq_two]; decide : 1 < (Finset.univ : Finset Comp).card)
  have hcomp_univ : (Finset.univ : Finset Comp) = {K₁, K₂} := by
    refine (Finset.eq_univ_of_card ({K₁, K₂} : Finset Comp) (by rw [Finset.card_pair hKne, hcomp_eq_two])).symm
  have hO_pair : ∀ K K' : Comp, K ≠ K' → (O K').card ≤ σ := by
    intro K K' hne
    have hle := hO_other_le K
    have hmem : K' ∈ Finset.univ.erase K := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
    exact (Finset.single_le_sum (f := fun X : Comp => (O X).card) (fun _ _ => Nat.zero_le _) hmem).trans hle
  have hO1_le : (O K₁).card ≤ σ := hO_pair K₂ K₁ hKne.symm
  have hO2_le : (O K₂).card ≤ σ := hO_pair K₁ K₂ hKne
  have hE12_le : (E K₁).card + (E K₂).card ≤ σ := by
    have h1 := hsum_E
    rw [hcomp_univ, Finset.sum_pair hKne] at h1
    exact h1
  have hO12_ge : σ + 2 ≤ (O K₁).card + (O K₂).card := by
    have h1 := hsum_O_ge
    rw [hcomp_univ, Finset.sum_pair hKne] at h1
    exact h1
  have hVcomp_le_2sigma : ∀ K : Comp, (Vcomp K).card ≤ 2 * σ := by
    intro K
    have : K ∈ ({K₁, K₂} : Finset Comp) := hcomp_univ ▸ Finset.mem_univ K
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h <;> { rw [h]; have := hOE_card K₁; have := hOE_card K₂; omega }
  -- Pick the unique vertex x₀ of possibly minimum degree
  haveI : Nonempty V := hconn.nonempty
  obtain ⟨x₀, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun v : V => G.degree v)
    Finset.univ_nonempty
  have hx0 : ∀ v : V, v ≠ x₀ → σ ≤ G.degree v := by
    intro v hv
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.degree_pair (G := G) x₀ v (Ne.symm hv) with h | h
    · exact h.trans (hmin v (Finset.mem_univ v))
    · exact h
  -- For each component K (with partner K' ≠ K), prove there is a Hamiltonian path in G[Vcomp K] ending at a neighbor of c!
  have hcomp_path : ∀ K K' : Comp, K ≠ K' →
      ∃ l : List V, l.Nodup ∧ l.length = (Vcomp K).card ∧ l.IsChain G.Adj ∧
        (∀ v ∈ l, v ∈ Vcomp K) ∧ ∃ t ∈ Vcomp K, G.Adj c t ∧ l.getLast? = some t := by
    intro K K' hne
    have hpair_univ : (Finset.univ : Finset Comp) = {K, K'} :=
      (Finset.eq_univ_of_card ({K, K'} : Finset Comp) (by rw [Finset.card_pair hne, hcomp_eq_two])).symm
    have hOK_le : (O K).card ≤ σ := hO_pair K' K hne.symm
    have hOK'_ge : 2 ≤ (O K').card := hO_ge_two K'
    have hOsum : σ + 2 ≤ (O K).card + (O K').card := by
      have := hsum_O_ge; rw [hpair_univ, Finset.sum_pair hne] at this; exact this
    -- Step A: c has at least 2 neighbors in Vcomp K
    let T_V := (Vcomp K).filter (G.Adj c)
    have hTV_ge2 : 2 ≤ T_V.card := by
      obtain ⟨u, huK, hcu⟩ := exists_adj_in_comp hconn K
      by_contra hlt
      have huniq : ∀ v : V, (hv : v ≠ c) →
          Gc.connectedComponentMk ⟨v, hv⟩ = Gc.connectedComponentMk u → G.Adj c v → v = u.1 := by
        intro v hv hmk hcv
        have hvT : v ∈ T_V := Finset.mem_filter.mpr ⟨(hmem_Vcomp K v).mpr ⟨hv, hmk.trans huK⟩, hcv⟩
        have huT : u.1 ∈ T_V := Finset.mem_filter.mpr ⟨(hmem_Vcomp K u.1).mpr ⟨u.2, huK⟩, hcu⟩
        exact Finset.card_le_one.mp (by omega) v hvT u.1 huT
      have hsub : O K ∪ O K' ⊆ Finset.univ.filter (fun w => Even (G.dist u.1 w)) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases Finset.mem_union.mp hw with hw1 | hw2
        · obtain ⟨hwc, hwmk⟩ := (hmem_Vcomp K w).mp (Finset.mem_filter.mp hw1).1
          have hodd := (Finset.mem_filter.mp hw1).2
          have hdeq := dist_eq_succ_of_unique_nbr hconn u.2 hcu huniq hwc (hwmk.trans huK.symm)
          obtain ⟨j, hj⟩ := hodd
          exact ⟨j, by omega⟩
        · obtain ⟨hwc, hwmk⟩ := (hmem_Vcomp K' w).mp (Finset.mem_filter.mp hw2).1
          have hodd := (Finset.mem_filter.mp hw2).2
          have hdt := dist_through_cut hconn u.2 hwc (by
            change Gc.connectedComponentMk u ≠ Gc.connectedComponentMk ⟨w, hwc⟩
            rw [huK, hwmk]; exact hne)
          have hdu : G.dist u.1 c = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hcu.symm
          rw [hdt, hdu]
          obtain ⟨j, hj⟩ := hodd
          exact ⟨j + 1, by omega⟩
      have hdisjO : Disjoint (O K) (O K') :=
        (hdisj_comp K K' hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisjO] at hc
      have hHu : (Finset.univ.filter (fun w => Even (G.dist u.1 w))).card ≤ 1 + σ := hH u.1
      omega
    -- Step B: Diameter-2 in G for any v, w ∈ Vcomp K \ {x₀}
    have hdiam2 : ∀ v ∈ Vcomp K, v ≠ x₀ → ∀ w ∈ Vcomp K, w ≠ x₀ → G.dist v w ≤ 2 := by
      intro v hvK hvx w hwK hwx
      by_cases hvc : G.Adj v c
      · by_cases hwc : G.Adj w c
        · have h1 := hconn.dist_triangle (u := v) (v := c) (w := w)
          have h2 : G.dist v c = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hvc
          have h3 : G.dist c w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwc.symm
          omega
        · by_contra hgt
          let A := insert v ((G.neighborFinset v).erase c)
          let B := insert w (G.neighborFinset w)
          have hAsub : A ⊆ Vcomp K := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz'
            · exact hvK
            · obtain ⟨hzc, hzv⟩ := Finset.mem_erase.mp hz'
              obtain ⟨hvc', hvmk⟩ := (hmem_Vcomp K v).mp hvK
              exact (hmem_Vcomp K z).mpr ⟨hzc,
                (ConnectedComponent.eq.mpr (Adj.reachable (show Gc.Adj ⟨z, hzc⟩ ⟨v, hvc'⟩ from
                  ((mem_neighborFinset _ _ _).mp hzv).symm))).trans hvmk⟩
          have hBsub : B ⊆ Vcomp K := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz'
            · exact hwK
            · have hzw : G.Adj w z := (mem_neighborFinset _ _ _).mp hz'
              have hzc : z ≠ c := fun h => hwc (h ▸ hzw)
              obtain ⟨hwc', hwmk⟩ := (hmem_Vcomp K w).mp hwK
              exact (hmem_Vcomp K z).mpr ⟨hzc,
                (ConnectedComponent.eq.mpr (Adj.reachable (show Gc.Adj ⟨z, hzc⟩ ⟨w, hwc'⟩ from
                  hzw.symm))).trans hwmk⟩
          have hdisjAB : Disjoint A B := by
            refine Finset.disjoint_left.mpr (fun z hzA hzB => ?_)
            have hdvz : G.dist v z ≤ 1 := by
              rcases Finset.mem_insert.mp hzA with rfl | hz'
              · simp
              · exact (SimpleGraph.dist_eq_one_iff_adj.mpr ((mem_neighborFinset _ _ _).mp (Finset.mem_erase.mp hz').2)).le
            have hdwz : G.dist z w ≤ 1 := by
              rcases Finset.mem_insert.mp hzB with rfl | hz'
              · simp
              · exact (SimpleGraph.dist_eq_one_iff_adj.mpr ((mem_neighborFinset _ _ _).mp hz').symm).le
            have := hconn.dist_triangle (u := v) (v := z) (w := w)
            omega
          have hAcard : σ ≤ A.card := by
            have hv_not : v ∉ (G.neighborFinset v).erase c := fun h =>
              G.loopless.irrefl v ((mem_neighborFinset _ _ _).mp (Finset.mem_erase.mp h).2)
            rw [Finset.card_insert_of_notMem hv_not]
            have h1 := Finset.pred_card_le_card_erase (s := G.neighborFinset v) (a := c)
            rw [card_neighborFinset_eq_degree] at h1
            have := hx0 v hvx
            omega
          have hBcard : σ + 1 ≤ B.card := by
            have hw_not : w ∉ G.neighborFinset w := fun h =>
              G.loopless.irrefl w ((mem_neighborFinset _ _ _).mp h)
            rw [Finset.card_insert_of_notMem hw_not, card_neighborFinset_eq_degree]
            have := hx0 w hwx
            omega
          have htot := Finset.card_le_card (Finset.union_subset hAsub hBsub)
          rw [Finset.card_union_of_disjoint hdisjAB] at htot
          have := hVcomp_le_2sigma K
          omega
      · by_contra hgt
        let A := insert v (G.neighborFinset v)
        let B := insert w ((G.neighborFinset w).erase c)
        have hAsub : A ⊆ Vcomp K := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact hvK
          · have hzv : G.Adj v z := (mem_neighborFinset _ _ _).mp hz'
            have hzc : z ≠ c := fun h => hvc (h ▸ hzv)
            obtain ⟨hvc', hvmk⟩ := (hmem_Vcomp K v).mp hvK
            exact (hmem_Vcomp K z).mpr ⟨hzc,
              (ConnectedComponent.eq.mpr (Adj.reachable (show Gc.Adj ⟨z, hzc⟩ ⟨v, hvc'⟩ from
                hzv.symm))).trans hvmk⟩
        have hBsub : B ⊆ Vcomp K := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact hwK
          · obtain ⟨hzc, hzw⟩ := Finset.mem_erase.mp hz'
            obtain ⟨hwc', hwmk⟩ := (hmem_Vcomp K w).mp hwK
            exact (hmem_Vcomp K z).mpr ⟨hzc,
              (ConnectedComponent.eq.mpr (Adj.reachable (show Gc.Adj ⟨z, hzc⟩ ⟨w, hwc'⟩ from
                ((mem_neighborFinset _ _ _).mp hzw).symm))).trans hwmk⟩
        have hdisjAB : Disjoint A B := by
          refine Finset.disjoint_left.mpr (fun z hzA hzB => ?_)
          have hdvz : G.dist v z ≤ 1 := by
            rcases Finset.mem_insert.mp hzA with rfl | hz'
            · simp
            · exact (SimpleGraph.dist_eq_one_iff_adj.mpr ((mem_neighborFinset _ _ _).mp hz')).le
          have hdwz : G.dist z w ≤ 1 := by
            rcases Finset.mem_insert.mp hzB with rfl | hz'
            · simp
            · exact (SimpleGraph.dist_eq_one_iff_adj.mpr ((mem_neighborFinset _ _ _).mp (Finset.mem_erase.mp hz').2).symm).le
          have := hconn.dist_triangle (u := v) (v := z) (w := w)
          omega
        have hAcard : σ + 1 ≤ A.card := by
          have hv_not : v ∉ G.neighborFinset v := fun h =>
            G.loopless.irrefl v ((mem_neighborFinset _ _ _).mp h)
          rw [Finset.card_insert_of_notMem hv_not, card_neighborFinset_eq_degree]
          have := hx0 v hvx
          omega
        have hBcard : σ ≤ B.card := by
          have hw_not : w ∉ (G.neighborFinset w).erase c := fun h =>
            G.loopless.irrefl w ((mem_neighborFinset _ _ _).mp (Finset.mem_erase.mp h).2)
          rw [Finset.card_insert_of_notMem hw_not]
          have h1 := Finset.pred_card_le_card_erase (s := G.neighborFinset w) (a := c)
          rw [card_neighborFinset_eq_degree] at h1
          have := hx0 w hwx
          omega
        have htot := Finset.card_le_card (Finset.union_subset hAsub hBsub)
        rw [Finset.card_union_of_disjoint hdisjAB] at htot
        have := hVcomp_le_2sigma K
        omega
    -- Step C: Induced graph H on W = {v : V // v ∈ Vcomp K}
    let W := {v : V // v ∈ Vcomp K}
    let H : SimpleGraph W := G.induce {v : V | v ∈ Vcomp K}
    have hWcard : Fintype.card W = (Vcomp K).card := Fintype.card_coe (Vcomp K)
    have hWge2 : 2 ≤ Fintype.card W := by
      rw [hWcard]
      exact (hO_ge_two K).trans (Finset.card_le_card (Finset.filter_subset _ _))
    have hHconn : H.Connected := by
      haveI hWne : Nonempty W := Fintype.card_pos_iff.mp (by omega)
      refine ⟨fun a b => ?_⟩
      obtain ⟨hac, hamk⟩ := (hmem_Vcomp K a.1).mp a.2
      obtain ⟨hbc, hbmk⟩ := (hmem_Vcomp K b.1).mp b.2
      have hreach : Gc.Reachable ⟨a.1, hac⟩ ⟨b.1, hbc⟩ :=
        ConnectedComponent.eq.mp (hamk.trans hbmk.symm)
      obtain ⟨p⟩ := hreach
      have hp_mem : ∀ z ∈ (p.map (Embedding.induce {x : V | x ≠ c}).toHom).support, z ∈ Vcomp K := by
        intro z hz
        rw [Walk.support_map] at hz
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
        refine (hmem_Vcomp K u.1).mpr ⟨u.2, ?_⟩
        have hru : Gc.Reachable ⟨a.1, hac⟩ u := ⟨p.takeUntil u hu⟩
        exact (ConnectedComponent.eq.mpr hru).symm.trans hamk
      exact walk_induce_of_notMem (S := {v : V | v ∈ Vcomp K})
        (p.map (Embedding.induce {x : V | x ≠ c}).toHom) hp_mem
    let TW : Finset W := Finset.univ.filter (fun v : W => G.Adj c v.1)
    have hTW_card : TW.card = T_V.card := by
      refine Finset.card_bij (fun (v : W) _ => v.1) ?_ ?_ ?_
      · intro v hv
        exact Finset.mem_filter.mpr ⟨v.2, (Finset.mem_filter.mp hv).2⟩
      · intro v₁ _ v₂ _ h; exact Subtype.ext h
      · intro v hv
        obtain ⟨hvK, hcv⟩ := Finset.mem_filter.mp hv
        exact ⟨⟨v, hvK⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩, rfl⟩
    -- Degree in H vs G
    have hdegH : ∀ v : W,
        (H.degree v = ((G.neighborFinset v.1).erase c).card) ∧
        (¬ G.Adj c v.1 → H.degree v = G.degree v.1) ∧
        (G.degree v.1 ≤ H.degree v + 1) := by
      intro v
      have hbij : (H.neighborFinset v).card = ((G.neighborFinset v.1).erase c).card := by
        refine Finset.card_bij (fun (u : W) _ => u.1) ?_ ?_ ?_
        · intro u hu
          have hadj : G.Adj v.1 u.1 := (H.mem_neighborFinset v u).mp hu
          obtain ⟨huc, -⟩ := (hmem_Vcomp K u.1).mp u.2
          exact Finset.mem_erase.mpr ⟨huc, (G.mem_neighborFinset v.1 u.1).mpr hadj⟩
        · intro u₁ _ u₂ _ h; exact Subtype.ext h
        · intro u hu
          obtain ⟨huc, huN⟩ := Finset.mem_erase.mp hu
          have hadj : G.Adj v.1 u := (mem_neighborFinset _ _ _).mp huN
          obtain ⟨hvc, hvmk⟩ := (hmem_Vcomp K v.1).mp v.2
          have huK : u ∈ Vcomp K := (hmem_Vcomp K u).mpr ⟨huc,
            (ConnectedComponent.eq.mpr (Adj.reachable (show Gc.Adj ⟨u, huc⟩ ⟨v.1, hvc⟩ from
              hadj.symm))).trans hvmk⟩
          exact ⟨⟨u, huK⟩, (mem_neighborFinset _ _ _).mpr hadj, rfl⟩
      rw [← card_neighborFinset_eq_degree, hbij]
      refine ⟨rfl, ?_, ?_⟩
      · intro hna
        have hnot : c ∉ G.neighborFinset v.1 := fun h => hna ((mem_neighborFinset _ _ _).mp h).symm
        rw [Finset.erase_eq_of_notMem hnot, card_neighborFinset_eq_degree]
      · have h1 := Finset.pred_card_le_card_erase (s := G.neighborFinset v.1) (a := c)
        rw [card_neighborFinset_eq_degree] at h1
        omega
    -- Key degree bound for every v ∈ W with v.1 ≠ x₀
    have hdeg_bound : ∀ v : W, v.1 ≠ x₀ →
        ((x₀ ∉ Vcomp K ∨ G.dist x₀ v.1 ≤ 2) → Fintype.card W ≤ 2 * H.degree v) ∧
        Fintype.card W - 1 ≤ 2 * H.degree v := by
      intro v hvx
      -- Define S1: either all of Vcomp K (if x0 ∉ Vcomp K or G.dist x0 v <= 2) or (Vcomp K).erase x0
      have hcore : ∀ (S1 : Finset V), S1 ⊆ Vcomp K →
          (∀ y ∈ S1, G.dist v.1 y ≤ 2) →
          ((G.neighborFinset v.1).erase c ⊆ S1) →
          S1.card ≤ 2 * H.degree v := by
        intro S1 hS1sub hS1d hNsub
        let E_in := S1 \ (G.neighborFinset v.1).erase c
        have hE_in_card : E_in.card = S1.card - H.degree v := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hNsub, (hdegH v).1]
        have hE_in_even : ∀ y ∈ E_in, Even (G.dist v.1 y) := by
          intro y hy
          obtain ⟨hyS1, hyN⟩ := Finset.mem_sdiff.mp hy
          have hd2 := hS1d y hyS1
          have hna : ¬ G.Adj v.1 y := by
            intro hadj
            obtain ⟨hyc, -⟩ := (hmem_Vcomp K y).mp (hS1sub hyS1)
            exact hyN (Finset.mem_erase.mpr ⟨hyc, (mem_neighborFinset _ _ _).mpr hadj⟩)
          have hne1 : G.dist v.1 y ≠ 1 := fun h => hna (SimpleGraph.dist_eq_one_iff_adj.mp h)
          have hcases : G.dist v.1 y = 0 ∨ G.dist v.1 y = 2 := by omega
          rcases hcases with h0 | h2
          · rw [h0]; exact ⟨0, rfl⟩
          · rw [h2]; exact ⟨1, rfl⟩
        have hdegv : σ ≤ G.degree v.1 := hx0 v.1 hvx
        rcases Nat.even_or_odd (G.dist c v.1) with hev | hodd
        · have hna_c : ¬ G.Adj c v.1 := by
            intro h
            have h1 : G.dist c v.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
            rw [h1] at hev
            exact Nat.not_even_one hev
          have hdv_eq : H.degree v = G.degree v.1 := (hdegH v).2.1 hna_c
          have hsub : insert c E_in ⊆ Finset.univ.filter (fun w => Even (G.dist v.1 w)) := by
            intro w hw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rcases Finset.mem_insert.mp hw with rfl | hw'
            · rw [SimpleGraph.dist_comm]; exact hev
            · exact hE_in_even w hw'
          have hc_not : c ∉ E_in := fun h =>
            ((hmem_Vcomp K c).mp (hS1sub (Finset.mem_sdiff.mp h).1)).1 rfl
          have hc := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hc_not] at hc
          have hHv : (Finset.univ.filter (fun w => Even (G.dist v.1 w))).card ≤ 1 + σ := hH v.1
          have hNle : H.degree v ≤ S1.card := by
            rw [(hdegH v).1]; exact Finset.card_le_card hNsub
          omega
        · have hsub : E_in ∪ O K' ⊆ Finset.univ.filter (fun w => Even (G.dist v.1 w)) := by
            intro w hw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rcases Finset.mem_union.mp hw with hw1 | hw2
            · exact hE_in_even w hw1
            · obtain ⟨hvc, hvmk⟩ := (hmem_Vcomp K v.1).mp v.2
              obtain ⟨hwc, hwmk⟩ := (hmem_Vcomp K' w).mp (Finset.mem_filter.mp hw2).1
              have hdt := dist_through_cut hconn hvc hwc (by rw [hvmk, hwmk]; exact hne)
              rw [hdt, SimpleGraph.dist_comm (u := v.1) (v := c)]
              obtain ⟨a, ha⟩ := hodd
              obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hw2).2
              exact ⟨a + b + 1, by omega⟩
          have hdisj : Disjoint E_in (O K') :=
            (hdisj_comp K K' hne).mono (Finset.sdiff_subset.trans hS1sub) (Finset.filter_subset _ _)
          have hc := Finset.card_le_card hsub
          rw [Finset.card_union_of_disjoint hdisj] at hc
          have hHv : (Finset.univ.filter (fun w => Even (G.dist v.1 w))).card ≤ 1 + σ := hH v.1
          have hdv1 := (hdegH v).2.2
          have hNle : H.degree v ≤ S1.card := by
            rw [(hdegH v).1]; exact Finset.card_le_card hNsub
          omega
      have hN_in_K : (G.neighborFinset v.1).erase c ⊆ Vcomp K := by
        intro z hz
        obtain ⟨hzc, hzv⟩ := Finset.mem_erase.mp hz
        obtain ⟨hvc, hvmk⟩ := (hmem_Vcomp K v.1).mp v.2
        exact (hmem_Vcomp K z).mpr ⟨hzc,
          (ConnectedComponent.eq.mpr (Adj.reachable (show Gc.Adj ⟨z, hzc⟩ ⟨v.1, hvc⟩ from
            ((mem_neighborFinset _ _ _).mp hzv).symm))).trans hvmk⟩
      constructor
      · intro hcond
        rw [hWcard]
        apply hcore (Vcomp K) Finset.Subset.rfl _ hN_in_K
        intro y hy
        by_cases hyx : y = x₀
        · subst hyx
          rcases hcond with hnot | hd2
          · exact absurd hy hnot
          · rwa [SimpleGraph.dist_comm]
        · exact hdiam2 v.1 v.2 hvx y hy hyx
      · by_cases hdist : x₀ ∉ Vcomp K ∨ G.dist x₀ v.1 ≤ 2
        · have hfull : Fintype.card W ≤ 2 * H.degree v := by
            rw [hWcard]
            apply hcore (Vcomp K) Finset.Subset.rfl _ hN_in_K
            intro y hy
            by_cases hyx : y = x₀
            · subst hyx
              rcases hdist with hnot | hd2
              · exact absurd hy hnot
              · rwa [SimpleGraph.dist_comm]
            · exact hdiam2 v.1 v.2 hvx y hy hyx
          omega
        · push Not at hdist
          obtain ⟨hx0K, hgt2⟩ := hdist
          have hN_er : (G.neighborFinset v.1).erase c ⊆ (Vcomp K).erase x₀ := by
            intro z hz
            refine Finset.mem_erase.mpr ⟨?_, hN_in_K hz⟩
            intro hzx
            rw [hzx] at hz
            have hadj : G.Adj v.1 x₀ := (mem_neighborFinset _ _ _).mp (Finset.mem_erase.mp hz).2
            have : G.dist x₀ v.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
            omega
          have hc := hcore ((Vcomp K).erase x₀) (Finset.erase_subset _ _) (fun y hy =>
            hdiam2 v.1 v.2 hvx y (Finset.mem_erase.mp hy).2 (Finset.mem_erase.mp hy).1) hN_er
          rw [Finset.card_erase_of_mem hx0K, ← hWcard] at hc
          exact hc
    -- Pick distinguished vertex xW : W (either ⟨x₀, _⟩ if x₀ ∈ Vcomp K, or arbitrary W!)
    obtain ⟨xW, hxW⟩ : ∃ xW : W, ∀ v : W, v ≠ xW →
        (H.dist xW v ≤ 2 → Fintype.card W ≤ 2 * H.degree v) ∧
        Fintype.card W - 1 ≤ 2 * H.degree v := by
      by_cases hx0K : x₀ ∈ Vcomp K
      · refine ⟨⟨x₀, hx0K⟩, fun v hv => ?_⟩
        have hvx : v.1 ≠ x₀ := fun h => hv (Subtype.ext h)
        refine ⟨fun hd => (hdeg_bound v hvx).1 (Or.inr ?_), (hdeg_bound v hvx).2⟩
        exact (dist_induce_ge ⟨x₀, hx0K⟩ v (hHconn ⟨x₀, hx0K⟩ v)).trans hd
      · have hWne : Nonempty W := Fintype.card_pos_iff.mp (by omega)
        refine ⟨Classical.arbitrary W, fun v _ => ?_⟩
        have hvx : v.1 ≠ x₀ := fun h => hx0K (h ▸ v.2)
        exact ⟨fun _ => (hdeg_bound v hvx).1 (Or.inl hx0K), (hdeg_bound v hvx).2⟩
    obtain ⟨lW, hlW_nd, hlW_len, hlW_ch, tW, htW, hlW_last⟩ :=
      ham_path_of_component H hWge2 hHconn TW (by omega) xW (by convert hxW)
    refine ⟨lW.map Subtype.val, hlW_nd.map Subtype.val_injective, by rw [List.length_map, hlW_len, hWcard],
      ?_, ?_, tW.1, tW.2, (Finset.mem_filter.mp htW).2, ?_⟩
    · rw [List.isChain_map]; exact hlW_ch
    · intro v hv
      obtain ⟨u, -, rfl⟩ := List.mem_map.mp hv
      exact u.2
    · rw [List.getLast?_map, hlW_last]; rfl
  -- Apply hcomp_path to K₁ and K₂, then concatenate at c!
  obtain ⟨l₁, hnd₁, hlen₁, hch₁, hmem₁, t₁, ht₁K, hct₁, hlast₁⟩ := hcomp_path K₁ K₂ hKne
  obtain ⟨l₂, hnd₂, hlen₂, hch₂, hmem₂, t₂, ht₂K, hct₂, hlast₂⟩ := hcomp_path K₂ K₁ hKne.symm
  let L := l₁ ++ c :: l₂.reverse
  have hc_not₁ : c ∉ l₁ := fun h => ((hmem_Vcomp K₁ c).mp (hmem₁ c h)).1 rfl
  have hc_not₂ : c ∉ l₂ := fun h => ((hmem_Vcomp K₂ c).mp (hmem₂ c h)).1 rfl
  have hdisj₁₂ : ∀ a ∈ l₁, ∀ b ∈ l₂.reverse, a ≠ b := by
    intro a ha b hb hab
    subst hab
    exact Finset.disjoint_left.mp (hdisj_comp K₁ K₂ hKne) (hmem₁ a ha) (hmem₂ a (List.mem_reverse.mp hb))
  have hL_nd : L.Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd₁, List.nodup_cons.mpr ⟨by simpa using hc_not₂, List.nodup_reverse.mpr hnd₂⟩, ?_⟩
    intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact fun h => hc_not₁ (h ▸ ha)
    · exact hdisj₁₂ a ha b hb'
  have hL_len : L.length = Fintype.card V := by
    simp only [L, List.length_append, List.length_cons, List.length_reverse, hlen₁, hlen₂]
    have hsum2 : (Vcomp K₁).card + (Vcomp K₂).card = Fintype.card V - 1 := by
      rw [← hsum_Vcomp, hcomp_univ, Finset.sum_pair hKne]
    omega
  have hL_ch : L.IsChain G.Adj := by
    refine List.isChain_append.mpr ⟨hch₁, List.isChain_cons.mpr ⟨?_, ?_⟩, ?_⟩
    · intro y hy
      rw [List.head?_reverse, hlast₂, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hct₂
    · rw [List.isChain_reverse]
      exact hch₂.imp (fun _ _ e => e.symm)
    · intro a ha b hb
      rw [hlast₁, Option.mem_def, Option.some.injEq] at ha
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst ha hb
      exact hct₁.symm
  have hL_ne : L ≠ [] := by intro h0; rw [h0] at hL_len; simp at hL_len; omega
  exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.ham_of_list L hL_ne hL_nd hL_ch hL_len
