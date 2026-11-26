import FormalConjectures.ErdosProblems.«1009»

-- Problem: Erdős Problem 1009 — sauer
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1009.lean:67 (declaration Erdos1009.erdos_1009.variants.sauer)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof: vertices of Fin (2r+4) get class 0 (v < r), 1 (r ≤ v < 2r) or 2 (the last four).
-- Two distinct vertices are adjacent iff their classes differ or both have class 2
-- (complete tripartite r, r, 4 plus a K4). Edge count by the degree sum. Every triangle not
-- inside class 2 has exactly two (non-class-2, class-2) ordered vertex pairs, these pair sets
-- are disjoint for triangles sharing at most one vertex, and there are only 8r such pairs;
-- at most one triangle lies inside the 4 vertices of class 2.

namespace OMA.O5S

open Finset

def cls (r : ℕ) (n : ℕ) : ℕ := if n < r then 0 else if n < 2 * r then 1 else 2

lemma cls_le (r n : ℕ) : cls r n ≤ 2 := by
  unfold cls; split_ifs <;> omega

def G (r : ℕ) : SimpleGraph (Fin (2 * r + 4)) where
  Adj u v := u ≠ v ∧ (cls r u.val ≠ cls r v.val ∨ cls r u.val = 2)
  symm := ⟨fun u v h => by
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h2 | h2
    · exact Or.inl (Ne.symm h2)
    · by_cases hv : cls r v.val = 2
      · exact Or.inr hv
      · exact Or.inl (fun e => hv (e ▸ h2))⟩
  loopless := ⟨fun u h => h.1 rfl⟩

lemma adj_iff (r : ℕ) (u v : Fin (2 * r + 4)) :
    (G r).Adj u v ↔ u ≠ v ∧ (cls r u.val ≠ cls r v.val ∨ cls r u.val = 2) := by
  rfl

instance (r : ℕ) : DecidableRel (G r).Adj := fun u v =>
  decidable_of_iff _ (adj_iff r u v).symm

lemma cardF (m : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter (fun v : Fin m => P v.val)).card = ((range m).filter P).card := by
  apply Finset.card_bij (fun v _ => v.val)
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    simp only [mem_filter, mem_range]
    exact ⟨v.isLt, hv⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    simp only [mem_filter, mem_range] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

lemma card0 (r : ℕ) :
    (univ.filter (fun v : Fin (2 * r + 4) => cls r v.val = 0)).card = r := by
  refine (cardF (2 * r + 4) (fun n => cls r n = 0)).trans ?_
  rw [show (range (2 * r + 4)).filter (fun n => cls r n = 0) = range r from ?_]
  · simp
  · ext v
    rw [mem_filter]
    simp only [mem_range, mem_Ico]
    unfold cls
    split_ifs <;> simp <;> omega

lemma card2 (r : ℕ) :
    (univ.filter (fun v : Fin (2 * r + 4) => cls r v.val = 2)).card = 4 := by
  refine (cardF (2 * r + 4) (fun n => cls r n = 2)).trans ?_
  rw [show (range (2 * r + 4)).filter (fun n => cls r n = 2) = Ico (2 * r) (2 * r + 4) from ?_]
  · simp
  · ext v
    rw [mem_filter]
    simp only [mem_range, mem_Ico]
    simp only [mem_Ico, cls]
    split_ifs <;> simp <;> omega

lemma cardN2 (r : ℕ) :
    (univ.filter (fun v : Fin (2 * r + 4) => ¬ cls r v.val = 2)).card = 2 * r := by
  refine (cardF (2 * r + 4) (fun n => ¬ cls r n = 2)).trans ?_
  rw [show (range (2 * r + 4)).filter (fun n => ¬ cls r n = 2) = range (2 * r) from ?_]
  · simp
  · ext v
    rw [mem_filter]
    simp only [mem_range, mem_Ico]
    unfold cls
    split_ifs <;> simp <;> omega

lemma card1 (r : ℕ) :
    (univ.filter (fun v : Fin (2 * r + 4) => cls r v.val = 1)).card = r := by
  refine (cardF (2 * r + 4) (fun n => cls r n = 1)).trans ?_
  rw [show (range (2 * r + 4)).filter (fun n => cls r n = 1) = Ico r (2 * r) from ?_]
  · simp; omega
  · ext v
    rw [mem_filter]
    simp only [mem_range, mem_Ico]
    simp only [mem_Ico, cls]
    split_ifs <;> simp <;> omega

lemma deg (r : ℕ) (v : Fin (2 * r + 4)) :
    (G r).degree v = if cls r v.val = 2 then 2 * r + 3 else r + 4 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  split_ifs with h
  · rw [show univ.filter (fun w => (G r).Adj v w) = univ.erase v from ?_]
    · rw [card_erase_of_mem (mem_univ v), card_univ, Fintype.card_fin]
      omega
    · ext w
      simp only [mem_filter, mem_univ, true_and, mem_erase, and_true, adj_iff]
      constructor
      · rintro ⟨h1, _⟩; exact Ne.symm h1
      · intro h1; exact ⟨Ne.symm h1, Or.inr h⟩
  · have hc : cls r v.val = 0 ∨ cls r v.val = 1 := by
      have := cls_le r v.val; omega
    rcases hc with hc | hc
    · rw [show univ.filter (fun w => (G r).Adj v w) =
          univ.filter (fun w : Fin (2 * r + 4) => ¬ cls r w.val = 0) from ?_]
      · have := Finset.card_filter_add_card_filter_not (s := univ)
          (p := fun w : Fin (2 * r + 4) => cls r w.val = 0)
        rw [card0, card_univ, Fintype.card_fin] at this
        omega
      · ext w
        simp only [mem_filter, mem_univ, true_and, adj_iff, hc]
        constructor
        · rintro ⟨_, h2 | h2⟩
          · exact Ne.symm h2
          · omega
        · intro h2
          refine ⟨fun e => h2 (e ▸ hc), Or.inl (Ne.symm h2)⟩
    · rw [show univ.filter (fun w => (G r).Adj v w) =
          univ.filter (fun w : Fin (2 * r + 4) => ¬ cls r w.val = 1) from ?_]
      · have := Finset.card_filter_add_card_filter_not (s := univ)
          (p := fun w : Fin (2 * r + 4) => cls r w.val = 1)
        rw [card1, card_univ, Fintype.card_fin] at this
        omega
      · ext w
        simp only [mem_filter, mem_univ, true_and, adj_iff, hc]
        constructor
        · rintro ⟨_, h2 | h2⟩
          · exact Ne.symm h2
          · omega
        · intro h2
          refine ⟨fun e => h2 (e ▸ hc), Or.inl (Ne.symm h2)⟩

lemma edges (r : ℕ) : 2 * (G r).edgeFinset.card = 2 * (r * r + 8 * r + 6) := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp only [deg]
  rw [Finset.sum_ite]
  simp only [sum_const, smul_eq_mul, card2, cardN2]
  ring

lemma tri_bound (r : ℕ) (T : Finset (Finset (Fin (2 * r + 4))))
    (hT : ∀ t ∈ T, (G r).IsNClique 3 t)
    (hP : (T : Set (Finset (Fin (2 * r + 4)))).Pairwise (fun s t => (s ∩ t).card ≤ 1)) :
    T.card ≤ 4 * r + 1 := by
  set Z := univ.filter (fun v : Fin (2 * r + 4) => cls r v.val = 2) with hZ
  set W := univ.filter (fun v : Fin (2 * r + 4) => ¬ cls r v.val = 2) with hW
  let E : Finset (Fin (2 * r + 4)) → Finset (Fin (2 * r + 4) × Fin (2 * r + 4)) := fun t =>
    (t.filter (fun v => ¬ cls r v.val = 2)) ×ˢ (t.filter (fun v => cls r v.val = 2))
  set T1 := T.filter (fun t => t ⊆ Z) with hT1
  set T2 := T.filter (fun t => ¬ t ⊆ Z) with hT2
  have hsplit : T1.card + T2.card = T.card :=
    Finset.card_filter_add_card_filter_not _
  -- each triangle outside Z has exactly two crossing pairs
  have hA : ∀ t ∈ T2, 2 ≤ (E t).card := by
    intro t ht
    rw [hT2, mem_filter] at ht
    obtain ⟨htT, hnZ⟩ := ht
    have hc := hT t htT
    have hab : (t.filter (fun v => cls r v.val = 2)).card +
        (t.filter (fun v => ¬ cls r v.val = 2)).card = 3 := by
      rw [Finset.card_filter_add_card_filter_not]
      exact hc.card_eq
    have ha1 : 1 ≤ (t.filter (fun v => ¬ cls r v.val = 2)).card := by
      obtain ⟨v, hv, hvZ⟩ := Finset.not_subset.mp hnZ
      apply Finset.card_pos.mpr
      refine ⟨v, mem_filter.mpr ⟨hv, ?_⟩⟩
      intro h2
      exact hvZ (by rw [hZ, mem_filter]; exact ⟨mem_univ v, h2⟩)
    have hone : ∀ c : ℕ, c ≠ 2 → (t.filter (fun v => cls r v.val = c)).card ≤ 1 := by
      intro c hc2
      apply Finset.card_le_one.mpr
      intro x hx y hy
      by_contra hne
      rw [mem_filter] at hx hy
      have := hc.isClique (Finset.mem_coe.mpr hx.1) (Finset.mem_coe.mpr hy.1) hne
      rw [adj_iff] at this
      rcases this with ⟨_, h2 | h2⟩
      · exact h2 (hx.2.trans hy.2.symm)
      · omega
    have ha2 : (t.filter (fun v => ¬ cls r v.val = 2)).card ≤ 2 := by
      have hsub : t.filter (fun v => ¬ cls r v.val = 2) ⊆
          t.filter (fun v => cls r v.val = 0) ∪ t.filter (fun v => cls r v.val = 1) := by
        intro v hv
        rw [mem_filter] at hv
        rw [mem_union, mem_filter, mem_filter]
        have := cls_le r v.val
        rcases (by omega : cls r v.val = 0 ∨ cls r v.val = 1) with h | h
        · exact Or.inl ⟨hv.1, h⟩
        · exact Or.inr ⟨hv.1, h⟩
      have h1 := card_le_card hsub
      have h2 := card_union_le (t.filter (fun v => cls r v.val = 0))
        (t.filter (fun v => cls r v.val = 1))
      have h3 := hone 0 (by norm_num)
      have h4 := hone 1 (by norm_num)
      omega
    show 2 ≤ ((t.filter (fun v => ¬ cls r v.val = 2)) ×ˢ
      (t.filter (fun v => cls r v.val = 2))).card
    rw [card_product]
    rcases (by omega : ((t.filter (fun v => ¬ cls r v.val = 2)).card = 1 ∧
        (t.filter (fun v => cls r v.val = 2)).card = 2) ∨
        ((t.filter (fun v => ¬ cls r v.val = 2)).card = 2 ∧
        (t.filter (fun v => cls r v.val = 2)).card = 1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]
  -- crossing pair sets are disjoint
  have hB : ∀ t ∈ T2, ∀ t' ∈ T2, t ≠ t' → Disjoint (E t) (E t') := by
    intro t ht t' ht' hne
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [E, mem_product, mem_filter] at hp hp'
    have hne2 : p.1 ≠ p.2 := by
      intro e
      rw [e] at hp
      exact hp.1.2 hp.2.2
    have h2 : 1 < (t ∩ t').card := by
      rw [Finset.one_lt_card]
      exact ⟨p.1, mem_inter.mpr ⟨hp.1.1, hp'.1.1⟩, p.2, mem_inter.mpr ⟨hp.2.1, hp'.2.1⟩, hne2⟩
    have htT : t ∈ T := (mem_filter.mp ht).1
    have htT' : t' ∈ T := (mem_filter.mp ht').1
    have := hP (Finset.mem_coe.mpr htT) (Finset.mem_coe.mpr htT') hne
    simp only at this
    omega
  have hU : (T2.biUnion E).card = ∑ t ∈ T2, (E t).card := by
    apply Finset.card_biUnion
    intro x hx y hy hxy
    exact hB x hx y hy hxy
  have hsubWZ : T2.biUnion E ⊆ W ×ˢ Z := by
    intro p hp
    rw [mem_biUnion] at hp
    obtain ⟨t, _, hpt⟩ := hp
    simp only [E, mem_product, mem_filter] at hpt
    rw [mem_product, hW, hZ, mem_filter, mem_filter]
    exact ⟨⟨mem_univ _, hpt.1.2⟩, ⟨mem_univ _, hpt.2.2⟩⟩
  have hWZ : (W ×ˢ Z).card = 2 * r * 4 := by
    rw [card_product, hW, hZ, cardN2, card2]
  have hsum : T2.card * 2 ≤ ∑ t ∈ T2, (E t).card := by
    have := Finset.card_nsmul_le_sum T2 (fun t => (E t).card) 2 hA
    simpa [smul_eq_mul] using this
  have hT2b : T2.card * 2 ≤ 2 * r * 4 := by
    have := card_le_card hsubWZ
    omega
  -- at most one triangle inside Z
  have hT1b : T1.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro t ht t' ht'
    by_contra hne
    rw [hT1, mem_filter] at ht ht'
    have hu : (t ∪ t').card ≤ 4 := by
      have := card_le_card (union_subset ht.2 ht'.2)
      rw [hZ, card2] at this
      exact this
    have hi := hP (Finset.mem_coe.mpr ht.1) (Finset.mem_coe.mpr ht'.1) hne
    simp only at hi
    have h3 := (hT t ht.1).card_eq
    have h3' := (hT t' ht'.1).card_eq
    have := card_union_add_card_inter t t'
    omega
  omega

end OMA.O5S

theorem OMA.solution : type_of% @Erdos1009.erdos_1009.variants.sauer := by
  intro r _
  refine ⟨OMA.O5S.G r, ?_, ?_⟩
  · rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    have h := OMA.O5S.edges r
    have h4 : (2 * r + 4) ^ 2 / 4 = r * r + 4 * r + 4 := by
      rw [show (2 * r + 4) ^ 2 = (r * r + 4 * r + 4) * 4 by ring]
      exact Nat.mul_div_cancel _ (by norm_num)
    rw [h4]
    omega
  · intro T hT hP
    have := OMA.O5S.tri_bound r T hT hP
    omega
