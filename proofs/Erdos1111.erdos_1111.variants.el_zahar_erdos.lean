import FormalConjectures.ErdosProblems.«1111»

-- Problem: Erdős Problem 1111 — el zahar erdos
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1111.lean:87 (declaration Erdos1111.erdos_1111.variants.el_zahar_erdos)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open SimpleGraph

/-- A segment of a walk, as a walk. -/
lemma seg {V : Type*} {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ p.length) :
    ∃ q : G.Walk (p.getVert i) (p.getVert j), q.length = j - i := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact ⟨Walk.nil, by simp⟩
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · obtain ⟨q, hq⟩ := ih (by omega) (by omega)
      refine ⟨q.concat (p.adj_getVert_succ (by omega)), ?_⟩
      rw [Walk.length_concat, hq]; omega
    · obtain rfl : i = j + 1 := by omega
      exact ⟨Walk.nil, by simp⟩

/-- A segment of a walk, as a walk in an induced subgraph containing it. -/
lemma segInd {V : Type*} {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (S : Set V)
    (hS : ∀ n, p.getVert n ∈ S) (j : ℕ) (hj : j ≤ p.length) :
    ∃ q : (G.induce S).Walk ⟨p.getVert 0, hS 0⟩ ⟨p.getVert j, hS j⟩, q.length = j := by
  induction j with
  | zero => exact ⟨Walk.nil, by simp⟩
  | succ j ih =>
    obtain ⟨q, hq⟩ := ih (by omega)
    have hadj : (G.induce S).Adj ⟨p.getVert j, hS j⟩ ⟨p.getVert (j + 1), hS (j + 1)⟩ := by
      simpa using p.adj_getVert_succ (by omega : j < p.length)
    refine ⟨q.concat hadj, ?_⟩
    rw [Walk.length_concat, hq]

/-- The colour of position `i` on a closed walk of length `k`. -/
def g (k i : ℕ) : ℕ := if i + 3 < k then i % 2 else i + 5 - k

lemma g_lt (k i : ℕ) (hi : i < k) : g k i < 5 := by
  unfold g; split_ifs <;> omega

lemma g_eq {k i j : ℕ} (hij : i < j) (hj : j < k) (h : g k i = g k j) :
    j + 3 < k ∧ (j - i) % 2 = 0 := by
  unfold g at h; split_ifs at h <;> omega

end OMA

open SimpleGraph in
theorem OMA.three_three (V : Type*) [Finite V] (G : SimpleGraph V)
    (hG : 8 ≤ G.chromaticNumber) (hT : G.CliqueFree 3) :
    ∃ A B : Set V, Erdos1111.Anticomplete G A B ∧
      3 ≤ (G.induce A).chromaticNumber ∧ 3 ≤ (G.induce B).chromaticNumber := by
  classical
  -- G is not 2-colourable
  have h2 : ¬ G.Colorable 2 := by
    intro h
    have := hG.trans h.chromaticNumber_le
    exact absurd this (by decide)
  rw [two_colorable_iff_forall_loop_even] at h2
  push_neg at h2
  obtain ⟨u0, w0, hw0⟩ := h2
  rw [Nat.not_even_iff_odd] at hw0
  have hex : ∃ k, ∃ u, ∃ w : G.Walk u u, w.length = k ∧ Odd k := ⟨_, u0, w0, rfl, hw0⟩
  obtain ⟨x, p, hpk, hodd⟩ := Nat.find_spec hex
  have hmin : ∀ u (w : G.Walk u u), Odd w.length → Nat.find hex ≤ w.length :=
    fun u w hw => Nat.find_min' hex ⟨u, w, rfl, hw⟩
  generalize Nat.find hex = k at hpk hodd hmin
  have hk0 : 0 < k := hodd.pos
  have hck : ∀ n, k ≤ n → p.getVert n = p.getVert 0 := by
    intro n hn
    rw [Walk.getVert_of_length_le p (by omega), Walk.getVert_zero]
  set N : Set V := {v | ∃ i, i < k ∧ G.Adj v (p.getVert i)} with hN
  set A : Set V := {v | ∃ n, v = p.getVert n} with hA
  have hAN : A ⊆ N := by
    rintro v ⟨n, rfl⟩
    have key : ∀ n, n < k → p.getVert n ∈ N := by
      intro n hn
      have hadj := p.adj_getVert_succ (by omega : n < p.length)
      rcases Nat.lt_or_ge (n + 1) k with h | h
      · exact ⟨n + 1, h, hadj⟩
      · exact ⟨0, hk0, by rw [← hck (n + 1) h]; exact hadj⟩
    rcases Nat.lt_or_ge n k with h | h
    · exact key n h
    · rw [hck n h]; exact key 0 hk0
  refine ⟨A, Nᶜ, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact Set.disjoint_left.mpr fun v hv hv' => hv' (hAN hv)
  · rintro a ⟨n, rfl⟩ b hb hab
    apply hb
    rcases Nat.lt_or_ge n k with h | h
    · exact ⟨n, h, hab.symm⟩
    · exact ⟨0, hk0, by rw [← hck n h]; exact hab.symm⟩
  · obtain ⟨q, hq⟩ := OMA.segInd p A (fun n => ⟨n, rfl⟩) k (by omega)
    have hend : (⟨p.getVert k, ⟨k, rfl⟩⟩ : A) = ⟨p.getVert 0, ⟨0, rfl⟩⟩ :=
      Subtype.ext (hck k le_rfl)
    have := (q.copy rfl hend).three_le_chromaticNumber_of_odd_loop
      (by rw [Walk.length_copy, hq]; exact hodd)
    exact this
  · by_contra hcon
    have hB : (G.induce Nᶜ).Colorable 2 := by
      rw [← chromaticNumber_le_iff_colorable]
      exact Order.le_of_lt_add_one (not_le.mp hcon)
    obtain ⟨C2⟩ := hB
    -- key property of the colouring of N
    have hkey : ∀ i j u w, i < j → j < k → G.Adj u (p.getVert i) → G.Adj w (p.getVert j) →
        G.Adj u w → OMA.g k i ≠ OMA.g k j := by
      intro i j u w hij hj hu hw huw heq
      obtain ⟨h1, h2⟩ := OMA.g_eq hij hj heq
      obtain ⟨q, hq⟩ := OMA.seg p i j hij.le (by omega)
      have := hmin _ (Walk.cons hu.symm (Walk.cons huw (Walk.cons hw q.reverse))) (by
        simp only [Walk.length_cons, Walk.length_reverse, hq]
        rw [Nat.odd_iff]; omega)
      simp only [Walk.length_cons, Walk.length_reverse, hq] at this
      omega
    have hG7 : G.Colorable 7 := by
      rw [colorable_iff_exists_bdd_nat_coloring]
      refine ⟨Coloring.mk (fun v => if h : v ∈ N then OMA.g k (Classical.choose h)
        else 5 + (C2 ⟨v, h⟩ : ℕ)) ?_, ?_⟩
      · intro v w hvw
        by_cases hv : v ∈ N <;> by_cases hw : w ∈ N
        · simp only [dif_pos hv, dif_pos hw]
          obtain ⟨hi, hvi⟩ := Classical.choose_spec hv
          obtain ⟨hj, hwj⟩ := Classical.choose_spec hw
          rcases Nat.lt_trichotomy (Classical.choose hv) (Classical.choose hw) with h | h | h
          · exact hkey _ _ v w h hj hvi hwj hvw
          · intro _
            rw [← h] at hwj
            exact hT _ (is3Clique_triple_iff.mpr ⟨hvw, hvi, hwj⟩)
          · exact (hkey _ _ w v h hi hwj hvi hvw.symm).symm
        · simp only [dif_pos hv, dif_neg hw]
          have := OMA.g_lt k _ (Classical.choose_spec hv).1
          omega
        · simp only [dif_neg hv, dif_pos hw]
          have := OMA.g_lt k _ (Classical.choose_spec hw).1
          omega
        · simp only [dif_neg hv, dif_neg hw]
          have hadj : (G.induce Nᶜ).Adj ⟨v, hv⟩ ⟨w, hw⟩ := by simpa using hvw
          have := C2.valid hadj
          intro h
          apply this
          apply Fin.ext
          omega
      · intro v
        show (if h : v ∈ N then OMA.g k (Classical.choose h) else 5 + (C2 ⟨v, h⟩ : ℕ)) < 7
        split_ifs with h
        · have := OMA.g_lt k _ (Classical.choose_spec h).1
          omega
        · omega
    have := hG.trans hG7.chromaticNumber_le
    exact absurd this (by decide)

namespace OMA

open SimpleGraph

lemma lt_colorable {V : Type*} [Finite V] (H : SimpleGraph V) (n : ℕ)
    (h : H.chromaticNumber < (n : ℕ∞)) : H.Colorable (n - 1) := by
  have hne : H.chromaticNumber ≠ ⊤ := ne_top_of_lt h
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hm] at h
  have hmn : m < n := by exact_mod_cast h
  have : H.Colorable m := chromaticNumber_le_iff_colorable.mp (le_of_eq hm.symm)
  exact this.mono (by omega)

lemma transfer {V : Type*} (G : SimpleGraph V) (S : Set V) (A' : Set S) :
    ((G.induce S).induce A').chromaticNumber ≤
      (G.induce (Subtype.val '' A')).chromaticNumber := by
  let f : ((G.induce S).induce A') →g (G.induce (Subtype.val '' A')) :=
    { toFun := fun v => ⟨v.1.1, ⟨v.1, v.2, rfl⟩⟩
      map_rel' := by
        intro a b hab
        simpa using hab }
  exact chromaticNumber_mono_of_hom f

lemma nbr_cliqueFree {V : Type*} (G : SimpleGraph V) (t : ℕ) (x : V)
    (h : G.CliqueFree (t + 1)) : (G.induce (G.neighborSet x)).CliqueFree t := by
  classical
  intro s hs
  rw [isNClique_iff] at hs
  obtain ⟨hc, hcard⟩ := hs
  have h1 : G.IsNClique t (s.map (Function.Embedding.subtype _)) := by
    rw [isNClique_iff]
    refine ⟨?_, by simpa using hcard⟩
    intro u hu w hw huw
    simp only [Finset.coe_map, Function.Embedding.subtype_apply, Set.mem_image,
      Finset.mem_coe] at hu hw
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨w', hw', rfl⟩ := hw
    have := hc hu' hw' (fun e => huw (by rw [e]))
    simpa using this
  refine h _ (h1.insert (a := x) ?_)
  intro b hb
  simp only [Finset.mem_map, Function.Embedding.subtype_apply] at hb
  obtain ⟨b', _, rfl⟩ := hb
  exact b'.2

lemma fin2 : ∀ x y z : Fin 2, x ≠ y → x ≠ z → y ≠ z → False := by decide

end OMA

open SimpleGraph in
theorem OMA.solution : type_of% @Erdos1111.erdos_1111.variants.el_zahar_erdos := by
  classical
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    refine ⟨8, by norm_num, ?_⟩
    intro V _ G hG hT
    exact OMA.three_three V G (by exact_mod_cast hG) (hT.mono (by norm_num))
  | succ t ht ih =>
    obtain ⟨d', hd', ih⟩ := ih
    refine ⟨3 * d' + 8, by omega, ?_⟩
    intro V _ G hG hT
    by_cases h3 : G.CliqueFree 3
    · refine OMA.three_three V G (le_trans ?_ hG) h3
      exact_mod_cast (by omega : 8 ≤ 3 * d' + 8)
    by_cases hbig : ∃ x, (d' : ℕ∞) ≤ (G.induce (G.neighborSet x)).chromaticNumber
    · obtain ⟨x, hx⟩ := hbig
      obtain ⟨A', B', ⟨hdis, hanti⟩, hA', hB'⟩ :=
        ih _ (G.induce (G.neighborSet x)) hx (OMA.nbr_cliqueFree G t x hT)
      refine ⟨Subtype.val '' A', Subtype.val '' B', ⟨?_, ?_⟩,
        hA'.trans (OMA.transfer G _ A'), hB'.trans (OMA.transfer G _ B')⟩
      · exact (Set.disjoint_image_iff Subtype.val_injective).mpr hdis
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
        exact hanti a ha b hb (by simpa using hab)
    · push_neg at hbig
      have hcol : ∀ x, (G.induce (G.neighborSet x)).Colorable (d' - 1) :=
        fun x => OMA.lt_colorable _ _ (hbig x)
      unfold CliqueFree at h3
      push_neg at h3
      obtain ⟨s, hs⟩ := h3
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp hs
      set N : Set V := G.neighborSet a ∪ G.neighborSet b ∪ G.neighborSet c with hN
      refine ⟨{a, b, c}, Nᶜ, ⟨?_, ?_⟩, ?_, ?_⟩
      · refine Set.disjoint_left.mpr fun v hv hv' => hv' ?_
        rcases hv with rfl | rfl | rfl
        · exact Or.inl (Or.inr hab.symm)
        · exact Or.inl (Or.inl hab)
        · exact Or.inl (Or.inl hac)
      · intro v hv w hw hvw
        apply hw
        rcases hv with rfl | rfl | rfl
        · exact Or.inl (Or.inl hvw)
        · exact Or.inl (Or.inr hvw)
        · exact Or.inr hvw
      · by_contra hcon
        have hC := OMA.lt_colorable _ 3 (not_le.mp hcon)
        obtain ⟨C⟩ := hC
        have ha : a ∈ ({a, b, c} : Set V) := by simp
        have hb : b ∈ ({a, b, c} : Set V) := by simp
        have hc : c ∈ ({a, b, c} : Set V) := by simp
        exact OMA.fin2 (C ⟨a, ha⟩) (C ⟨b, hb⟩) (C ⟨c, hc⟩)
          (C.valid (by simpa using hab)) (C.valid (by simpa using hac))
          (C.valid (by simpa using hbc))
      · by_contra hcon
        have hC := OMA.lt_colorable _ 3 (not_le.mp hcon)
        obtain ⟨CB⟩ := hC
        obtain ⟨Ca⟩ := hcol a
        obtain ⟨Cb⟩ := hcol b
        obtain ⟨Cc⟩ := hcol c
        let col : V → (Fin 3 × Fin (d' - 1)) ⊕ Fin 2 := fun v =>
          if h1 : v ∈ G.neighborSet a then Sum.inl (0, Ca ⟨v, h1⟩)
          else if h2 : v ∈ G.neighborSet b then Sum.inl (1, Cb ⟨v, h2⟩)
          else if h3 : v ∈ G.neighborSet c then Sum.inl (2, Cc ⟨v, h3⟩)
          else Sum.inr (CB ⟨v, fun h => h.elim (fun h => h.elim h1 h2) h3⟩)
        have hvalid : ∀ v w, G.Adj v w → col v ≠ col w := by
          intro v w hvw
          simp only [col]
          split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 <;>
            simp only [ne_eq, Sum.inl.injEq, Prod.mk.injEq, Sum.inr.injEq, reduceCtorEq,
              not_false_eq_true, Fin.reduceEq, false_and, true_and, Fin.isValue] <;>
            first
              | exact Ca.valid (by simpa using hvw)
              | exact Cb.valid (by simpa using hvw)
              | exact Cc.valid (by simpa using hvw)
              | exact CB.valid (by simpa using hvw)
        have hGc : G.Colorable (Fintype.card ((Fin 3 × Fin (d' - 1)) ⊕ Fin 2)) :=
          (Coloring.mk col (fun {v w} h => hvalid v w h)).colorable
        have h4 := hG.trans hGc.chromaticNumber_le
        have h5 : 3 * d' + 8 ≤ Fintype.card ((Fin 3 × Fin (d' - 1)) ⊕ Fin 2) := by
          exact_mod_cast h4
        simp at h5
        omega
