import FormalConjectures.ErdosProblems.«570»

/-! # The cycle Ramsey bound in Erdős problem 570 -/

/- The graph Ramsey number as a threshold on arbitrary finite hosts -/

namespace OMA
open SimpleGraph

private def HasCliqueIn {V : Type*} (G : SimpleGraph V) (s : Finset V) (a : ℕ) : Prop :=
  ∃ A ⊆ s, A.card = a ∧ G.IsClique (↑A : Set V)

private theorem two_cliques {V : Type*} (G : SimpleGraph V) (a b : ℕ) (s : Finset V)
    (size : 2^(a+b) ≤ s.card) : HasCliqueIn G s a ∨ HasCliqueIn Gᶜ s b := by
  classical
  cases a with
  | zero => exact Or.inl ⟨∅, by simp, rfl, by simp⟩
  | succ a =>
    cases b with
    | zero => exact Or.inr ⟨∅, by simp, rfl, by simp⟩
    | succ b =>
      obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < s.card from (by positivity : 0 < 2^_).trans_le size)
      let R := (s.erase v).filter (G.Adj v)
      let B := (s.erase v).filter (fun x => ¬G.Adj v x)
      have split : R.card + B.card = (s.erase v).card := Finset.card_filter_add_card_filter_not ..
      have count := Finset.card_erase_add_one hv
      have rs : R ⊆ s := fun _ h => Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1
      have bs : B ⊆ s := fun _ h => Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1
      have lift {A : Finset V} {J : SimpleGraph V} {n : ℕ} (sub : A ⊆ s)
          (adj : ∀ x ∈ A, J.Adj v x) (cl : HasCliqueIn J A n) : HasCliqueIn J s (n+1) := by
        obtain ⟨D,hD,sz,ok⟩ := cl
        have nv : v ∉ D := fun h => (adj _ (hD h)).ne rfl
        refine ⟨insert v D, Finset.insert_subset hv (hD.trans sub), by simp [nv,sz], ?_⟩
        rw [Finset.coe_insert]
        exact (SimpleGraph.isClique_insert).mpr ⟨ok, fun x hx _ => adj x (hD hx)⟩
      by_cases r : 2^(a+(b+1)) ≤ R.card
      · rcases two_cliques G a (b+1) R r with h|⟨A,hA,sz,cl⟩
        · exact Or.inl (lift rs (fun _ h => (Finset.mem_filter.mp h).2) h)
        · exact Or.inr ⟨A,hA.trans rs,sz,cl⟩
      · have hb : 2^(a+1+b) ≤ B.card := by
          rw [show a+1+(b+1) = (a+(b+1))+1 by omega, pow_succ] at size
          rw [show a+1+b = a+(b+1) by omega]
          omega
        rcases two_cliques G (a+1) b B hb with ⟨A,hA,sz,cl⟩|h
        · exact Or.inl ⟨A,hA.trans bs,sz,cl⟩
        · apply Or.inr (lift bs _ h)
          intro x hx
          exact ⟨(Finset.ne_of_mem_erase (Finset.mem_filter.mp hx).1).symm,
            (Finset.mem_filter.mp hx).2⟩
termination_by a+b

private theorem copy_of_clique {V W : Type*} [Fintype W] (H : SimpleGraph W)
    (G : SimpleGraph V) {s : Finset V} (cl : HasCliqueIn G s (Fintype.card W)) : H ⊑ G := by
  obtain ⟨A, _,sz,ok⟩ := cl
  obtain ⟨f⟩ : Nonempty (W ↪ A) := Function.Embedding.nonempty_of_card_le (by simp [sz])
  let g := f.trans (Function.Embedding.subtype _)
  exact ⟨⟨⟨g, fun {i j} h => ok (f i).prop (f j).prop (g.injective.ne h.ne)⟩, g.injective⟩⟩

theorem graphRamsey_property {U W : Type*} [Fintype U] [Fintype W]
    (X : SimpleGraph U) (H : SimpleGraph W) (G : SimpleGraph (Fin (graphRamsey X H))) :
    X ⊑ G ∨ H ⊑ Gᶜ := by
  apply Nat.sInf_mem (s := {n : ℕ | ∀ C : SimpleGraph (Fin n), X ⊑ C ∨ H ⊑ Cᶜ}) _ G
  refine ⟨2^(Fintype.card U + Fintype.card W), fun C => ?_⟩
  exact (two_cliques C _ _ Finset.univ (by simp)).imp (copy_of_clique X C) (copy_of_clique H Cᶜ)

theorem graphRamsey_host {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (X : SimpleGraph U) (H : SimpleGraph W) (G : SimpleGraph V)
    (size : graphRamsey X H ≤ Fintype.card V) : X ⊑ G ∨ H ⊑ Gᶜ := by
  classical
  obtain ⟨f⟩ : Nonempty (Fin (graphRamsey X H) ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by simpa using size)
  rcases graphRamsey_property X H (G.comap f) with h|h
  · exact Or.inl (h.trans ⟨⟨⟨f, fun e => e⟩, f.injective⟩⟩)
  · exact Or.inr (h.trans ⟨⟨⟨f, fun e => ⟨f.injective.ne e.1, e.2⟩⟩, f.injective⟩⟩)

theorem graphRamsey_le_iff {U W : Type*} [Fintype U] [Fintype W] {N : ℕ}
    (X : SimpleGraph U) (H : SimpleGraph W) :
    graphRamsey X H ≤ N ↔ ∀ G : SimpleGraph (Fin N), X ⊑ G ∨ H ⊑ Gᶜ :=
  ⟨fun h G => graphRamsey_host X H G (by simpa using h), fun h => by apply Nat.sInf_le; exact h⟩

end OMA

/- Paths versus properly colored graphs -/

namespace OMA
open SimpleGraph

private theorem path_of_chain {V : Type*} (G : SimpleGraph V) (p : List V)
    (hd : p.Nodup) (hc : p.IsChain G.Adj) {k : ℕ} (hk : k ≤ p.length) :
    pathGraph k ⊑ G := by
  let f (i : Fin k) : V := p[i.val]'(by omega)
  have step (i j : Fin k) (h : i.val + 1 = j.val) : G.Adj (f i) (f j) := by
    have ha := List.isChain_iff_getElem.mp hc i.val (by omega)
    simpa only [f, h] using ha
  refine ⟨⟨⟨f, fun {i j} hij => ?_⟩, ?_⟩⟩
  · rcases pathGraph_adj.mp hij with h | h
    · exact step i j h
    · exact (step j i h).symm
  · intro i j hij
    have eq : i.castLE hk = j.castLE hk := hd.injective_get hij
    exact Fin.ext (congrArg (fun z : Fin p.length => z.val) eq)

set_option maxHeartbeats 800000 in
private theorem dfs {V : Type*} [DecidableEq V] (G : SimpleGraph V) {k a b : ℕ}
    (free : ¬ pathGraph k ⊑ G) (fuel : ℕ)
    (u w : Finset V) (p : List V) (nd : p.Nodup) (chain : p.IsChain G.Adj)
    (pu : ∀ x ∈ p, x ∉ u) (pw : ∀ x ∈ p, x ∉ w)
    (uw : ∀ x ∈ u, ∀ y ∈ w, x ≠ y ∧ ¬ G.Adj x y)
    (hu : u.card ≤ a) (hc : a + b + k ≤ u.card + w.card + p.length)
    (hf : 2*w.card+p.length ≤ fuel) :
    ∃ A B : Finset V, A.card = a ∧ b ≤ B.card ∧
      ∀ x ∈ A, ∀ y ∈ B, Gᶜ.Adj x y := by
  induction fuel generalizing u w p with
  | zero =>
    have hp : p.length < k := by
      by_contra! h
      exact free (path_of_chain G p nd chain h)
    omega
  | succ fuel ih =>
    have hp : p.length < k := by
      by_contra! h
      exact free (path_of_chain G p nd chain h)
    by_cases done : u.card = a
    · exact ⟨u, w, done, by omega, uw⟩
    have ha : u.card < a := by omega
    have hw : w.Nonempty := Finset.card_pos.mp (by omega)
    cases p with
    | nil =>
      obtain ⟨x, hx⟩ := hw
      have he := Finset.card_erase_add_one hx
      refine ih u (w.erase x) [x] (by simp) (by simp) ?_ (by simp) ?_ hu ?_ ?_
      · simpa using fun h => (uw x h x hx).1 rfl
      · exact fun i hi j hj => uw i hi j (Finset.mem_of_mem_erase hj)
      · simp only [List.length_nil] at hc
        simp only [List.length_cons, List.length_nil]
        omega
      · simp only [List.length_cons, List.length_nil] at *
        omega
    | cons x xs =>
      by_cases ext : ∃ y ∈ w, G.Adj y x
      · obtain ⟨y, hy, hyx⟩ := ext
        have he := Finset.card_erase_add_one hy
        have fresh : y ∉ x :: xs := fun h => pw y h hy
        refine ih u (w.erase y) (y :: x :: xs) (List.nodup_cons.mpr ⟨fresh, nd⟩)
          (by simpa using And.intro hyx chain) ?_ ?_ ?_ hu ?_ ?_
        · exact List.forall_mem_cons.mpr ⟨fun h => (uw y h y hy).1 rfl, pu⟩
        · intro i hi
          rcases List.mem_cons.mp hi with rfl | h
          · simp
          · exact fun hj => pw i h (Finset.mem_of_mem_erase hj)
        · exact fun i hi j hj => uw i hi j (Finset.mem_of_mem_erase hj)
        · simp only [List.length_cons] at *
          omega
        · simp only [List.length_cons] at *
          omega
      · have hxu := pu x List.mem_cons_self
        have hcard := Finset.card_insert_of_notMem hxu
        refine ih (insert x u) w xs (List.nodup_cons.mp nd).2 chain.tail ?_ ?_ ?_ ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun e => (List.nodup_cons.mp nd).1 (e ▸ hi), pu i (List.mem_cons_of_mem _ hi)⟩
        · exact fun i hi => pw i (List.mem_cons_of_mem _ hi)
        · intro i hi j hj
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact ⟨fun e => pw i List.mem_cons_self (e ▸ hj), fun h => ext ⟨j, hj, h.symm⟩⟩
          · exact uw i hi j hj
        · omega
        · simp only [List.length_cons] at hc
          omega
        · simp only [List.length_cons] at hf
          omega

theorem path_separator {V : Type*} [Fintype V] (G : SimpleGraph V) {k a b : ℕ}
    (hsize : a + b + k ≤ Fintype.card V) (free : ¬ pathGraph k ⊑ G) :
    ∃ A B : Finset V, A.card = a ∧ b ≤ B.card ∧
      ∀ x ∈ A, ∀ y ∈ B, Gᶜ.Adj x y := by
  classical
  exact dfs G free (2 * Fintype.card V) ∅ Finset.univ [] (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simpa using hsize) (by simp)

private theorem embed_colored {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (c : W → ℕ) (t k : ℕ)
    (bounded : ∀ x, c x ≤ t) (proper : ∀ {x y}, H.Adj x y → c x ≠ c y)
    (space : Fintype.card W + k * t ≤ Fintype.card V) (free : ¬ pathGraph k ⊑ G) :
    H ⊑ Gᶜ := by
  classical
  cases t with
  | zero =>
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (by simpa using space)
    refine ⟨⟨⟨f, fun {x y} h => ?_⟩, f.injective⟩⟩
    exact False.elim (proper h (by have := bounded x; have := bounded y; omega))
  | succ t =>
    let P := fun x => c x = t + 1
    let X := {x : W // P x}
    let Y := {x : W // ¬ P x}
    have hsum : Fintype.card X + Fintype.card Y = Fintype.card W := by
      exact (Fintype.card_subtype_compl P) ▸ Nat.add_sub_of_le (Fintype.card_subtype_le P)
    obtain ⟨A, B, ha, hb, cross⟩ := path_separator G
      (a := Fintype.card X) (b := Fintype.card Y + k*t)
      (by rw [Nat.mul_succ] at space; omega) free
    obtain ⟨f⟩ : Nonempty (X ↪ A) := Function.Embedding.nonempty_of_card_le (by simp [ha])
    let G' := G.induce (↑B : Set V)
    let H' := H.induce {x | ¬ P x}
    have free' : ¬ pathGraph k ⊑ G' := fun h =>
      free (h.trans ⟨Copy.induce G (↑B : Set V)⟩)
    obtain ⟨g⟩ := embed_colored G' H' (fun x => c x.val) t k
      (fun x => by have h := x.prop; change c x.val ≠ t+1 at h; have := bounded x.val; omega)
      (fun h => proper h) (by change Fintype.card Y + k*t ≤ Fintype.card (↥B); simpa only [Fintype.card_coe] using hb) free'
    let F (x : W) : V := if h : P x then (f ⟨x,h⟩).val else (g ⟨x,h⟩).val
    have disj {x : A} {y : B} : x.val ≠ y.val := (cross _ x.prop _ y.prop).ne
    refine ⟨⟨⟨F, fun {x y} h => ?_⟩, ?_⟩⟩
    · by_cases hx : P x <;> by_cases hy : P y
      · exact False.elim (proper h (hx.trans hy.symm))
      · simpa only [F, dif_pos hx, dif_neg hy] using
          cross _ (f ⟨x,hx⟩).prop _ (g ⟨y,hy⟩).prop
      · simpa only [F, dif_pos hy, dif_neg hx] using
          (cross _ (f ⟨y,hy⟩).prop _ (g ⟨x,hx⟩).prop).symm
      · simp only [F, dif_neg hx, dif_neg hy]
        have h' := g.toHom.map_rel' (show H'.Adj ⟨x,hx⟩ ⟨y,hy⟩ from h)
        exact ⟨fun e => h'.ne (Subtype.ext e), h'.2⟩
    · intro x y e
      change F x = F y at e
      by_cases hx : P x <;> by_cases hy : P y <;> simp only [F, hx, hy, ↓reduceDIte] at e
      · exact congrArg Subtype.val (f.injective (Subtype.ext e))
      · exact False.elim (disj e)
      · exact False.elim (disj e.symm)
      · exact congrArg Subtype.val (g.injective (Subtype.ext e))
termination_by t

theorem path_ramsey_of_coloring {W : Type*} [Fintype W] (H : SimpleGraph W) (k t : ℕ)
    (c : H.Coloring (Fin (t + 1))) :
    graphRamsey (pathGraph k) H ≤ Fintype.card W + k * t := by
  apply Nat.sInf_le
  intro G
  by_cases h : pathGraph k ⊑ G
  · exact Or.inl h
  · exact Or.inr (embed_colored G H (fun x => (c x).val) t k
      (fun x => Nat.le_of_lt_succ (c x).isLt)
      (fun hxy e => c.valid hxy (Fin.ext e)) (by simp) h)

open scoped Sym2

/-- Every pair of colors occurs on an edge of an optimal coloring. -/
theorem choose_chromatic_le_edges {W : Type*} [Fintype W] (H : SimpleGraph W) :
    H.chromaticNumber.toNat.choose 2 ≤ H.edgeSet.ncard := by
  classical
  let q := H.chromaticNumber.toNat
  obtain ⟨c⟩ := H.colorable_chromaticNumber_of_fintype
  let Q := H.map (c : W → Fin q)
  let f : H →g Q := ⟨c, fun h => map_adj_apply' h (c.valid h)⟩
  have hq : (q : ℕ∞) = H.chromaticNumber :=
    ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top _) H.chromaticNumber_le_card)
  have ht : Q = ⊤ := eq_top_of_chromaticNumber_eq_card (le_antisymm Q.chromaticNumber_le_card
    (by rw [Fintype.card_fin]; exact hq.le.trans (chromaticNumber_mono_of_hom f)))
  have surj : Function.Surjective f.mapEdgeSet := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ i j =>
      obtain ⟨_, x, y, h, hx, hy⟩ := (map_adj' _ _ i j).mp he
      refine ⟨⟨s(x,y), h⟩, Subtype.ext ?_⟩
      change s(c x, c y) = s(i,j)
      rw [hx, hy]
  have h := Fintype.card_le_of_surjective _ surj
  rw [Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard, ht] at h
  have hc : (⊤ : SimpleGraph (Fin q)).edgeSet.ncard = q.choose 2 := by
    rw [Set.ncard_eq_toFinset_card']
    exact (card_edgeFinset_top_eq_card_choose_two (V := Fin q)).trans (by rw [Fintype.card_fin])
  exact hc ▸ h

theorem chromatic_sub_one_le_sqrt {W : Type*} [Fintype W] (H : SimpleGraph W) :
    H.chromaticNumber.toNat - 1 ≤ Nat.sqrt (2 * H.edgeSet.ncard) := by
  have h := choose_chromatic_le_edges H
  generalize H.chromaticNumber.toNat = q at *
  cases q with
  | zero => simp
  | succ p =>
    simp only [Nat.add_sub_cancel]
    apply Nat.le_sqrt.mpr
    rw [Nat.choose_two_right, Nat.add_sub_cancel] at h
    cases p with
    | zero => simp
    | succ p =>
      rw [Nat.add_mul, one_mul] at h
      omega

theorem path_ramsey_chromatic {W : Type*} [Fintype W] (H : SimpleGraph W) (k : ℕ) :
    graphRamsey (pathGraph k) H ≤ Fintype.card W + k * (H.chromaticNumber.toNat - 1) := by
  have hc := H.colorable_chromaticNumber_of_fintype
  have bound : H.chromaticNumber.toNat ≤ H.chromaticNumber.toNat - 1 + 1 := by omega
  exact path_ramsey_of_coloring H k _ (hc.mono bound).some

theorem path_ramsey_edges {W : Type*} [Fintype W] (H : SimpleGraph W) (k : ℕ) :
    graphRamsey (pathGraph k) H ≤ Fintype.card W + k * Nat.sqrt (2 * H.edgeSet.ncard) :=
  (path_ramsey_chromatic H k).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (chromatic_sub_one_le_sqrt H)) _)

end OMA

/- Paths in the first and second neighborhoods of a vertex -/

namespace OMA
open SimpleGraph

private theorem cycle_of_sequence {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (f : ℕ → V) (inj : ∀ i < k, ∀ j < k, f i = f j → i = j)
    (step : ∀ i, i+1 < k → G.Adj (f i) (f (i+1)))
    (close : G.Adj (f (k-1)) (f 0)) : cycleGraph k ⊑ G := by
  refine ⟨⟨⟨fun i => f i.val, ?_⟩, fun {i j} h => Fin.ext (inj _ i.isLt _ j.isLt h)⟩⟩
  intro i j h
  wlog lt : i < j generalizing i j
  · exact (this h.symm (lt_of_le_of_ne (le_of_not_gt lt) h.ne.symm)).symm
  rcases cycleGraph_adj'.mp h with h | h
  · rw [Fin.coe_sub_iff_lt.mpr lt] at h
    have hi : i.val = 0 := by omega
    have hj : j.val = k-1 := by omega
    simpa only [hi, hj] using close.symm
  · rw [Fin.sub_val_of_le lt.le] at h
    have hj : j.val = i.val+1 := by omega
    rw [hj]
    exact step _ (hj ▸ j.isLt)

private theorem cycle_from_interval {V : Type*} {G : SimpleGraph V}
    (x : ℕ → V) (pre : List V) (a b : ℕ) (hab : a ≤ b)
    (nd : pre.Nodup) (ch : pre.IsChain G.Adj) (hne : pre ≠ [])
    (dis : ∀ i, a ≤ i → i ≤ b → x i ∉ pre)
    (inj : ∀ i, a ≤ i → i ≤ b → ∀ j, a ≤ j → j ≤ b → x i = x j → i=j)
    (step : ∀ i, a ≤ i → i < b → G.Adj (x i) (x (i+1)))
    (start : G.Adj (pre.getLast hne) (x a)) (finish : G.Adj (x b) (pre.head hne)) :
    cycleGraph (pre.length + (b-a+1)) ⊑ G := by
  let f (i : ℕ) := if h : i < pre.length then pre[i] else x (a+(i-pre.length))
  apply cycle_of_sequence f
  · intro i hi j hj
    dsimp only [f]
    split <;> split
    · exact fun h => congrArg Fin.val (nd.injective_get
        (show pre.get ⟨i,by omega⟩ = pre.get ⟨j,by omega⟩ from h))
    · exact fun h => False.elim (dis _ (by omega) (by omega) (h ▸ List.getElem_mem ..))
    · exact fun h => False.elim (dis _ (by omega) (by omega) (h.symm ▸ List.getElem_mem ..))
    · intro h
      have := inj _ (by omega) (by omega) _ (by omega) (by omega) h
      omega
  · intro i hi
    dsimp only [f]
    split <;> split
    · exact List.isChain_iff_getElem.mp ch i (by omega)
    · have eq : i+1 = pre.length := by omega
      simpa [eq, List.getLast_eq_getElem, show pre.length-1 = i by omega] using start
    · omega
    · convert step (a+(i-pre.length)) (by omega) (by omega) using 2
      omega
  · have hlen := List.length_pos_iff.mpr hne
    have e : a+(pre.length+(b-a+1)-1-pre.length) = b := by omega
    simpa only [f, dif_neg (show ¬ pre.length+(b-a+1)-1 < pre.length by omega),
      dif_pos hlen, e, List.head_eq_getElem] using finish

theorem cycle_of_neighborhood_path {V : Type*} (G : SimpleGraph V) (v : V) (k : ℕ)
    (hk : 3 ≤ k) (path : pathGraph (k-1) ⊑ G.induce (G.neighborSet v)) : cycleGraph k ⊑ G := by
  obtain ⟨p⟩ := path
  let idx (i : ℕ) : Fin (k-1) := ⟨i % (k-1), Nat.mod_lt _ (by omega)⟩
  let x (i : ℕ) := (p (idx i)).val
  have vx (i : ℕ) : G.Adj v (x i) := (p (idx i)).prop
  have hc := cycle_from_interval (G := G) x [v] 0 (k-2) (by omega) (by simp) (by simp)
    (by simp) (fun i _ _ => by simp [(vx i).ne.symm])
    (fun i _ hi j _ hj eq => by
      have e := congrArg Fin.val (p.injective (Subtype.ext eq))
      simpa only [idx, Nat.mod_eq_of_lt (show i < k-1 by omega),
        Nat.mod_eq_of_lt (show j < k-1 by omega)] using e)
    (fun i _ hi => by
      apply p.toHom.map_rel'
      exact pathGraph_adj.mpr (Or.inl (by simp [idx, Nat.mod_eq_of_lt (show i < k-1 by omega),
        Nat.mod_eq_of_lt (show i+1 < k-1 by omega)])))
    (by simpa using vx 0) (by simpa using (vx (k-2)).symm)
  exact (show [v].length+(k-2-0+1) = k by simp; omega) ▸ hc

/-- The exact distance-two shell. -/
def secondShell {V : Type*} (G : SimpleGraph V) (v : V) : Set V :=
  {x | x ≠ v ∧ ¬ G.Adj v x ∧ ∃ u, G.Adj v u ∧ G.Adj u x}

theorem cycle_of_second_shell_path {V : Type*} (G : SimpleGraph V) (v : V)
    (k : ℕ) (hk : 5 ≤ k)
    (path : pathGraph (2*k) ⊑ G.induce (secondShell G v)) :
    cycleGraph k ⊑ G := by
  classical
  obtain ⟨p⟩ := path
  let idx (i : ℕ) : Fin (2*k) := ⟨i % (2*k), Nat.mod_lt _ (by omega)⟩
  let x (i : ℕ) := (p (idx i)).val
  have xx {i j} (hi : i < 2*k) (hj : j < 2*k) (eq : x i = x j) : i = j := by
    have e := congrArg Fin.val (p.injective (Subtype.ext eq))
    simpa only [idx, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using e
  have steps (i : ℕ) (h : i+1 < 2*k) : G.Adj (x i) (x (i+1)) := by
    apply p.toHom.map_rel'
    exact pathGraph_adj.mpr (Or.inl (by simp [idx, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt (show i < 2*k by omega)]))
  have hx (i : ℕ) : x i ≠ v ∧ ¬G.Adj v (x i) ∧ ∃ u, G.Adj v u ∧ G.Adj u (x i) :=
    (p (idx i)).prop
  choose u vu ux using fun i => (hx i).2.2
  have xu (i j : ℕ) : x i ≠ u j := fun e => (hx i).2.1 (e ▸ vu j)
  let d := k-4
  have hd : 0 < d := by dsimp [d]; omega
  have kd : k = d+4 := by dsimp [d]; omega
  by_contra free
  have period (i : ℕ) (hi : i+d < 2*k) : u i = u (i+d) := by
    by_contra ne
    let pre := [u (i+d),v,u i]
    have hc := cycle_from_interval (G := G) x pre i (i+d) (by omega)
      (by simp [pre, Ne.symm ne, (vu (i+d)).ne.symm, (vu i).ne])
      (by simp [pre, (vu (i+d)).symm, vu i]) (by simp [pre])
      (fun j _ _ => by simp [pre, xu, (hx j).1])
      (fun _ _ hj _ _ hl => xx (by omega) (by omega))
      (fun j _ hj => steps j (by omega)) (by simpa [pre] using ux i)
      (by simpa [pre] using (ux (i+d)).symm)
    exact free ((show pre.length+(i+d-i+1) = k by simp [pre]; omega) ▸ hc)
  have near (i : ℕ) (hi : i ≤ 1) : u i = u (i+1) := by
    by_contra ne
    let a := i+1+d
    let b := i+d+d
    have ha : a = i+1+d := rfl
    have hb : b = i+d+d := rfl
    have eq₁ : u i = u b := (period i (by omega)).trans (period (i+d) (by omega))
    have eq₂ : u (i+1) = u a := period (i+1) (by omega)
    let pre := [u i,x i,x (i+1),u (i+1)]
    have dif : x i ≠ x (i+1) := fun h => by have := xx (by omega) (by omega) h; omega
    have hc := cycle_from_interval (G := G) x pre a b (by omega)
      (by simp [pre, ne, xu, (xu _ _).symm, dif])
      (by simp [pre, ux i, steps i (by omega), (ux (i+1)).symm]) (by simp [pre])
      (fun j hj hl => by
        have e₁ : x j ≠ x i := fun e => by have := xx (by omega) (by omega) e; omega
        have e₂ : x j ≠ x (i+1) := fun e => by have := xx (by omega) (by omega) e; omega
        simp [pre, xu, e₁, e₂])
      (fun _ _ hj _ _ hl => xx (by omega) (by omega))
      (fun j _ hj => steps j (by omega))
      (by simpa [pre, eq₂] using ux a) (by simpa [pre, eq₁] using (ux b).symm)
    exact free ((show pre.length+(b-a+1) = k by simp [pre]; omega) ▸ hc)
  have eq : u 0 = u (2+d) := (near 0 (by decide)).trans ((near 1 (by decide)).trans (period 2 (by omega)))
  have hc := cycle_from_interval (G := G) x [u 0] 0 (2+d) (by omega) (by simp)
    (by simp) (by simp) (fun j _ _ => by simp [xu])
    (fun _ _ hj _ _ hl => xx (by omega) (by omega))
    (fun j _ hj => steps j (by omega))
    (by simpa using ux 0) (by simpa [eq] using (ux (2+d)).symm)
  exact free ((show [u 0].length+(2+d-0+1) = k by simp; omega) ▸ hc)

end OMA

/- Edge counts in fixed-size vertex subsets -/

namespace OMA
open SimpleGraph Finset
open scoped BigOperators

/-- The exact two-vertex sampling bound, with denominators cleared. -/
theorem sparse_subset {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (s : ℕ) (hs : s ≤ Fintype.card V) :
    ∃ S : Finset V, S.card = s ∧
      (H.induce (S : Set V)).edgeSet.ncard * (Fintype.card V).choose 2 ≤
        H.edgeSet.ncard * s.choose 2 := by
  classical
  let n := Fintype.card V
  let T := (univ : Finset V).powersetCard s
  have nt : T.Nonempty := by
    apply card_pos.mp
    simpa [T] using Nat.choose_pos hs
  have cardT : T.card = n.choose s := by simp [T,n]
  obtain ⟨S, hS, hmin⟩ := T.exists_min_image
    (fun S => (H.induce (S : Set V)).edgeFinset.card) nt
  have sz := (mem_powersetCard.mp hS).2
  refine ⟨S, sz, ?_⟩
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  change (H.induce (S : Set V)).edgeFinset.card * _ ≤ H.edgeFinset.card * _
  change _ * n.choose 2 ≤ _
  by_cases small : s < 2
  · have e := (H.induce (S : Set V)).card_edgeFinset_le_card_choose_two
    have hz : (H.induce (S : Set V)).edgeFinset.card = 0 := by
      simpa [sz, Nat.choose_eq_zero_of_lt small] using e
    simp [hz]
  have htwo : 2 ≤ s := by omega
  have dbl : T.card * (H.induce (S : Set V)).edgeFinset.card ≤
      H.edgeFinset.card * (n - 2).choose (s - 2) := by
    apply Finset.card_mul_le_card_mul (r := fun (A : Finset V) (e : Sym2 V) => e.toFinset ⊆ A)
    · intro A hA
      exact (hmin A hA).trans_eq (H.card_filter_edgeFinset_toFinset_subset A).symm
    · intro e he
      have hc := H.card_toFinset_mem_edgeFinset ⟨e, he⟩
      change e.toFinset.card = 2 at hc
      change ((univ.powersetCard s).filter (e.toFinset ⊆ ·)).card ≤ _
      rw [card_filter_powersetCard_subset _ _ _ (subset_univ _) (hc ▸ htwo), hc, card_univ]
  have pos : 0 < n.choose s := Nat.choose_pos hs
  apply (Nat.mul_le_mul_left_iff pos).mp
  calc
    _ = (T.card * (H.induce (S : Set V)).edgeFinset.card) * n.choose 2 := by rw [cardT]; ring
    _ ≤ (H.edgeFinset.card * (n-2).choose (s-2)) * n.choose 2 := Nat.mul_le_mul_right _ dbl
    _ = H.edgeFinset.card * (n.choose s * s.choose 2) := by rw [Nat.choose_mul htwo]; ring
    _ = _ := by ring

/-- The square bound used to choose the smaller induced piece in Claim 3. -/
theorem sparse_subset_square {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (s : ℕ) (hs : s ≤ Fintype.card V) :
    ∃ S : Finset V, S.card = s ∧ (H.induce (S : Set V)).edgeSet.ncard * Fintype.card V ^ 2
      ≤ H.edgeSet.ncard * s ^ 2 := by
  obtain ⟨S, sz, h⟩ := sparse_subset H s hs
  refine ⟨S, sz, ?_⟩
  by_cases small : Fintype.card V ≤ 1
  · classical
    have ss : s < 2 := by omega
    have e := (H.induce (S : Set V)).card_edgeFinset_le_card_choose_two
    have hz : (H.induce (S : Set V)).edgeFinset.card = 0 := by
      simpa [sz, Nat.choose_eq_zero_of_lt ss] using e
    rw [Set.ncard_eq_toFinset_card']
    change (H.induce (S : Set V)).edgeFinset.card * _ ≤ _
    simp [hz]
  let n : ℚ := Fintype.card V
  let t : ℚ := s
  let e : ℚ := (H.induce (S : Set V)).edgeSet.ncard
  let m : ℚ := H.edgeSet.ncard
  have hh : e * ((Fintype.card V).choose 2 : ℚ) ≤ m * (s.choose 2 : ℚ) := by dsimp only [e,m]; exact_mod_cast h
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at hh
  change e * (n * (n-1)/2) ≤ m * (t * (t-1)/2) at hh
  have nt : t ≤ n := by dsimp only [t,n]; exact_mod_cast hs
  have hn : 1 < n := by dsimp only [n]; exact_mod_cast Nat.lt_of_not_ge small
  have hn0 : 0 ≤ n := by linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hm : 0 ≤ m := by dsimp [m]; positivity
  suffices hq : e*n^2 ≤ m*t^2 by dsimp only [e,n,m,t] at hq; exact_mod_cast hq
  apply (le_of_mul_le_mul_right _ (sub_pos.mpr hn) : e*n^2 ≤ m*t^2)
  nlinarith [mul_le_mul_of_nonneg_right hh hn0, mul_nonneg (mul_nonneg hm ht) (sub_nonneg.mpr nt)]

end OMA

/- Numerical estimates for the dense cutoff and the final partition -/

namespace OMA

/-- Below the three-fifths cutoff the pentagon clique bound fits within a
linear budget: the conclusion is the square of the desired comparison. -/
theorem dense_cutoff {c n m : ℕ} (large : c^10 ≤ m) (small : n^5 ≤ m^3) :
    c^2 * n^3 ≤ m^2 := by
  apply le_of_not_gt
  intro h
  have strict := Nat.pow_lt_pow_left h (by decide : 5 ≠ 0)
  have le : (c^2 * n^3)^5 ≤ (m^2)^5 := calc
    _ = c^10 * (n^5)^3 := by ring
    _ ≤ m * (m^3)^3 := Nat.mul_le_mul large (Nat.pow_le_pow_left small 3)
    _ = _ := by ring
  omega

/-- Above the same cutoff, the order dominates any fixed multiple of the
square root of the edge count. -/
theorem sparse_cutoff {c n m : ℕ} (large : c^10 ≤ m) (big : m^3 ≤ n^5) :
    c^2 * m ≤ n^2 := by
  apply le_of_not_gt
  intro h
  have strict := Nat.pow_lt_pow_left h (by decide : 5 ≠ 0)
  have le : (c^2 * m)^5 ≤ (n^2)^5 := calc
    _ = c^10 * m^5 := by ring
    _ ≤ m * m^5 := Nat.mul_le_mul_right _ large
    _ = (m^3)^2 := by ring
    _ ≤ (n^5)^2 := Nat.pow_le_pow_left big 2
    _ = _ := by ring
  omega

/-- Claim 2, using a positive margin in the upper bound for the order of H. -/
theorem first_neighborhood_lower {m n u slack δ : ℝ}
    (hm : 0 < m) (hn : 0 ≤ n) (hu : 0 ≤ u)
    (degree : δ*n ≤ 2*m) (neighbors : 2*m-n ≤ δ*u)
    (gap : 2*m*slack ≤ n*(m-n)) :
    n/2 + slack ≤ u := by
  nlinarith [mul_le_mul_of_nonneg_right degree hu,
    mul_le_mul_of_nonneg_right neighbors hn]

/-- Claim 3 with a whole-vertex allowance d and an explicit margin of 6d. -/
theorem far_neighborhood_lower {m n u p N B d t : ℝ}
    (hm : 0 ≤ m) (hd : 1 ≤ d) (gap : n + 6*d ≤ m)
    (base : 2*m ≤ N) (budget : 2*m+B-d ≤ N)
    (fraction : 1/2 ≤ t ∧ t ≤ 1) (first : u = n*t+d) (second : p ≤ n+2*d) :
    max (n*(1-t)) (2*m*(1-t)^2+B) ≤ N-1-u-p := by
  apply max_le
  · linarith
  · have shape : 1 ≤ 3*t-2*t^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr fraction.1) (sub_nonneg.mpr fraction.2)]
    have cost := mul_le_mul_of_nonneg_left shape hm
    have nt := mul_nonneg (show 0 ≤ m-n by linarith) (show 0 ≤ t by linarith [fraction.1])
    nlinarith

end OMA

/- Joining copies on two parts and restoring isolated vertices -/

namespace OMA
open SimpleGraph

theorem join_copies {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (P : Set W)
    (f : (H.induce P).Copy G) (g : (H.induce Pᶜ).Copy G)
    (apart : ∀ i j, f i ≠ g j)
    (cross : ∀ i j, H.Adj i.val j.val → G.Adj (f i) (g j)) : H ⊑ G := by
  classical
  let F (i : W) := if hi : i ∈ P then f ⟨i,hi⟩ else g ⟨i,hi⟩
  refine ⟨⟨⟨F, fun {i j} h => ?_⟩, ?_⟩⟩
  · by_cases hi : i ∈ P <;> by_cases hj : j ∈ P <;> simp only [F, hi, hj, ↓reduceDIte]
    · exact f.toHom.map_rel' h
    · exact cross _ _ h
    · exact (cross _ _ h.symm).symm
    · exact g.toHom.map_rel' h
  · intro i j e
    change F i = F j at e
    by_cases hi : i ∈ P <;> by_cases hj : j ∈ P <;> simp only [F, hi, hj, ↓reduceDIte] at e
    · exact congrArg Subtype.val (f.injective e)
    · exact False.elim (apart _ _ e)
    · exact False.elim (apart _ _ e.symm)
    · exact congrArg Subtype.val (g.injective e)

theorem join_across_complete {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (P : Set W) (A B : Set V) (cross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (left : H.induce P ⊑ G.induce A) (right : H.induce Pᶜ ⊑ G.induce B) :
    H ⊑ G := by
  obtain ⟨f⟩ := left
  obtain ⟨g⟩ := right
  exact join_copies G H P ((Copy.induce G A).comp f) ((Copy.induce G B).comp g)
    (fun i j => (cross _ (f i).prop _ (g j).prop).ne)
    (fun i j _ => cross _ (f i).prop _ (g j).prop)

theorem restore_isolates {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (H : SimpleGraph W) (size : Fintype.card W ≤ Fintype.card V)
    (h : H.induce H.support ⊑ G) : H ⊑ G := by
  classical
  obtain ⟨f⟩ := h
  let R : Set V := Set.range f
  have hr : Fintype.card R = Fintype.card H.support :=
    (Fintype.card_congr (Equiv.ofInjective f f.injective)).symm
  obtain ⟨g⟩ : Nonempty ((↥H.supportᶜ) ↪ (↥Rᶜ)) := Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, hr]
    omega)
  let c : (H.induce H.supportᶜ).Copy G :=
    ⟨⟨fun i => (g i).val, fun {i _} e => False.elim (i.prop (show H.Adj _ _ from e).mem_support_left)⟩,
      fun {_ _} h => g.injective (Subtype.ext h)⟩
  exact join_copies G H H.support f c
    (fun i j e => (g j).prop (show (g j).val ∈ R from ⟨i,e⟩))
    (fun _ j e => False.elim (j.prop e.mem_support_right))

end OMA

namespace OMA
open SimpleGraph Finset

private def BlueSet {V : Type*} (G : SimpleGraph V) (S : Finset V) (r : ℕ) : Prop :=
  ∃ A ⊆ S, A.card = r ∧ Gᶜ.IsClique (A : Set V)

private theorem blue_of_path_free {V : Type*} (G : SimpleGraph V) (S : Finset V) (h r : ℕ)
    (free : ¬pathGraph h ⊑ G.induce (S : Set V)) (size : (h+1)*r ≤ S.card) :
    BlueSet G S r := by
  classical
  let H := (⊤ : SimpleGraph (Fin r))
  have bound : Fintype.card (Fin r) + h*r ≤ Fintype.card S := by
    simpa [Nat.add_mul, Nat.add_comm] using size
  obtain ⟨f⟩ := embed_colored (G.induce (↑S : Set V)) H (fun i => i.val) r h
    (fun i => i.isLt.le) (fun e h => e.ne (Fin.ext h)) bound free
  let g : Fin r ↪ V := ⟨fun i => (f i).val, fun _ _ e => f.injective (Subtype.ext e)⟩
  refine ⟨univ.map g, ?_, by simp, ?_⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := mem_map.mp hx
    exact (f i).prop
  · intro i hi j hj ne
    obtain ⟨a,_,rfl⟩ := mem_map.mp hi
    obtain ⟨b,_,rfl⟩ := mem_map.mp hj
    have e := f.toHom.map_rel' (show H.Adj a b from fun eq => ne (congrArg g eq))
    exact ⟨ne,e.2⟩

private theorem dense_independent {V : Type*} (G : SimpleGraph V) {k : ℕ} (hk : 5 ≤ k)
    (free : ¬cycleGraph k ⊑ G) (t : ℕ) (ht : 0 < t) (r : ℕ) (S : Finset V)
    (small : r ≤ t*t) (size : (4*k+4)*t*r ≤ S.card) : BlueSet G S r := by
  classical
  let L := 2*k+1
  let C := 4*k+4
  change C*t*r ≤ S.card at size
  induction r using Nat.strong_induction_on generalizing S with
  | h r ih =>
    by_cases z : r = 0
    · subst r; exact ⟨∅, by simp, rfl, by simp⟩
    have cpos : 0 < C*t := by dsimp [C]; positivity
    obtain ⟨v,hv⟩ := card_pos.mp ((Nat.mul_pos cpos (Nat.pos_of_ne_zero z)).trans_le size)
    let R := S.filter (G.Adj v)
    let P := S.filter (· ∈ secondShell G v)
    have rsub : (↑R : Set V) ⊆ G.neighborSet v := fun _ h => (mem_filter.mp h).2
    have psub : (↑P : Set V) ⊆ secondShell G v := fun _ h => (mem_filter.mp h).2
    have redR : ¬pathGraph (k-1) ⊑ G.induce (R : Set V) := fun p => free
      (cycle_of_neighborhood_path G v k (by omega) (p.trans ⟨(G.induceHomOfLE rsub).toCopy⟩))
    have redP : ¬pathGraph (2*k) ⊑ G.induce (P : Set V) := fun p => free
      (cycle_of_second_shell_path G v k hk (p.trans ⟨(G.induceHomOfLE psub).toCopy⟩))
    have pickR (a : ℕ) (h : L*a ≤ R.card) : BlueSet G R a := blue_of_path_free G R _ _ redR
      ((Nat.mul_le_mul_right a (show k-1+1 ≤ L by dsimp [L]; omega)).trans h)
    have lift {A : Finset V} (sub : A ⊆ S) : BlueSet G A r → BlueSet G S r :=
      fun ⟨I,hi,sz,cl⟩ => ⟨I,hi.trans sub,sz,cl⟩
    by_cases bigR : L*r ≤ R.card
    · exact lift (filter_subset ..) (pickR r bigR)
    by_cases bigP : L*r ≤ P.card
    · exact lift (filter_subset ..) (blue_of_path_free G P _ _ redP bigP)
    have peel (A D : Finset V) (a : ℕ) (ain : A ⊆ S) (sz : A.card = a)
        (cl : Gᶜ.IsClique (A : Set V)) (ha : a ≤ r) (hap : 0 < a)
        (price : D.card ≤ C*t*a) (cross : ∀ i ∈ A, ∀ j ∈ S \ D, Gᶜ.Adj i j) : BlueSet G S r := by
      have hsum := card_le_card_sdiff_add_card (s := S) (t := D)
      have budget := Nat.mul_sub (C*t) r a
      obtain ⟨B, bsub, bsz, bcl⟩ := ih (r-a) (by omega) (S \ D) (by omega) (by omega)
      have dj : Disjoint A B := Finset.disjoint_left.mpr fun {_} hi hj => (cross _ hi _ (bsub hj)).ne rfl
      refine ⟨A ∪ B, union_subset ain (bsub.trans sdiff_subset), ?_, ?_⟩
      · rw [card_union_of_disjoint dj,sz,bsz]; omega
      · intro i hi j hj ne
        rcases mem_union.mp hi with hi|hi <;> rcases mem_union.mp hj with hj|hj
        · exact cl hi hj ne
        · exact cross _ hi _ (bsub hj)
        · exact (cross _ hj _ (bsub hi)).symm
        · exact bcl hi hj ne
    by_cases rich : L*t ≤ R.card
    · have tr : t ≤ r := by
        by_contra! h
        exact bigR ((Nat.mul_le_mul_left L h.le).trans rich)
      obtain ⟨A,sub,sz,cl⟩ := pickR t rich
      let D := insert v (R ∪ P)
      have cnt : D.card ≤ R.card+P.card+1 :=
        (card_insert_le ..).trans (Nat.add_le_add_right (card_union_le ..) _)
      have price : D.card ≤ C*t*t := by
        have m := Nat.mul_le_mul_left C small
        have two : L + L + 1 ≤ C := by dsimp [L,C]; omega
        have hh := Nat.mul_le_mul_right r two
        rw [Nat.add_mul, Nat.add_mul, one_mul] at hh
        rw [← Nat.mul_assoc] at m
        omega
      apply peel A D t (sub.trans (filter_subset ..)) sz cl tr ht price
      intro i hi j hj
      have vi := (mem_filter.mp (sub hi)).2
      obtain ⟨js,jn⟩ := mem_sdiff.mp hj
      have eq : j ≠ v := fun e => jn (e ▸ mem_insert_self ..)
      have nr : j ∉ R := fun h => jn (mem_insert_of_mem (mem_union_left _ h))
      have np : j ∉ P := fun h => jn (mem_insert_of_mem (mem_union_right _ h))
      exact ⟨fun e => nr (e ▸ sub hi), fun e => np (mem_filter.mpr ⟨js,eq,
        fun h => nr (mem_filter.mpr ⟨js,h⟩),i,vi,e⟩)⟩
    · have cost : (insert v R).card ≤ C*t*1 := by
        have le := Nat.mul_le_mul_right t (show L ≤ C by dsimp [L,C]; omega)
        have := card_insert_le v R
        omega
      apply peel {v} (insert v R) 1 (by simpa using hv) (by simp) (by simp) (by omega)
        (by decide) cost
      intro i hi j hj
      obtain rfl := mem_singleton.mp hi
      obtain ⟨js,jn⟩ := mem_sdiff.mp hj
      exact ⟨fun e => jn (e ▸ mem_insert_self ..),
        fun e => jn (mem_insert_of_mem (mem_filter.mpr ⟨js,e⟩))⟩

/-- A uniform three-halves exponent suffices for the three-fifths cutoff,
for odd and even cycles of length at least five. -/
theorem dense_cycle_clique (k r t : ℕ) (hk : 5 ≤ k) (ht : 0 < t) (hr : r ≤ t*t) :
    graphRamsey (cycleGraph k) (completeGraph (Fin r)) ≤ (4*k+4)*t*r := by
  classical
  apply Nat.sInf_le
  intro G
  by_cases h : cycleGraph k ⊑ G
  · exact Or.inl h
  · obtain ⟨A,_,sz,cl⟩ := dense_independent G hk h t ht r univ hr (by simp)
    obtain ⟨f⟩ : Nonempty (Fin r ↪ A) := Function.Embedding.nonempty_of_card_le (by simp [sz])
    let g := f.trans (Function.Embedding.subtype _)
    exact Or.inr ⟨⟨⟨g, fun {i j} hij => cl (f i).prop (f j).prop (g.injective.ne hij)⟩,g.injective⟩⟩

end OMA

namespace OMA
open SimpleGraph Finset

/-- The whole dense-target branch of Claim 1, in an integer-only form.
The host has just m vertices. Isolated vertices in H are allowed. -/
theorem dense_target {W : Type*} [Fintype W] (H : SimpleGraph W) {k m : ℕ} (hk : 5 ≤ k)
    (large : (2*(4*k+4))^10 ≤ m) (small : (Fintype.card W)^5 ≤ m^3) :
    graphRamsey (cycleGraph k) H ≤ m := by
  classical
  let n := Fintype.card W
  let C := 4*k+4
  let t := n.sqrt+1
  have nt : n ≤ t*t := (Nat.lt_succ_sqrt n).le
  have space : C*t*n ≤ m := by
    by_cases z : n = 0
    · simp [z]
    have pos := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero z)
    have tt : t^2 ≤ 4*n := by
      have bound : t ≤ 2*n.sqrt := by dsimp [t]; omega
      calc
        _ ≤ (2*n.sqrt)^2 := Nat.pow_le_pow_left bound 2
        _ = 4*n.sqrt^2 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.sqrt_le' n)
    have cmp : (C*t*n)^2 ≤ m^2 := calc
      _ = C^2*t^2*n^2 := by ring
      _ ≤ C^2*(4*n)*n^2 := by gcongr
      _ = (2*C)^2*n^3 := by ring
      _ ≤ _ := dense_cutoff large small
    exact le_of_not_gt fun h => (Nat.pow_lt_pow_left h (by decide : 2 ≠ 0)).not_ge cmp
  apply Nat.sInf_le
  intro G
  by_cases h : cycleGraph k ⊑ G
  · exact Or.inl h
  · obtain ⟨A,_,sz,cl⟩ := dense_independent G hk h t (Nat.succ_pos _) n univ nt
      (by simpa only [card_univ, Fintype.card_fin] using space)
    obtain ⟨f⟩ : Nonempty (W ↪ A) := Function.Embedding.nonempty_of_card_le (by simp [sz,n])
    let g := f.trans (Function.Embedding.subtype _)
    exact Or.inr ⟨⟨⟨g, fun {i j} hij => cl (f i).prop (f j).prop (g.injective.ne hij.ne)⟩,g.injective⟩⟩

end OMA

/- Finite coloring statements sufficient for Erdős 570 -/

namespace OMA
open SimpleGraph Filter

theorem vertices_le_twice_edges {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hn : ∀ v, 0 < H.degree v) :
    Fintype.card W ≤ 2 * H.edgeSet.ncard := by
  classical
  calc
    Fintype.card W = ∑ _ : W, 1 := by simp
    _ ≤ ∑ v : W, H.degree v := Finset.sum_le_sum fun v _ => hn v
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
    _ = _ := by rw [Set.ncard_eq_toFinset_card']; rfl

/-- A finite host of the specified order forces one of the two copies. -/
def Forces (k m N : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
    (∀ v, 0 < H.degree v) → H.edgeSet.ncard = m → Fintype.card W ≤ 2*m →
    ∀ G : SimpleGraph (Fin N), cycleGraph k ⊑ G ∨ H ⊑ Gᶜ

private theorem bound_of_forces {k m N : ℕ} (h : Forces k m N)
    {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hn : ∀ v, 0 < H.degree v) (he : H.edgeSet.ncard = m) :
    graphRamsey (cycleGraph k) H ≤ N :=
  Nat.sInf_le (h W H hn he (he ▸ vertices_le_twice_edges H hn))

end OMA

namespace OMA
open SimpleGraph Filter

/-- The large-order bound for each fixed cycle length at least five. -/
def LargeOrderBound (k : ℕ) : Prop :=
  ∃ M, ∀ m ≥ M, ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
    (∀ v, 0 < H.degree v) → H.edgeSet.ncard = m → m^3 < (Fintype.card W)^5 →
    graphRamsey (cycleGraph k) H ≤ 2*m+(k-1)/2

end OMA

/- Extending a partial copy in a square-free host -/

namespace OMA
open SimpleGraph
open scoped BigOperators

/-- Distinct vertices in a square-free graph have at most one common neighbor. -/
theorem square_common_unique {V : Type*} {G : SimpleGraph V}
    (free : ¬ cycleGraph 4 ⊑ G) {w x a b : V} (wx : w ≠ x)
    (wa : G.Adj w a) (wb : G.Adj w b) (xa : G.Adj x a) (xb : G.Adj x b) : a = b := by
  by_contra ab
  apply free
  let f : Fin 4 → V := ![w,a,x,b]
  have hne := wa.ne
  have hne' := wb.ne
  have hne'' := xa.ne
  have hne''' := xb.ne
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | exact wa | exact wa.symm | exact wb | exact wb.symm | exact xa | exact xa.symm | exact xb | exact xb.symm | exact False.elim ((by decide : ¬ _) h)
  · intro i j
    change f i = f j → i = j
    fin_cases i <;> fin_cases j <;> simp_all [f, ne_comm]

/-- A vertex whose incident target edges all have the required color extends a copy. -/
theorem small_extend {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (v : W) (f : (H.induce {v}ᶜ).Copy G) (z : V)
    (fresh : ∀ i, z ≠ f i) (good : ∀ i, H.Adj v i.val → G.Adj z (f i)) : H ⊑ G := by
  let c : (H.induce {v}).Copy G :=
    ⟨⟨fun _ => z, fun {a b} h => False.elim (h.ne (Subsingleton.elim a b))⟩,
      fun {_ _} _ => Subsingleton.elim ..⟩
  apply join_copies G H {v} c f
  · exact fun _ i => fresh i
  · intro i j h
    exact good j (by simpa only [show i.val = v from i.prop] using h)

/-- Reserve at most d+2 vertices before embedding the deletion of a degree-d vertex.
Every copy on the remaining vertices extends when the red host has no square. -/
theorem square_reserve {V W : Type*} [Fintype V] [Nonempty V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (v : W)
    (free : ¬ cycleGraph 4 ⊑ G) :
    ∃ S : Finset V, S.card ≤ H.degree v + 2 ∧
      (H.induce {v}ᶜ ⊑ Gᶜ.induce (↑S : Set V)ᶜ → H ⊑ Gᶜ) := by
  classical
  let w : V := Classical.arbitrary V
  let d := H.degree v
  by_cases h : d + 1 ≤ (G.neighborFinset w).card
  · obtain ⟨Y,hY,cardY⟩ := Finset.exists_subset_card_eq h
    let S := insert w Y
    refine ⟨S, (Finset.card_insert_le ..).trans (by omega), ?_⟩
    rintro ⟨f⟩
    let g := (Copy.induce Gᶜ (↑S : Set V)ᶜ).comp f
    have out (i) : g i ∉ S := (f i).prop
    have wy {y} (hy : y ∈ Y) : G.Adj w y := (G.mem_neighborFinset _ _).mp (hY hy)
    let idx (i : ↥(H.neighborFinset v)) : ↥({v}ᶜ : Set W) :=
      ⟨i.val, ((H.mem_neighborFinset _ _).mp i.prop).ne.symm⟩
    have pick : ∃ y ∈ Y, ∀ i : ↥(H.neighborFinset v), ¬G.Adj (g (idx i)) y := by
      by_contra! blocked
      choose p hp using fun y : ↥Y => blocked y.val y.prop
      have inj : Function.Injective p := by
        intro a b eq
        apply Subtype.ext
        exact square_common_unique (w := w) (x := g (idx (p a))) free (fun e => out (idx (p a)) (e ▸ Finset.mem_insert_self ..))
          (wy a.prop) (wy b.prop) (hp a) (eq ▸ hp b)
      have := Fintype.card_le_of_injective p inj
      simp only [Fintype.card_coe, cardY, card_neighborFinset_eq_degree] at this
      omega
    obtain ⟨y,hy,ok⟩ := pick
    have fresh (i) : y ≠ g i := fun e => out i (e ▸ Finset.mem_insert_of_mem hy)
    apply small_extend v g y fresh
    intro i hi
    exact ⟨fresh i, fun bad => ok ⟨i.val,(H.mem_neighborFinset _ _).mpr hi⟩ bad.symm⟩
  · let S := insert w (G.neighborFinset w)
    refine ⟨S, (Finset.card_insert_le ..).trans (by omega), ?_⟩
    rintro ⟨f⟩
    let g := (Copy.induce Gᶜ (↑S : Set V)ᶜ).comp f
    have out (i) : g i ∉ S := (f i).prop
    have fresh (i) : w ≠ g i := fun e => out i (e ▸ Finset.mem_insert_self ..)
    exact small_extend v g w fresh (fun i _ => ⟨fresh i, fun bad =>
      out i (Finset.mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr bad))⟩)

end OMA

/- Deleting an isolated edge and embedding a star in a square-free coloring -/

namespace OMA
open SimpleGraph

theorem small_blue_edge {V : Type} [Fintype V] (G : SimpleGraph V)
    (big : 4 ≤ Fintype.card V) (free : ¬ cycleGraph 4 ⊑ G) :
    ∃ x y, Gᶜ.Adj x y := by
  obtain ⟨a⟩ : Nonempty (Fin 4 ↪ V) := Function.Embedding.nonempty_of_card_le (by simpa)
  by_contra! h
  exact free ⟨⟨⟨a, fun {i j} e => by
    by_contra no
    exact h _ _ ⟨a.injective.ne e.ne,no⟩⟩, a.injective⟩⟩

theorem square_star_degree {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel Gᶜ.Adj]
    {d : ℕ} (hd : 2 ≤ d) (size : 2*d+1 ≤ Fintype.card V)
    (free : ¬ cycleGraph 4 ⊑ G) : ∃ w, d ≤ Gᶜ.degree w := by
  classical
  obtain ⟨a,b,ab⟩ := small_blue_edge G (by omega) free
  by_contra! low
  have ia : (G.neighborFinset a ∩ G.neighborFinset b).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro x y hx hy
    simp only [Finset.mem_inter, mem_neighborFinset] at hx hy
    exact square_common_unique free ab.ne hx.1 hy.1 hx.2 hy.2
  have away : G.neighborFinset a ∪ G.neighborFinset b ⊆ Finset.univ.erase a := by
    intro x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    rintro rfl
    simp only [Finset.mem_union, mem_neighborFinset] at hx
    exact hx.elim (fun h => h.ne rfl) (fun bad => ab.2 bad.symm)
  have n := Finset.card_le_card away
  have c := Finset.card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
  have la := low a
  have lb := low b
  rw [G.degree_compl] at la lb
  simp only [card_neighborFinset_eq_degree] at c
  simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at n
  omega

theorem small_star_copy {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (H : SimpleGraph W) [DecidableRel H.Adj] (v : W)
    (pos : ∀ i, 0 < H.degree i) (star : ∀ i j, H.Adj i j → i = v ∨ j = v)
    (hd : 2 ≤ H.degree v) (size : 2 * H.degree v + 1 ≤ Fintype.card V)
    (free : ¬ cycleGraph 4 ⊑ G) : H ⊑ Gᶜ := by
  classical
  obtain ⟨x,hx⟩ := square_star_degree G hd size free
  have sub : ({v}ᶜ : Set W) ⊆ H.neighborSet v := by
    intro i hi
    obtain ⟨j,e⟩ := (H.degree_pos_iff_mem_support i).mp (pos i)
    rcases star i j e with h|rfl
    · exact False.elim (hi h)
    · exact e.symm
  have count := Fintype.card_le_of_injective (Set.inclusion sub) (Set.inclusion_injective sub)
  obtain ⟨f⟩ : Nonempty (↥({v}ᶜ : Set W) ↪ Gᶜ.neighborSet x) :=
    Function.Embedding.nonempty_of_card_le (by rw [card_neighborSet_eq_degree] at count ⊢; exact count.trans hx)
  let g := f.trans (Function.Embedding.subtype _)
  let c : (H.induce {v}ᶜ).Copy Gᶜ := ⟨⟨g, fun {i j} h =>
    False.elim ((star _ _ h).elim i.prop j.prop)⟩, g.injective⟩
  exact small_extend v c x (fun i => (show Gᶜ.Adj x (c i) from (f i).prop).ne) (fun i _ => (f i).prop)

theorem small_remove_pair {V W : Type} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    {a b : W} (ab : H.Adj a b) (ha : H.degree a = 1) (hb : H.degree b = 1)
    {x y : V} (xy : Gᶜ.Adj x y) :
    let P : Set W := {a,b}
    let Q : Set V := {x,y}
    (H.induce Pᶜ).edgeFinset.card = H.edgeFinset.card - 1 ∧
    (H.induce Pᶜ ⊑ Gᶜ.induce Qᶜ → H ⊑ Gᶜ) := by
  classical
  dsimp only
  let P : Set W := {a,b}
  let Q : Set V := {x,y}
  have uniq {i j : W} (d : H.degree i = 1) {k : W} (u : H.Adj i j) (t : H.Adj i k) :
      j = k := (degree_eq_one_iff_existsUnique_adj.mp d).unique u t
  have cross {i j : W} (ip : i ∈ P) (jp : j ∈ Pᶜ) (e : H.Adj i j) : False := by
    rcases ip with rfl|rfl
    · exact jp (Or.inr (uniq ha e ab))
    · exact jp (Or.inl (uniq hb e ab.symm))
  constructor
  · let D := H.deleteIncidenceSet a
    have eq : (H.induce Pᶜ).edgeFinset.card = (D.induce Pᶜ).edgeFinset.card := by
      rw [edgeFinset_card,edgeFinset_card,← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card]
      exact congrArg (fun K : SimpleGraph ↥Pᶜ => Nat.card K.edgeSet)
        (H.induce_deleteIncidenceSet_of_notMem (s := Pᶜ) (x := a) (by simp [P])).symm
    rw [eq, card_edgeFinset_induce_of_support_subset, H.card_edgeFinset_deleteIncidenceSet, ha]
    rintro i ⟨j,e⟩ ip
    change (H.deleteIncidenceSet a).Adj i j at e
    rw [deleteIncidenceSet_adj] at e
    rcases ip with rfl|rfl
    · exact e.2.1 rfl
    · exact e.2.2 (uniq hb e.1 ab.symm)
  · rintro ⟨g⟩
    let f (i : P) : V := if i.val = a then x else y
    have inj : Function.Injective f := by
      intro i j eq
      apply Subtype.ext
      rcases i.prop with hi|hi <;> rcases j.prop with hj|hj <;>
        simp_all [f,Set.mem_singleton_iff,ab.ne,xy.ne,xy.ne.symm]
    let c : (H.induce P).Copy Gᶜ := ⟨⟨f, fun {i j} h => by
      have ne := inj.ne h.ne
      dsimp only [f] at ne ⊢
      split_ifs at ne ⊢ <;> first | contradiction | exact xy | exact xy.symm⟩, inj⟩
    apply join_copies Gᶜ H P c ((Copy.induce Gᶜ Qᶜ).comp g)
    · intro i j eq
      apply (g j).prop
      have h : f i ∈ Q := by dsimp [f,Q]; split <;> simp
      exact (show f i = (g j).val from eq) ▸ h
    · intro i j e
      exact (cross i.prop j.prop e).elim

end OMA

/- Finite square Ramsey cases on five and seven vertices

Each branch tests one edge color. At each leaf the kernel checks distinctness and
the colors of the edges of the reported square, pair of disjoint edges, or triangle
with a pendant edge. The verification theorem covers both outcomes of every test.
-/

namespace OMA
open SimpleGraph

private abbrev Quad (n : ℕ) := Fin n × Fin n × Fin n × Fin n

private def distinctQ (q : Quad n) : Bool :=
  let (a,b,c,d) := q
  decide (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)

private def sqB (col : Fin n → Fin n → Bool) (q : Quad n) : Bool :=
  let (a,b,c,d) := q
  distinctQ q && col a b && col b c && col c d && col d a

private def pairB (col : Fin n → Fin n → Bool) (q : Quad n) : Bool :=
  let (a,b,c,d) := q
  distinctQ q && !col a b && !col c d

private def pawB (col : Fin n → Fin n → Bool) (q : Quad n) : Bool :=
  let (a,b,c,d) := q
  distinctQ q && !col a b && !col b c && !col a c && !col c d

private def symCol (col : Fin n → Fin n → Bool) (i j : Fin n) := col (min i j) (max i j)

private inductive ProofTree (n : ℕ) where
  | r (q : Quad n)
  | b (q : Quad n)
  | fork (i j : Fin n) (yes no : ProofTree n)

private def key (i j : Fin n) := (min i j).val * n + (max i j).val

private def verify (paw : Bool) (t : ProofTree n) (r b : List ℕ) : Bool :=
  match t with
  | .r q => sqB (fun i j => r.contains (key i j)) q
  | .b q =>
    let col := fun i j => !(b.contains (key i j))
    if paw then pawB col q else pairB col q
  | .fork i j yes no =>
    verify paw yes (key i j :: r) b && verify paw no r (key i j :: b)

private theorem verified {paw : Bool} (t : ProofTree n) (r b : List ℕ) (c : ℕ → Bool)
    (hr : ∀ x ∈ r, c x = true) (hb : ∀ x ∈ b, c x = false)
    (h : verify paw t r b = true) :
    (∃ q : Quad n, sqB (fun i j => c (key i j)) q = true) ∨
    (∃ q : Quad n, (if paw then pawB else pairB) (fun i j => c (key i j)) q = true) := by
  induction t generalizing r b with
  | r q =>
    left
    refine ⟨q,?_⟩
    rcases q with ⟨i,j,k,l⟩
    simp only [verify,sqB,Bool.and_eq_true,List.contains_iff_mem] at h ⊢
    exact ⟨⟨⟨⟨h.1.1.1.1,hr _ h.1.1.1.2⟩,hr _ h.1.1.2⟩,hr _ h.1.2⟩,hr _ h.2⟩
  | b q =>
    right
    refine ⟨q,?_⟩
    rcases q with ⟨i,j,k,l⟩
    cases paw <;> simp only [verify,pairB,pawB,Bool.false_eq_true,if_false,if_true,
      Bool.and_eq_true,Bool.not_not,List.contains_iff_mem,Bool.not_eq_true'] at h ⊢
    · exact ⟨⟨h.1.1,hb _ h.1.2⟩,hb _ h.2⟩
    · exact ⟨⟨⟨⟨h.1.1.1.1,hb _ h.1.1.1.2⟩,hb _ h.1.1.2⟩,hb _ h.1.2⟩,hb _ h.2⟩
  | fork i j yes no iy ino =>
    simp only [verify,Bool.and_eq_true] at h
    obtain ⟨hy,hn⟩ := h
    cases col : c (key i j) with
    | false => exact ino _ _ hr (by simpa [col] using hb) hn
    | true => exact iy _ _ (by simpa [col] using hr) hb hy

private def colors {n : ℕ} (c : Fin n → Fin n → Bool) (x : ℕ) : Bool :=
  if h : 0 < n then c ⟨x / n % n,Nat.mod_lt _ h⟩ ⟨x % n,Nat.mod_lt _ h⟩ else false

private theorem colors_key (c : Fin n → Fin n → Bool) (i j : Fin n) :
    colors c (key i j) = symCol c i j := by
  have hn := Nat.zero_lt_of_lt i.isLt
  let a := min i j
  let b := max i j
  have div : (a.val * n + b.val) / n = a.val := by
    rw [Nat.mul_comm a.val n,Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt, Nat.add_zero]
  have mod : (a.val * n + b.val) % n = b.val := by simp [Nat.mod_eq_of_lt b.isLt]
  dsimp only [colors,key,symCol]
  rw [dif_pos hn]
  change c ⟨((a.val*n+b.val)/n)%n,_⟩ ⟨(a.val*n+b.val)%n,_⟩ = c a b
  congr 1 <;> apply Fin.ext
  · simp only [div,Nat.mod_eq_of_lt a.isLt]
  · exact mod

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def pairTree : ProofTree 5 :=
  (.fork 0 1 (.fork 0 2 (.fork 0 3 (.fork 1 2 (.fork 1 3 (.r ⟨3,1,2,0⟩) (.fork 0 4 (.fork 2 4 (.r ⟨4,2,1,0⟩) (.b ⟨4,2,3,1⟩)) (.b ⟨3,1,4,0⟩))) (.fork 0 4 (.fork 3 4 (.fork 1 3 (.r ⟨4,3,1,0⟩) (.fork 2 4 (.r ⟨3,4,2,0⟩) (.b ⟨4,2,3,1⟩))) (.b ⟨4,3,2,1⟩)) (.b ⟨2,1,4,0⟩))) (.fork 1 2 (.fork 1 4 (.fork 2 4 (.r ⟨2,4,1,0⟩) (.b ⟨4,2,3,0⟩)) (.b ⟨4,1,3,0⟩)) (.b ⟨2,1,3,0⟩))) (.fork 1 3 (.fork 1 4 (.fork 3 4 (.fork 0 3 (.r ⟨3,4,1,0⟩) (.fork 1 2 (.fork 2 4 (.r ⟨3,4,2,1⟩) (.b ⟨4,2,3,0⟩)) (.b ⟨2,1,3,0⟩))) (.b ⟨4,3,2,0⟩)) (.b ⟨4,1,2,0⟩)) (.b ⟨3,1,2,0⟩))) (.fork 2 3 (.fork 2 4 (.fork 3 4 (.fork 0 2 (.fork 0 3 (.r ⟨3,4,2,0⟩) (.fork 1 2 (.fork 1 4 (.r ⟨4,3,2,1⟩) (.b ⟨4,1,3,0⟩)) (.b ⟨2,1,3,0⟩))) (.fork 1 3 (.fork 1 4 (.r ⟨4,2,3,1⟩) (.b ⟨4,1,2,0⟩)) (.b ⟨3,1,2,0⟩))) (.b ⟨4,3,1,0⟩)) (.b ⟨4,2,1,0⟩)) (.b ⟨3,2,1,0⟩)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem pairCover (c : Fin 5 → Fin 5 → Bool) :
    (∃ q, sqB (symCol c) q = true) ∨ (∃ q, pairB (symCol c) q = true) := by
  have ok : verify false pairTree [] [] = true := by decide +kernel
  simpa only [colors_key,Bool.false_eq_true,if_false] using
    verified pairTree [] [] (colors c) (by simp) (by simp) ok

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def pawTree : ProofTree 7 :=
  (.fork 0 1 (.fork 2 3 (.fork 4 5 (.fork 0 2 (.fork 1 3 (.r ⟨2,3,1,0⟩) (.fork 1 6 (.fork 2 6 (.r ⟨2,6,1,0⟩) (.fork 3 6 (.fork 1 2 (.r ⟨6,3,2,1⟩) (.fork 1 4 (.fork 5 6 (.r ⟨6,5,4,1⟩) (.fork 2 5 (.fork 3 4 (.r ⟨6,3,4,1⟩) (.fork 1 5 (.r ⟨2,5,1,0⟩) (.fork 3 5 (.fork 0 5 (.r ⟨5,4,1,0⟩) (.fork 0 6 (.r ⟨6,3,2,0⟩) (.b ⟨6,0,5,1⟩))) (.b ⟨5,3,1,2⟩)))) (.b ⟨6,5,2,1⟩))) (.fork 2 4 (.fork 3 4 (.fork 2 5 (.r ⟨5,4,3,2⟩) (.fork 1 5 (.fork 5 6 (.r ⟨6,5,4,3⟩) (.b ⟨6,5,2,1⟩)) (.b ⟨5,2,1,3⟩))) (.b ⟨4,3,1,2⟩)) (.b ⟨4,2,1,3⟩)))) (.fork 3 4 (.fork 2 5 (.r ⟨5,4,3,2⟩) (.fork 5 6 (.fork 0 5 (.r ⟨5,6,1,0⟩) (.fork 0 3 (.fork 1 4 (.r ⟨3,4,1,0⟩) (.fork 2 4 (.r ⟨3,4,2,0⟩) (.fork 1 2 (.r ⟨3,2,1,0⟩) (.b ⟨4,2,1,3⟩)))) (.fork 3 5 (.fork 0 6 (.fork 1 5 (.r ⟨6,5,1,0⟩) (.fork 1 2 (.r ⟨6,1,2,0⟩) (.b ⟨2,1,5,0⟩))) (.b ⟨6,0,3,1⟩)) (.b ⟨5,0,3,1⟩)))) (.b ⟨5,2,6,3⟩))) (.fork 4 6 (.fork 1 4 (.fork 5 6 (.r ⟨6,5,4,1⟩) (.fork 3 5 (.fork 0 6 (.r ⟨6,4,1,0⟩) (.fork 0 3 (.fork 0 5 (.r ⟨5,4,1,0⟩) (.b ⟨5,0,6,2⟩)) (.b ⟨6,0,3,1⟩))) (.b ⟨6,5,3,1⟩))) (.b ⟨4,1,3,6⟩)) (.b ⟨6,4,3,1⟩))))) (.fork 3 6 (.fork 1 4 (.fork 1 5 (.fork 2 4 (.r ⟨2,4,1,0⟩) (.fork 0 4 (.r ⟨4,5,1,0⟩) (.fork 0 6 (.r ⟨6,3,2,0⟩) (.fork 4 6 (.fork 0 5 (.r ⟨5,4,1,0⟩) (.fork 5 6 (.r ⟨5,6,4,1⟩) (.b ⟨5,0,6,1⟩))) (.b ⟨4,0,6,1⟩))))) (.fork 5 6 (.fork 3 5 (.fork 2 5 (.r ⟨5,6,3,2⟩) (.fork 1 2 (.fork 2 4 (.r ⟨2,4,1,0⟩) (.fork 3 4 (.r ⟨4,3,2,1⟩) (.fork 2 6 (.r ⟨6,5,3,2⟩) (.fork 4 6 (.r ⟨6,4,5,3⟩) (.b ⟨4,2,6,1⟩))))) (.b ⟨5,2,1,3⟩))) (.b ⟨5,3,1,6⟩)) (.b ⟨6,5,1,3⟩))) (.fork 4 6 (.fork 3 4 (.fork 2 6 (.r ⟨6,4,3,2⟩) (.fork 1 2 (.fork 5 6 (.r ⟨6,5,4,3⟩) (.fork 1 5 (.fork 2 5 (.r ⟨2,5,1,0⟩) (.b ⟨5,2,6,1⟩)) (.b ⟨5,1,6,2⟩))) (.b ⟨6,2,1,3⟩))) (.b ⟨4,3,1,6⟩)) (.b ⟨6,4,1,3⟩))) (.fork 1 4 (.fork 3 5 (.fork 0 3 (.fork 3 4 (.r ⟨3,4,1,0⟩) (.b ⟨6,1,3,4⟩)) (.b ⟨6,1,3,0⟩)) (.b ⟨6,1,3,5⟩)) (.b ⟨6,3,1,4⟩))))) (.fork 0 6 (.fork 0 4 (.fork 1 5 (.r ⟨4,5,1,0⟩) (.fork 5 6 (.r ⟨6,5,4,0⟩) (.fork 1 6 (.fork 2 5 (.fork 1 4 (.r ⟨6,1,4,0⟩) (.fork 3 4 (.r ⟨5,4,3,2⟩) (.fork 1 3 (.fork 3 6 (.r ⟨6,3,1,0⟩) (.fork 4 6 (.r ⟨4,6,1,0⟩) (.b ⟨6,3,4,1⟩))) (.b ⟨4,3,1,5⟩)))) (.fork 1 2 (.fork 2 6 (.r ⟨6,2,1,0⟩) (.b ⟨6,5,2,0⟩)) (.b ⟨5,1,2,0⟩))) (.fork 2 5 (.fork 1 3 (.fork 1 2 (.fork 1 4 (.r ⟨4,5,2,1⟩) (.b ⟨6,5,1,4⟩)) (.b ⟨6,5,1,2⟩)) (.b ⟨6,5,1,3⟩)) (.b ⟨6,1,5,2⟩))))) (.fork 2 4 (.fork 3 5 (.r ⟨4,5,3,2⟩) (.fork 0 3 (.fork 1 2 (.r ⟨3,2,1,0⟩) (.fork 2 5 (.fork 2 6 (.r ⟨6,2,3,0⟩) (.fork 1 6 (.fork 1 3 (.r ⟨6,1,3,0⟩) (.fork 3 4 (.r ⟨5,4,3,2⟩) (.fork 1 4 (.fork 1 5 (.r ⟨5,2,4,1⟩) (.b ⟨5,3,1,2⟩)) (.b ⟨3,1,4,0⟩)))) (.b ⟨6,1,2,0⟩))) (.fork 1 5 (.fork 0 5 (.fork 5 6 (.r ⟨6,5,1,0⟩) (.fork 2 6 (.r ⟨6,2,3,0⟩) (.b ⟨6,5,2,0⟩))) (.b ⟨5,0,2,1⟩)) (.b ⟨5,1,2,0⟩)))) (.fork 0 5 (.fork 3 4 (.fork 2 5 (.r ⟨5,4,3,2⟩) (.fork 1 5 (.fork 5 6 (.r ⟨6,5,1,0⟩) (.fork 2 6 (.fork 3 6 (.r ⟨6,3,4,2⟩) (.b ⟨6,5,3,0⟩)) (.b ⟨6,5,2,0⟩))) (.fork 1 2 (.fork 1 3 (.r ⟨3,4,2,1⟩) (.b ⟨5,1,3,0⟩)) (.b ⟨5,1,2,0⟩)))) (.b ⟨4,3,0,2⟩)) (.b ⟨5,3,0,2⟩)))) (.fork 1 2 (.fork 0 3 (.r ⟨3,2,1,0⟩) (.b ⟨4,2,0,3⟩)) (.b ⟨4,0,2,1⟩)))) (.fork 2 6 (.fork 0 4 (.fork 0 5 (.fork 1 4 (.r ⟨5,4,1,0⟩) (.fork 1 6 (.fork 4 6 (.r ⟨4,6,1,0⟩) (.fork 1 3 (.r ⟨6,2,3,1⟩) (.fork 3 4 (.fork 0 3 (.r ⟨5,4,3,0⟩) (.fork 3 6 (.fork 2 4 (.r ⟨6,3,4,2⟩) (.fork 1 2 (.r ⟨6,3,2,1⟩) (.b ⟨4,1,2,0⟩))) (.b ⟨6,0,3,1⟩))) (.b ⟨3,1,4,6⟩)))) (.fork 4 6 (.fork 3 4 (.r ⟨6,4,3,2⟩) (.fork 1 3 (.fork 1 5 (.r ⟨4,5,1,0⟩) (.fork 5 6 (.r ⟨5,6,4,0⟩) (.b ⟨5,1,6,0⟩))) (.b ⟨4,3,1,6⟩))) (.b ⟨4,1,6,0⟩)))) (.fork 5 6 (.fork 2 5 (.fork 3 5 (.r ⟨6,5,3,2⟩) (.fork 0 3 (.fork 2 4 (.r ⟨4,2,3,0⟩) (.fork 3 4 (.r ⟨5,4,3,2⟩) (.fork 3 6 (.r ⟨5,6,3,2⟩) (.fork 4 6 (.r ⟨6,4,5,2⟩) (.b ⟨4,3,6,0⟩))))) (.b ⟨5,3,0,2⟩))) (.b ⟨5,2,0,6⟩)) (.b ⟨6,5,0,2⟩))) (.fork 4 6 (.fork 2 4 (.fork 3 6 (.r ⟨4,6,3,2⟩) (.fork 0 3 (.fork 5 6 (.r ⟨6,5,4,2⟩) (.fork 0 5 (.fork 3 5 (.r ⟨4,5,3,2⟩) (.b ⟨5,3,6,0⟩)) (.b ⟨6,5,0,2⟩))) (.b ⟨6,3,0,2⟩))) (.b ⟨4,2,0,6⟩)) (.b ⟨6,4,0,2⟩))) (.fork 4 6 (.fork 5 6 (.fork 1 6 (.fork 0 4 (.r ⟨4,6,1,0⟩) (.b ⟨6,2,0,4⟩)) (.b ⟨2,0,6,1⟩)) (.b ⟨2,0,6,5⟩)) (.b ⟨2,0,6,4⟩))))) (.fork 4 6 (.fork 0 4 (.fork 1 6 (.r ⟨4,6,1,0⟩) (.fork 1 5 (.fork 5 6 (.fork 1 4 (.r ⟨5,6,4,1⟩) (.fork 1 2 (.fork 3 5 (.r ⟨5,3,2,1⟩) (.fork 3 4 (.fork 2 6 (.r ⟨5,6,2,1⟩) (.fork 1 3 (.r ⟨4,3,1,0⟩) (.fork 3 6 (.fork 0 3 (.r ⟨3,2,1,0⟩) (.fork 0 5 (.r ⟨5,6,4,0⟩) (.b ⟨5,0,3,1⟩))) (.b ⟨3,1,6,2⟩)))) (.b ⟨5,3,4,1⟩))) (.fork 2 4 (.fork 2 6 (.fork 3 4 (.r ⟨6,4,3,2⟩) (.fork 1 3 (.fork 3 5 (.r ⟨6,5,3,2⟩) (.b ⟨5,3,4,1⟩)) (.b ⟨4,3,1,2⟩))) (.b ⟨6,2,1,4⟩)) (.b ⟨2,1,4,5⟩)))) (.fork 2 5 (.fork 1 3 (.r ⟨5,2,3,1⟩) (.fork 3 6 (.fork 0 3 (.r ⟨4,6,3,0⟩) (.fork 0 5 (.fork 2 4 (.r ⟨5,2,4,0⟩) (.fork 1 2 (.r ⟨5,2,1,0⟩) (.fork 1 4 (.r ⟨5,1,4,0⟩) (.b ⟨4,2,1,3⟩)))) (.fork 3 5 (.fork 0 6 (.fork 3 4 (.r ⟨6,3,4,0⟩) (.fork 1 4 (.r ⟨6,4,1,0⟩) (.b ⟨4,1,3,0⟩))) (.b ⟨5,0,6,1⟩)) (.b ⟨5,0,3,1⟩)))) (.b ⟨3,1,6,5⟩))) (.fork 2 6 (.fork 2 4 (.fork 3 6 (.r ⟨4,6,3,2⟩) (.fork 3 5 (.fork 0 6 (.r ⟨6,2,4,0⟩) (.fork 0 5 (.fork 0 3 (.r ⟨3,5,1,0⟩) (.b ⟨3,0,6,1⟩)) (.b ⟨5,0,6,1⟩))) (.b ⟨5,3,6,1⟩))) (.b ⟨4,2,5,6⟩)) (.b ⟨5,2,6,1⟩)))) (.fork 5 6 (.fork 1 4 (.fork 1 2 (.fork 3 4 (.r ⟨4,3,2,1⟩) (.fork 3 5 (.fork 2 4 (.r ⟨4,2,1,0⟩) (.fork 2 5 (.fork 2 6 (.r ⟨4,6,2,1⟩) (.fork 1 3 (.r ⟨3,5,2,1⟩) (.fork 3 6 (.r ⟨5,6,3,2⟩) (.b ⟨3,1,6,2⟩)))) (.b ⟨4,2,5,1⟩))) (.b ⟨4,3,5,1⟩))) (.fork 2 5 (.fork 2 6 (.fork 3 5 (.r ⟨6,5,3,2⟩) (.fork 1 3 (.fork 3 4 (.r ⟨4,3,1,0⟩) (.b ⟨4,3,5,1⟩)) (.b ⟨5,3,1,2⟩))) (.b ⟨6,2,1,5⟩)) (.b ⟨2,1,5,4⟩))) (.b ⟨5,4,1,6⟩)) (.b ⟨6,1,5,4⟩)))) (.fork 0 5 (.fork 2 4 (.fork 3 4 (.fork 2 6 (.r ⟨6,4,3,2⟩) (.fork 5 6 (.fork 2 5 (.r ⟨5,6,4,2⟩) (.fork 1 6 (.r ⟨5,6,1,0⟩) (.fork 1 2 (.fork 1 4 (.r ⟨4,3,2,1⟩) (.fork 1 5 (.fork 0 2 (.r ⟨5,1,2,0⟩) (.fork 0 6 (.r ⟨6,5,1,0⟩) (.b ⟨2,0,6,1⟩))) (.b ⟨5,1,4,0⟩))) (.b ⟨6,1,2,5⟩)))) (.fork 2 5 (.fork 1 2 (.r ⟨5,2,1,0⟩) (.fork 1 6 (.fork 3 5 (.r ⟨5,3,4,2⟩) (.fork 3 6 (.r ⟨4,6,3,2⟩) (.b ⟨5,3,6,2⟩))) (.b ⟨2,1,6,5⟩))) (.b ⟨6,2,5,4⟩)))) (.fork 3 5 (.fork 0 3 (.fork 1 3 (.r ⟨5,3,1,0⟩) (.fork 1 4 (.fork 0 2 (.r ⟨2,4,1,0⟩) (.fork 1 2 (.r ⟨3,2,1,0⟩) (.fork 1 5 (.r ⟨3,5,1,0⟩) (.fork 2 5 (.r ⟨5,2,3,0⟩) (.b ⟨5,1,2,0⟩))))) (.b ⟨3,1,4,0⟩))) (.b ⟨3,0,4,5⟩)) (.b ⟨5,3,4,0⟩))) (.fork 2 5 (.fork 0 2 (.fork 1 5 (.r ⟨2,5,1,0⟩) (.fork 1 4 (.fork 3 5 (.r ⟨5,3,2,0⟩) (.fork 3 4 (.fork 1 3 (.r ⟨2,3,1,0⟩) (.b ⟨3,1,5,4⟩)) (.b ⟨5,3,4,0⟩))) (.b ⟨5,1,4,0⟩))) (.b ⟨2,0,4,5⟩)) (.b ⟨5,2,4,0⟩))) (.fork 2 5 (.fork 3 5 (.fork 1 5 (.fork 0 2 (.r ⟨2,5,1,0⟩) (.b ⟨5,4,0,2⟩)) (.b ⟨4,0,5,1⟩)) (.b ⟨4,0,5,3⟩)) (.b ⟨4,0,5,2⟩)))) (.fork 5 6 (.fork 0 4 (.fork 2 4 (.fork 1 4 (.fork 3 4 (.fork 0 2 (.r ⟨2,4,1,0⟩) (.fork 0 3 (.r ⟨3,4,1,0⟩) (.fork 1 2 (.r ⟨4,2,1,0⟩) (.fork 0 5 (.fork 1 3 (.r ⟨4,3,1,0⟩) (.fork 1 6 (.r ⟨5,6,1,0⟩) (.fork 2 6 (.fork 3 6 (.r ⟨6,3,4,2⟩) (.b ⟨6,1,3,0⟩)) (.b ⟨6,1,2,0⟩)))) (.fork 2 5 (.fork 3 5 (.r ⟨5,3,4,2⟩) (.b ⟨5,3,0,2⟩)) (.b ⟨5,0,2,1⟩)))))) (.fork 3 5 (.fork 3 6 (.fork 0 3 (.r ⟨4,2,3,0⟩) (.fork 0 2 (.r ⟨2,4,1,0⟩) (.fork 2 5 (.r ⟨5,6,3,2⟩) (.fork 0 5 (.fork 0 6 (.r ⟨6,3,5,0⟩) (.fork 2 6 (.r ⟨6,5,3,2⟩) (.b ⟨6,2,0,3⟩))) (.b ⟨5,2,0,3⟩))))) (.b ⟨6,3,4,5⟩)) (.b ⟨5,3,4,6⟩))) (.fork 1 5 (.fork 1 6 (.fork 3 4 (.fork 1 2 (.r ⟨4,2,1,0⟩) (.fork 0 2 (.r ⟨4,3,2,0⟩) (.fork 0 5 (.r ⟨5,6,1,0⟩) (.fork 2 5 (.fork 2 6 (.r ⟨6,2,5,1⟩) (.fork 0 6 (.r ⟨6,5,1,0⟩) (.b ⟨6,0,2,1⟩))) (.b ⟨5,0,2,1⟩))))) (.fork 3 5 (.fork 3 6 (.r ⟨6,3,5,1⟩) (.b ⟨6,3,4,1⟩)) (.b ⟨5,3,4,1⟩))) (.b ⟨6,1,4,5⟩)) (.b ⟨5,1,4,6⟩))) (.fork 2 5 (.fork 2 6 (.fork 1 4 (.fork 3 5 (.r ⟨6,5,3,2⟩) (.fork 3 4 (.fork 0 3 (.r ⟨3,4,1,0⟩) (.fork 0 5 (.fork 0 2 (.r ⟨4,3,2,0⟩) (.fork 0 6 (.r ⟨6,2,5,0⟩) (.fork 3 6 (.r ⟨5,6,3,2⟩) (.b ⟨6,3,0,2⟩)))) (.b ⟨3,0,5,4⟩))) (.b ⟨5,3,4,2⟩))) (.fork 1 5 (.fork 1 6 (.r ⟨6,2,5,1⟩) (.b ⟨6,1,4,2⟩)) (.b ⟨5,1,4,2⟩))) (.b ⟨6,2,4,5⟩)) (.b ⟨5,2,4,6⟩))) (.fork 0 5 (.fork 0 6 (.fork 2 4 (.fork 3 4 (.fork 1 5 (.r ⟨6,5,1,0⟩) (.fork 1 4 (.fork 1 2 (.r ⟨4,3,2,1⟩) (.fork 2 5 (.fork 0 2 (.r ⟨2,4,1,0⟩) (.fork 2 6 (.r ⟨6,2,5,0⟩) (.fork 1 6 (.r ⟨5,6,1,0⟩) (.b ⟨6,1,2,0⟩)))) (.b ⟨2,1,5,4⟩))) (.b ⟨5,1,4,0⟩))) (.fork 3 5 (.fork 3 6 (.r ⟨6,3,5,0⟩) (.b ⟨6,3,4,0⟩)) (.b ⟨5,3,4,0⟩))) (.fork 2 5 (.fork 2 6 (.r ⟨6,2,5,0⟩) (.b ⟨6,2,4,0⟩)) (.b ⟨5,2,4,0⟩))) (.b ⟨6,0,4,5⟩)) (.b ⟨5,0,4,6⟩))) (.fork 0 4 (.fork 2 4 (.fork 1 4 (.fork 3 4 (.fork 0 5 (.fork 2 5 (.r ⟨5,2,4,0⟩) (.b ⟨6,4,5,2⟩)) (.b ⟨6,4,5,0⟩)) (.b ⟨6,5,4,3⟩)) (.b ⟨6,5,4,1⟩)) (.b ⟨6,5,4,2⟩)) (.b ⟨6,5,4,0⟩))))) (.fork 2 4 (.fork 3 5 (.fork 2 6 (.fork 0 2 (.fork 1 4 (.r ⟨2,4,1,0⟩) (.fork 1 6 (.r ⟨2,6,1,0⟩) (.fork 4 6 (.fork 1 3 (.fork 0 4 (.r ⟨4,6,2,0⟩) (.fork 0 5 (.r ⟨5,3,1,0⟩) (.fork 4 5 (.fork 5 6 (.r ⟨6,5,4,2⟩) (.fork 0 6 (.r ⟨6,4,2,0⟩) (.b ⟨5,0,6,1⟩))) (.b ⟨5,0,4,1⟩)))) (.fork 3 4 (.fork 3 6 (.r ⟨6,3,4,2⟩) (.b ⟨6,1,3,2⟩)) (.b ⟨4,1,3,2⟩))) (.fork 1 3 (.fork 4 5 (.fork 3 4 (.fork 0 4 (.r ⟨4,3,1,0⟩) (.b ⟨6,1,4,0⟩)) (.b ⟨6,1,4,3⟩)) (.b ⟨6,1,4,5⟩)) (.b ⟨6,4,1,3⟩))))) (.fork 0 3 (.fork 1 5 (.r ⟨3,5,1,0⟩) (.fork 1 2 (.fork 0 4 (.r ⟨4,2,1,0⟩) (.fork 0 5 (.fork 0 6 (.r ⟨6,2,1,0⟩) (.fork 4 6 (.fork 1 4 (.r ⟨4,6,2,1⟩) (.fork 1 3 (.r ⟨5,3,1,0⟩) (.fork 3 4 (.fork 4 5 (.r ⟨5,4,3,0⟩) (.b ⟨5,1,4,0⟩)) (.b ⟨3,1,4,0⟩)))) (.b ⟨6,4,0,2⟩))) (.fork 4 5 (.fork 2 5 (.fork 5 6 (.r ⟨6,5,4,2⟩) (.fork 0 6 (.r ⟨6,2,1,0⟩) (.b ⟨6,0,5,1⟩))) (.b ⟨2,0,5,1⟩)) (.b ⟨4,0,5,1⟩)))) (.fork 2 5 (.fork 1 3 (.fork 0 5 (.r ⟨5,3,1,0⟩) (.fork 4 5 (.fork 5 6 (.r ⟨6,5,4,2⟩) (.fork 0 6 (.fork 1 6 (.r ⟨6,1,3,0⟩) (.b ⟨6,1,5,0⟩)) (.b ⟨6,0,5,1⟩))) (.fork 0 4 (.fork 1 4 (.r ⟨4,1,3,0⟩) (.b ⟨4,1,5,0⟩)) (.b ⟨4,0,5,1⟩)))) (.b ⟨3,1,2,0⟩)) (.b ⟨5,1,2,0⟩)))) (.fork 0 4 (.fork 0 6 (.r ⟨6,2,4,0⟩) (.b ⟨3,2,0,6⟩)) (.b ⟨3,2,0,4⟩)))) (.fork 3 6 (.fork 0 2 (.fork 1 2 (.fork 0 4 (.r ⟨4,2,1,0⟩) (.fork 4 6 (.fork 0 6 (.r ⟨6,4,2,0⟩) (.fork 4 5 (.r ⟨6,4,5,3⟩) (.fork 0 5 (.fork 2 5 (.r ⟨5,2,1,0⟩) (.fork 5 6 (.fork 0 3 (.r ⟨5,6,3,0⟩) (.fork 3 4 (.r ⟨5,6,4,3⟩) (.b ⟨4,0,3,2⟩))) (.b ⟨5,2,6,0⟩))) (.b ⟨5,4,0,6⟩)))) (.fork 0 6 (.fork 0 5 (.r ⟨6,3,5,0⟩) (.fork 4 5 (.fork 1 4 (.r ⟨2,4,1,0⟩) (.fork 1 6 (.r ⟨6,1,2,0⟩) (.b ⟨6,1,4,0⟩))) (.b ⟨5,0,4,6⟩))) (.b ⟨4,0,6,2⟩)))) (.fork 1 6 (.fork 1 3 (.fork 1 5 (.r ⟨6,3,5,1⟩) (.fork 2 5 (.fork 0 3 (.r ⟨3,6,1,0⟩) (.fork 0 5 (.r ⟨5,3,1,0⟩) (.fork 0 6 (.r ⟨6,3,1,0⟩) (.fork 5 6 (.r ⟨6,5,3,1⟩) (.b ⟨6,0,5,1⟩))))) (.b ⟨5,1,2,3⟩))) (.b ⟨3,1,2,6⟩)) (.b ⟨6,1,2,3⟩))) (.fork 0 6 (.fork 0 3 (.fork 1 6 (.r ⟨3,6,1,0⟩) (.fork 1 2 (.fork 5 6 (.r ⟨6,5,3,0⟩) (.fork 2 5 (.fork 1 5 (.r ⟨3,5,1,0⟩) (.b ⟨5,1,6,2⟩)) (.b ⟨6,5,2,0⟩))) (.b ⟨6,1,2,0⟩))) (.b ⟨3,0,2,6⟩)) (.b ⟨6,0,2,3⟩))) (.fork 0 6 (.fork 1 6 (.fork 4 6 (.fork 0 2 (.r ⟨6,4,2,0⟩) (.b ⟨6,3,2,0⟩)) (.b ⟨3,2,6,4⟩)) (.b ⟨3,2,6,1⟩)) (.b ⟨3,2,6,0⟩)))) (.fork 2 5 (.fork 3 6 (.fork 0 3 (.fork 1 3 (.fork 0 6 (.r ⟨6,3,1,0⟩) (.fork 5 6 (.fork 0 5 (.r ⟨5,6,3,0⟩) (.fork 4 6 (.r ⟨5,6,4,2⟩) (.fork 0 4 (.fork 3 4 (.r ⟨4,3,1,0⟩) (.fork 4 5 (.fork 0 2 (.r ⟨4,5,2,0⟩) (.fork 2 6 (.r ⟨6,5,4,2⟩) (.b ⟨6,0,2,3⟩))) (.b ⟨4,3,5,0⟩))) (.b ⟨6,4,0,5⟩)))) (.fork 0 5 (.fork 0 4 (.r ⟨5,2,4,0⟩) (.fork 4 6 (.fork 1 5 (.r ⟨5,1,3,0⟩) (.fork 1 6 (.r ⟨3,6,1,0⟩) (.b ⟨5,1,6,0⟩))) (.b ⟨4,0,6,5⟩))) (.b ⟨6,0,5,3⟩)))) (.fork 1 5 (.fork 1 2 (.fork 1 4 (.r ⟨5,2,4,1⟩) (.fork 3 4 (.fork 0 2 (.r ⟨2,5,1,0⟩) (.fork 0 4 (.r ⟨4,2,1,0⟩) (.fork 0 5 (.r ⟨5,2,1,0⟩) (.fork 4 5 (.r ⟨5,4,2,1⟩) (.b ⟨5,0,4,1⟩))))) (.b ⟨4,1,3,2⟩))) (.b ⟨2,1,3,5⟩)) (.b ⟨5,1,3,2⟩))) (.fork 0 5 (.fork 0 2 (.fork 1 5 (.r ⟨2,5,1,0⟩) (.fork 1 3 (.fork 4 5 (.r ⟨5,4,2,0⟩) (.fork 3 4 (.fork 1 4 (.r ⟨2,4,1,0⟩) (.b ⟨4,1,5,3⟩)) (.b ⟨5,4,3,0⟩))) (.b ⟨5,1,3,0⟩))) (.b ⟨2,0,3,5⟩)) (.b ⟨5,0,3,2⟩))) (.fork 5 6 (.fork 2 6 (.fork 0 3 (.fork 1 3 (.fork 4 5 (.r ⟨6,5,4,2⟩) (.fork 3 4 (.fork 0 4 (.r ⟨4,3,1,0⟩) (.fork 0 5 (.fork 0 2 (.r ⟨3,4,2,0⟩) (.fork 0 6 (.r ⟨6,2,5,0⟩) (.fork 4 6 (.r ⟨5,6,4,2⟩) (.b ⟨6,4,0,2⟩)))) (.b ⟨4,0,5,3⟩))) (.b ⟨5,4,3,2⟩))) (.fork 1 5 (.fork 1 6 (.r ⟨6,2,5,1⟩) (.b ⟨6,1,3,2⟩)) (.b ⟨5,1,3,2⟩))) (.fork 0 5 (.fork 0 6 (.r ⟨6,2,5,0⟩) (.b ⟨6,0,3,2⟩)) (.b ⟨5,0,3,2⟩))) (.b ⟨6,2,3,5⟩)) (.b ⟨6,5,3,2⟩))) (.fork 3 6 (.fork 0 5 (.fork 1 5 (.fork 4 5 (.fork 0 2 (.r ⟨5,4,2,0⟩) (.b ⟨5,3,2,0⟩)) (.b ⟨3,2,5,4⟩)) (.b ⟨3,2,5,1⟩)) (.b ⟨3,2,5,0⟩)) (.b ⟨5,2,3,6⟩)))) (.fork 3 4 (.fork 2 5 (.fork 2 6 (.fork 0 2 (.fork 1 5 (.r ⟨2,5,1,0⟩) (.fork 1 6 (.r ⟨2,6,1,0⟩) (.fork 5 6 (.fork 1 3 (.fork 1 4 (.fork 0 3 (.r ⟨3,4,1,0⟩) (.fork 0 5 (.r ⟨5,6,2,0⟩) (.fork 3 5 (.fork 0 4 (.r ⟨4,3,1,0⟩) (.fork 4 5 (.r ⟨4,5,3,1⟩) (.b ⟨4,0,5,1⟩))) (.b ⟨3,0,5,1⟩)))) (.fork 1 2 (.fork 4 5 (.fork 4 6 (.r ⟨6,4,5,2⟩) (.b ⟨6,1,4,2⟩)) (.b ⟨5,1,4,2⟩)) (.b ⟨4,1,2,3⟩))) (.fork 1 2 (.fork 3 5 (.fork 3 6 (.r ⟨6,3,5,2⟩) (.b ⟨6,1,3,2⟩)) (.b ⟨5,1,3,2⟩)) (.b ⟨3,1,2,4⟩))) (.fork 1 3 (.fork 1 4 (.fork 3 5 (.fork 4 5 (.r ⟨4,5,3,1⟩) (.b ⟨6,1,5,4⟩)) (.b ⟨6,1,5,3⟩)) (.b ⟨6,5,1,4⟩)) (.b ⟨6,5,1,3⟩))))) (.fork 0 3 (.fork 0 4 (.fork 1 3 (.r ⟨4,3,1,0⟩) (.fork 1 2 (.fork 1 4 (.r ⟨3,4,1,0⟩) (.fork 1 5 (.fork 1 6 (.r ⟨6,2,5,1⟩) (.fork 3 6 (.fork 4 6 (.r ⟨4,6,3,0⟩) (.b ⟨6,1,4,2⟩)) (.b ⟨6,1,3,2⟩))) (.fork 3 5 (.fork 4 5 (.r ⟨4,5,3,0⟩) (.b ⟨5,1,4,2⟩)) (.b ⟨5,1,3,2⟩)))) (.b ⟨3,1,2,0⟩))) (.b ⟨4,0,2,3⟩)) (.b ⟨3,0,2,4⟩))) (.fork 3 6 (.fork 4 6 (.fork 0 2 (.fork 1 2 (.fork 0 5 (.r ⟨5,2,1,0⟩) (.fork 0 3 (.fork 0 4 (.r ⟨4,6,3,0⟩) (.fork 4 5 (.fork 3 5 (.r ⟨3,5,2,0⟩) (.fork 0 6 (.r ⟨6,4,3,0⟩) (.fork 5 6 (.r ⟨6,5,4,3⟩) (.b ⟨5,0,6,2⟩)))) (.b ⟨5,0,4,2⟩))) (.fork 3 5 (.fork 4 5 (.r ⟨6,4,5,3⟩) (.fork 0 4 (.fork 0 6 (.r ⟨6,3,4,0⟩) (.fork 5 6 (.r ⟨5,6,4,3⟩) (.b ⟨5,0,6,2⟩))) (.b ⟨5,0,4,2⟩))) (.b ⟨5,0,3,2⟩)))) (.fork 1 3 (.fork 1 4 (.r ⟨4,6,3,1⟩) (.b ⟨4,1,2,3⟩)) (.b ⟨3,1,2,4⟩))) (.fork 0 3 (.fork 0 4 (.r ⟨4,6,3,0⟩) (.b ⟨4,0,2,3⟩)) (.b ⟨3,0,2,4⟩))) (.b ⟨6,4,2,3⟩)) (.b ⟨6,3,2,4⟩))) (.fork 3 5 (.fork 4 5 (.fork 2 6 (.fork 0 2 (.fork 1 2 (.fork 0 6 (.r ⟨6,2,1,0⟩) (.fork 0 3 (.fork 0 4 (.r ⟨4,5,3,0⟩) (.fork 4 6 (.fork 3 6 (.r ⟨3,6,2,0⟩) (.fork 0 5 (.r ⟨5,4,3,0⟩) (.fork 5 6 (.r ⟨5,6,4,3⟩) (.b ⟨6,0,5,2⟩)))) (.b ⟨6,0,4,2⟩))) (.fork 3 6 (.fork 4 6 (.r ⟨6,4,5,3⟩) (.fork 0 4 (.fork 0 5 (.r ⟨5,3,4,0⟩) (.fork 5 6 (.r ⟨6,5,4,3⟩) (.b ⟨6,0,5,2⟩))) (.b ⟨6,0,4,2⟩))) (.b ⟨6,0,3,2⟩)))) (.fork 1 3 (.fork 1 4 (.r ⟨4,5,3,1⟩) (.b ⟨4,1,2,3⟩)) (.b ⟨3,1,2,4⟩))) (.fork 0 3 (.fork 0 4 (.r ⟨4,5,3,0⟩) (.b ⟨4,0,2,3⟩)) (.b ⟨3,0,2,4⟩))) (.fork 3 6 (.fork 4 6 (.r ⟨6,4,5,3⟩) (.b ⟨6,4,2,3⟩)) (.b ⟨6,3,2,4⟩))) (.b ⟨5,4,2,3⟩)) (.b ⟨5,3,2,4⟩))) (.fork 2 5 (.fork 3 6 (.fork 0 4 (.fork 1 4 (.fork 4 5 (.fork 0 2 (.r ⟨4,5,2,0⟩) (.b ⟨4,3,2,0⟩)) (.b ⟨3,2,4,5⟩)) (.b ⟨3,2,4,1⟩)) (.b ⟨3,2,4,0⟩)) (.b ⟨4,2,3,6⟩)) (.b ⟨4,3,2,5⟩))))) (.fork 0 2 (.fork 1 3 (.fork 0 4 (.fork 1 5 (.fork 0 3 (.fork 1 2 (.r ⟨3,1,2,0⟩) (.fork 1 4 (.r ⟨4,1,3,0⟩) (.fork 2 4 (.fork 1 6 (.fork 2 3 (.r ⟨4,2,3,0⟩) (.fork 3 4 (.r ⟨3,4,2,0⟩) (.fork 3 5 (.fork 3 6 (.r ⟨6,3,5,1⟩) (.fork 2 6 (.fork 4 6 (.r ⟨4,6,2,0⟩) (.b ⟨6,3,4,1⟩)) (.b ⟨6,3,2,1⟩))) (.fork 2 5 (.fork 4 5 (.r ⟨4,5,2,0⟩) (.b ⟨5,3,4,1⟩)) (.b ⟨5,3,2,1⟩))))) (.fork 2 6 (.fork 4 6 (.r ⟨4,6,2,0⟩) (.b ⟨6,4,1,0⟩)) (.b ⟨6,2,1,0⟩))) (.b ⟨4,2,1,0⟩)))) (.fork 0 6 (.fork 0 5 (.fork 1 2 (.r ⟨5,1,2,0⟩) (.fork 1 4 (.r ⟨5,1,4,0⟩) (.fork 2 4 (.fork 2 6 (.r ⟨6,2,4,0⟩) (.fork 1 6 (.r ⟨6,1,5,0⟩) (.b ⟨6,2,1,0⟩))) (.b ⟨4,2,1,0⟩)))) (.fork 3 5 (.fork 1 2 (.fork 2 3 (.r ⟨5,3,2,1⟩) (.fork 2 5 (.r ⟨3,5,2,1⟩) (.fork 2 4 (.fork 2 6 (.r ⟨6,2,4,0⟩) (.fork 3 6 (.fork 5 6 (.r ⟨5,6,3,1⟩) (.b ⟨6,2,5,0⟩)) (.b ⟨6,2,3,0⟩))) (.fork 3 4 (.fork 4 5 (.r ⟨5,4,3,1⟩) (.b ⟨4,2,5,0⟩)) (.b ⟨4,2,3,0⟩))))) (.fork 2 4 (.fork 2 6 (.r ⟨6,2,4,0⟩) (.fork 1 6 (.fork 3 6 (.r ⟨6,3,5,1⟩) (.fork 2 3 (.fork 2 5 (.r ⟨5,2,3,1⟩) (.fork 5 6 (.r ⟨6,5,3,1⟩) (.b ⟨6,2,5,0⟩))) (.b ⟨6,2,3,0⟩))) (.b ⟨6,2,1,0⟩))) (.fork 1 4 (.fork 3 4 (.r ⟨5,3,4,1⟩) (.fork 2 3 (.fork 2 5 (.r ⟨5,2,3,1⟩) (.fork 4 5 (.r ⟨4,5,3,1⟩) (.b ⟨4,2,5,0⟩))) (.b ⟨4,2,3,0⟩))) (.b ⟨4,2,1,0⟩)))) (.b ⟨5,3,0,1⟩))) (.fork 3 6 (.fork 1 6 (.fork 3 5 (.r ⟨6,3,5,1⟩) (.fork 0 5 (.fork 5 6 (.r ⟨5,6,3,1⟩) (.fork 2 5 (.fork 4 5 (.r ⟨4,5,2,0⟩) (.fork 3 4 (.fork 4 6 (.r ⟨6,4,3,1⟩) (.b ⟨5,4,6,0⟩)) (.b ⟨5,4,3,0⟩))) (.fork 2 3 (.fork 2 6 (.r ⟨6,2,3,1⟩) (.b ⟨5,2,6,0⟩)) (.b ⟨5,2,3,0⟩)))) (.b ⟨5,3,0,1⟩))) (.b ⟨6,1,0,3⟩)) (.b ⟨6,3,0,1⟩)))) (.fork 0 5 (.fork 1 6 (.fork 2 5 (.fork 4 5 (.r ⟨4,5,2,0⟩) (.fork 1 4 (.fork 0 3 (.r ⟨4,1,3,0⟩) (.fork 0 6 (.r ⟨6,1,4,0⟩) (.fork 3 6 (.fork 3 4 (.r ⟨6,3,4,1⟩) (.fork 3 5 (.fork 5 6 (.r ⟨6,5,3,1⟩) (.fork 4 6 (.r ⟨4,6,3,1⟩) (.b ⟨5,4,6,0⟩))) (.b ⟨5,4,3,0⟩))) (.b ⟨6,3,0,1⟩)))) (.b ⟨5,4,1,0⟩))) (.fork 1 2 (.fork 1 4 (.r ⟨4,1,2,0⟩) (.fork 4 5 (.fork 2 4 (.r ⟨5,4,2,0⟩) (.fork 2 3 (.fork 2 6 (.r ⟨6,2,3,1⟩) (.fork 4 6 (.fork 5 6 (.r ⟨5,6,4,0⟩) (.b ⟨6,2,5,1⟩)) (.b ⟨6,2,4,1⟩))) (.fork 3 4 (.fork 3 5 (.r ⟨5,3,4,0⟩) (.b ⟨3,2,5,1⟩)) (.b ⟨3,2,4,1⟩)))) (.b ⟨5,4,1,0⟩))) (.b ⟨5,2,1,0⟩))) (.fork 5 6 (.fork 0 6 (.fork 2 5 (.r ⟨6,5,2,0⟩) (.fork 1 2 (.fork 4 5 (.r ⟨6,5,4,0⟩) (.fork 1 4 (.r ⟨4,1,2,0⟩) (.b ⟨5,4,1,0⟩))) (.b ⟨5,2,1,0⟩))) (.b ⟨6,0,1,5⟩)) (.b ⟨6,5,1,0⟩))) (.fork 5 6 (.fork 1 2 (.fork 0 3 (.r ⟨3,1,2,0⟩) (.b ⟨5,1,0,3⟩)) (.b ⟨5,0,1,2⟩)) (.b ⟨1,0,5,6⟩)))) (.fork 1 4 (.fork 0 5 (.fork 0 6 (.fork 0 3 (.fork 1 2 (.r ⟨3,1,2,0⟩) (.fork 1 5 (.r ⟨5,1,3,0⟩) (.fork 2 5 (.fork 2 6 (.r ⟨6,2,5,0⟩) (.fork 1 6 (.r ⟨6,1,3,0⟩) (.b ⟨6,2,1,0⟩))) (.b ⟨5,2,1,0⟩)))) (.fork 3 4 (.fork 1 2 (.fork 2 3 (.r ⟨4,3,2,1⟩) (.fork 2 4 (.r ⟨3,4,2,1⟩) (.fork 2 5 (.fork 2 6 (.r ⟨6,2,5,0⟩) (.fork 3 6 (.fork 4 6 (.r ⟨4,6,3,1⟩) (.b ⟨6,2,4,0⟩)) (.b ⟨6,2,3,0⟩))) (.fork 3 5 (.fork 4 5 (.r ⟨4,5,3,1⟩) (.b ⟨5,2,4,0⟩)) (.b ⟨5,2,3,0⟩))))) (.fork 2 5 (.fork 2 6 (.r ⟨6,2,5,0⟩) (.fork 1 6 (.fork 3 6 (.r ⟨6,3,4,1⟩) (.fork 2 3 (.fork 2 4 (.r ⟨4,2,3,1⟩) (.fork 4 6 (.r ⟨6,4,3,1⟩) (.b ⟨6,2,4,0⟩))) (.b ⟨6,2,3,0⟩))) (.b ⟨6,2,1,0⟩))) (.fork 1 5 (.fork 3 5 (.r ⟨5,3,4,1⟩) (.fork 2 3 (.fork 2 4 (.r ⟨4,2,3,1⟩) (.fork 4 5 (.r ⟨5,4,3,1⟩) (.b ⟨5,2,4,0⟩))) (.b ⟨5,2,3,0⟩))) (.b ⟨5,2,1,0⟩)))) (.b ⟨4,3,0,1⟩))) (.fork 4 6 (.fork 1 6 (.fork 3 4 (.r ⟨6,4,3,1⟩) (.fork 0 3 (.fork 3 6 (.r ⟨4,6,3,1⟩) (.fork 2 3 (.fork 3 5 (.r ⟨5,3,2,0⟩) (.fork 4 5 (.fork 5 6 (.r ⟨6,5,4,1⟩) (.b ⟨5,3,6,0⟩)) (.b ⟨5,3,4,0⟩))) (.fork 2 4 (.fork 2 6 (.r ⟨6,2,4,1⟩) (.b ⟨3,2,6,0⟩)) (.b ⟨3,2,4,0⟩)))) (.b ⟨4,3,0,1⟩))) (.b ⟨6,1,0,4⟩)) (.b ⟨6,4,0,1⟩))) (.fork 4 5 (.fork 1 5 (.fork 0 6 (.fork 3 4 (.r ⟨5,4,3,1⟩) (.fork 0 3 (.fork 3 5 (.r ⟨4,5,3,1⟩) (.fork 2 3 (.fork 3 6 (.r ⟨6,3,2,0⟩) (.fork 4 6 (.fork 5 6 (.r ⟨5,6,4,1⟩) (.b ⟨6,3,5,0⟩)) (.b ⟨6,3,4,0⟩))) (.fork 2 4 (.fork 2 5 (.r ⟨5,2,4,1⟩) (.b ⟨3,2,5,0⟩)) (.b ⟨3,2,4,0⟩)))) (.b ⟨4,3,0,1⟩))) (.fork 4 6 (.fork 5 6 (.r ⟨5,6,4,1⟩) (.b ⟨6,5,0,1⟩)) (.b ⟨6,4,0,1⟩))) (.b ⟨5,1,0,4⟩)) (.b ⟨5,4,0,1⟩))) (.fork 4 5 (.fork 0 6 (.fork 1 2 (.fork 0 3 (.r ⟨3,1,2,0⟩) (.b ⟨4,1,0,3⟩)) (.b ⟨4,0,1,2⟩)) (.b ⟨4,1,0,6⟩)) (.b ⟨1,0,4,5⟩)))) (.fork 0 3 (.fork 1 4 (.fork 1 5 (.fork 1 6 (.fork 1 2 (.fork 0 4 (.r ⟨4,1,2,0⟩) (.fork 0 5 (.r ⟨5,1,2,0⟩) (.fork 4 5 (.fork 4 6 (.r ⟨6,4,5,1⟩) (.fork 0 6 (.r ⟨6,1,2,0⟩) (.b ⟨6,4,0,1⟩))) (.b ⟨5,4,0,1⟩)))) (.fork 2 3 (.fork 0 4 (.fork 2 4 (.r ⟨4,2,3,0⟩) (.fork 3 4 (.r ⟨4,3,2,0⟩) (.fork 4 5 (.fork 4 6 (.r ⟨6,4,5,1⟩) (.fork 2 6 (.fork 3 6 (.r ⟨3,6,2,0⟩) (.b ⟨6,4,3,1⟩)) (.b ⟨6,4,2,1⟩))) (.fork 2 5 (.fork 3 5 (.r ⟨3,5,2,0⟩) (.b ⟨5,4,3,1⟩)) (.b ⟨5,4,2,1⟩))))) (.fork 4 5 (.fork 4 6 (.r ⟨6,4,5,1⟩) (.fork 0 6 (.fork 2 6 (.r ⟨6,2,3,0⟩) (.fork 2 4 (.fork 3 4 (.r ⟨3,4,2,0⟩) (.fork 3 6 (.r ⟨6,3,2,0⟩) (.b ⟨6,3,4,0⟩))) (.b ⟨6,2,4,0⟩))) (.b ⟨6,4,0,1⟩))) (.fork 0 5 (.fork 2 5 (.r ⟨5,2,3,0⟩) (.fork 2 4 (.fork 3 4 (.r ⟨3,4,2,0⟩) (.fork 3 5 (.r ⟨5,3,2,0⟩) (.b ⟨5,3,4,0⟩))) (.b ⟨5,2,4,0⟩))) (.b ⟨5,4,0,1⟩)))) (.b ⟨3,2,1,0⟩))) (.fork 3 6 (.fork 0 6 (.fork 2 3 (.r ⟨6,3,2,0⟩) (.fork 1 2 (.fork 2 6 (.r ⟨3,6,2,0⟩) (.fork 2 4 (.fork 2 5 (.r ⟨5,2,4,1⟩) (.fork 3 5 (.fork 5 6 (.r ⟨6,5,3,0⟩) (.b ⟨5,2,6,1⟩)) (.b ⟨5,2,3,1⟩))) (.fork 3 4 (.fork 4 6 (.r ⟨6,4,3,0⟩) (.b ⟨4,2,6,1⟩)) (.b ⟨4,2,3,1⟩)))) (.b ⟨3,2,1,0⟩))) (.b ⟨6,0,1,3⟩)) (.b ⟨6,3,1,0⟩))) (.fork 3 5 (.fork 0 5 (.fork 1 6 (.fork 2 3 (.r ⟨5,3,2,0⟩) (.fork 1 2 (.fork 2 5 (.r ⟨3,5,2,0⟩) (.fork 2 4 (.fork 2 6 (.r ⟨6,2,4,1⟩) (.fork 3 6 (.fork 5 6 (.r ⟨5,6,3,0⟩) (.b ⟨6,2,5,1⟩)) (.b ⟨6,2,3,1⟩))) (.fork 3 4 (.fork 4 5 (.r ⟨5,4,3,0⟩) (.b ⟨4,2,5,1⟩)) (.b ⟨4,2,3,1⟩)))) (.b ⟨3,2,1,0⟩))) (.fork 3 6 (.fork 5 6 (.r ⟨5,6,3,0⟩) (.b ⟨6,5,1,0⟩)) (.b ⟨6,3,1,0⟩))) (.b ⟨5,0,1,3⟩)) (.b ⟨5,3,1,0⟩))) (.fork 3 4 (.fork 0 4 (.fork 1 5 (.fork 1 6 (.fork 2 3 (.r ⟨4,3,2,0⟩) (.fork 1 2 (.fork 2 4 (.r ⟨3,4,2,0⟩) (.fork 2 5 (.fork 2 6 (.r ⟨6,2,5,1⟩) (.fork 3 6 (.fork 4 6 (.r ⟨4,6,3,0⟩) (.b ⟨6,2,4,1⟩)) (.b ⟨6,2,3,1⟩))) (.fork 3 5 (.fork 4 5 (.r ⟨4,5,3,0⟩) (.b ⟨5,2,4,1⟩)) (.b ⟨5,2,3,1⟩)))) (.b ⟨3,2,1,0⟩))) (.fork 3 6 (.fork 4 6 (.r ⟨4,6,3,0⟩) (.b ⟨6,4,1,0⟩)) (.b ⟨6,3,1,0⟩))) (.fork 3 5 (.fork 4 5 (.r ⟨4,5,3,0⟩) (.b ⟨5,4,1,0⟩)) (.b ⟨5,3,1,0⟩))) (.b ⟨4,0,1,3⟩)) (.b ⟨4,3,1,0⟩))) (.fork 1 4 (.fork 3 5 (.fork 0 6 (.fork 1 2 (.fork 0 4 (.r ⟨4,1,2,0⟩) (.b ⟨3,1,0,4⟩)) (.b ⟨3,0,1,2⟩)) (.b ⟨3,1,0,6⟩)) (.b ⟨1,0,3,5⟩)) (.b ⟨3,0,1,4⟩)))) (.fork 1 2 (.fork 0 3 (.fork 0 4 (.fork 0 5 (.fork 0 6 (.fork 3 4 (.fork 3 5 (.r ⟨5,3,4,0⟩) (.fork 3 6 (.r ⟨6,3,4,0⟩) (.fork 5 6 (.fork 4 5 (.r ⟨5,4,3,0⟩) (.fork 1 3 (.fork 2 4 (.r ⟨3,4,2,1⟩) (.fork 2 5 (.fork 4 6 (.r ⟨6,4,3,0⟩) (.fork 2 6 (.r ⟨6,2,5,0⟩) (.b ⟨6,4,2,0⟩))) (.b ⟨5,4,2,0⟩))) (.fork 1 5 (.fork 1 6 (.r ⟨6,1,5,0⟩) (.b ⟨6,3,1,0⟩)) (.b ⟨5,3,1,0⟩)))) (.fork 1 5 (.fork 2 6 (.fork 1 6 (.r ⟨6,1,5,0⟩) (.b ⟨5,3,6,1⟩)) (.b ⟨5,3,6,2⟩)) (.b ⟨6,3,5,1⟩))))) (.fork 3 5 (.fork 3 6 (.r ⟨6,3,5,0⟩) (.fork 4 6 (.fork 4 5 (.r ⟨4,5,3,0⟩) (.fork 1 3 (.fork 2 5 (.r ⟨3,5,2,1⟩) (.fork 2 4 (.fork 5 6 (.r ⟨6,5,3,0⟩) (.fork 2 6 (.r ⟨6,2,4,0⟩) (.b ⟨6,5,2,0⟩))) (.b ⟨5,4,2,0⟩))) (.fork 1 4 (.fork 1 6 (.r ⟨6,1,4,0⟩) (.b ⟨6,3,1,0⟩)) (.b ⟨4,3,1,0⟩)))) (.fork 1 4 (.fork 2 6 (.fork 1 6 (.r ⟨6,1,4,0⟩) (.b ⟨4,3,6,1⟩)) (.b ⟨4,3,6,2⟩)) (.b ⟨6,3,4,1⟩)))) (.fork 4 5 (.fork 1 3 (.fork 2 3 (.fork 4 6 (.r ⟨6,4,5,0⟩) (.fork 3 6 (.fork 1 6 (.r ⟨6,1,3,0⟩) (.fork 1 4 (.r ⟨4,1,3,0⟩) (.b ⟨6,4,1,0⟩))) (.b ⟨6,4,3,5⟩))) (.fork 2 4 (.fork 2 5 (.r ⟨5,2,4,0⟩) (.b ⟨5,3,2,0⟩)) (.b ⟨4,3,2,0⟩))) (.fork 1 4 (.fork 1 5 (.r ⟨5,1,4,0⟩) (.b ⟨5,3,1,0⟩)) (.b ⟨4,3,1,0⟩))) (.fork 1 3 (.fork 2 4 (.fork 1 4 (.r ⟨4,1,3,0⟩) (.b ⟨5,3,4,1⟩)) (.b ⟨5,3,4,2⟩)) (.b ⟨5,4,3,1⟩))))) (.fork 1 6 (.fork 2 6 (.fork 1 3 (.fork 2 3 (.r ⟨6,2,3,1⟩) (.fork 3 6 (.r ⟨3,6,2,1⟩) (.fork 3 4 (.fork 3 5 (.r ⟨5,3,4,0⟩) (.fork 2 5 (.fork 5 6 (.r ⟨6,5,2,1⟩) (.b ⟨5,3,6,0⟩)) (.b ⟨5,3,2,0⟩))) (.fork 2 4 (.fork 4 6 (.r ⟨6,4,2,1⟩) (.b ⟨4,3,6,0⟩)) (.b ⟨4,3,2,0⟩))))) (.fork 3 4 (.fork 3 5 (.r ⟨5,3,4,0⟩) (.fork 1 5 (.fork 2 5 (.r ⟨6,2,5,1⟩) (.fork 2 3 (.fork 3 6 (.r ⟨6,3,2,1⟩) (.fork 5 6 (.r ⟨5,6,2,1⟩) (.b ⟨5,3,6,0⟩))) (.b ⟨5,3,2,0⟩))) (.b ⟨5,3,1,0⟩))) (.fork 1 4 (.fork 2 4 (.r ⟨6,2,4,1⟩) (.fork 2 3 (.fork 3 6 (.r ⟨6,3,2,1⟩) (.fork 4 6 (.r ⟨4,6,2,1⟩) (.b ⟨4,3,6,0⟩))) (.b ⟨4,3,2,0⟩))) (.b ⟨4,3,1,0⟩)))) (.b ⟨6,2,0,1⟩)) (.b ⟨6,1,0,2⟩))) (.fork 1 5 (.fork 2 5 (.fork 0 6 (.fork 1 3 (.fork 2 3 (.r ⟨5,2,3,1⟩) (.fork 3 5 (.r ⟨3,5,2,1⟩) (.fork 3 4 (.fork 3 6 (.r ⟨6,3,4,0⟩) (.fork 2 6 (.fork 5 6 (.r ⟨5,6,2,1⟩) (.b ⟨6,3,5,0⟩)) (.b ⟨6,3,2,0⟩))) (.fork 2 4 (.fork 4 5 (.r ⟨5,4,2,1⟩) (.b ⟨4,3,5,0⟩)) (.b ⟨4,3,2,0⟩))))) (.fork 3 4 (.fork 3 6 (.r ⟨6,3,4,0⟩) (.fork 1 6 (.fork 2 6 (.r ⟨6,2,5,1⟩) (.fork 2 3 (.fork 3 5 (.r ⟨5,3,2,1⟩) (.fork 5 6 (.r ⟨6,5,2,1⟩) (.b ⟨6,3,5,0⟩))) (.b ⟨6,3,2,0⟩))) (.b ⟨6,3,1,0⟩))) (.fork 1 4 (.fork 2 4 (.r ⟨5,2,4,1⟩) (.fork 2 3 (.fork 3 5 (.r ⟨5,3,2,1⟩) (.fork 4 5 (.r ⟨4,5,2,1⟩) (.b ⟨4,3,5,0⟩))) (.b ⟨4,3,2,0⟩))) (.b ⟨4,3,1,0⟩)))) (.fork 1 6 (.fork 2 6 (.r ⟨6,2,5,1⟩) (.b ⟨6,2,0,1⟩)) (.b ⟨6,1,0,2⟩))) (.b ⟨5,2,0,1⟩)) (.b ⟨5,1,0,2⟩))) (.fork 1 4 (.fork 2 4 (.fork 0 5 (.fork 0 6 (.fork 1 3 (.fork 2 3 (.r ⟨4,2,3,1⟩) (.fork 3 4 (.r ⟨3,4,2,1⟩) (.fork 3 5 (.fork 3 6 (.r ⟨6,3,5,0⟩) (.fork 2 6 (.fork 4 6 (.r ⟨4,6,2,1⟩) (.b ⟨6,3,4,0⟩)) (.b ⟨6,3,2,0⟩))) (.fork 2 5 (.fork 4 5 (.r ⟨4,5,2,1⟩) (.b ⟨5,3,4,0⟩)) (.b ⟨5,3,2,0⟩))))) (.fork 3 5 (.fork 3 6 (.r ⟨6,3,5,0⟩) (.fork 1 6 (.fork 2 6 (.r ⟨6,2,4,1⟩) (.fork 2 3 (.fork 3 4 (.r ⟨4,3,2,1⟩) (.fork 4 6 (.r ⟨6,4,2,1⟩) (.b ⟨6,3,4,0⟩))) (.b ⟨6,3,2,0⟩))) (.b ⟨6,3,1,0⟩))) (.fork 1 5 (.fork 2 5 (.r ⟨5,2,4,1⟩) (.fork 2 3 (.fork 3 4 (.r ⟨4,3,2,1⟩) (.fork 4 5 (.r ⟨5,4,2,1⟩) (.b ⟨5,3,4,0⟩))) (.b ⟨5,3,2,0⟩))) (.b ⟨5,3,1,0⟩)))) (.fork 1 6 (.fork 2 6 (.r ⟨6,2,4,1⟩) (.b ⟨6,2,0,1⟩)) (.b ⟨6,1,0,2⟩))) (.fork 1 5 (.fork 2 5 (.r ⟨5,2,4,1⟩) (.b ⟨5,2,0,1⟩)) (.b ⟨5,1,0,2⟩))) (.b ⟨4,2,0,1⟩)) (.b ⟨4,1,0,2⟩))) (.fork 1 3 (.fork 2 3 (.fork 0 4 (.fork 0 5 (.fork 0 6 (.fork 1 4 (.fork 2 4 (.r ⟨4,2,3,1⟩) (.fork 3 4 (.r ⟨4,3,2,1⟩) (.fork 4 5 (.fork 4 6 (.r ⟨6,4,5,0⟩) (.fork 2 6 (.fork 3 6 (.r ⟨3,6,2,1⟩) (.b ⟨6,4,3,0⟩)) (.b ⟨6,4,2,0⟩))) (.fork 2 5 (.fork 3 5 (.r ⟨3,5,2,1⟩) (.b ⟨5,4,3,0⟩)) (.b ⟨5,4,2,0⟩))))) (.fork 4 5 (.fork 4 6 (.r ⟨6,4,5,0⟩) (.fork 1 6 (.fork 2 6 (.r ⟨6,2,3,1⟩) (.fork 2 4 (.fork 3 4 (.r ⟨3,4,2,1⟩) (.fork 3 6 (.r ⟨6,3,2,1⟩) (.b ⟨6,4,3,0⟩))) (.b ⟨6,4,2,0⟩))) (.b ⟨6,4,1,0⟩))) (.fork 1 5 (.fork 2 5 (.r ⟨5,2,3,1⟩) (.fork 2 4 (.fork 3 4 (.r ⟨3,4,2,1⟩) (.fork 3 5 (.r ⟨5,3,2,1⟩) (.b ⟨5,4,3,0⟩))) (.b ⟨5,4,2,0⟩))) (.b ⟨5,4,1,0⟩)))) (.fork 1 6 (.fork 2 6 (.r ⟨6,2,3,1⟩) (.b ⟨6,2,0,1⟩)) (.b ⟨6,1,0,2⟩))) (.fork 1 5 (.fork 2 5 (.r ⟨5,2,3,1⟩) (.b ⟨5,2,0,1⟩)) (.b ⟨5,1,0,2⟩))) (.fork 0 5 (.fork 1 4 (.fork 2 4 (.r ⟨4,2,3,1⟩) (.b ⟨4,2,0,1⟩)) (.b ⟨4,1,0,2⟩)) (.fork 0 6 (.fork 4 5 (.fork 1 4 (.fork 2 5 (.r ⟨4,5,2,1⟩) (.b ⟨5,2,0,1⟩)) (.b ⟨4,1,0,2⟩)) (.b ⟨5,4,0,1⟩)) (.fork 4 5 (.fork 4 6 (.fork 5 6 (.fork 1 4 (.fork 2 5 (.r ⟨4,5,2,1⟩) (.b ⟨5,2,0,1⟩)) (.b ⟨4,1,0,2⟩)) (.b ⟨6,5,0,1⟩)) (.b ⟨6,4,0,1⟩)) (.b ⟨5,4,0,1⟩))))) (.b ⟨3,2,0,1⟩)) (.b ⟨3,1,0,2⟩))) (.fork 0 3 (.fork 1 4 (.fork 2 5 (.fork 0 6 (.fork 1 3 (.fork 0 4 (.r ⟨4,1,3,0⟩) (.b ⟨2,1,0,4⟩)) (.b ⟨2,0,1,3⟩)) (.b ⟨2,1,0,6⟩)) (.b ⟨1,0,2,5⟩)) (.b ⟨2,0,1,4⟩)) (.b ⟨2,1,0,3⟩)))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem pawCover (c : Fin 7 → Fin 7 → Bool) :
    (∃ q, sqB (symCol c) q = true) ∨ (∃ q, pawB (symCol c) q = true) := by
  have ok : verify true pawTree [] [] = true := by decide +kernel
  simpa only [colors_key,if_true] using
    verified pawTree [] [] (colors c) (by simp) (by simp) ok

private theorem color_read {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Fin n ↪ V) (i j : Fin n) :
    symCol (fun a b => decide (G.Adj (f a) (f b))) i j = decide (G.Adj (f i) (f j)) := by
  rcases le_total i j with h|h
  · simp [symCol,min_eq_left h,max_eq_right h]
  · simp [symCol,min_eq_right h,max_eq_left h,SimpleGraph.adj_comm]

private theorem no_squareB {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    (free : ¬ cycleGraph 4 ⊑ G) (f : Fin n ↪ V) (q : Quad n) :
    sqB (symCol (fun a b => decide (G.Adj (f a) (f b)))) q ≠ true := by
  rcases q with ⟨a,b,c,d⟩
  intro he
  simp only [sqB,distinctQ,color_read,Bool.and_eq_true,decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨⟨_,ac,_,_,bd,_⟩,ab⟩,bc⟩,cd⟩,da⟩ := he
  exact bd (f.injective (square_common_unique free (f.injective.ne ac) ab da.symm bc.symm cd))

theorem square_pair_witness {V : Type} [Fintype V] (G : SimpleGraph V)
    (size : 5 ≤ Fintype.card V) (free : ¬ cycleGraph 4 ⊑ G) :
    ∃ a b c d : V, (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∧ Gᶜ.Adj a b ∧ Gᶜ.Adj c d := by
  classical
  obtain ⟨f⟩ : Nonempty (Fin 5 ↪ V) := Function.Embedding.nonempty_of_card_le (by simpa)
  have yes := pairCover (fun a b => decide (G.Adj (f a) (f b)))
  rcases yes with red|blue
  · obtain ⟨q,e⟩ := red
    exact (no_squareB G free f q e).elim
  · obtain ⟨⟨a,b,c,d⟩,e⟩ := blue
    simp only [pairB,distinctQ,color_read,Bool.and_eq_true,Bool.not_eq_true',
      decide_eq_false_iff_not,decide_eq_true_eq] at e
    obtain ⟨⟨⟨ab,ac,ad,bc,bd,cd⟩,u⟩,v⟩ := e
    exact ⟨f a,f b,f c,f d,⟨f.injective.ne ab,f.injective.ne ac,f.injective.ne ad,f.injective.ne bc,f.injective.ne bd,f.injective.ne cd⟩,
      ⟨f.injective.ne ab,u⟩,⟨f.injective.ne cd,v⟩⟩

theorem square_paw_witness {V : Type} [Fintype V] (G : SimpleGraph V)
    (size : 7 ≤ Fintype.card V) (free : ¬ cycleGraph 4 ⊑ G) :
    ∃ a b c d : V, (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∧ Gᶜ.Adj a b ∧ Gᶜ.Adj b c ∧ Gᶜ.Adj a c ∧ Gᶜ.Adj c d := by
  classical
  obtain ⟨f⟩ : Nonempty (Fin 7 ↪ V) := Function.Embedding.nonempty_of_card_le (by simpa)
  have yes := pawCover (fun a b => decide (G.Adj (f a) (f b)))
  rcases yes with red|blue
  · obtain ⟨q,e⟩ := red
    exact (no_squareB G free f q e).elim
  · obtain ⟨⟨a,b,c,d⟩,e⟩ := blue
    simp only [pawB,distinctQ,color_read,Bool.and_eq_true,Bool.not_eq_true',
      decide_eq_false_iff_not,decide_eq_true_eq] at e
    obtain ⟨⟨⟨⟨⟨ab,ac,ad,bc,bd,cd⟩,u⟩,v⟩,w⟩,z⟩ := e
    exact ⟨f a,f b,f c,f d,⟨f.injective.ne ab,f.injective.ne ac,f.injective.ne ad,f.injective.ne bc,f.injective.ne bd,f.injective.ne cd⟩,
      ⟨f.injective.ne ab,u⟩,⟨f.injective.ne bc,v⟩,⟨f.injective.ne ac,w⟩,⟨f.injective.ne cd,z⟩⟩

end OMA

/- Embedding a three-edge target on at most four vertices -/

namespace OMA
open SimpleGraph

theorem square_small_order {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (H : SimpleGraph W) [DecidableRel H.Adj] (pos : ∀ i, 0 < H.degree i)
    (edges : H.edgeFinset.card ≤ 3) (order : Fintype.card W ≤ 4)
    (size : 7 ≤ Fintype.card V) (free : ¬ cycleGraph 4 ⊑ G) : H ⊑ Gᶜ := by
  classical
  obtain ⟨a,b,c,d,⟨ab,ac,ad,bc,bd,cd⟩,eab,ebc,eac,ecd⟩ := square_paw_witness G size free
  let T : Finset V := {a,b,c}
  have ct : T.card = 3 := by simp [T,ab,ac,bc]
  have clique {i j : T} (ne : i ≠ j) : Gᶜ.Adj i.val j.val := by
    have ni : i.val = a ∨ i.val = b ∨ i.val = c := by
      simpa only [T,Finset.mem_insert,Finset.mem_singleton] using i.prop
    have nj : j.val = a ∨ j.val = b ∨ j.val = c := by
      simpa only [T,Finset.mem_insert,Finset.mem_singleton] using j.prop
    have nv : i.val ≠ j.val := fun h => ne (Subtype.ext h)
    rcases ni with hi|hi|hi <;> rcases nj with hj|hj|hj <;> rw [hi,hj] at nv ⊢ <;>
      first | contradiction | assumption | exact eab.symm | exact ebc.symm | exact eac.symm
  by_cases small : Fintype.card W ≤ 3
  · obtain ⟨f⟩ : Nonempty (W ↪ T) := Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe,ct])
    exact ⟨⟨⟨fun i => (f i).val,fun {i j} e => clique (f.injective.ne e.ne)⟩,
      fun {_ _} h => f.injective (Subtype.ext h)⟩⟩
  obtain ⟨v,hv⟩ : ∃ v, H.degree v = 1 := by
    by_contra! bad
    have bound (v : W) : 2 ≤ H.degree v := by have := bad v; have := pos v; omega
    have z := Finset.sum_le_sum (s := Finset.univ) (fun i _ => bound i)
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,H.sum_degrees_eq_twice_card_edges] at z
    omega
  obtain ⟨y,hy,uniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
  obtain ⟨f⟩ : Nonempty (↥({v}ᶜ : Set W) ↪ T) := Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_coe, ct, Fintype.card_compl_set,@Fintype.card_unique (↥({v} : Set W))]; omega)
  let y' : ↥({v}ᶜ : Set W) := ⟨y,hy.ne.symm⟩
  let c' : ↥T := ⟨c,by simp [T]⟩
  let g := f.trans (Equiv.swap (f y') c').toEmbedding
  let k : (H.induce {v}ᶜ).Copy Gᶜ := ⟨⟨fun i => (g i).val,fun {i j} e =>
    clique (g.injective.ne e.ne)⟩,fun {_ _} h => g.injective (Subtype.ext h)⟩
  apply small_extend v k d
  · intro i h
    have ht : d ∈ T := (show d = (g i).val from h) ▸ (g i).prop
    simp [T,ad.symm,bd.symm,cd.symm] at ht
  · intro i hi
    have eq : i = y' := Subtype.ext (uniq _ hi)
    subst i
    change Gᶜ.Adj d ((Equiv.swap (f y') c') (f y')).val
    simpa only [Equiv.swap_apply_left] using ecd.symm

end OMA

/- Induction on the number of edges of the blue target -/

namespace OMA
open SimpleGraph

/-- The exceptional targets in the square induction have at most three edges,
or every vertex of degree at least two is the unique such vertex. -/
def SquareBase : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel H.Adj], (∀ w, 0 < H.degree w) →
    (H.edgeFinset.card ≤ 3 ∨ ∀ v w, 2 ≤ H.degree v → 2 ≤ H.degree w → v = w) →
    2 ≤ H.edgeFinset.card → 2 * H.edgeFinset.card + 1 ≤ Fintype.card V →
    ¬ cycleGraph 4 ⊑ G → H ⊑ Gᶜ

theorem small_copy_one_edge {W V : Type} [Fintype W] [Fintype V]
    (H : SimpleGraph W) [DecidableRel H.Adj] (G : SimpleGraph V)
    (order : Fintype.card W ≤ Fintype.card V) (edges : H.edgeFinset.card ≤ 1)
    {x y : V} (xy : Gᶜ.Adj x y) : H ⊑ Gᶜ := by
  classical
  apply restore_isolates _ _ order
  have incident (v : ↥H.support) : 0 < (H.induce H.support).degree v := by
    rw [H.degree_induce_support, H.degree_pos_iff_mem_support]
    exact v.prop
  have few : Fintype.card H.support ≤ 2 := calc
    _ = ∑ _ : H.support, 1 := by simp
    _ ≤ ∑ v, (H.induce H.support).degree v := Finset.sum_le_sum fun v _ => incident v
    _ = _ := (H.induce H.support).sum_degrees_eq_twice_card_edges
    _ ≤ 2 := by rw [H.card_edgeFinset_induce_support]; omega
  let T : Finset V := {x,y}
  obtain ⟨f⟩ : Nonempty (↥H.support ↪ ↥T) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_coe, show T.card = 2 by simp [T,xy.ne]]; exact few)
  let g := f.trans (Function.Embedding.subtype _)
  refine ⟨⟨⟨g, fun {i j} e => ?_⟩, g.injective⟩⟩
  have hi : g i = x ∨ g i = y := Finset.mem_insert.mp (f i).prop |>.imp_right Finset.mem_singleton.mp
  have hj : g j = x ∨ g j = y := Finset.mem_insert.mp (f j).prop |>.imp_right Finset.mem_singleton.mp
  have ne := g.injective.ne e.ne
  rcases hi with hi|hi <;> rcases hj with hj|hj <;> simp_all [SimpleGraph.adj_comm]

private theorem one_edge_or_empty {W V : Type} [Fintype W] [Fintype V]
    (H : SimpleGraph W) [DecidableRel H.Adj] (G : SimpleGraph V)
    (order : Fintype.card W ≤ Fintype.card V) (edges : H.edgeFinset.card ≤ 1)
    (big : 4 ≤ Fintype.card V) (free : ¬ cycleGraph 4 ⊑ G) : H ⊑ Gᶜ := by
  obtain ⟨a⟩ : Nonempty (Fin 4 ↪ V) := Function.Embedding.nonempty_of_card_le (by simpa)
  obtain ⟨x,y,xy⟩ : ∃ x y, Gᶜ.Adj x y := by
    by_contra! h
    exact free ⟨⟨⟨a, fun {i j} e => by
      by_contra no
      exact h _ _ ⟨a.injective.ne e.ne,no⟩⟩, a.injective⟩⟩
  exact small_copy_one_edge H G order edges xy

theorem small_two_high_order {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (pos : ∀ w, 0 < H.degree w) {v w : W} (hv : 2 ≤ H.degree v) (hw : 2 ≤ H.degree w)
    (vw : v ≠ w) : Fintype.card W + H.degree v ≤ 2 * H.edgeFinset.card := by
  classical
  have bound (i : W) : 1 + (if i = v then H.degree v - 1 else 0) +
      (if i = w then 1 else 0) ≤ H.degree i := by
    split_ifs with h k k <;> subst_vars <;> first | contradiction | omega | exact pos _
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => bound i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    H.sum_degrees_eq_twice_card_edges] at sum
  omega

/-- The two high-degree vertices leave enough room to restore any isolates
created by deleting one of them. -/
theorem square_of_base (base : SquareBase) {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (pos : ∀ w, 0 < H.degree w) (two : 2 ≤ H.edgeFinset.card)
    (size : 2 * H.edgeFinset.card + 1 ≤ Fintype.card V)
    (free : ¬ cycleGraph 4 ⊑ G) : H ⊑ Gᶜ := by
  classical
  by_cases exc : H.edgeFinset.card ≤ 3 ∨ ∀ v w, 2 ≤ H.degree v → 2 ≤ H.degree w → v = w
  · exact base G H pos exc two size free
  push Not at exc
  obtain ⟨large,v,w,hv,hw,vw⟩ := exc
  have horder : Fintype.card W + H.degree v ≤ 2 * H.edgeFinset.card := by
    exact small_two_high_order H pos hv hw vw
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨S,hS,extend⟩ := square_reserve G H v free
  apply extend
  let P := (↑S : Set V)ᶜ
  let J := H.induce ({v}ᶜ : Set W)
  have cnt : J.edgeFinset.card = H.edgeFinset.card - H.degree v := by
    dsimp only [J]
    rw [H.card_edgeFinset_induce_compl_singleton,
      H.card_edgeFinset_deleteIncidenceSet]
  have room : Fintype.card P = Fintype.card V - S.card := by
    dsimp only [P]
    rw [Fintype.card_compl_set]
    congr 1
    exact Fintype.card_coe S
  have fit : Fintype.card (↥({v}ᶜ : Set W)) ≤ Fintype.card P := by
    rw [Fintype.card_compl_set, room]
    simp only [Fintype.card_unique]
    omega
  have inherit : ¬ cycleGraph 4 ⊑ G.induce P :=
    fun c => free (c.trans ⟨Copy.induce G P⟩)
  have swap : (G.induce P)ᶜ = Gᶜ.induce P := by
    ext a b
    simp [SimpleGraph.compl_adj, SimpleGraph.induce, Subtype.ext_iff]
  rw [← swap]
  by_cases small : J.edgeFinset.card ≤ 1
  · apply one_edge_or_empty J (G.induce P) fit small _ inherit
    have := H.degree_lt_card_verts v
    omega
  apply restore_isolates _ J fit
  apply square_of_base base (G.induce P) (J.induce J.support)
  · intro i
    rw [J.degree_induce_support, J.degree_pos_iff_mem_support]
    exact i.prop
  · rw [J.card_edgeFinset_induce_support]
    omega
  · rw [J.card_edgeFinset_induce_support]
    have := H.degree_le_card_edgeFinset v
    omega
  · exact inherit
termination_by H.edgeFinset.card
decreasing_by
  classical
  rw [J.card_edgeFinset_induce_support, cnt]
  omega

end OMA

/- The remaining square targets: stars, isolated edges, and small graphs -/

namespace OMA
open SimpleGraph

private theorem base_aux {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (H : SimpleGraph W) [DecidableRel H.Adj] (pos : ∀ i, 0 < H.degree i)
    (exc : H.edgeFinset.card ≤ 3 ∨ ∀ v w, 2 ≤ H.degree v → 2 ≤ H.degree w → v = w)
    (two : 2 ≤ H.edgeFinset.card) (size : 2 * H.edgeFinset.card + 1 ≤ Fintype.card V)
    (free : ¬ cycleGraph 4 ⊑ G) : H ⊑ Gᶜ := by
  classical
  by_cases pair : ∃ a b, H.Adj a b ∧ H.degree a = 1 ∧ H.degree b = 1
  · obtain ⟨a,b,ab,ha,hb⟩ := pair
    obtain ⟨x,y,z,t,⟨xy,xz,xt,yz,yt,zt⟩,e1,e2⟩ := square_pair_witness G (by omega) free
    let P : Set W := {a,b}
    let Q : Set V := {x,y}
    let J := H.induce Pᶜ
    obtain ⟨cnt,extend⟩ := small_remove_pair G H ab ha hb e1
    change J.edgeFinset.card = H.edgeFinset.card - 1 at cnt
    apply extend
    have dc (i : ↥Pᶜ) : J.degree i = H.degree i.val := by
      apply degree_induce_of_neighborSet_subset
      intro j e jp
      rcases jp with rfl|rfl
      · exact i.prop (Or.inr ((degree_eq_one_iff_existsUnique_adj.mp ha).unique
          (show H.Adj _ _ from e).symm ab))
      · exact i.prop (Or.inl ((degree_eq_one_iff_existsUnique_adj.mp hb).unique
          (show H.Adj _ _ from e).symm ab.symm))
    have room : Fintype.card (↥Qᶜ) = Fintype.card V - 2 := by
      rw [Fintype.card_compl_set]
      congr 1
      exact Set.toFinset_card (s := Q) ▸ (by simp [Q,xy] : Q.toFinset.card = 2)
    have size' : 2 * J.edgeFinset.card + 1 ≤ Fintype.card (↥Qᶜ) := by omega
    have red : ¬ cycleGraph 4 ⊑ G.induce Qᶜ := fun h => free (h.trans ⟨Copy.induce ..⟩)
    have flip : (G.induce Qᶜ)ᶜ = Gᶜ.induce Qᶜ := by
      ext u v
      simp [SimpleGraph.compl_adj,SimpleGraph.induce,Subtype.ext_iff]
    rw [← flip]
    by_cases tiny : J.edgeFinset.card ≤ 1
    · have fit : Fintype.card (↥Pᶜ) ≤ Fintype.card (↥Qᶜ) := calc
        _ = ∑ _ : ↥Pᶜ, 1 := by simp
        _ ≤ ∑ i, J.degree i := Finset.sum_le_sum fun i _ => by rw [dc]; exact pos _
        _ = _ := J.sum_degrees_eq_twice_card_edges
        _ ≤ _ := by omega
      let z' : ↥Qᶜ := ⟨z,by simp [Q,xz.symm,yz.symm]⟩
      let t' : ↥Qᶜ := ⟨t,by simp [Q,xt.symm,yt.symm]⟩
      exact small_copy_one_edge J (G.induce Qᶜ) fit tiny
        (x := z') (y := t') ⟨(fun h => zt (congrArg Subtype.val h)),e2.2⟩
    apply base_aux (G.induce Qᶜ) J
    · intro i
      rw [dc]
      exact pos _
    · rcases exc with h|h
      · exact Or.inl (by omega)
      · exact Or.inr fun i j hi hj => Subtype.ext (h _ _ (dc i ▸ hi) (dc j ▸ hj))
    · omega
    · exact size'
    · exact red
  push Not at pair
  by_cases center : ∀ v w, 2 ≤ H.degree v → 2 ≤ H.degree w → v = w
  · obtain ⟨v,hv⟩ : ∃ v, 2 ≤ H.degree v := by
      by_contra! low
      have nonempty : H.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨e,he⟩ := nonempty
      induction e using Sym2.inductionOn with
      | _ a b =>
        have adj : H.Adj a b := H.mem_edgeFinset.mp he
        have da := pos a
        have db := pos b
        exact (pair a b adj (by have := low a; omega)) (by have := low b; omega)
    apply small_star_copy G H v pos _ hv _ free
    · intro i j e
      by_contra! h
      have di : H.degree i = 1 := by
        have := pos i
        by_contra! ne
        exact h.1 (center _ _ (by omega) hv)
      have dj : H.degree j = 1 := by
        have := pos j
        by_contra! ne
        exact h.2 (center _ _ (by omega) hv)
      exact pair i j e di dj
    · have := H.degree_le_card_edgeFinset v
      omega
  · have tiny := exc.resolve_right center
    push Not at center
    obtain ⟨v,w,hv,hw,ne⟩ := center
    have order := small_two_high_order H pos hv hw ne
    have dv := H.degree_lt_card_verts v
    apply square_small_order G H pos tiny (by omega) (by omega) free
termination_by H.edgeFinset.card
decreasing_by omega

theorem square_base : SquareBase := fun G H => base_aux G H

end OMA

/- The red-degree bound and the vertex-extension step for triangles -/

namespace OMA
open SimpleGraph

theorem triangle_neighbors_blue {V : Type*} (G : SimpleGraph V) (v : V)
    (free : ¬ cycleGraph 3 ⊑ G) : Gᶜ.IsClique (G.neighborSet v) := by
  intro a ha b hb ab
  refine ⟨ab, fun e => free ?_⟩
  change G.Adj v a at ha
  change G.Adj v b at hb
  let f : Fin 3 → V := ![v,a,b]
  have na := ha.ne
  have nb := hb.ne
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      first | exact ha | exact hb | exact e | exact ha.symm | exact hb.symm | exact e.symm | exact False.elim (h.ne rfl)
  · intro i j
    change f i = f j → i = j
    fin_cases i <;> fin_cases j <;> simp_all [f,ne_comm]

theorem triangle_high_degree {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) (v : V)
    (large : Fintype.card W ≤ G.degree v) (free : ¬ cycleGraph 3 ⊑ G) : H ⊑ Gᶜ := by
  obtain ⟨f⟩ : Nonempty (W ↪ G.neighborSet v) :=
    Function.Embedding.nonempty_of_card_le (by rwa [G.card_neighborSet_eq_degree])
  let g := f.trans (Function.Embedding.subtype _)
  exact ⟨⟨⟨g, fun {a b} e => triangle_neighbors_blue G v free (f a).prop (f b).prop
    (g.injective.ne e.ne)⟩,g.injective⟩⟩

/-- Goddard–Kleitman's single-vertex extension inequality. The unused vertices
in a failed extension are covered by the red neighborhoods of the required neighbors. -/
theorem triangle_extension_bound {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (v : W) (f : (H.induce {v}ᶜ).Copy Gᶜ) (no : ¬ H ⊑ Gᶜ) {t : ℕ}
    (bound : ∀ x, G.degree x ≤ t) :
    Fintype.card V + 1 ≤ Fintype.card W + H.degree v * t := by
  classical
  let R : Finset V := Finset.univ.image f
  let idx (i : ↥(H.neighborFinset v)) : ↥({v}ᶜ : Set W) :=
    ⟨i.val, ((H.mem_neighborFinset _ _).mp i.prop).ne.symm⟩
  let A (i : ↥(H.neighborFinset v)) := G.neighborFinset (f (idx i))
  have cover : Rᶜ ⊆ Finset.univ.biUnion A := by
    intro x hx
    by_contra miss
    apply no (small_extend v f x _ _)
    · intro i eq
      exact Finset.mem_compl.mp hx (eq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i))
    · intro i hi
      refine ⟨fun eq => Finset.mem_compl.mp hx (eq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i)), ?_⟩
      intro red
      exact miss (Finset.mem_biUnion.mpr ⟨⟨i.val,(H.mem_neighborFinset _ _).mpr hi⟩,
        Finset.mem_univ _, (G.mem_neighborFinset _ _).mpr red.symm⟩)
  have count : Rᶜ.card ≤ H.degree v * t := calc
    _ ≤ _ := Finset.card_le_card cover
    _ ≤ ∑ i, (A i).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : ↥(H.neighborFinset v), t :=
      Finset.sum_le_sum fun i _ => by simpa [A] using bound (f (idx i))
    _ = _ := by simp
  have hc : R.card = Fintype.card W - 1 := by
    change (Finset.univ.image (fun i => f i)).card = _
    rw [Finset.card_image_of_injective (f := fun i => f i) _ f.injective, Finset.card_univ, Fintype.card_compl_set,
      @Fintype.card_unique (↥({v} : Set W))]
  have htotal := Finset.card_compl_add_card R
  have hn : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

end OMA

/- Contracting an edge between two minimum-degree vertices -/

namespace OMA
open SimpleGraph
open scoped Sym2

/-- Identifying the endpoints of an edge maps it to a loop, which is absent
from the image simple graph. Hence the image has strictly fewer edges. -/
theorem small_map_edge_lt {W U : Type} [Fintype W] [Fintype U]
    (H : SimpleGraph W) [DecidableRel H.Adj] (f : W → U) [DecidableRel (H.map f).Adj]
    {a b : W} (adj : H.Adj a b) (eq : f a = f b) :
    (H.map f).edgeFinset.card < H.edgeFinset.card := by
  classical
  let e := s(a,b)
  have he : e ∈ H.edgeFinset := H.mem_edgeFinset.mpr adj
  have sub : (H.map f).edgeFinset ⊆ (H.edgeFinset.erase e).image (Sym2.map f) := by
    intro p
    induction p using Sym2.inductionOn with
    | _ x y =>
      intro hp
      obtain ⟨ne,u,v,hu,rfl,rfl⟩ := (H.map_adj' f x y).mp ((H.map f).mem_edgeFinset.mp hp)
      apply Finset.mem_image.mpr
      refine ⟨s(u,v),Finset.mem_erase.mpr ⟨?_,H.mem_edgeFinset.mpr hu⟩,rfl⟩
      intro clash
      obtain h|h := Sym2.eq_iff.mp clash <;> obtain ⟨rfl,rfl⟩ := h
      · exact ne eq
      · exact ne eq.symm
  exact ((Finset.card_le_card sub).trans Finset.card_image_le).trans_lt (Finset.card_erase_lt_of_mem he)

private theorem candidates_two {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V)
    [DecidableRel G.Adj] (F : W → V) (P : Finset W) (R : Finset V) {d : ℕ}
    (low : ∀ x, G.degree x ≤ Fintype.card W - 1)
    (hp : P.card + 1 ≤ d) (hr : R.card + 1 ≤ Fintype.card W)
    (big : d * Fintype.card W + 1 ≤ Fintype.card V) :
    ∃ x y, x ≠ y ∧ x ∉ R ∧ y ∉ R ∧
      (∀ i ∈ P, ¬ G.Adj x (F i)) ∧ (∀ i ∈ P, ¬ G.Adj y (F i)) := by
  classical
  let B := P.biUnion (fun i => G.neighborFinset (F i))
  have cb : B.card ≤ P.card * (Fintype.card W - 1) := calc
    _ ≤ ∑ i ∈ P, (G.neighborFinset (F i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ P, (Fintype.card W - 1) := Finset.sum_le_sum fun i _ => low _
    _ = _ := by simp
  have tot := Finset.card_compl_add_card (R ∪ B)
  have cu := Finset.card_union_le R B
  have bound := Nat.mul_le_mul_right (Fintype.card W - 1) hp
  rw [Nat.add_mul,one_mul] at bound
  have eq : Fintype.card W - 1 + 1 = Fintype.card W := by omega
  have sub : d * (Fintype.card W - 1) + d = d * Fintype.card W := by
    conv_rhs => rw [← eq,Nat.mul_add,Nat.mul_one]
  have many : 1 < (R ∪ B)ᶜ.card := by omega
  obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp many
  have outside {z} (h : z ∈ (R ∪ B)ᶜ) : z ∉ R ∧ ∀ i ∈ P, ¬ G.Adj z (F i) := by
    have out := Finset.mem_compl.mp h
    refine ⟨fun hz => out (Finset.mem_union_left _ hz), fun i hi bad => ?_⟩
    exact out (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i,hi,(G.mem_neighborFinset _ _).mpr bad.symm⟩))
  exact ⟨x,y,ne,(outside hx).1,(outside hy).1,(outside hx).2,(outside hy).2⟩

/-- A copy with the adjacent vertices u,v identified extends back to the
original graph when both have degree d and the host has at least dn+1 vertices. -/
theorem triangle_split_pair {V W : Type} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (u v : W) (uv : H.Adj u v) (same : H.degree u = H.degree v)
    (large : H.degree u * Fintype.card W + 1 ≤ Fintype.card V)
    (free : ¬ cycleGraph 3 ⊑ G)
    (f : (H.map (fun i => if i = u then v else i)).Copy Gᶜ) : H ⊑ Gᶜ := by
  classical
  by_contra no
  let F := fun i => f i
  let P : Set W := {u,v}
  let R := (Finset.univ.erase u).image F
  have low (x : V) : G.degree x ≤ Fintype.card W - 1 := by
    have hn : ¬ Fintype.card W ≤ G.degree x := fun hi => no (triangle_high_degree G H x hi free)
    omega
  have hr : R.card + 1 ≤ Fintype.card W := by
    have h := Finset.card_image_le (f := F) (s := Finset.univ.erase u)
    have c := Finset.card_erase_add_one (Finset.mem_univ u)
    simpa only [R,Finset.card_univ] using (Nat.add_le_add_right h 1).trans_eq c
  let A := (H.neighborFinset u).erase v
  let B := (H.neighborFinset v).erase u
  have ca : A.card + 1 = H.degree u :=
    Finset.card_erase_add_one ((H.mem_neighborFinset _ _).mpr uv)
  have cb : B.card + 1 = H.degree v :=
    Finset.card_erase_add_one ((H.mem_neighborFinset _ _).mpr uv.symm)
  obtain ⟨x,_,_,hx,_,gx,_⟩ := candidates_two G F A R low ca.le hr large
  obtain ⟨y,z,yz,hy,hz,gy,gz⟩ := candidates_two G F B R low (cb.trans same.symm).le hr large
  obtain ⟨y,xy,hy,gy⟩ : ∃ y, x ≠ y ∧ y ∉ R ∧ ∀ i ∈ B, ¬G.Adj y (F i) := by
    by_cases eq : x = y
    · exact ⟨z,eq ▸ yz,hz,gz⟩
    · exact ⟨y,eq,hy,gy⟩
  have inR {i : W} (h : i ≠ u) : F i ∈ R :=
    Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨h,Finset.mem_univ _⟩)
  have lift {a b : W} (e : H.Adj a b) (na : a ≠ u) (nb : b ≠ u) : Gᶜ.Adj (F a) (F b) := by
    apply f.toHom.map_rel'
    exact ⟨e.ne,a,b,e,if_neg na,if_neg nb⟩
  let g : (H.induce Pᶜ).Copy Gᶜ := ⟨⟨fun i => F i.val,fun {i j} e =>
    lift e (fun h => i.prop (Or.inl h)) (fun h => j.prop (Or.inl h))⟩,
    fun {_ _} e => Subtype.ext (f.injective e)⟩
  let Good (w : W) (p : V) := (∀ i, p ≠ g i) ∧ ∀ i, H.Adj w i.val → Gᶜ.Adj p (g i)
  have fresh {x : V} (hx : x ∉ R) (i : ↥Pᶜ) : x ≠ g i :=
    fun e => hx (e ▸ inR (fun h => i.prop (Or.inl h)))
  have goodx : Good u x := ⟨fresh hx,fun i hi =>
    ⟨fresh hx i,gx _ (Finset.mem_erase.mpr ⟨fun h => i.prop (Or.inr h),
      (H.mem_neighborFinset _ _).mpr hi⟩)⟩⟩
  have goody : Good v y := ⟨fresh hy,fun i hi =>
    ⟨fresh hy i,gy _ (Finset.mem_erase.mpr ⟨fun h => i.prop (Or.inl h),
      (H.mem_neighborFinset _ _).mpr hi⟩)⟩⟩
  have central (i : ↥Pᶜ) : F v ≠ g i :=
    fun e => i.prop (Or.inr (f.injective e).symm)
  have centeru : Good u (F v) := by
    refine ⟨central,fun i hi => f.toHom.map_rel' ?_⟩
    exact ⟨fun h => i.prop (Or.inr h.symm),u,i.val,hi,if_pos rfl,
      if_neg (fun h => i.prop (Or.inl h))⟩
  have centerv : Good v (F v) := ⟨central,fun i hi =>
    lift hi uv.ne.symm (fun h => i.prop (Or.inl h))⟩
  have place {p q} (gu : Good u p) (gv : Good v q) (pq : Gᶜ.Adj p q) : False := by
    let k (i : P) := if i.val = u then p else q
    have inj : Function.Injective k := by
      intro i j h
      apply Subtype.ext
      rcases i.prop with hi|hi <;> rcases j.prop with hj|hj <;>
        simp_all [k,Set.mem_singleton_iff,uv.ne,pq.ne,pq.ne.symm]
    let c : (H.induce P).Copy Gᶜ := ⟨⟨k,fun {i j} h => by
      have ne := inj.ne h.ne
      dsimp only [k] at ne ⊢
      split_ifs at ne ⊢ <;> first | contradiction | exact pq | exact pq.symm⟩,inj⟩
    apply no (join_copies Gᶜ H P c g _ _)
    · intro i j
      change (if i.val = u then p else q) ≠ g j
      split <;> first | exact gu.1 j | exact gv.1 j
    · intro i j h
      change Gᶜ.Adj (if i.val = u then p else q) (g j)
      rcases i.prop with hi|hi
      · rw [if_pos hi]
        exact gu.2 j (hi ▸ h)
      · have e : i.val = v := hi
        rw [if_neg (e ▸ uv.ne.symm)]
        exact gv.2 j (e ▸ h)
  have xv : x ≠ F v := fun h => hx (h ▸ inR uv.ne.symm)
  have yv : y ≠ F v := fun h => hy (h ▸ inR uv.ne.symm)
  by_cases rx : G.Adj (F v) x
  · by_cases ry : G.Adj (F v) y
    · exact place goodx goody (triangle_neighbors_blue G (F v) free rx ry xy)
    · exact place centeru goody ⟨yv.symm,ry⟩
  · exact place goodx centerv ⟨xv,fun e => rx e.symm⟩

end OMA

/- The sharp triangle bound for every tree -/

namespace OMA
open SimpleGraph

theorem triangle_tree {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (H : SimpleGraph W) (tree : H.IsTree) (big : 2 * Fintype.card W ≤ Fintype.card V + 1)
    (free : ¬ cycleGraph 3 ⊑ G) : H ⊑ Gᶜ := by
  classical
  cases subsingleton_or_nontrivial W with
  | inl h =>
    have hn := Fintype.card_le_one_iff_subsingleton.mpr h
    obtain ⟨f⟩ : Nonempty (W ↪ V) := Function.Embedding.nonempty_of_card_le (by omega)
    exact ⟨⟨⟨f,fun {a b} e => False.elim (e.ne (h.elim a b))⟩,f.injective⟩⟩
  | inr h =>
    obtain ⟨v,hv⟩ := tree.exists_vert_degree_one_of_nontrivial
    let J := H.induce ({v}ᶜ : Set W)
    have order : Fintype.card (↥({v}ᶜ : Set W)) = Fintype.card W - 1 := by
      rw [Fintype.card_compl_set,@Fintype.card_unique (↥({v} : Set W))]
    have jt : J.IsTree := ⟨tree.connected.induce_compl_singleton_of_degree_eq_one hv,
      tree.isAcyclic.comap (Copy.induce H _).toHom (Copy.induce H _).injective⟩
    obtain ⟨f⟩ := triangle_tree G J jt (by omega) free
    by_contra no
    have low (x : V) : G.degree x ≤ Fintype.card W - 1 := by
      have hn : ¬ Fintype.card W ≤ G.degree x := fun hi => no (triangle_high_degree G H x hi free)
      omega
    have cover := triangle_extension_bound G H v f no low
    rw [hv,one_mul] at cover
    have pos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨v⟩
    omega
termination_by Fintype.card W
decreasing_by
  classical
  rw [order]
  have := Fintype.card_pos_iff.mpr (show Nonempty W from ⟨v⟩)
  omega

end OMA

/- Strong induction for the triangle bound

The extra host requirement is C + m. It absorbs finite starting cases and
disappears once m is large. In a disconnected target a cyclic component
uses at most one vertex per edge. A tree component can instead be embedded last.
-/

namespace OMA
open SimpleGraph Filter

/-- Only connected targets whose minimum-degree vertices are independent
need the averaging argument. The smaller vertex-deleted copy is supplied. -/
def IndependentMinimumStep (K : ℕ) : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel H.Adj] (v : W), H.Connected → K ≤ H.edgeFinset.card →
    H.degree v = H.minDegree → 2 ≤ H.degree v →
    H.IsIndepSet {i | H.degree i = H.degree v} →
    2 * H.edgeFinset.card + 1 ≤ Fintype.card V → ¬ cycleGraph 3 ⊑ G →
    H.induce {v}ᶜ ⊑ Gᶜ → H ⊑ Gᶜ

private theorem vertex_budget {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (pos : ∀ i, 0 < H.degree i) : Fintype.card W ≤ 2 * H.edgeFinset.card := calc
  _ = ∑ _ : W, 1 := by simp
  _ ≤ ∑ i, H.degree i := Finset.sum_le_sum fun i _ => pos i
  _ = _ := H.sum_degrees_eq_twice_card_edges

private theorem triangle_induct {K : ℕ} (step : IndependentMinimumStep K)
    {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel H.Adj] (pos : ∀ i, 0 < H.degree i)
    (size : 2*H.edgeFinset.card+1 ≤ Fintype.card V)
    (room : graphRamsey (cycleGraph 3) (completeGraph (Fin (2*K))) + H.edgeFinset.card ≤ Fintype.card V)
    (free : ¬ cycleGraph 3 ⊑ G) : H ⊑ Gᶜ := by
  classical
  by_cases small : H.edgeFinset.card < K ∨ H.edgeFinset.card = 0
  · have hn := vertex_budget H pos
    obtain ⟨f⟩ : Nonempty (W ↪ Fin (2*K)) := Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_fin]; omega)
    have sub : H ⊑ completeGraph (Fin (2*K)) := ⟨⟨⟨f,fun {i j} e => f.injective.ne e.ne⟩,f.injective⟩⟩
    exact sub.trans ((graphRamsey_host (cycleGraph 3) _ G (by omega)).resolve_left free)
  have both := not_or.mp small
  have : Nonempty W := by
    by_contra! empty
    have zero : H.edgeFinset.card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e
      induction e using Sym2.inductionOn with | _ a _ => exact isEmptyElim a
    exact both.2 zero
  by_cases conn : H.Connected
  · obtain ⟨v,hv⟩ := H.exists_minimal_degree_vertex
    let J := H.induce ({v}ᶜ : Set W)
    have cnt : J.edgeFinset.card = H.edgeFinset.card - H.degree v :=
      (H.card_edgeFinset_induce_compl_singleton v).trans (H.card_edgeFinset_deleteIncidenceSet v)
    have je : (J.induce J.support).edgeFinset.card < H.edgeFinset.card := by
      rw [J.card_edgeFinset_induce_support,cnt]
      have := pos v
      omega
    have support_copy := triangle_induct step G (J.induce J.support) (fun i => by
      rw [J.degree_induce_support,J.degree_pos_iff_mem_support]; exact i.prop) (by omega) (by omega) free
    have hn := vertex_budget H pos
    have fit : Fintype.card (↥({v}ᶜ : Set W)) ≤ Fintype.card V :=
      (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans (by omega)
    have partialCopy := restore_isolates Gᶜ J fit support_copy
    by_cases leaf : H.degree v = 1
    · obtain ⟨f⟩ := partialCopy
      by_contra no
      have low (x : V) : G.degree x ≤ Fintype.card W - 1 := by
        have hn : ¬ Fintype.card W ≤ G.degree x := fun hi => no (triangle_high_degree G H x hi free)
        omega
      have ord : Fintype.card W ≤ H.edgeFinset.card + 1 := by
        simpa only [Nat.card_eq_fintype_card,edgeFinset_card] using conn.card_vert_le_card_edgeSet_add_one
      have cover := triangle_extension_bound G H v f no low
      rw [leaf,one_mul] at cover
      omega
    by_cases ind : H.IsIndepSet {i | H.degree i = H.degree v}
    · exact step G H v conn (by omega) hv.symm (by have := pos v; omega) ind size free partialCopy
    rw [isIndepSet_iff, Set.Pairwise] at ind
    push Not at ind
    obtain ⟨a,ha,b,hb,_,ab⟩ := ind
    change H.degree a = H.degree v at ha
    change H.degree b = H.degree v at hb
    let τ := fun i => if i = a then b else i
    let L := H.map τ
    have lt : L.edgeFinset.card < H.edgeFinset.card :=
      small_map_edge_lt H τ ab (by simp [τ])
    have lc := triangle_induct step G (L.induce L.support) (fun i => by
      rw [L.degree_induce_support,L.degree_pos_iff_mem_support]; exact i.prop)
      (by rw [L.card_edgeFinset_induce_support]; omega)
      (by rw [L.card_edgeFinset_induce_support]; omega) free
    obtain ⟨f⟩ := restore_isolates Gᶜ L (by omega) lc
    apply triangle_split_pair G H a b ab (ha.trans hb.symm) _ free f
    have sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => H.minDegree_le_degree i)
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,H.sum_degrees_eq_twice_card_edges] at sum
    rw [ha,← hv,Nat.mul_comm]
    omega
  · have dis : ¬ ∀ u w, H.Reachable u w := fun c => conn
        ((H.connected_iff_exists_forall_reachable).mpr ⟨Classical.arbitrary W,c _⟩)
    push Not at dis
    obtain ⟨u,w,uw⟩ := dis
    let P := {x | H.Reachable u x}
    let J := H.induce P
    let L := H.induce Pᶜ
    have ldeg (i : ↥P) : J.degree i = H.degree i.val :=
      degree_induce_of_neighborSet_subset (fun _ e => i.prop.trans (show H.Adj _ _ from e).reachable)
    have rdeg (i : ↥Pᶜ) : L.degree i = H.degree i.val :=
      degree_induce_of_neighborSet_subset (fun _ e p => i.prop (p.trans (show H.Adj _ _ from e).symm.reachable))
    have parts := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ P) (fun i => H.degree i)
    change (∑ i : ↥P, H.degree i.val) + (∑ i : ↥Pᶜ, H.degree i.val) = _ at parts
    simp_rw [← ldeg,← rdeg] at parts
    rw [J.sum_degrees_eq_twice_card_edges,L.sum_degrees_eq_twice_card_edges,
      H.sum_degrees_eq_twice_card_edges] at parts
    have jpos (i : ↥P) : 0 < J.degree i := ldeg i ▸ pos i.val
    have lpos (i : ↥Pᶜ) : 0 < L.degree i := rdeg i ▸ pos i.val
    have jj := (jpos ⟨u,Reachable.refl _⟩).trans_le (J.degree_le_card_edgeFinset _)
    have ll := (lpos ⟨w,uw⟩).trans_le (L.degree_le_card_edgeFinset _)
    have jlt : J.edgeFinset.card < H.edgeFinset.card := by omega
    have llt : L.edgeFinset.card < H.edgeFinset.card := by omega
    have cross (i : P) (j : ↥Pᶜ) (e : H.Adj i.val j.val) : False := j.prop (i.prop.trans e.reachable)
    have flip (S : Set V) : (G.induce S)ᶜ = Gᶜ.induce S := by
      ext a b
      simp [SimpleGraph.compl_adj,SimpleGraph.induce,Subtype.ext_iff]
    by_cases sparse : Fintype.card P ≤ J.edgeFinset.card
    · obtain ⟨f⟩ := triangle_induct step G J jpos (by omega) (by omega) free
      let R := Set.range f
      have cr : Fintype.card R = Fintype.card P :=
        (Fintype.card_congr (Equiv.ofInjective f f.injective)).symm
      have restSize : Fintype.card (↥Rᶜ) = Fintype.card V - Fintype.card P := by
        rw [Fintype.card_compl_set,cr]
      have rest := triangle_induct step (G.induce Rᶜ) L lpos (by omega) (by omega)
        (fun c => free (c.trans ⟨Copy.induce ..⟩))
      rw [flip] at rest
      obtain ⟨g⟩ := rest
      exact join_copies Gᶜ H P f ((Copy.induce Gᶜ Rᶜ).comp g)
        (fun i j e => (g j).prop ⟨i,e⟩) (fun i j e => (cross i j e).elim)
    · have connected : J.Connected := by
        have eq : P = (H.connectedComponentMk u).supp := by
          ext x
          exact ⟨fun r => ConnectedComponent.sound r.symm,fun r => (ConnectedComponent.exact r).symm⟩
        change (H.induce P).Connected
        rw [eq]
        exact (H.connectedComponentMk u).maximal_connected_induce_supp.1
      have ord : Fintype.card P ≤ J.edgeFinset.card + 1 := by
        simpa only [Nat.card_eq_fintype_card,edgeFinset_card] using connected.card_vert_le_card_edgeSet_add_one
      have tree : J.IsTree := (isTree_iff_connected_and_card).mpr ⟨connected,by
        simp only [Nat.card_eq_fintype_card,← edgeFinset_card]; omega⟩
      obtain ⟨g⟩ := triangle_induct step G L lpos (by omega) (by omega) free
      let R := Set.range g
      have cr : Fintype.card R = Fintype.card (↥Pᶜ) :=
        (Fintype.card_congr (Equiv.ofInjective g g.injective)).symm
      have restSize : Fintype.card (↥Rᶜ) = Fintype.card V - Fintype.card (↥Pᶜ) := by
        rw [Fintype.card_compl_set,cr]
      have vert := vertex_budget L lpos
      have rest := triangle_tree (G.induce Rᶜ) J tree (by omega)
        (fun c => free (c.trans ⟨Copy.induce ..⟩))
      rw [flip] at rest
      obtain ⟨f⟩ := rest
      exact join_copies Gᶜ H P ((Copy.induce Gᶜ Rᶜ).comp f) g
        (fun i j e => (f i).prop ⟨j,e.symm⟩) (fun i j e => (cross i j e).elim)
termination_by H.edgeFinset.card
decreasing_by
  all_goals classical
  all_goals first | assumption | rw [L.card_edgeFinset_induce_support]; exact lt

theorem triangle_forces_of_independent {K : ℕ} (step : IndependentMinimumStep K) :
    ∀ᶠ m : ℕ in atTop, Forces 3 m (2*m+1) := by
  apply eventually_atTop.mpr
  refine ⟨graphRamsey (cycleGraph 3) (completeGraph (Fin (2*K))),fun m hm W _ H _ pos he _ G => ?_⟩
  by_cases red : cycleGraph 3 ⊑ G
  · exact Or.inl red
  · have count : H.edgeFinset.card = m := by rw [edgeFinset_card,← Nat.card_eq_fintype_card]; exact he
    exact Or.inr (triangle_induct step G H pos (by simp [count]) (by simp only [Fintype.card_fin,count]; omega) red)

end OMA

/- Edge and degree counts for an independent set and a largest clique -/

namespace OMA
open SimpleGraph
open scoped Sym2 Classical

theorem independent_degree_edges {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (P : Set W) (ind : H.IsIndepSet P) {d : ℕ}
    (deg : ∀ i : P, H.degree i.val = d) : Fintype.card P * d ≤ H.edgeFinset.card := by
  classical
  let I := Σ i : ↥P, H.neighborSet i.val
  let F (i : I) : H.edgeSet := ⟨s(i.1.val,i.2.val),i.2.prop⟩
  have inj : Function.Injective F := by
    rintro ⟨i,j⟩ ⟨k,l⟩ eq
    have e : s(i.val,j.val) = s(k.val,l.val) := congrArg Subtype.val eq
    rcases Sym2.eq_iff.mp e with ⟨ik,jl⟩|⟨_,jk⟩
    · have h : i = k := Subtype.ext ik
      subst k
      exact congrArg (Sigma.mk i) (Subtype.ext jl)
    · have adj : H.Adj i.val j.val := j.prop
      exact (ind i.prop (jk.symm ▸ k.prop) adj.ne adj).elim
  have := Fintype.card_le_of_injective F inj
  simpa only [I,Fintype.card_sigma,card_neighborSet_eq_degree,deg,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,← edgeFinset_card] using this

theorem degree_surplus {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] {d : ℕ} (low : ∀ i, d ≤ H.degree i)
    (P : Set W) (defP : ∀ i, i ∈ P ↔ H.degree i = d) :
    (d+1)*Fintype.card W ≤ 2*H.edgeFinset.card + Fintype.card P := by
  classical
  have bound (i : W) : d+1 ≤ H.degree i + if i ∈ P then 1 else 0 := by
    have := low i
    split_ifs with h
    · omega
    · have ne := mt (defP i).mpr h
      omega
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => bound i)
  simp only [Finset.sum_add_distrib,H.sum_degrees_eq_twice_card_edges,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one,Finset.sum_boole] at sum
  simpa only [Nat.cast_id,Fintype.card_subtype,Nat.add_mul,one_mul,Nat.mul_comm d] using sum

/-- Thin the allowed blue edges so each clique vertex has exactly Y-t
outside neighbors. This gives a uniform upper bound for each candidate row. -/
theorem small_thin_columns {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (T : Finset V) (low : ∀ x, G.degree x ≤ T.card)
    (y : ℕ) (cy : Fintype.card (↥Tᶜ) = y) :
    ∃ B : ↥Tᶜ → Finset ↥T,
      (∀ j i, i ∈ B j → Gᶜ.Adj i.val j.val) ∧
      (∀ i : ↥T, (Finset.univ.filter (fun j : ↥Tᶜ => i ∈ B j)).card = y-T.card) ∧
      ∑ j, (B j).card = T.card * (y-T.card) := by
  classical
  let A (i : ↥T) := Finset.univ.filter (fun j : ↥Tᶜ => ¬G.Adj i.val j.val)
  have num (i : ↥T) : y-T.card ≤ (A i).card := by
    let bad := Finset.univ.filter (fun j : ↥Tᶜ => G.Adj i.val j.val)
    have sub : bad.map (Function.Embedding.subtype _) ⊆ G.neighborFinset i.val := by
      intro z hz
      obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hz
      exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hk).2
    have le := Finset.card_le_card sub
    simp only [Finset.card_map,card_neighborFinset_eq_degree] at le
    have eq : bad.card + (A i).card = y := by
      rw [← cy,← Finset.card_univ]
      exact Finset.card_filter_add_card_filter_not ..
    have := low i
    omega
  choose C sub card using fun i => Finset.exists_subset_card_eq (num i)
  let B (j : ↥Tᶜ) := Finset.univ.filter (fun i : ↥T => j ∈ C i)
  have exactC (i : ↥T) : Finset.univ.filter (fun j : ↥Tᶜ => i ∈ B j) = C i := by ext j; simp [B]
  refine ⟨B,?_,fun i => (congrArg Finset.card (exactC i)).trans (card i),?_⟩
  · intro j i hi
    have good := (Finset.mem_filter.mp (sub i (Finset.mem_filter.mp hi).2)).2
    exact ⟨fun eq => (Finset.mem_compl.mp j.prop) (eq ▸ i.prop),good⟩
  · calc
      _ = ∑ j : ↥Tᶜ, ∑ i : ↥T, if j ∈ C i then 1 else 0 := by simp [B]
      _ = ∑ i : ↥T, ∑ j : ↥Tᶜ, if j ∈ C i then 1 else 0 := Finset.sum_comm
      _ = _ := by
        have row (i : ↥T) : (∑ j : ↥Tᶜ, if j ∈ C i then 1 else 0) = y-T.card := by
          rw [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter,card,Nat.cast_id]
        simp only [row,Finset.sum_const,Finset.card_univ,smul_eq_mul,Fintype.card_coe]

end OMA

/- Placing independent vertices inside and outside a clique -/

namespace OMA
open SimpleGraph

/-- All rows may use the same spare vertices. Outside that reserve each row has
at most D choices. A failure of Hall's condition bounds the total outside choices. -/
theorem small_hall_reserve {I V : Type*} [Fintype I] [DecidableEq V]
    (U : Finset V) (A : I → Finset V) (D f : ℕ)
    (apart : ∀ i, Disjoint U (A i)) (cap : ∀ i, (A i).card ≤ D)
    (slots : U.card + f = Fintype.card I)
    (edges : (f-1) * max D (Fintype.card I) < ∑ i, (A i).card) :
    ∃ g : I ↪ V, ∀ i, g i ∈ U ∪ A i := by
  classical
  suffices hall : ∀ s : Finset I, s.card ≤ (s.biUnion (fun i => U ∪ A i)).card by
    obtain ⟨g,inj,ok⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' _).mp hall
    exact ⟨⟨g,inj⟩,ok⟩
  intro s
  by_contra! fail
  have sn : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i,hi⟩ := sn
  let B := s.biUnion A
  have bd : Disjoint U B := Finset.disjoint_left.mpr (by
    intro x hx hb
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hb
    exact Finset.disjoint_left.mp (apart j) hx hj)
  have sub : U ∪ B ⊆ s.biUnion (fun i => U ∪ A i) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hu|hb
    · exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_union_left _ hu⟩
    · obtain ⟨j,hj,e⟩ := Finset.mem_biUnion.mp hb
      exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_union_right _ e⟩
  have cb := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint bd] at cb
  have count := Finset.card_compl_add_card s
  have shortage : sᶜ.card + B.card ≤ f-1 := by omega
  have sumS : ∑ j ∈ s, (A j).card ≤ s.card * B.card := calc
    _ ≤ ∑ _ ∈ s, B.card := Finset.sum_le_sum (fun j hj =>
      Finset.card_le_card (Finset.subset_biUnion_of_mem A hj))
    _ = _ := by simp
  have sumC : ∑ j ∈ sᶜ, (A j).card ≤ sᶜ.card * D := calc
    _ ≤ ∑ _ ∈ sᶜ, D := Finset.sum_le_sum (fun j _ => cap j)
    _ = _ := by simp
  have hs := Finset.card_le_univ s
  have E : (∑ i, (A i).card) ≤ (sᶜ.card + B.card) * max D (Fintype.card I) := calc
    _ = _ := (Finset.sum_add_sum_compl s _).symm
    _ ≤ s.card * B.card + sᶜ.card * D := Nat.add_le_add sumS sumC
    _ ≤ (max D (Fintype.card I)) * B.card + sᶜ.card * max D (Fintype.card I) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ (hs.trans (le_max_right ..)))
        (Nat.mul_le_mul_left _ (le_max_left ..))
    _ = _ := by ring
  exact edges.not_ge (E.trans (Nat.mul_le_mul_right _ shortage))

theorem independent_clique_placement {V W : Type*} [Fintype W] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) (P : Set W) (T : Finset V)
    (ind : H.IsIndepSet P) (cl : G.IsClique (↑T : Set V))
    (h : ↥Pᶜ ↪ T) (g : ↥P ↪ V) (apart : ∀ i j, g i ≠ (h j).val)
    (ok : ∀ i j, H.Adj i.val j.val → g i ∈ T ∨ G.Adj (g i) (h j).val) : H ⊑ G := by
  let left : (H.induce P).Copy G := ⟨⟨g,fun {i j} e =>
    (ind i.prop j.prop (show H.Adj _ _ from e).ne e).elim⟩,g.injective⟩
  let emb := h.trans (Function.Embedding.subtype _)
  let right : (H.induce Pᶜ).Copy G := ⟨⟨emb,fun {i j} e =>
    cl (h i).prop (h j).prop (emb.injective.ne e.ne)⟩,emb.injective⟩
  exact join_copies G H P left right apart (fun i j e => (ok i j e).elim
    (fun ht => cl ht (h j).prop (apart i j)) id)

end OMA

/- Averaging common-neighbor counts over placements in a clique -/

open scoped Classical

namespace OMA

private theorem small_orbit_sum {D T : Type*} [Fintype D] [Fintype T] [DecidableEq T] (e : D ↪ T)
    (score : (D ↪ T) → ℕ) :
    (Fintype.card T).descFactorial (Fintype.card D) *
      (∑ σ : Equiv.Perm T, score (e.trans σ.toEmbedding)) =
      Fintype.card (Equiv.Perm T) * ∑ f, score f := by
  classical
  let act (σ : Equiv.Perm T) (f : D ↪ T) := f.trans σ.toEmbedding
  have orbit (f : D ↪ T) :
      (∑ σ : Equiv.Perm T, score (act σ e)) = ∑ σ : Equiv.Perm T, score (act σ f) := by
    obtain ⟨τ,hτ⟩ := Equiv.Perm.exists_extending_pair e f e.injective f.injective
    let p : Equiv.Perm (Equiv.Perm T) := Equiv.mulRight τ
    apply (Fintype.sum_equiv p.symm _ _ _)
    intro σ
    congr 1
    ext x
    change σ (e x) = (σ * τ⁻¹) (f x)
    simp [Equiv.Perm.mul_apply,← hτ x]
  have action (σ : Equiv.Perm T) : (∑ f : D ↪ T, score (act σ f)) = ∑ f, score f := by
    let k := (Equiv.refl D).embeddingCongr σ
    exact k.sum_comp score
  calc
    _ = ∑ _ : D ↪ T, ∑ σ : Equiv.Perm T, score (act σ e) := by
      simp [act,Fintype.card_embedding_eq]
    _ = ∑ f : D ↪ T, ∑ σ : Equiv.Perm T, score (act σ f) :=
      Finset.sum_congr rfl (fun f _ => orbit f)
    _ = ∑ σ : Equiv.Perm T, ∑ f : D ↪ T, score (act σ f) := Finset.sum_comm
    _ = ∑ _ : Equiv.Perm T, ∑ f, score f := Finset.sum_congr rfl (fun σ _ => action σ)
    _ = _ := by simp

private theorem small_count_into {T D : Type*} [Fintype T] [Fintype D] [DecidableEq T]
    (A : Finset T) [DecidablePred (fun f : D ↪ T => ∀ j, f j ∈ A)] :
    (∑ f : D ↪ T, if ∀ j, f j ∈ A then 1 else 0) =
      A.card.descFactorial (Fintype.card D) := by
  classical
  let S := {f : D ↪ T // ∀ j, f j ∈ A}
  let E : S ≃ (D ↪ A) := {
    toFun := fun f => ⟨fun j => ⟨f.val j,f.prop j⟩,fun {_ _} eq => f.val.injective (congrArg Subtype.val eq)⟩
    invFun := fun g => ⟨g.trans (Function.Embedding.subtype _),fun j => (g j).prop⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    _ = Fintype.card S := by simp [S,Fintype.card_subtype]
    _ = _ := by rw [Fintype.card_congr E,Fintype.card_embedding_eq,Fintype.card_coe]

/-- A single permutation places the prescribed d-tuples so that the total
number of admissible outside vertices is at least its permutation average. -/
theorem permutation_placement {T Y I : Type*} [Fintype T] [Fintype Y] [Fintype I]
    [DecidableEq T] {d : ℕ} (nbr : I → Fin d ↪ T) (blue : Y → Finset T)
    [DecidableEq Y] :
    ∃ σ : Equiv.Perm T,
      Fintype.card I * (∑ y, (blue y).card.descFactorial d) ≤
        (Fintype.card T).descFactorial d *
          ∑ i, (Finset.univ.filter (fun y => ∀ j, σ (nbr i j) ∈ blue y)).card := by
  classical
  let score (f : Fin d ↪ T) := (Finset.univ.filter (fun y => ∀ j, f j ∈ blue y)).card
  have total : (∑ f, score f) = ∑ y, (blue y).card.descFactorial d := calc
    _ = ∑ f : Fin d ↪ T, ∑ y, if ∀ j, f j ∈ blue y then 1 else 0 := by
      simp [score,Finset.sum_boole]
    _ = ∑ y, ∑ f : Fin d ↪ T, if ∀ j, f j ∈ blue y then 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      simpa only [Fintype.card_fin] using (small_count_into (D := Fin d) (blue y))
  let val (σ : Equiv.Perm T) := ∑ i, score ((nbr i).trans σ.toEmbedding)
  obtain ⟨σ,_,best⟩ := Finset.exists_max_image Finset.univ val (Finset.univ_nonempty)
  refine ⟨σ,?_⟩
  change _ ≤ _ * val σ
  let p := Fintype.card (Equiv.Perm T)
  have pp : 0 < p := Fintype.card_pos
  apply Nat.le_of_mul_le_mul_left _ pp
  calc
    _ = ∑ i, (Fintype.card T).descFactorial d *
        (∑ τ : Equiv.Perm T, score ((nbr i).trans τ.toEmbedding)) := by
      have eq (i : I) : (Fintype.card T).descFactorial d *
          (∑ τ : Equiv.Perm T, score ((nbr i).trans τ.toEmbedding)) =
          p * ∑ y, (blue y).card.descFactorial d := by
        simpa only [Fintype.card_fin,total,p] using (small_orbit_sum (nbr i) score)
      simp only [eq,Finset.sum_const,Finset.card_univ,smul_eq_mul]
      ring
    _ = (Fintype.card T).descFactorial d * ∑ τ, val τ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ (Fintype.card T).descFactorial d * ∑ _ : Equiv.Perm T, val σ :=
      Nat.mul_le_mul_left _ (Finset.sum_le_sum fun τ _ => best τ (Finset.mem_univ _))
    _ = _ := by simp [p,mul_left_comm]

end OMA

/- Placing the independent minimum-degree vertices of the target -/

namespace OMA
open SimpleGraph
open scoped Classical

/-- Embed the core in the given clique, then complete the independent vertices
using the permutation average and Hall's theorem. Each clique vertex has exactly
D allowed neighbors outside; this can be imposed by discarding extra blue edges. -/
theorem small_place_average {V W : Type} [Fintype V] [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (G : SimpleGraph V)
    (P : Set W) (T : Finset V) (ind : H.IsIndepSet P) (cl : G.IsClique (↑T : Set V))
    {d f D : ℕ} (pos : 0 < d) (deg : ∀ i : P, H.degree i.val = d)
    (slots : T.card + f = Fintype.card W) (core : Fintype.card (↥Pᶜ) ≤ T.card)
    (B : ↥Tᶜ → Finset ↥T)
    (allow : ∀ y i, i ∈ B y → G.Adj i.val y.val)
    (cap : ∀ i : ↥T, (Finset.univ.filter (fun y : ↥Tᶜ => i ∈ B y)).card ≤ D)
    (bound : T.card.descFactorial d * ((f-1) * max D (Fintype.card P)) <
      Fintype.card P * ∑ y, (B y).card.descFactorial d) : H ⊑ G := by
  classical
  obtain ⟨h⟩ : Nonempty (↥Pᶜ ↪ T) := Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe])
  have nc (i : P) (j : H.neighborSet i.val) : j.val ∈ Pᶜ :=
    fun hj => ind i.prop hj (show H.Adj _ _ from j.prop).ne j.prop
  let enumer (i : P) : Fin d ≃ H.neighborSet i.val :=
    (Fintype.equivFinOfCardEq (by rw [H.card_neighborSet_eq_degree,deg])).symm
  let embed (i : P) : H.neighborSet i.val ↪ ↥Pᶜ :=
    ⟨fun j => ⟨j.val,nc i j⟩, fun {_ _} eq => Subtype.ext (congrArg (fun x : ↥Pᶜ => (x.val : W)) eq)⟩
  let n (i : P) := (enumer i).toEmbedding.trans ((embed i).trans h)
  obtain ⟨σ,good⟩ := permutation_placement n B
  let c := h.trans σ.toEmbedding
  let A' (i : P) := Finset.univ.filter (fun y : ↥Tᶜ => ∀ j, σ (n i j) ∈ B y)
  let A (i : P) := (A' i).map (Function.Embedding.subtype _)
  let used := Finset.univ.image (fun j => (c j).val)
  let U := T \ used
  have usub : used ⊆ T := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    exact (c j).prop
  have cardU : U.card + f = Fintype.card P := by
    have inj : Function.Injective (fun j => (c j).val) := fun {_ _} eq => c.injective (Subtype.ext eq)
    have usedCard : used.card = Fintype.card (↥Pᶜ) := by
      dsimp only [used]
      rw [Finset.card_image_of_injective _ inj,Finset.card_univ]
    have cu := Finset.card_sdiff_add_card_eq_card usub
    have cp := Fintype.card_compl_set P
    have cp' : Fintype.card P ≤ Fintype.card W :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    change U.card + used.card = T.card at cu
    omega
  have memA {i : P} {z} (hz : z ∈ A i) :
      ∃ y : ↥Tᶜ, y.val = z ∧ ∀ j, σ (n i j) ∈ B y := by
    obtain ⟨y,hy,e⟩ := Finset.mem_map.mp hz
    exact ⟨y,e,(Finset.mem_filter.mp hy).2⟩
  have disj (i : P) : Disjoint U (A i) := by
    apply Finset.disjoint_left.mpr
    intro z hu hz
    obtain ⟨y,rfl,_⟩ := memA hz
    exact (Finset.mem_compl.mp y.prop) (Finset.mem_sdiff.mp hu).1
  have capA (i : P) : (A i).card ≤ D := by
    rw [Finset.card_map]
    exact (Finset.card_le_card (s := A' i) (t := Finset.univ.filter (fun y : ↥Tᶜ => σ (n i ⟨0,pos⟩) ∈ B y))
      (fun y hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(show ∀ j, σ (n i j) ∈ B y from (Finset.mem_filter.mp hy).2) ⟨0,pos⟩⟩)).trans (cap _)
  have E : (f-1)*max D (Fintype.card P) < ∑ i, (A i).card := by
    have lt := bound.trans_le (by simpa only [Fintype.card_coe] using good)
    simp only [A,Finset.card_map]
    exact Nat.lt_of_mul_lt_mul_left lt
  obtain ⟨g,mem⟩ := small_hall_reserve U A D f disj capA cardU E
  apply independent_clique_placement H G P T ind cl c g
  · intro i j eq
    rcases Finset.mem_union.mp (mem i) with hu|ha
    · exact (Finset.mem_sdiff.mp hu).2 (eq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j))
    · obtain ⟨y,ey,_⟩ := memA ha
      exact (Finset.mem_compl.mp y.prop) (ey.trans eq ▸ (c j).prop)
  · intro i j e
    rcases Finset.mem_union.mp (mem i) with hu|ha
    · exact Or.inl (Finset.mem_sdiff.mp hu).1
    · obtain ⟨y,ey,ok⟩ := memA ha
      right
      rw [← ey]
      apply Adj.symm
      apply allow
      let j' : H.neighborSet i.val := ⟨j.val,e⟩
      have matchJ : embed i j' = j := Subtype.ext rfl
      have hgood := ok ((enumer i).symm j')
      change σ (h (embed i ((enumer i) ((enumer i).symm j')))) ∈ B y at hgood
      rw [Equiv.apply_symm_apply,matchJ] at hgood
      exact hgood

end OMA

/- Averaging the number of ways to choose distinct neighbors -/

namespace OMA

/-- Falling factorial on the reals, truncated at zero between its roots. -/
def smallFalling (d : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.range d, max (x - (j : ℝ)) 0

theorem smallFalling_nonneg (d : ℕ) (x : ℝ) : 0 ≤ smallFalling d x :=
  Finset.prod_nonneg fun _ _ => le_max_right _ _

theorem smallFalling_mono (d : ℕ) : Monotone (smallFalling d) := by
  intro x y xy
  exact Finset.prod_le_prod (fun _ _ => le_max_right _ _)
    (fun _ _ => max_le_max_right _ (sub_le_sub_right xy _))

theorem smallFalling_convex (d : ℕ) : ConvexOn ℝ Set.univ (smallFalling d) := by
  induction d with
  | zero =>
    have eq : smallFalling 0 = fun _ => (1 : ℝ) := by funext x; simp [smallFalling]
    rw [eq]
    exact convexOn_const _ convex_univ
  | succ d ih =>
    let g := fun x : ℝ => max (x - (d : ℝ)) 0
    have gm : Monotone g := fun a b h => max_le_max_right _ (sub_le_sub_right h _)
    have cg : ConvexOn ℝ Set.univ g := by
      apply ConvexOn.sup
      · exact (convexOn_id convex_univ).sub (concaveOn_const _ convex_univ)
      · exact convexOn_const _ convex_univ
    have eq : smallFalling (d+1) = smallFalling d * g := by
      funext x
      simp [smallFalling,g,Finset.prod_range_succ]
    rw [eq]
    exact ih.mul cg (fun _ _ => smallFalling_nonneg ..) (fun _ _ => le_max_right _ _)
      (((smallFalling_mono d).monovary gm).monovaryOn _)

theorem smallFalling_nat (d x : ℕ) : smallFalling d x = (x.descFactorial d : ℕ) := by
  induction d with
  | zero => simp [smallFalling]
  | succ d ih =>
    have a : max ((x:ℝ) - d) 0 = ((x-d : ℕ) : ℝ) := by
      rcases le_total d x with h|h
      · rw [Nat.cast_sub h,max_eq_left]; exact_mod_cast Nat.zero_le (x-d)
      · rw [Nat.sub_eq_zero_of_le h,Nat.cast_zero,max_eq_right]; exact sub_nonpos.mpr (by exact_mod_cast h)
    rw [Nat.descFactorial_succ,Nat.cast_mul]
    simp only [smallFalling,Finset.prod_range_succ,← ih,a,mul_comm]

/-- The count of ordered d-tuples is at least that predicted by the mean
degree, even when the average is fractional. -/
theorem smallFalling_average {Y : Type*} [Fintype Y] [Nonempty Y] (a : Y → ℕ) (d : ℕ) :
    (Fintype.card Y : ℝ) * smallFalling d ((∑ y, (a y : ℝ)) / Fintype.card Y) ≤
      ∑ y, ((a y).descFactorial d : ℕ) := by
  have pos : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  have sum : ∑ _ : Y, (Fintype.card Y : ℝ)⁻¹ = 1 := by simp [ne_of_gt pos]
  have bound := (smallFalling_convex d).map_sum_le (t := Finset.univ)
    (w := fun _ : Y => (Fintype.card Y : ℝ)⁻¹) (p := fun y => (a y : ℝ))
    (fun _ _ => inv_nonneg.mpr pos.le) sum (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul,← Finset.mul_sum,smallFalling_nat] at bound
  rw [div_eq_inv_mul]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left bound pos.le
    _ = _ := by rw [← mul_assoc,mul_inv_cancel₀ pos.ne',one_mul,Nat.cast_sum]

end OMA

/- Lower bounds for the falling-factorial ratio -/

namespace OMA

theorem falling_succ (r : ℕ) (x : ℝ) :
    smallFalling (r+1) x = smallFalling r x * max (x-r) 0 := by
  simp [smallFalling,Finset.prod_range_succ]

private theorem falling_one (x : ℝ) (hx : 0 ≤ x) : smallFalling 1 x = x := by
  simp [smallFalling,max_eq_left hx]

/-- A telescoping product controls all degrees at least six, uniformly in t. -/
theorem small_ratio_large {d : ℕ} {y t : ℝ} (hd : 6 ≤ d)
    (ht : 2*((d:ℝ)-1) ≤ t) (hy : ((d:ℝ)-1)*t ≤ y) :
    (y-t)*smallFalling d t ≤ d*y*smallFalling d (t*(y-t)/y) := by
  let D : ℝ := d
  have D6 : 6 ≤ D := by dsimp [D]; exact_mod_cast hd
  change 2*(D-1) ≤ t at ht
  change (D-1)*t ≤ y at hy
  have tp : 0 < t := by linarith
  have yp : 0 < y := by nlinarith [mul_nonneg (show 0 ≤ D-2 by linarith) tp.le]
  have yt : 0 ≤ y-t := by nlinarith [mul_nonneg (show 0 ≤ D-2 by linarith) tp.le]
  let μ := t*(y-t)/y
  have mu : μ*y = t*(y-t) := div_mul_cancel₀ _ yp.ne'
  have mp : 0 ≤ μ := div_nonneg (mul_nonneg tp.le yt) yp.le
  let k := (2*D-3)*(2*D-4)
  let p := fun r : ℕ => (2*D-2-r)*(2*D-3-r)
  have kp : 0 < k := mul_pos (by linarith) (by linarith)
  have seq (r : ℕ) (rpos : 1 ≤ r) (rd : r ≤ d) :
      (y-t)*smallFalling r t * p r ≤ y*smallFalling r μ*k := by
    induction r with
    | zero => omega
    | succ r ih =>
      by_cases rz : r = 0
      · subst r
        rw [falling_one _ tp.le,falling_one _ mp]
        have base : p 1 = k := by dsimp [p,k]; norm_num; ring
        rw [base]
        nlinarith only [congrArg (fun z : ℝ => z*k) mu]
      have rr : (r:ℝ) < D := by dsimp [D]; exact_mod_cast (show r < d by omega)
      have rn : 0 ≤ (r:ℝ) := by positivity
      have prev := ih (by omega) (by omega)
      let a := 2*D-2-r
      have ap : 2 < a := by dsimp [a]; linarith
      have tr : 0 ≤ t-r := by linarith
      have cross : t^2 * a ≤ 2*y*(t-r) := by
        have e1 : t*a ≤ 2*(D-1)*(t-r) := by
          dsimp [a]
          nlinarith only [mul_nonneg rn (sub_nonneg.mpr ht)]
        have e2 := mul_le_mul_of_nonneg_left e1 tp.le
        have e3 := mul_le_mul_of_nonneg_right hy tr
        nlinarith
      have ratio : (t-r)*(a-2) ≤ (μ-r)*a := by
        apply le_of_mul_le_mul_right (a := y) _ yp
        nlinarith only [cross,congrArg (fun z : ℝ => z*a) mu]
      have pr : p r = a*(a-1) := by dsimp [p,a]; ring
      have pn : p (r+1) = (a-1)*(a-2) := by dsimp [p,a]; push_cast; ring
      rw [pr] at prev
      rw [pn,falling_succ,falling_succ,max_eq_left tr]
      have rt : (t-r)*(a-2) ≤ max (μ-r) 0*a :=
        ratio.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by linarith))
      apply le_of_mul_le_mul_right (a := a) _ (by linarith)
      have e1 := mul_le_mul_of_nonneg_right prev (mul_nonneg tr (by linarith : 0 ≤ a-2))
      have e2 := mul_le_mul_of_nonneg_left rt
        (mul_nonneg (mul_nonneg yp.le (smallFalling_nonneg r μ)) kp.le)
      nlinarith only [e1,e2]
  have main := seq d (by omega) le_rfl
  have endp : k ≤ D * p d := by
    change (2*D-3)*(2*D-4) ≤ D*((2*D-2-D)*(2*D-3-D))
    nlinarith only [mul_nonneg (mul_nonneg (by linarith : 0 ≤ D-2) (by linarith : 0 ≤ D-1))
      (by linarith : 0 ≤ D-6)]
  have x := mul_le_mul_of_nonneg_left endp (mul_nonneg yt (smallFalling_nonneg d t))
  have z := mul_le_mul_of_nonneg_left main (by linarith : 0 ≤ D)
  change (y-t)*smallFalling d t ≤ D*y*smallFalling d μ
  apply le_of_mul_le_mul_right (a := k) _ kp
  nlinarith only [x,z]

/-- A fixed lower bound on each factor after the first gives a power bound. -/
theorem small_ratio_factors {d : ℕ} {y t c : ℝ} (hd : 1 ≤ d) (yp : 0 < y)
    (yt : 0 ≤ y-t) (dt : (d:ℝ) ≤ t) (cp : 0 ≤ c)
    (factor : ∀ j : ℕ, 1 ≤ j → j < d →
      c*(t-j) ≤ t*(y-t)/y-j) :
    (y-t)*smallFalling d t * c^(d-1) ≤ y*smallFalling d (t*(y-t)/y) := by
  let μ := t*(y-t)/y
  have tp : 0 ≤ t := (Nat.cast_nonneg d).trans dt
  have mp : 0 ≤ μ := div_nonneg (mul_nonneg tp yt) yp.le
  have aux (r : ℕ) (hr : 1 ≤ r) (rd : r ≤ d) :
      (y-t)*smallFalling r t * c^(r-1) ≤ y*smallFalling r μ := by
    induction r with
    | zero => omega
    | succ r ih =>
      by_cases z : r = 0
      · subst r
        rw [falling_one _ tp,falling_one _ mp]
        simp only [Nat.reduceSubDiff,pow_zero,mul_one]
        dsimp [μ]; field_simp; ring_nf; rfl
      have hr' : 1 ≤ r := by omega
      have old := ih hr' (by omega)
      have tr : 0 ≤ t-r := sub_nonneg.mpr ((by exact_mod_cast (show r ≤ d by omega) : (r:ℝ) ≤ d).trans dt)
      have rat := (factor r hr' (by omega)).trans (le_max_left (μ-r) 0)
      rw [falling_succ,falling_succ,max_eq_left tr,show r+1-1 = r-1+1 by omega,pow_succ]
      have prod := mul_le_mul old rat (mul_nonneg cp tr) (mul_nonneg yp.le (smallFalling_nonneg r μ))
      nlinarith only [prod]
  exact aux d hd le_rfl

end OMA

/- The degree-two endpoint of the clique-placement estimate -/

namespace OMA

theorem small_ratio_two {y t s f : ℝ}
    (large : 1000 ≤ t) (hf : 1 ≤ f) (sf : 2*f ≤ s) (sp : s ≤ t+f)
    (yt : t + 2*f ≤ y) (mix : 7*t + 12*f ≤ 5*y)
    (dist : 2*t + 3*f ≤ y+s) (tf : 2*f ≤ t) :
    smallFalling 2 t * ((f-1)*max (y-t) s) <
      s*y*smallFalling 2 (t*(y-t)/y) := by
  let D := y-t
  let L := D*(t-1)-t
  have dy : y = D+t := by dsimp [D]; ring
  have dlow : 2*f ≤ D := by dsimp [D]; linarith only [yt]
  have dmix : 2*t+12*f ≤ 5*D := by dsimp [D]; linarith
  have dp : 0 < D := by linarith
  have yp : 0 < y := by linarith
  have tp : 0 < t := by linarith
  have spos : 0 < s := by linarith
  have Lp : 0 < L := by
    dsimp [L]
    nlinarith [mul_nonneg (show 0 ≤ D-2 by linarith) (by linarith : 0 ≤ t-1)]
  have q : y*(f+1) ≤ D^2 := by
    have sq := sq_nonneg (3*D-7*f)
    have fy := mul_nonneg (show 0 ≤ 5*D-2*t-12*f by linarith) (by linarith : 0 ≤ f)
    have d14 : 14 ≤ D := by linarith
    have grow := mul_nonneg dp.le (sub_nonneg.mpr d14)
    nlinarith [sq_nonneg f]
  have first : y*(t-1)*(f-1) < D*L := by
    have p := mul_le_mul_of_nonneg_right q (by linarith : 0 ≤ t-1)
    have dq := mul_nonneg (show 0 ≤ y-D by linarith) tp.le
    dsimp [L]
    nlinarith only [p,dq, mul_pos yp (show 0 < t-2 by linarith)]
  have second : y*(t-1)*(f-1) < s*L := by
    by_cases big : 2*t ≤ y
    · have p := mul_le_mul_of_nonneg_right sf Lp.le
      have h1 := mul_nonneg (show 0 ≤ y-2*t by linarith)
        (mul_nonneg (by linarith : 0 ≤ f+1) (by linarith : 0 ≤ t-1))
      have h2 := mul_pos tp (show 0 < t-1-f by linarith)
      dsimp [L,D] at p ⊢
      nlinarith only [p,h1,h2]
    · let z := 2*t-y
      have zp : 0 ≤ z := by dsimp [z]; linarith
      have sz : 3*f+z ≤ s := by dsimp [z]; linarith
      have bound : f*t ≤ s*D-f*y := by
        have e1 := mul_le_mul_of_nonneg_right sz dp.le
        have e2 := mul_nonneg zp (sub_nonneg.mpr dlow)
        dsimp [D,z] at *
        nlinarith only [e1,e2]
      have b1 := mul_le_mul_of_nonneg_right bound tp.le
      have b2 := mul_le_mul_of_nonneg_right sp yp.le
      have b3 := mul_le_mul_of_nonneg_right hf (sq_nonneg t)
      have b4 := mul_pos tp (by linarith : 0 < t-2)
      dsimp [L,D] at *
      nlinarith only [b1,b2,b3,b4,lt_of_not_ge big]
  let μ := t*(y-t)/y
  have mu : μ*y = t*D := div_mul_cancel₀ _ yp.ne'
  have mp : 1 ≤ μ := by
    apply le_of_mul_le_mul_right (a := y) _ yp
    rw [one_mul,mu]
    dsimp [L,D] at Lp ⊢
    nlinarith
  have rt : smallFalling 2 t = t*(t-1) := by
    simp [smallFalling,Finset.prod_range_succ,max_eq_left (by linarith : 0 ≤ t),
      max_eq_left (by linarith : 0 ≤ t-1)]
  have rm : smallFalling 2 μ = μ*(μ-1) := by
    simp [smallFalling,Finset.prod_range_succ,max_eq_left (by linarith : 0 ≤ μ),
      max_eq_left (by linarith : 0 ≤ μ-1)]
  change smallFalling 2 t * ((f-1)*max D s) < s*y*smallFalling 2 μ
  rw [rt,rm]
  have combined : y*(t-1)*(f-1)*max D s < s*D*L := by
    rcases le_total D s with h|h
    · rw [max_eq_right h]
      nlinarith only [mul_lt_mul_of_pos_right first spos]
    · rw [max_eq_left h]
      nlinarith only [mul_lt_mul_of_pos_right second dp]
  apply lt_of_mul_lt_mul_right (a := y) _ yp.le
  have sqmu := congrArg (fun x : ℝ => s*x^2) mu
  have linmu := congrArg (fun x : ℝ => s*y*x) mu
  have c := mul_lt_mul_of_pos_left combined tp
  dsimp [L,D] at c mu sqmu linmu
  dsimp [D]
  nlinarith only [c, sqmu, linmu]

end OMA

/- Numerical comparison for the independent minimum-degree case -/

namespace OMA

/-- For degrees three to five the size hypothesis leaves a fixed margin
in each of the at most four nontrivial factors. -/
private theorem moderate {d : ℕ} {y t : ℝ} (hd : 3 ≤ d) (upper : d ≤ 5)
    (big : 1000 ≤ t) (yt : t ≤ y)
    (mix : 2*(d:ℝ)*(d+1)*t ≤ (2*(d:ℝ)+1)*(y+t)) :
    (y-t)*smallFalling d t ≤ d*y*smallFalling d (t*(y-t)/y) := by
  have yp : 0 < y := by linarith
  have factors {c : ℝ} (cp : 0 ≤ c) (cq : c ≤ 1)
      (hmin : t*t ≤ (1-c)*y*(t-4)) (pow : 1 ≤ d*c^(d-1)) :
      (y-t)*smallFalling d t ≤ d*y*smallFalling d (t*(y-t)/y) := by
    have h := small_ratio_factors (d := d) (c := c) (by omega) yp (sub_nonneg.mpr yt)
      (by
        have : (d:ℝ) ≤ 5 := by exact_mod_cast upper
        linarith) cp (by
        intro j _ jd
        have j4 : (j:ℝ) ≤ 4 := by exact_mod_cast (show j ≤ 4 by omega)
        have extra := mul_nonneg (mul_nonneg (sub_nonneg.mpr cq) yp.le) (sub_nonneg.mpr j4)
        apply (le_sub_iff_add_le).mpr
        apply (le_div_iff₀ yp).mpr
        nlinarith only [hmin,extra])
    have non := mul_nonneg (sub_nonneg.mpr yt) (smallFalling_nonneg d t)
    have p := mul_le_mul_of_nonneg_left pow non
    have q := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg d (α := ℝ))
    nlinarith only [p,q]
  interval_cases d
  · apply factors (c := 7/12) (by norm_num) (by norm_num) _ (by norm_num)
    have h : 17*t ≤ 7*y := by norm_num at mix; linarith
    nlinarith only [mul_nonneg (sub_nonneg.mpr h) (by linarith : 0 ≤ t-4),
      mul_nonneg (by linarith : 0 ≤ t-340) (by linarith : 0 ≤ t)]
  · apply factors (c := 7/10) (by norm_num) (by norm_num) _ (by norm_num)
    have h : 31*t ≤ 9*y := by norm_num at mix; linarith
    nlinarith only [mul_nonneg (sub_nonneg.mpr h) (by linarith : 0 ≤ t-4),
      mul_nonneg (by linarith : 0 ≤ t-124) (by linarith : 0 ≤ t)]
  · apply factors (c := 3/4) (by norm_num) (by norm_num) _ (by norm_num)
    have h : 49*t ≤ 11*y := by norm_num at mix; linarith
    nlinarith only [mul_nonneg (sub_nonneg.mpr h) (by linarith : 0 ≤ t-4),
      mul_nonneg (by linarith : 0 ≤ t-196) (by linarith : 0 ≤ t)]

theorem small_numeric_bound {d s f t y : ℕ} (hd : 2 ≤ d) (hf : 1 ≤ f)
    (sp : s ≤ t+f) (ss : d*f ≤ s)
    (a : d*(t+f) < y+t) (b : (d+1)*(t+f) < y+t+s)
    (c : 2*d*s < y+t) (failed : y < f+d*t) (big : 10000 ≤ y+t) :
    (t.descFactorial d : ℝ) * ((f-1 : ℕ)*max (y-t : ℕ) s) <
      (s:ℝ)*y*smallFalling d ((t:ℝ)*(y-t)/y) := by
  have mixN : 2*d*(d+1)*(t+f) ≤ (2*d+1)*(y+t) := by
    nlinarith only [Nat.mul_le_mul_left (2*d) b.le,c.le]
  have tlarge : (2*d-2)*f ≤ t := by
    have largeD : 2*d-2+2 = 2*d := by omega
    have w := Nat.mul_le_mul_left (2*d+1) (by omega : y+t ≤ f+d*t+t)
    by_contra! no
    have bad := Nat.mul_le_mul_left (d+1) no.le
    nlinarith only [hf,mixN,w,bad,congrArg (fun z : ℕ => z*f*(d+1)) largeD]
  have tf : 2*d-2 ≤ t := (Nat.le_mul_of_pos_right _ hf).trans tlarge
  have td : d ≤ t := by omega
  have yt : t+d*f ≤ y := by nlinarith only [a, Nat.mul_le_mul_right t hd]
  have D := Nat.sub_add_cancel (by omega : t ≤ y)
  have th : d ≤ 5 → 1000 ≤ t := by
    intro dh
    have tt : f ≤ t := (Nat.le_mul_of_pos_left _ (by omega : 0 < 2*d-2)).trans tlarge
    nlinarith only [big,failed,tt,Nat.mul_le_mul_right t dh]
  have castD : ((y-t : ℕ):ℝ) = (y:ℝ)-t := Nat.cast_sub (by omega)
  push_cast
  rw [Nat.cast_sub hf, Nat.cast_one,castD]
  by_cases h2 : d = 2
  · subst d
    rw [← smallFalling_nat]
    apply small_ratio_two (by exact_mod_cast th (by decide)) (by exact_mod_cast hf)
      (by exact_mod_cast ss) (by exact_mod_cast sp) (by exact_mod_cast yt)
    · exact_mod_cast (show 7*t + 12*f ≤ 5*y by nlinarith only [mixN])
    · exact_mod_cast (show 2*t + 3*f ≤ y+s by nlinarith only [b])
    · exact_mod_cast (show 2*f ≤ t by simpa using tlarge)
  have d3 : 3 ≤ d := by omega
  have yp : 0 < (y:ℝ) := by exact_mod_cast (show 0 < y by omega)
  have dp : 0 < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
  have p : 0 < (t.descFactorial d : ℝ) := by
    exact_mod_cast (Nat.descFactorial_pos.mpr td)
  have ratio : ((y:ℝ)-t)*(t.descFactorial d : ℝ) ≤
      d*y*smallFalling d ((t:ℝ)*(y-t)/y) := by
    rw [← smallFalling_nat]
    by_cases dh : 6 ≤ d
    · apply small_ratio_large dh
      · have h : 2*d ≤ t+2 := by omega
        have h' : 2*(d:ℝ) ≤ t+2 := by exact_mod_cast h
        linarith
      · have h : d*t ≤ y+t := by nlinarith only [a,Nat.zero_le (d*f)]
        have h' : (d:ℝ)*t ≤ y+t := by exact_mod_cast h
        linarith
    · apply moderate d3 (by omega) (by exact_mod_cast th (by omega)) (by exact_mod_cast (show t ≤ y by omega))
      exact_mod_cast (show 2*d*(d+1)*t ≤ (2*d+1)*(y+t) by nlinarith only [mixN,Nat.zero_le (2*d*(d+1)*f)])
  have sge : (d:ℝ)*f ≤ s := by exact_mod_cast ss
  have yge : (t:ℝ)+d*f ≤ y := by exact_mod_cast yt
  have fp : (1:ℝ) ≤ f := by exact_mod_cast hf
  have sy : 0 < (s:ℝ) := by nlinarith [mul_pos dp (by linarith : 0 < (f:ℝ))]
  have Dy : 0 < (y:ℝ)-t := by nlinarith [mul_pos dp (by linarith : 0 < (f:ℝ))]
  have strict : d*((f:ℝ)-1)*max ((y:ℝ)-t) s < s*((y:ℝ)-t) := by
    rcases le_total ((y:ℝ)-t) s with h|h
    · rw [max_eq_right h]
      nlinarith only [mul_lt_mul_of_pos_right (show (d:ℝ)*(f-1) < y-t by nlinarith) sy]
    · rw [max_eq_left h]
      nlinarith only [mul_lt_mul_of_pos_right (show (d:ℝ)*(f-1) < s by nlinarith) Dy]
  apply lt_of_mul_lt_mul_left (a := (d:ℝ)) _ dp.le
  nlinarith only [mul_lt_mul_of_pos_left strict p,mul_le_mul_of_nonneg_left ratio sy.le]

end OMA

/- The independent minimum-degree case of the triangle induction -/

namespace OMA
open SimpleGraph
open scoped Classical

theorem small_independent_step : IndependentMinimumStep 10000 := by
  intro V W _ _ G H _ v _ large minEq hd ind size free del
  classical
  obtain ⟨T,cl⟩ := Gᶜ.maximumClique_exists
  let n := Fintype.card W
  let m := H.edgeFinset.card
  let t := T.card
  let d := H.degree v
  obtain ⟨P,defP,indP⟩ : ∃ P : Set W, (∀ i, i ∈ P ↔ H.degree i = d) ∧ H.IsIndepSet P :=
    ⟨_,fun _ => Iff.rfl,ind⟩
  let s := Fintype.card P
  let f := n-t
  let y := Fintype.card (↥Tᶜ)
  have cy : y+t = Fintype.card V := by
    dsimp only [y,t]
    rw [Fintype.card_coe]
    exact Finset.card_compl_add_card T
  have cH (i : ↥P) : H.degree i.val = d := (defP _).mp i.prop
  have minD (i : W) : d ≤ H.degree i := by dsimp [d]; rw [minEq]; exact H.minDegree_le_degree i
  have countS : s*d ≤ m := independent_degree_edges H P indP cH
  have surplus : (d+1)*n ≤ 2*m+s := degree_surplus H minD P defP
  have floorN : n*d ≤ 2*m := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => minD i)
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,H.sum_degrees_eq_twice_card_edges] using h
  have low (x : V) : G.degree x ≤ t := by
    apply cl.2 (G.neighborFinset x)
    simpa only [coe_neighborFinset] using triangle_neighbors_blue G x free
  by_contra no
  have tn : t < n := by
    by_contra! hn
    obtain ⟨k⟩ : Nonempty (W ↪ T) := Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe])
    let e := k.trans (Function.Embedding.subtype _)
    exact no ⟨⟨⟨e,fun {i j} adj => cl.1 (k i).prop (k j).prop (e.injective.ne adj.ne)⟩,e.injective⟩⟩
  have cf : t+f = n := by dsimp [f]; omega
  have hf : 1 ≤ f := by omega
  obtain ⟨k⟩ := del
  have fail : y+t+1 ≤ n+d*t := by rw [cy]; exact triangle_extension_bound G H v k no low
  have hsize : 2*m+1 ≤ y+t := cy ▸ size
  have sp : s ≤ n := Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have ss : d*f ≤ s := by
    rw [← cf] at surplus
    nlinarith only [surplus,hsize,fail,cf]
  have enough : Fintype.card (↥Pᶜ) ≤ t := by
    rw [Fintype.card_compl_set]
    change n-s ≤ t
    have := (Nat.le_mul_of_pos_left f (by omega : 0 < d)).trans ss
    omega
  have a : d*(t+f) < y+t := by nlinarith only [floorN,cf,hsize,congrArg (fun z : ℕ => d*z) cf]
  have b : (d+1)*(t+f) < y+t+s := by rw [cf]; omega
  have c : 2*d*s < y+t := by nlinarith only [countS,hsize]
  have fail' : y < f+d*t := by omega
  have big : 10000 ≤ y+t := by change 10000 ≤ m at large; omega
  have ss' : s ≤ t+f := cf ▸ sp
  have hyt : t ≤ y := by nlinarith only [a,Nat.mul_le_mul_right (t+f) hd]
  have yp : 0 < y := by nlinarith only [a,Nat.mul_le_mul_right (t+f) hd,hf]
  obtain ⟨B,allow,cap,tot⟩ := small_thin_columns G T low y rfl
  have : Nonempty (↥Tᶜ) := Fintype.card_pos_iff.mp yp
  have sum : (∑ j, ((B j).card : ℝ)) = (t:ℝ)*(y-t) := by
    have h : (∑ j, (B j).card) = t*(y-t) := tot
    rw [← Nat.cast_sub hyt]
    exact_mod_cast h
  have avg := smallFalling_average (fun j => (B j).card) d
  rw [sum] at avg
  change (y:ℝ)*smallFalling d ((t:ℝ)*(y-t)/y) ≤ _ at avg
  have ns := small_numeric_bound hd hf ss' ss a b c fail' big
  apply no
  apply small_place_average H Gᶜ P T indP cl.1 (by omega : 0 < d) cH cf enough B allow
      (fun i => (cap i).le)
  have E : (t.descFactorial d : ℝ) * ((f-1 : ℕ)*max (y-t : ℕ) s) <
      ((s * ∑ j, (B j).card.descFactorial d : ℕ) : ℝ) := by
    apply ns.trans_le
    rw [Nat.cast_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left avg (Nat.cast_nonneg s)
  exact_mod_cast E

end OMA

/- The triangle and four-cycle cases of Erdős 570 -/

namespace OMA
open SimpleGraph Filter

/-- The triangle bound for all sufficiently large edge counts. -/
theorem triangle_forces : ∀ᶠ m : ℕ in atTop, Forces 3 m (2*m+1) :=
  triangle_forces_of_independent small_independent_step

/-- Every edge count starting at two satisfies the sharp square bound. -/
theorem square_forces_of_two_le {m : ℕ} (hm : 2 ≤ m) : Forces 4 m (2*m+1) := by
  intro W _ H _ pos edges _ G
  by_cases red : cycleGraph 4 ⊑ G
  · exact Or.inl red
  · right
    have cnt : H.edgeFinset.card = m := by
      rw [edgeFinset_card,← Nat.card_eq_fintype_card]; exact edges
    apply square_of_base square_base G H pos (by omega) _ red
    simp [cnt]

theorem square_forces : ∀ᶠ m : ℕ in atTop, Forces 4 m (2*m+1) :=
  eventually_atTop.mpr ⟨2, fun _ hm => square_forces_of_two_le hm⟩

end OMA

/- Counting two-step walks in an even-cycle-free graph -/

namespace OMA
open SimpleGraph Finset

private theorem bipartite_prune {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : Finset V)
    (many : k*(a.card+b.card) < ∑ x ∈ a, (b.filter (G.Adj x)).card) :
    ∃ A ⊆ a, ∃ B ⊆ b, A.Nonempty ∧ (∀ x ∈ A, k < (B.filter (G.Adj x)).card) ∧
      (∀ y ∈ B, k < (A.filter (G.Adj y)).card) := by
  classical
  have swap (s t : Finset V) :
      (∑ x ∈ s, (t.filter (G.Adj x)).card) = ∑ y ∈ t, (s.filter (G.Adj y)).card := by
    exact (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := s) (t := t) G.Adj).trans
      (sum_congr rfl fun y _ => congrArg card (filter_congr fun x _ => G.adj_comm x y))
  by_cases small : ∃ x ∈ a, (b.filter (G.Adj x)).card ≤ k
  · obtain ⟨x,hx,lo⟩ := small
    have eq := sum_erase_add a (fun i => (b.filter (G.Adj i)).card) hx
    have card := card_erase_add_one hx
    have room : k*((a.erase x).card+b.card) < ∑ i ∈ a.erase x, (b.filter (G.Adj i)).card := by
      rw [← card] at many
      simp only [Nat.mul_add, Nat.mul_one] at many ⊢
      omega
    obtain ⟨A,hA,B,hB,ok⟩ := bipartite_prune G k (a.erase x) b room
    exact ⟨A,hA.trans (erase_subset ..),B,hB,ok⟩
  by_cases small' : ∃ y ∈ b, (a.filter (G.Adj y)).card ≤ k
  · obtain ⟨y,hy,lo⟩ := small'
    have eq := sum_erase_add b (fun i => (a.filter (G.Adj i)).card) hy
    have card := card_erase_add_one hy
    have room : k*(a.card+(b.erase y).card) < ∑ i ∈ a, ((b.erase y).filter (G.Adj i)).card := by
      rw [swap] at many ⊢
      rw [← card] at many
      simp only [Nat.mul_add, Nat.mul_one] at many ⊢
      omega
    obtain ⟨A,hA,B,hB,ok⟩ := bipartite_prune G k a (b.erase y) room
    exact ⟨A,hA,B,hB.trans (erase_subset ..),ok⟩
  have nonempty : a.Nonempty := by
    by_contra! h
    simp [h] at many
  exact ⟨a,by rfl,b,by rfl,nonempty,fun x hx => Nat.lt_of_not_ge (fun le => small ⟨x,hx,le⟩),
    fun y hy => Nat.lt_of_not_ge (fun le => small' ⟨y,hy,le⟩)⟩
termination_by a.card + b.card
decreasing_by all_goals omega

private theorem alternating_chain {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) {k : ℕ} (a b : Finset V) (ha : a.Nonempty)
    (nv : v ∉ a) (ab : ∀ x ∈ a, k < (b.filter (G.Adj x)).card)
    (ba : ∀ y ∈ b, k < (a.filter (G.Adj y)).card) (t : ℕ) (ht : 2*t+2 ≤ k) :
    ∃ (p : List V) (hn : p ≠ []), p.length = 2*t+1 ∧ p.Nodup ∧ p.IsChain G.Adj ∧
      v ∉ p ∧ p.head hn ∈ a ∧ p.getLast hn ∈ a := by
  induction t with
  | zero =>
    obtain ⟨x,hx⟩ := ha
    exact ⟨[x],by simp,by simp,by simp,by simp,by simpa using (fun h => nv (h ▸ hx) : v ≠ x),by simpa,by simpa⟩
  | succ t ih =>
    obtain ⟨p,hn,len,nd,ch,vp,head,last⟩ := ih (by omega)
    have pick (s : Finset V) (L : List V) (h : L.length < s.card) :
        ∃ x ∈ s, x ∉ L := by
      by_contra! no
      have bnd := card_le_card (show s ⊆ L.toFinset from fun x hx => List.mem_toFinset.mpr (no x hx))
      have := List.toFinset_card_le L
      omega
    obtain ⟨y,hy,ny⟩ := pick (b.filter (G.Adj (p.head hn))) (v::p) (by simp [len]; have := ab _ head; omega)
    obtain ⟨z,hz,nz⟩ := pick (a.filter (G.Adj y)) (y::p) (by simp [len]; have := ba y (mem_filter.mp hy).1; omega)
    obtain ⟨yb,xy⟩ := mem_filter.mp hy
    obtain ⟨za,yz⟩ := mem_filter.mp hz
    refine ⟨z::y::p,by simp,by simp [len]; omega,?_,?_,?_,by simpa,?_⟩
    · simp_all
    · apply List.isChain_cons_cons.mpr ⟨yz.symm,?_⟩
      cases p with
      | nil => contradiction
      | cons w tail => exact List.isChain_cons_cons.mpr ⟨xy.symm,ch⟩
    · have vz : v ≠ z := fun eq => nv (eq ▸ za)
      have vy : v ≠ y := fun eq => ny (List.mem_cons.mpr (.inl eq.symm))
      simp [vz,vy,vp]
    · simpa [List.getLast_cons hn] using last

/-- The sum of the degrees of the neighbors of a vertex is linear in the
order when the specified even cycle is absent. -/
theorem long_even_neighbor_degree_sum {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) {l : ℕ} (hl : 2 ≤ l)
    (no : ¬ cycleGraph (2*l) ⊑ G) :
    ∑ u ∈ G.neighborFinset v, G.degree u ≤ (2*l)*(G.degree v + Fintype.card V) := by
  classical
  by_contra! h
  have count (x : V) : (univ.filter (G.Adj x)).card = G.degree x := by
    rw [← G.card_neighborFinset_eq_degree]
    congr 1
    ext y
    simp
  obtain ⟨A,sub,B,_,ne,ab,ba⟩ := bipartite_prune G (2*l) (G.neighborFinset v) univ
    (by simpa only [card_univ, count, card_neighborFinset_eq_degree] using h)
  have nv : v ∉ A := fun hv => ((G.mem_neighborFinset _ _).mp (sub hv)).ne rfl
  obtain ⟨p,hn,len,nd,ch,vp,start,finish⟩ :=
    alternating_chain G v A B ne nv ab ba (l-1) (by omega)
  let L := v::p
  have size : L.length = 2*l := by simp [L,len]; omega
  have chain : L.IsChain G.Adj := by
    cases p with
    | nil => contradiction
    | cons w ps =>
      exact List.isChain_cons.mpr ⟨by simpa using (G.mem_neighborFinset _ _).mp (sub start),ch⟩
  have nodup : L.Nodup := List.nodup_cons.mpr ⟨vp,nd⟩
  let f (i : ℕ) := if h : i < L.length then L[i] else v
  apply no (cycle_of_sequence f ?_ ?_ ?_)
  · intro i hi j hj eq
    simp only [f, dif_pos (size ▸ hi : i < L.length), dif_pos (size ▸ hj : j < L.length)] at eq
    exact congrArg Fin.val (nodup.injective_get eq)
  · intro i hi
    simpa only [f,dif_pos (by omega : i < L.length), dif_pos (by omega : i+1 < L.length)] using
      List.isChain_iff_getElem.mp chain i (by omega)
  · have close := ((G.mem_neighborFinset _ _).mp (sub finish)).symm
    have e : L[2*l-1]'(by omega) = p.getLast hn := by
      rw [← List.getLast_cons (a := v) hn, List.getLast_eq_getElem]
      simp only [L, ← size]
    simpa only [f,dif_pos (by omega : 2*l-1 < L.length),dif_pos (by omega : 0 < L.length),e]
      using (show G.Adj (p.getLast hn) L[0] from close)

/-- Only a small fraction of vertices can have red degree above the square-root scale. -/
theorem long_even_high_degree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {l : ℕ} (hl : 2 ≤ l) (no : ¬ cycleGraph (2*l) ⊑ G) (r : ℕ) :
    (univ.filter (fun v => r ≤ G.degree v)).card * r^2 ≤ 4*l*(Fintype.card V)^2 := by
  classical
  let T := univ.filter (fun v => r ≤ G.degree v)
  let N := Fintype.card V
  let h (v : V) := T.filter (G.Adj v)
  have localBound (v : V) : (h v).card*r ≤ 4*l*N := by
    have sub : h v ⊆ G.neighborFinset v := fun u hu => (G.mem_neighborFinset _ _).mpr (mem_filter.mp hu).2
    calc
      _ = ∑ _ ∈ h v, r := by simp
      _ ≤ ∑ u ∈ h v, G.degree u := sum_le_sum fun u hu => (mem_filter.mp (mem_filter.mp hu).1).2
      _ ≤ ∑ u ∈ G.neighborFinset v, G.degree u := sum_le_sum_of_subset_of_nonneg sub (by intros; omega)
      _ ≤ 2*l*(G.degree v+N) := long_even_neighbor_degree_sum G v hl no
      _ ≤ 2*l*(N+N) := Nat.mul_le_mul_left _ (by have := G.card_neighborFinset_eq_degree v; have := card_le_univ (G.neighborFinset v); omega)
      _ = _ := by ring
  have eq : (∑ v, (h v).card) = ∑ u ∈ T, G.degree u := by
    apply (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := univ) (t := T) G.Adj).trans
    apply sum_congr rfl
    intro u _
    rw [← G.card_neighborFinset_eq_degree]
    congr 1
    ext v
    simp [adj_comm]
  have lower : T.card*r ≤ ∑ v, (h v).card := by
    rw [eq]
    calc
      _ = ∑ _ ∈ T, r := by simp
      _ ≤ _ := sum_le_sum fun u hu => (mem_filter.mp hu).2
  calc
    _ = T.card*r*r := by dsimp [T]; ring
    _ ≤ (∑ v, (h v).card)*r := Nat.mul_le_mul_right _ lower
    _ = ∑ v, (h v).card*r := Finset.sum_mul ..
    _ ≤ ∑ _ : V, 4*l*N := sum_le_sum fun v _ => localBound v
    _ = _ := by simp [N]; ring

end OMA

/- A large-neighborhood witness for the cycle Ramsey induction -/

namespace OMA
open SimpleGraph Finset

/-- Failure to add a vertex to a blue copy gives a large red neighborhood at
one of the images of its neighbors. -/
theorem long_extension_obstruction {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (x : W) (r : ℕ) (bound : ∀ u, G.degree u ≤ r)
    (f : (H.induce ({x}ᶜ : Set W)).Copy Gᶜ) (noBlue : ¬ H ⊑ Gᶜ) :
    Fintype.card V + 1 - Fintype.card W ≤ H.degree x * r := by
  classical
  let P : Set W := {x}ᶜ
  let S := (univ.map f.toEmbedding)ᶜ
  let hood (i : H.neighborSet x) : P := ⟨i.val, by
    simpa [P] using (show H.Adj x i.val from i.prop).ne.symm⟩
  have cover : S ⊆ univ.biUnion (fun i : H.neighborSet x => G.neighborFinset (f (hood i))) := by
    intro z hz
    by_contra h
    have fresh (j : P) : z ≠ f j := by
      rintro rfl
      exact (mem_compl.mp hz) (mem_map.mpr ⟨j,mem_univ _,rfl⟩)
    let single : (H.induce ({x} : Set W)).Copy Gᶜ :=
      ⟨⟨fun _ => z, fun {a b} e => False.elim (e.ne (Subsingleton.elim a b))⟩,
        fun {_ _} _ => Subsingleton.elim ..⟩
    apply noBlue (join_copies Gᶜ H {x} single f (fun _ j => fresh j) ?_)
    intro i j e
    have ix : i.val = x := i.prop
    have ed : H.Adj x j.val := by simpa only [← ix] using (show H.Adj i.val j.val from e)
    refine ⟨fresh j, fun red => h (mem_biUnion.mpr ⟨⟨j.val,ed⟩,mem_univ _, ?_⟩)⟩
    exact (G.mem_neighborFinset _ _).mpr red.symm
  have le := (card_le_card cover).trans (card_biUnion_le_card_mul univ
    (fun i : H.neighborSet x => G.neighborFinset (f (hood i)))
    r (fun i _ => by simpa using bound (f (hood i))))
  have sp : S.card = Fintype.card V - (Fintype.card W - 1) := by
    simp only [S, Finset.card_compl, card_map, card_univ, Fintype.card_compl_set, Fintype.card_unique]
  have wp : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨x⟩
  simp only [card_univ, card_neighborSet_eq_degree, sp] at le
  omega

theorem long_degree_witness {V W : Type*} [Fintype V] [Fintype W] [Nonempty V]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (x : W) (f : (H.induce ({x}ᶜ : Set W)).Copy Gᶜ) (noBlue : ¬ H ⊑ Gᶜ) :
    ∃ u : V, Fintype.card V + 1 - Fintype.card W ≤ H.degree x * G.degree u := by
  classical
  obtain ⟨u,_,bound⟩ := (univ : Finset V).exists_max_image (fun z => G.degree z) univ_nonempty
  exact ⟨u,long_extension_obstruction G H x _ (fun z => bound z (mem_univ _)) f noBlue⟩

private theorem induced_edge_count_le {W : Type*} [Fintype W] (H : SimpleGraph W)
    (P : Set W) : (H.induce P).edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using
    Fintype.card_le_of_embedding (Copy.induce H P).mapEdgeSet

/-- Embed the two pieces chosen by averaging. The cardinality bounds are
given in integers, so no rounding is needed at the point of gluing. -/
theorem long_partition_step {W V : Type} [Fintype W] [Fintype V]
    (H : SimpleGraph W) [DecidableRel H.Adj] (G : SimpleGraph V) (v : V)
    {k s B : ℕ} (hk : 5 ≤ k) (hs : s < Fintype.card W) (hm : 0 < H.edgeSet.ncard)
    (far : Finset V)
    (cross : ∀ x ∈ G.neighborSet v, ∀ y ∈ far, Gᶜ.Adj x y)
    (nearSize : Fintype.card W - s + (k-1)*Nat.sqrt (2*H.edgeSet.ncard) ≤
      (G.neighborSet v).ncard)
    (farSize : s ≤ far.card)
    (budget : 2*H.edgeSet.ncard*s^2 + B*(Fintype.card W)^2 ≤ far.card*(Fintype.card W)^2)
    (ih : ∀ (U : Type) [Fintype U] (J : SimpleGraph U) [DecidableRel J.Adj],
      (∀ x, 0 < J.degree x) → J.edgeSet.ncard < H.edgeSet.ncard →
      graphRamsey (cycleGraph k) J ≤ 2*J.edgeSet.ncard + B) :
    cycleGraph k ⊑ G ∨ H ⊑ Gᶜ := by
  classical
  by_cases cyc : cycleGraph k ⊑ G
  · exact Or.inl cyc
  apply Or.inr
  obtain ⟨S,sz,avg⟩ := sparse_subset_square H s hs.le
  let P := (S : Set W)
  let J := H.induce P
  have er : J.edgeSet.ncard < H.edgeSet.ncard := by
    apply lt_of_not_ge
    intro h
    have aux := Nat.mul_le_mul_right (Fintype.card W ^ 2) h
    have small := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hs (by decide : 2 ≠ 0)) hm
    exact small.not_ge (aux.trans avg)
  have room : 2*J.edgeSet.ncard+B ≤ far.card := by
    apply (Nat.mul_le_mul_right_iff (pow_pos (by omega : 0 < Fintype.card W) 2)).mp
    calc
      _ = 2*(J.edgeSet.ncard * Fintype.card W ^ 2) + B*Fintype.card W ^ 2 := by ring
      _ ≤ 2*(H.edgeSet.ncard * s^2) + B*Fintype.card W ^ 2 := by gcongr
      _ ≤ _ := by simpa only [Nat.mul_assoc] using budget
  let L := H.induce Pᶜ
  let A := G.neighborSet v
  have leftSpace : graphRamsey (pathGraph (k-1)) L ≤ Fintype.card A := by
    apply (path_ramsey_edges L _).trans
    have el : L.edgeSet.ncard ≤ H.edgeSet.ncard := induced_edge_count_le H _
    have z : Fintype.card P = s := by simpa [P] using sz
    have z' : Fintype.card (↥Pᶜ) = Fintype.card W - s := by rw [Fintype.card_compl_set,z]
    change Fintype.card (↥Pᶜ) + _ ≤ _
    rw [z']
    have near' : Fintype.card W - s + (k-1) * Nat.sqrt (2*H.edgeSet.ncard) ≤ Fintype.card A := by
      simpa only [A, Set.ncard_eq_toFinset_card', Set.toFinset_card] using nearSize
    apply le_trans _ near'
    gcongr
  obtain path | left := graphRamsey_host (pathGraph (k-1)) L (G.induce A) leftSpace
  · exact (cyc (cycle_of_neighborhood_path G v k (by omega) path)).elim
  let T := J.induce J.support
  have et : T.edgeSet.ncard ≤ J.edgeSet.ncard := induced_edge_count_le J _
  have posT : ∀ x, 0 < T.degree x := by
    intro x
    obtain ⟨y,hy⟩ := x.prop
    exact (T.degree_pos_iff_exists_adj _).mpr ⟨⟨y,(show J.Adj x.val y from hy).mem_support_right⟩,hy⟩
  have rightSpace := (ih _ T posT (et.trans_lt er)).trans (show 2*T.edgeSet.ncard + B ≤
      Fintype.card far by simpa using (le_trans (by omega : 2*T.edgeSet.ncard+B ≤ 2*J.edgeSet.ncard+B) room))
  obtain rc | right := graphRamsey_host (cycleGraph k) T (G.induce (far : Set V)) rightSpace
  · exact (cyc (rc.trans ⟨Copy.induce G _⟩)).elim
  have right' := restore_isolates ((G.induce (far : Set V))ᶜ) J
    (show Fintype.card P ≤ Fintype.card far by simpa [P,sz] using farSize) right
  have flip (D : Set V) : (G.induce D)ᶜ ≤ Gᶜ.induce D := by
    intro i j e
    exact ⟨fun h => e.1 (Subtype.ext h), e.2⟩
  apply join_across_complete Gᶜ H P (far : Set V) A (fun y hy x hx => (cross x hx y hy).symm)
  · exact right'.trans ⟨Copy.ofLE _ _ (flip _)⟩
  · exact left.trans ⟨Copy.ofLE _ _ (flip _)⟩

/-- After placing the high-degree vertices, the target extends whenever each
remaining vertex has at most d neighbors and the host has d*r spare vertices. -/
theorem long_embed_low_degree {W V : Type} [Fintype W] [Fintype V]
    (H : SimpleGraph W) [DecidableRel H.Adj] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Set W) (core : H.induce P ⊑ Gᶜ) {d r : ℕ}
    (low : ∀ x ∉ P, H.degree x ≤ d) (red : ∀ u, G.degree u ≤ r)
    (space : Fintype.card W + d*r ≤ Fintype.card V) : H ⊑ Gᶜ := by
  classical
  by_cases all : P = Set.univ
  · subst P
    let e : H.Copy (H.induce Set.univ) :=
      ⟨⟨fun x => ⟨x,Set.mem_univ _⟩,fun h => h⟩,fun _ _ h => congrArg Subtype.val h⟩
    exact (show H ⊑ _ from ⟨e⟩).trans core
  obtain ⟨x,hx⟩ : ∃ x, x ∉ P := by simpa only [Set.eq_univ_iff_forall,not_forall] using all
  let A : Set W := {x}ᶜ
  let J := H.induce A
  let T : Set A := {z | z.val ∈ P}
  let f : (J.induce T).Copy (H.induce P) :=
    ⟨⟨fun z => ⟨z.val.val, z.prop⟩,fun e => e⟩,fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun a : P => a.val) h))⟩
  have sub : J.induce T ⊑ Gᶜ := (show _ ⊑ H.induce P from ⟨f⟩).trans core
  have cardA : Fintype.card A = Fintype.card W - 1 := by
    dsimp only [A]
    rw [Fintype.card_compl_set]
    simp
  have pos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨x⟩
  obtain ⟨copy⟩ := long_embed_low_degree J G T sub
    (fun z hz => ((Copy.induce H A).degree_le z).trans (low _ hz)) red (by omega)
  by_contra h
  have obs := long_extension_obstruction G H x r red copy h
  have := Nat.mul_le_mul_right r (low x hx)
  omega
termination_by Fintype.card W
decreasing_by
  classical
  exact (show Fintype.card A < Fintype.card W by omega)

end OMA

/- Embedding sparse targets against even cycles -/

namespace OMA
open SimpleGraph Finset

set_option maxRecDepth 4096 in
/-- Fixed even cycles admit arbitrary sparse targets when an eighth of the
host order is available for the embedding. Connectivity is unnecessary. -/
theorem long_even_with_slack (l : ℕ) (hl : 3 ≤ l) :
    ∃ N₀, ∀ (V W : Type) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
      [DecidableRel H.Adj], N₀ ≤ Fintype.card V → 8*Fintype.card W ≤ 7*Fintype.card V →
      H.edgeSet.ncard ≤ 2*Fintype.card V → cycleGraph (2*l) ⊑ G ∨ H ⊑ Gᶜ := by
  classical
  let C := 1048576*(l+1)
  let K := 65536^5 + 16*C + (2*(4*(2*l)+4))^10 + 1
  refine ⟨2*K^12, fun V W _ _ G H _ large spare edges => ?_⟩
  by_cases cyc : cycleGraph (2*l) ⊑ G
  · exact Or.inl cyc
  apply Or.inr
  let N := Fintype.card V
  let t := Nat.nthRoot 12 (N/2)
  have kt : K ≤ t := (Nat.le_nthRoot_iff (by decide : 12 ≠ 0)).mpr (by dsimp [N]; omega)
  have tp : 0 < t := by dsimp only [K] at kt; omega
  have base : 2*t^12 ≤ N := by
    have h : t^12 ≤ N/2 := Nat.pow_nthRoot_le (Or.inl (by decide))
    omega
  have cap : N ≤ 8193*t^12 := by
    have ub := Nat.lt_pow_nthRoot_add_one (by decide : 12 ≠ 0) (N/2)
    change N/2 < (t+1)^12 at ub
    have cmp := Nat.pow_le_pow_left (by omega : t+1 ≤ 2*t) 12
    rw [mul_pow] at cmp
    norm_num at cmp
    omega
  let d := t^5
  let r := C*t^6
  have rp : 0 < r^2 := by dsimp [r,C]; positivity
  have rbig : 64*l*N ≤ r^2 := calc
    _ ≤ 64*l*(8193*t^12) := Nat.mul_le_mul_left _ cap
    _ ≤ r^2 := by
      dsimp [r,C]
      have cmp : 64*l*8193 ≤ (1048576*(l+1))^2 := by nlinarith
      convert Nat.mul_le_mul_right (t^12) cmp using 1 <;> ring
  let bad := univ.filter (fun v => r ≤ G.degree v)
  have badSmall : 16*bad.card ≤ N := by
    apply (Nat.mul_le_mul_right_iff rp).mp
    calc
      _ = 16*(bad.card*r^2) := by ring
      _ ≤ 16*(4*l*N^2) := Nat.mul_le_mul_left _ (long_even_high_degree G (by omega) cyc r)
      _ = (64*l*N)*N := by ring
      _ ≤ r^2*N := Nat.mul_le_mul_right _ rbig
      _ = _ := by ring
  let good := badᶜ
  have goodCard : good.card = N - bad.card := card_compl _
  have goodRed (u : good) : (G.induce (good : Set V)).degree u ≤ r := by
    apply ((Copy.induce G (good : Set V)).degree_le u).trans
    have hu := mem_compl.mp u.prop
    change u.val ∉ univ.filter _ at hu
    simp only [mem_filter,mem_univ,true_and,not_le] at hu
    exact hu.le
  let P := univ.filter (fun w => d ≤ H.degree w)
  have highBound : P.card ≤ 65536*t^7 := by
    have dp : 0 < d := by dsimp [d]; positivity
    apply (Nat.mul_le_mul_right_iff dp).mp
    have hand : (∑ w, H.degree w) = 2*H.edgeSet.ncard := by
      rw [Set.ncard_eq_toFinset_card']; exact H.sum_degrees_eq_twice_card_edges
    calc
      _ = ∑ _ ∈ P, d := by simp
      _ ≤ ∑ w ∈ P, H.degree w := sum_le_sum fun w hw => (mem_filter.mp hw).2
      _ ≤ ∑ w, H.degree w := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
      _ ≤ 4*N := by change H.edgeSet.ncard ≤ 2*N at edges; omega
      _ ≤ 4*(8193*t^12) := Nat.mul_le_mul_left _ cap
      _ ≤ _ := by dsimp [d]; ring_nf; omega
  have nsmall : (Fintype.card P)^5 ≤ (t^12)^3 := calc
    _ ≤ (65536*t^7)^5 := Nat.pow_le_pow_left (by simpa using highBound) _
    _ = 65536^5 * t^35 := by ring
    _ ≤ t*t^35 := Nat.mul_le_mul_right _ (by dsimp only [K] at kt; omega)
    _ = _ := by ring
  have coreBound := dense_target (H.induce (P : Set W)) (k := 2*l) (m := t^12) (by omega)
    (by have h := Nat.le_self_pow (by decide : 12 ≠ 0) t; dsimp only [K] at kt; omega) nsmall
  have room : graphRamsey (cycleGraph (2*l)) (H.induce (P : Set W)) ≤ Fintype.card good :=
    coreBound.trans (by simp only [Fintype.card_coe]; omega)
  obtain rc | core := graphRamsey_host _ _ (G.induce (good : Set V)) room
  · exact (cyc (rc.trans ⟨Copy.induce G _⟩)).elim
  have cost : 16*(d*r) ≤ t^12 := calc
    _ = (16*C)*t^11 := by dsimp [r,d]; ring
    _ ≤ t*t^11 := Nat.mul_le_mul_right _ ((show 16*C ≤ K from ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)).trans kt)
    _ = _ := by ring
  have space : Fintype.card W + d*r ≤ Fintype.card good := by
    rw [Fintype.card_coe]
    change 8*Fintype.card W ≤ 7*N at spare
    omega
  have fit := long_embed_low_degree H (G.induce (good : Set V)) (P : Set W) core
    (d := d) (fun x hx => Nat.le_of_lt (Nat.lt_of_not_ge fun h => hx (mem_filter.mpr ⟨mem_univ _,h⟩)))
    goodRed space
  exact fit.trans ⟨⟨⟨Subtype.val,fun {i j} e => ⟨fun h => e.1 (Subtype.ext h),e.2⟩⟩,
    Subtype.val_injective⟩⟩

theorem long_sparse_even (l : ℕ) (hl : 3 ≤ l) :
    ∃ n₀, ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      n₀ ≤ Fintype.card W → H.edgeSet.ncard ≤ 2*Fintype.card W →
      graphRamsey (cycleGraph (2*l)) H ≤ 2*Fintype.card W-1 := by
  obtain ⟨N,h⟩ := long_even_with_slack l hl
  refine ⟨N+2, fun W _ H _ large edges => (graphRamsey_le_iff ..).2 fun G => ?_⟩
  apply h _ _ G H <;> simp only [Fintype.card_fin] <;> omega

end OMA

/- The eventual cycle versus matching bound, for both parities -/

namespace OMA
open SimpleGraph

private def Fits {W V : Type*} (H : SimpleGraph W) (B : SimpleGraph V) (s : Finset V) :=
  ∃ f : H.Copy B, ∀ x, f x ∈ s

private theorem fits_clique {W V : Type*} [Fintype W] (H : SimpleGraph W)
    (B : SimpleGraph V) (q : Finset V) (hq : B.IsClique (↑q : Set V))
    (size : Fintype.card W ≤ q.card) : Fits H B q := by
  obtain ⟨f⟩ : Nonempty (W ↪ q) :=
    Function.Embedding.nonempty_of_card_le (by simpa using size)
  let g := f.trans (Function.Embedding.subtype _)
  exact ⟨⟨⟨g, fun {x y} e => hq (f x).prop (f y).prop (g.injective.ne e.ne)⟩,
    g.injective⟩, fun i => (f i).prop⟩

/-- Alternate between a clique and its common neighborhood. For odd lengths the
closing edge lies in the clique. -/
theorem long_cycle_of_join {V : Type*} (G : SimpleGraph V) {k : ℕ} (_hk : 3 ≤ k)
    (a q : Finset V) (ha : G.IsClique (↑a : Set V))
    (cross : ∀ x ∈ a, ∀ y ∈ q, G.Adj x y)
    (sa : (k+1)/2 ≤ a.card) (sq : k/2 ≤ q.card) : cycleGraph k ⊑ G := by
  obtain ⟨f⟩ : Nonempty (Fin ((k+1)/2) ↪ a) :=
    Function.Embedding.nonempty_of_card_le (by simpa using sa)
  obtain ⟨g⟩ : Nonempty (Fin (k/2) ↪ q) :=
    Function.Embedding.nonempty_of_card_le (by simpa using sq)
  let F (i : Fin k) : V := if h : i.val % 2 = 0 then
    (f ⟨i.val/2, by omega⟩).val else (g ⟨i.val/2, by omega⟩).val
  have inj : Function.Injective F := by
    intro i j e
    dsimp only [F] at e
    split at e <;> split at e
    · have h := congrArg Fin.val (f.injective (Subtype.ext e))
      apply Fin.ext
      dsimp at h
      omega
    · exact False.elim ((cross _ (f _).prop _ (g _).prop).ne e)
    · exact False.elim ((cross _ (f _).prop _ (g _).prop).ne e.symm)
    · have h := congrArg Fin.val (g.injective (Subtype.ext e))
      apply Fin.ext
      dsimp at h
      omega
  refine ⟨⟨⟨F, fun {i j} e => ?_⟩, inj⟩⟩
  have ne := inj.ne e.ne
  have parity : i.val % 2 ≠ 1 ∨ j.val % 2 ≠ 1 := by
    have aux {u v : Fin k} (h : (u-v).val = 1) : u.val % 2 ≠ 1 ∨ v.val % 2 ≠ 1 := by
      by_cases lt : u < v
      · rw [Fin.coe_sub_iff_lt.mpr lt] at h
        omega
      · rw [Fin.sub_val_of_le (le_of_not_gt lt)] at h
        omega
    rcases cycleGraph_adj'.mp e with h|h
    · exact aux h
    · exact (aux h).symm
  dsimp only [F] at ne ⊢
  split <;> split
  · apply ha (f _).prop (f _).prop
    simpa only [dif_pos ‹i.val % 2 = 0›, dif_pos ‹j.val % 2 = 0›] using ne
  · exact cross _ (f _).prop _ (g _).prop
  · exact (cross _ (f _).prop _ (g _).prop).symm
  · omega

private theorem fits_add_pair {V W : Type*} [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph W) (B : SimpleGraph V) (s t : Finset V)
    (x y : W) (xy : H.Adj x y) (unique : ∀ z, ∃! w, H.Adj z w)
    (v w : V) (vw : B.Adj v w) (vs : v ∈ s) (ws : w ∈ s)
    (ts : t ⊆ s) (vt : v ∉ t) (wt : w ∉ t)
    (rest : Fits (H.induce ({x,y}ᶜ : Set W)) B t) : Fits H B s := by
  classical
  obtain ⟨g,hg⟩ := rest
  let f (z : W) : V := if hx : z = x then v else if hy : z = y then w else
    g ⟨z, by simp_all⟩
  have xne := xy.ne
  have vne := vw.ne
  have finj : Function.Injective f := by
    intro i j eq
    dsimp only [f] at eq
    repeat' split at eq
    all_goals first | exact congrArg Subtype.val (g.injective eq) | grind only
  refine ⟨⟨⟨f, fun {i j} e => ?_⟩, finj⟩, fun i => ?_⟩
  · have ix (h : i = x) : j = y := (unique x).unique (h ▸ e) xy
    have iy (h : i = y) : j = x := (unique y).unique (h ▸ e) xy.symm
    have jx (h : j = x) : i = y := (unique x).unique (h ▸ e.symm) xy
    have jy (h : j = y) : i = x := (unique y).unique (h ▸ e.symm) xy.symm
    dsimp only [f]
    repeat' split
    all_goals first | exact g.toHom.map_rel' e | exact vw.symm | grind only
  · change f i ∈ s
    dsimp only [f]
    repeat' split
    all_goals first | assumption | exact ts (hg _)

/-- Keep a blue clique in reserve while removing blue edges. Once the outside
is a red clique it has fewer than k vertices, so every subsequent cross-edge
removal leaves enough of the reserve for an alternating red cycle. -/
private theorem matching_aux {V W : Type} [DecidableEq V] [Fintype W]
    (H : SimpleGraph W) (G : SimpleGraph V) {k : ℕ} (hk : 3 ≤ k)
    (unique : ∀ z, ∃! w, H.Adj z w) (a q : Finset V)
    (dis : Disjoint a q) (hq : Gᶜ.IsClique (↑q : Set V))
    (reserve : k + min k a.card ≤ q.card)
    (size : Fintype.card W + (k-1)/2 ≤ a.card + q.card) :
    cycleGraph k ⊑ G ∨ Fits H Gᶜ (a ∪ q) := by
  classical
  by_cases fits : Fintype.card W ≤ q.card
  · obtain ⟨f,hf⟩ := fits_clique H Gᶜ q hq fits
    exact Or.inr ⟨f,fun z => Finset.mem_union_right _ (hf z)⟩
  obtain ⟨x⟩ : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨y,xy,_⟩ := unique x
  have xne := xy.ne
  let P : Set W := {x,y}ᶜ
  have cardP : Fintype.card P + 2 = Fintype.card W := by
    dsimp [P]
    rw [Fintype.card_compl_set]
    have h : Fintype.card ({x,y} : Set W) = 2 := by simp [xne]
    have le := Fintype.card_subtype_le (fun i => i ∈ ({x,y} : Set W))
    omega
  have uniqueP : ∀ z : P, ∃! w, (H.induce P).Adj z w := by
    intro z
    obtain ⟨w,zw,hw⟩ := unique z.val
    have wp : w ∈ P := by
      have zx : z.val ≠ x ∧ z.val ≠ y := by
        exact ⟨fun h => z.prop (Or.inl h), fun h => z.prop (Or.inr h)⟩
      simp only [P, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · rintro rfl
        exact zx.2 ((unique _).unique zw.symm xy)
      · rintro rfl
        exact zx.1 ((unique _).unique zw.symm xy.symm)
    exact ⟨⟨w, wp⟩, zw, fun z' ez => Subtype.ext (hw _ ez)⟩
  have peel (a' q' : Finset V) (v w : V) (vw : Gᶜ.Adj v w)
      (vs : v ∈ a ∪ q) (ws : w ∈ a ∪ q) (asub : a' ⊆ a) (qsub : q' ⊆ q)
      (vt : v ∉ a' ∪ q') (wt : w ∉ a' ∪ q')
      (rs : k + min k a'.card ≤ q'.card) (count : a'.card + q'.card + 2 = a.card + q.card) :
      cycleGraph k ⊑ G ∨ Fits H Gᶜ (a ∪ q) := by
    rcases matching_aux (H.induce P) G hk uniqueP a' q' (dis.mono asub qsub)
        (hq.subset (by exact_mod_cast qsub)) rs (by omega) with cyc | rest
    · exact Or.inl cyc
    · exact Or.inr (fits_add_pair H Gᶜ _ _ x y xy unique v w vw vs ws
        (Finset.union_subset_union asub qsub) vt wt rest)
  by_cases blue : ∃ v ∈ a, ∃ w ∈ a, Gᶜ.Adj v w
  · obtain ⟨v,hv,w,hw,vw⟩ := blue
    have ne := vw.ne
    have hw' : w ∈ a.erase v := Finset.mem_erase.mpr ⟨ne.symm,hw⟩
    have h₁ := Finset.card_erase_add_one hv
    have h₂ := Finset.card_erase_add_one hw'
    have vn := Finset.disjoint_left.mp dis hv
    have wn := Finset.disjoint_left.mp dis hw
    exact peel ((a.erase v).erase w) q v w vw (by simp [hv]) (by simp [hw])
      ((Finset.erase_subset ..).trans (Finset.erase_subset ..)) (fun ⦃_⦄ h => h)
      (by simp [vn]) (by simp [wn]) (by omega) (by omega)
  have ha : G.IsClique (↑a : Set V) := by
    intro v hv w hw ne
    by_contra h
    exact blue ⟨v,hv,w,hw,ne,h⟩
  by_cases many : k ≤ a.card
  · obtain ⟨f,_⟩ := fits_clique (cycleGraph k) G a ha (by simpa using many)
    exact Or.inl ⟨f⟩
  by_cases bridge : ∃ v ∈ a, ∃ w ∈ q, Gᶜ.Adj v w
  · obtain ⟨v,hv,w,hw,vw⟩ := bridge
    have h₁ := Finset.card_erase_add_one hv
    have h₂ := Finset.card_erase_add_one hw
    have vn := Finset.disjoint_left.mp dis hv
    have wn := Finset.disjoint_right.mp dis hw
    exact peel (a.erase v) (q.erase w) v w vw (by simp [hv]) (by simp [hw])
      (Finset.erase_subset ..) (Finset.erase_subset ..) (by simp [vn]) (by simp [wn])
      (by omega) (by omega)
  exact Or.inl (long_cycle_of_join G hk a q ha (fun v hv w hw => by
    by_contra h
    exact bridge ⟨v,hv,w,hw,(fun eq => Finset.disjoint_left.mp dis hv (eq ▸ hw)),h⟩)
    (by omega) (by omega))
termination_by Fintype.card W
decreasing_by
  classical
  exact (show Fintype.card P < Fintype.card W by omega)

/-- The matching target fits on any sufficiently large host with the stated slack. -/
theorem long_matching_host {V W : Type} [Fintype V] [Fintype W]
    (k : ℕ) (hk : 3 ≤ k) (G : SimpleGraph V) (H : SimpleGraph W)
    (unique : ∀ v, ∃! w, H.Adj v w)
    (rich : graphRamsey (cycleGraph k) (⊤ : SimpleGraph (Fin (2*k))) ≤ Fintype.card V)
    (size : Fintype.card W + (k-1)/2 ≤ Fintype.card V) : cycleGraph k ⊑ G ∨ H ⊑ Gᶜ := by
  classical
  let K : SimpleGraph (Fin (2*k)) := ⊤
  by_cases cyc : cycleGraph k ⊑ G
  · exact Or.inl cyc
  have b := (graphRamsey_host (cycleGraph k) K G rich).resolve_left cyc
  let f := b.some
  let q := Finset.univ.map f.toEmbedding
  have qc : q.card = 2*k := by simp [q]
  have cl : Gᶜ.IsClique (↑q : Set _) := by
    intro x hx y hy ne
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hy
    apply f.toHom.map_rel'
    exact fun h => ne (congrArg _ h)
  have le : q.card ≤ Fintype.card V := Finset.card_le_univ _
  have res := matching_aux H G hk unique qᶜ q disjoint_compl_left cl (by omega)
    (by rw [Finset.card_compl]; omega)
  exact res.imp_right fun ⟨g,_⟩ => ⟨g⟩

/-- For each cycle length the sharp matching upper bound holds for all
sufficiently large matchings, for both parities of the cycle length. -/
theorem long_matching_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ M, ∀ m ≥ M, ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v, H.degree v = 1) → H.edgeSet.ncard = m →
      graphRamsey (cycleGraph k) H ≤ 2*m+(k-1)/2 := by
  classical
  refine ⟨graphRamsey (cycleGraph k) (⊤ : SimpleGraph (Fin (2*k))), fun m hm W _ H _ deg he => ?_⟩
  apply (graphRamsey_le_iff ..).2
  intro G
  have sz := H.sum_degrees_eq_twice_card_edges
  have card : Fintype.card W = 2*m := by
    rw [Set.ncard_eq_toFinset_card'] at he
    change H.edgeFinset.card = m at he
    simpa [deg, he] using sz
  apply long_matching_host k hk G H (fun z => degree_eq_one_iff_existsUnique_adj.mp (deg z))
  · simp only [Fintype.card_fin]; omega
  · simp only [Fintype.card_fin, card]; omega

end OMA

/- The large-order bound for all even cycle lengths at least six -/

namespace OMA
open SimpleGraph Finset

private theorem split_matching_components {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (pos : ∀ w, 0 < H.degree w) :
    ∃ P : Finset W, 4*P.card ≤ 6*H.edgeSet.ncard ∧
      (∀ x ∈ P, ∀ y ∉ P, ¬ H.Adj x y) ∧
      (∀ z : ↥(↑P : Set W)ᶜ, ∃! w, (H.induce (↑P : Set W)ᶜ).Adj z w) := by
  classical
  let D := univ.filter (fun w => 1 < H.degree w)
  let T := D.biUnion (fun w => H.neighborFinset w)
  let L := T \ D
  let P := D ∪ L
  have dmem (v : W) : v ∈ D ↔ 1 < H.degree v := by simp [D]
  have mem (v : W) : v ∈ P ↔ v ∈ D ∨ v ∈ T := by
    simp only [P,L,mem_union,mem_sdiff]; tauto
  have cross (x : W) (hx : x ∈ P) (y : W) (hy : y ∉ P) (e : H.Adj x y) : False := by
    by_cases dx : x ∈ D
    · exact hy ((mem y).mpr (Or.inr (mem_biUnion.mpr ⟨x,dx,(H.mem_neighborFinset _ _).mpr e⟩)))
    obtain ⟨z,dz,zx⟩ := mem_biUnion.mp ((mem x).mp hx |>.resolve_left dx)
    have one : H.degree x = 1 := by have := pos x; have := (dmem x).not.mp dx; omega
    have eq := (degree_eq_one_iff_existsUnique_adj.mp one).unique e ((H.mem_neighborFinset _ _).mp zx).symm
    exact hy ((mem y).mpr (Or.inl (eq ▸ dz)))
  have sumD : 2*D.card ≤ ∑ x ∈ D, H.degree x := by
    simpa [Nat.mul_comm] using sum_le_sum (s := D) (f := fun _ => 2) (g := fun w => H.degree w)
      (fun x hx => (dmem x).mp hx)
  have sumL : L.card ≤ ∑ x ∈ D, H.degree x := by
    apply (card_le_card (sdiff_subset : L ⊆ T)).trans
    simpa only [card_neighborFinset_eq_degree] using
      (card_biUnion_le (s := D) (t := fun w => H.neighborFinset w))
  have dis : Disjoint D L := disjoint_sdiff_self_right
  have pc : P.card = D.card+L.card := card_union_of_disjoint dis
  have allD : (∑ x ∈ D, H.degree x) + L.card ≤ 2*H.edgeSet.ncard := calc
    _ ≤ (∑ x ∈ D, H.degree x) + ∑ x ∈ L, H.degree x := by
      have h := sum_le_sum (s := L) (f := fun _ => 1) (g := fun w => H.degree w) (fun x _ => pos x)
      simpa using h
    _ = ∑ x ∈ P, H.degree x := (sum_union dis).symm
    _ ≤ ∑ x, H.degree x := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
    _ = _ := by rw [Set.ncard_eq_toFinset_card']; exact H.sum_degrees_eq_twice_card_edges
  refine ⟨P,by omega,cross,?_⟩
  intro z
  have dh : z.val ∉ D := fun h => z.prop ((mem _).mpr (.inl h))
  have one : H.degree z.val = 1 := by have := (dmem _).not.mp dh; have := pos z.val; omega
  obtain ⟨w,e,hu⟩ := degree_eq_one_iff_existsUnique_adj.mp one
  have wp : w ∉ P := fun h => cross _ h _ z.prop e.symm
  exact ⟨⟨w,wp⟩,e,fun w' hw => Subtype.ext (hu _ hw)⟩

theorem long_even_bound (l : ℕ) (hl : 3 ≤ l) : LargeOrderBound (2*l) := by
  classical
  obtain ⟨N₀,hN⟩ := long_even_with_slack l hl
  let R := graphRamsey (cycleGraph (2*l)) (⊤ : SimpleGraph (Fin (2*(2*l))))
  refine ⟨N₀ + 2*R, fun m large W _ H _ pos edges _ => ?_⟩
  apply (graphRamsey_le_iff ..).2
  intro G
  by_cases cyc : cycleGraph (2*l) ⊑ G
  · exact Or.inl cyc
  apply Or.inr
  obtain ⟨P,pc,cross,unique⟩ := split_matching_components H pos
  let J := H.induce (P : Set W)
  have bounds : J.edgeSet.ncard ≤ H.edgeSet.ncard := by
    simpa only [Set.ncard_eq_toFinset_card',Set.toFinset_card] using
      Fintype.card_le_of_embedding (Copy.induce H (P : Set W)).mapEdgeSet
  obtain ⟨f⟩ := (hN _ _ G J (by simp; omega) (by simp; omega) (by simp; omega)).resolve_left cyc
  let Q := (univ.map f.toEmbedding)ᶜ
  have qc : Q.card = 2*m+(2*l-1)/2-P.card := by
    simp only [Q, card_compl, card_map, card_univ, Fintype.card_fin]
    rw [show Fintype.card (↥(P : Set W)) = P.card by simp]
  let K := H.induce (↑P : Set W)ᶜ
  have total := vertices_le_twice_edges H pos
  have right := long_matching_host (2*l) (by omega) (G.induce (Q : Set _)) K unique
    (by change R ≤ Fintype.card Q; simp only [Fintype.card_coe]; omega)
    (by rw [Fintype.card_compl_set]; have hp : Fintype.card (↥(P : Set W)) = P.card := by simp
        have hq : Fintype.card (↥(Q : Set (Fin (2*m+(2*l-1)/2)))) = Q.card := by simp
        omega)
  have nr : ¬ cycleGraph (2*l) ⊑ G.induce (Q : Set _) := fun rc => cyc (rc.trans ⟨Copy.induce G _⟩)
  obtain ⟨g⟩ := right.resolve_left nr
  let lift : ((G.induce (Q : Set _))ᶜ).Copy Gᶜ :=
    ⟨⟨Subtype.val,fun {i j} e => ⟨fun h => e.1 (Subtype.ext h),e.2⟩⟩,Subtype.val_injective⟩
  apply join_copies Gᶜ H (P : Set W) f (lift.comp g)
  · intro x y eq
    exact (mem_compl.mp (g y).prop) (mem_map.mpr ⟨x,mem_univ _,eq⟩)
  · intro x y e
    exact (cross _ x.prop _ y.prop e).elim

end OMA

/- The two-neighborhood step of the long-cycle induction -/

namespace OMA
open SimpleGraph Finset

private theorem card_irrel {α : Type*} (a b : Fintype α) : @Fintype.card α a = @Fintype.card α b := by
  rw [Subsingleton.elim a b]

private theorem lift_blue_from_induce {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (A : Set V) (h : H ⊑ (G.induce A)ᶜ) : H ⊑ Gᶜ :=
  h.trans ⟨⟨⟨Subtype.val,fun {_ _} e => ⟨fun eq => e.1 (Subtype.ext eq),e.2⟩⟩,
    Subtype.val_injective⟩⟩

private theorem partition_arithmetic {u n m d p N B : ℕ} (hn : 0 < n)
    (hd : 1 ≤ d) (hlo : n+2*d ≤ 2*u) (hhi : u < n+d) (gap : n+6*d ≤ m)
    (base : 2*m ≤ N) (budget : 2*m+B ≤ N+d) (shell : p ≤ n+2*d) :
    let s := n+d-u
    s ≤ N-(1+u+p) ∧ 2*m*s^2+B*n^2 ≤ (N-(1+u+p))*n^2 := by
  let t := ((u : ℝ)-d)/n
  have np : (0:ℝ) < n := by exact_mod_cast hn
  have frac : 1/2 ≤ t ∧ t ≤ 1 := by
    dsimp [t]
    constructor
    · apply (le_div_iff₀ np).mpr
      have : (n:ℝ)+2*d ≤ 2*u := by exact_mod_cast hlo
      linarith
    · apply (div_le_iff₀ np).mpr
      have : (u:ℝ) < n+d := by exact_mod_cast hhi
      linarith
  have first : (u : ℝ) = n*t+d := by dsimp [t]; field_simp; ring
  have bound := far_neighborhood_lower (m := (m:ℝ)) (n := (n:ℝ)) (u := (u:ℝ))
    (p := (p:ℝ)) (N := (N:ℝ)) (B := (B:ℝ)) (d := (d:ℝ)) (t := t) (by positivity)
    (by exact_mod_cast hd) (by exact_mod_cast gap) (by exact_mod_cast base)
    (by
      have : (2:ℝ)*m+B ≤ N+d := by exact_mod_cast budget
      linarith) frac first (by exact_mod_cast shell)
  have nonneg : 1+u+p ≤ N := by omega
  have sub : u ≤ n+d := by omega
  have eq : (↑(n+d-u) : ℝ) = n*(1-t) := by rw [Nat.cast_sub sub,Nat.cast_add]; linarith
  have sz := (le_max_left ..).trans bound
  have cost := (le_max_right ..).trans bound
  have farEq : (↑(N-(1+u+p)):ℝ) = N-1-u-p := by push_cast [Nat.cast_sub nonneg]; ring
  constructor
  · exact_mod_cast (show (↑(n+d-u):ℝ) ≤ ↑(N-(1+u+p)) by rw [eq,farEq]; exact sz)
  · have h := mul_le_mul_of_nonneg_right cost (sq_nonneg (n:ℝ))
    have realBound : (2:ℝ)*m*(↑(n+d-u):ℝ)^2 + B*(n:ℝ)^2 ≤ (↑(N-(1+u+p)):ℝ)*(n:ℝ)^2 := by
      rw [eq,farEq]
      nlinarith only [h]
    exact_mod_cast realBound

/-- The middle-density case, given the density margins and the inductive
blue copy with a minimum-degree vertex removed. -/
theorem long_middle_step {W V : Type} [Fintype W] [Fintype V] [Nonempty V]
    (H : SimpleGraph W) [DecidableRel H.Adj] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k B d : ℕ} (hk : 5 ≤ k) (x : W)
    (copy : H.induce ({x}ᶜ : Set W) ⊑ Gᶜ)
    (hm : 0 < H.edgeSet.ncard)
    (avg : H.degree x * Fintype.card W ≤ 2*H.edgeSet.ncard)
    (pathCost : k*Nat.sqrt (2*H.edgeSet.ncard) ≤ d) (hd : 0 < d)
    (lower : 2*H.edgeSet.ncard*d + (Fintype.card W)^2 ≤ Fintype.card W * H.edgeSet.ncard)
    (gap : Fintype.card W+6*d ≤ H.edgeSet.ncard)
    (base : 2*H.edgeSet.ncard ≤ Fintype.card V) (budget : 2*H.edgeSet.ncard+B ≤ Fintype.card V+d)
    (ih : ∀ (U : Type) [Fintype U] (J : SimpleGraph U) [DecidableRel J.Adj],
      (∀ w, 0 < J.degree w) → J.edgeSet.ncard < H.edgeSet.ncard →
      graphRamsey (cycleGraph k) J ≤ 2*J.edgeSet.ncard + B) :
    cycleGraph k ⊑ G ∨ H ⊑ Gᶜ := by
  classical
  by_contra fail
  have bad := not_or.mp fail
  obtain ⟨v,pivot⟩ := long_degree_witness G H x copy.some bad.2
  let n := Fintype.card W
  let m := H.edgeSet.ncard
  let N := Fintype.card V
  let A := G.neighborFinset v
  let P := (secondShell G v).toFinset
  let F := (insert v (A ∪ P))ᶜ
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨x⟩
  have near : 2*m ≤ H.degree x * A.card + n := by
    change N+1-n ≤ H.degree x*A.card at pivot
    change 2*m ≤ N at base
    omega
  have h₁ : n+2*d ≤ 2*A.card := by
    have lb := first_neighborhood_lower (m := (m:ℝ)) (n := (n:ℝ)) (u := (A.card:ℝ))
      (δ := (H.degree x : ℝ)) (slack := (d:ℝ)) (by exact_mod_cast hm) (by positivity) (by positivity)
      (by exact_mod_cast avg) (by
        have h : (2:ℝ)*m ≤ H.degree x*A.card+n := by exact_mod_cast near
        linarith)
      (by
        have h : (2:ℝ)*m*d + (n:ℝ)^2 ≤ n*m := by exact_mod_cast lower
        nlinarith)
    exact_mod_cast (show (n:ℝ)+2*d ≤ 2*A.card by linarith)
  have localSize (Q : Set V) (j : ℕ) (free : ¬ pathGraph j ⊑ G.induce Q) :
      Fintype.card Q < n + j*Nat.sqrt (2*m) := by
    by_contra! enough
    have b := (graphRamsey_host _ _ (G.induce Q) ((path_ramsey_edges H j).trans enough)).resolve_left free
    exact bad.2 (lift_blue_from_induce G H Q b)
  have h₂ : A.card < n+d := by
    have l := localSize (G.neighborSet v) (k-1) (fun p => bad.1 (cycle_of_neighborhood_path G v k (by omega) p))
    have le := Nat.mul_le_mul_right (Nat.sqrt (2*m)) (by omega : k-1 ≤ k)
    change k*Nat.sqrt (2*m) ≤ d at pathCost
    have e : A.card = (G.neighborSet v).ncard := (Set.ncard_eq_toFinset_card' _).symm
    rw [e,Set.ncard_eq_toFinset_card',Set.toFinset_card]
    convert! l.trans_le (Nat.add_le_add_left (le.trans pathCost) n) using 1
    apply card_irrel
  have h₃ : P.card ≤ n+2*d := by
    have l := localSize (secondShell G v) (2*k) (fun p => bad.1 (cycle_of_second_shell_path G v k hk p))
    change k*Nat.sqrt (2*m) ≤ d at pathCost
    rw [Nat.mul_assoc] at l
    change (secondShell G v).toFinset.card ≤ n+2*d
    rw [Set.toFinset_card]; omega
  have room := partition_arithmetic hn hd h₁ h₂ gap base budget h₃
  have farSize : N-(1+A.card+P.card) ≤ F.card := by
    rw [show F.card = N-(insert v (A ∪ P)).card from card_compl _]
    have ins := card_insert_le v (A ∪ P)
    have add := card_union_le A P
    omega
  have cross (a : V) (ha : a ∈ G.neighborSet v) (b : V) (hb : b ∈ F) : Gᶜ.Adj a b := by
    have bb := mem_compl.mp hb
    simp only [mem_insert, mem_union, not_or] at bb
    have nb : ¬G.Adj v b := fun h => bb.2.1 ((G.mem_neighborFinset _ _).mpr h)
    exact ⟨fun eq => nb (eq ▸ ha),fun e => bb.2.2 ((secondShell G v).mem_toFinset.mpr ⟨bb.1,nb,a,ha,e⟩)⟩
  have nearSize : n-(n+d-A.card)+(k-1)*Nat.sqrt (2*m) ≤ A.card := by
    have le := Nat.mul_le_mul_right (Nat.sqrt (2*m)) (by omega : k-1 ≤ k)
    change k*Nat.sqrt (2*m) ≤ d at pathCost
    omega
  have res := long_partition_step H G v hk (s := n+d-A.card) (by omega) hm F cross
    (by rwa [Set.ncard_eq_toFinset_card' (G.neighborSet v)])
    (room.1.trans farSize) (room.2.trans (Nat.mul_le_mul_right _ farSize)) ih
  exact res.elim bad.1 bad.2

end OMA

/- Removing a connected component in the cycle Ramsey induction -/

namespace OMA
open SimpleGraph

def longBudget (t B m : ℕ) := 2*m + max (B-m.sqrt) t

private theorem sqrt_step (m : ℕ) : (m+1).sqrt ≤ m.sqrt+1 := by
  apply Nat.le_of_lt_succ
  apply Nat.sqrt_lt.mpr
  have := Nat.lt_succ_sqrt m
  nlinarith

theorem longBudget_mono (t B : ℕ) : Monotone (longBudget t B) := by
  apply monotone_nat_of_le_succ
  intro m
  have := sqrt_step m
  simp only [longBudget]
  omega

/-- Removing a component with at least two edges frees its full order in
the budget, including the loss from the square-root correction. -/
theorem longBudget_remove {p e : ℕ} (he : 2 ≤ e) (t B : ℕ) :
    longBudget t B p + (e+1) ≤ longBudget t B (p+e) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le he
  have growth : (p+(2+s)).sqrt < p.sqrt + (2+s) := by
    apply Nat.sqrt_lt.mpr
    have := Nat.lt_succ_sqrt p
    nlinarith [Nat.zero_le (p.sqrt*s),Nat.zero_le (s*s)]
  simp only [longBudget]
  omega

private theorem hand {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] :
    (∑ x, H.degree x) = 2*H.edgeSet.ncard := by
  rw [Set.ncard_eq_toFinset_card']; exact H.sum_degrees_eq_twice_card_edges

/-- A disconnected nonmatching target splits off a component with at least
two edges. Both pieces retain their vertex degrees. -/
theorem long_component_step {V W : Type} [Fintype V] [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (G : SimpleGraph V) {k t B : ℕ}
    (pos : ∀ w, 0 < H.degree w) (disc : ¬H.Connected) (branch : ∃ w, 1 < H.degree w)
    (size : longBudget t B H.edgeSet.ncard ≤ Fintype.card V)
    (ih : ∀ (U : Type) [Fintype U] (J : SimpleGraph U) [DecidableRel J.Adj],
      (∀ u, 0 < J.degree u) → J.edgeSet.ncard < H.edgeSet.ncard →
      graphRamsey (cycleGraph k) J ≤ longBudget t B J.edgeSet.ncard) :
    cycleGraph k ⊑ G ∨ H ⊑ Gᶜ := by
  classical
  by_cases cyc : cycleGraph k ⊑ G
  · exact Or.inl cyc
  apply Or.inr
  obtain ⟨v,hv⟩ := branch
  let C := H.connectedComponentMk v
  let P := C.supp
  let A := H.induce P
  let D := H.induce Pᶜ
  have da (x : P) : A.degree x = H.degree x :=
    H.degree_induce_of_neighborSet_subset fun _ hy => C.mem_supp_of_adj_mem_supp x.prop hy
  have dd (x : ↥Pᶜ) : D.degree x = H.degree x :=
    H.degree_induce_of_neighborSet_subset fun _ hy h => x.prop (C.mem_supp_of_adj_mem_supp h hy.symm)
  have sum : D.edgeSet.ncard + A.edgeSet.ncard = H.edgeSet.ncard := by
    have e := Fintype.sum_subtype_add_sum_subtype (· ∈ P) (fun z => H.degree z)
    have h₁ := hand A
    have h₂ := hand D
    simp only [da] at h₁
    simp only [dd] at h₂
    have both : 2*A.edgeSet.ncard + 2*D.edgeSet.ncard = 2*H.edgeSet.ncard := calc
      _ = (∑ z : P, H.degree z.val) + ∑ z : ↥Pᶜ, H.degree z.val := congrArg₂ (·+·) h₁.symm h₂.symm
      _ = ∑ z, H.degree z := e
      _ = _ := hand H
    omega
  have ae : 2 ≤ A.edgeSet.ncard := by
    let x : P := ⟨v,rfl⟩
    have h := Finset.card_le_card (A.incidenceFinset_subset x)
    rw [A.card_incidenceFinset_eq_degree] at h
    rw [Set.ncard_eq_toFinset_card']
    change 2 ≤ A.edgeFinset.card
    rw [da] at h
    exact le_trans hv h
  have other : ∃ w, w ∉ P := by
    by_contra! h
    exact disc { preconnected := fun a b => C.reachable_of_mem_supp (h a) (h b), nonempty := ⟨v⟩ }
  obtain ⟨w,hw⟩ := other
  have de : 0 < D.edgeSet.ncard := by
    let x : ↥Pᶜ := ⟨w,hw⟩
    have h := Finset.card_le_card (D.incidenceFinset_subset x)
    rw [D.card_incidenceFinset_eq_degree] at h
    rw [Set.ncard_eq_toFinset_card']
    change 0 < D.edgeFinset.card
    exact lt_of_lt_of_le (by rw [dd]; exact pos _ : 0 < D.degree x) h
  have na : Fintype.card P ≤ A.edgeSet.ncard+1 := by
    have h := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    change Nat.card P ≤ Nat.card A.edgeSet+1 at h
    simpa only [Nat.card_coe_set_eq, ← Set.toFinset_card, ← Set.ncard_eq_toFinset_card'] using h
  have room := longBudget_remove ae (p := D.edgeSet.ncard) t B
  rw [sum] at room
  have left := ih _ A (fun x => (da x).symm ▸ pos _) (by omega)
  have fits := left.trans ((longBudget_mono t B (by omega : A.edgeSet.ncard ≤ H.edgeSet.ncard)).trans size)
  obtain ⟨f⟩ := (graphRamsey_host _ _ G fits).resolve_left cyc
  let R := (Finset.univ.map f.toEmbedding)ᶜ
  have rc : R.card = Fintype.card V - Fintype.card P := by
    simp only [R, Finset.card_compl, Finset.card_map, Finset.card_univ]
  have right := ih _ D (fun x => (dd x).symm ▸ pos _) (by omega)
  have fitsR : graphRamsey (cycleGraph k) D ≤ Fintype.card R := by
    rw [Fintype.card_coe,rc]; omega
  obtain ⟨g⟩ := (graphRamsey_host _ _ (G.induce (R : Set V)) fitsR).resolve_left
    (fun c => cyc (c.trans ⟨Copy.induce G _⟩))
  let lift : ((G.induce (R : Set V))ᶜ).Copy Gᶜ :=
    ⟨⟨Subtype.val,fun {i j} e => ⟨fun h => e.1 (Subtype.ext h),e.2⟩⟩,Subtype.val_injective⟩
  apply join_copies Gᶜ H P f (lift.comp g)
  · intro x y eq
    exact (Finset.mem_compl.mp (g y).prop) (Finset.mem_map.mpr ⟨x,Finset.mem_univ _,eq⟩)
  · intro i j e
    exact (j.prop (C.mem_supp_of_adj_mem_supp i.prop e)).elim

end OMA

/- Reduction of the long-cycle bound to sparse connected targets -/

namespace OMA
open SimpleGraph

/-- The connected, almost-tree upper bound used in the induction. -/
def LongSparseBound (k : ℕ) := ∃ n₀, ∀ (W : Type) [Fintype W] (H : SimpleGraph W)
  [DecidableRel H.Adj], H.Connected → n₀ ≤ Fintype.card W →
  (36*k^2)*H.edgeSet.ncard ≤ (36*k^2+1)*Fintype.card W →
  graphRamsey (cycleGraph k) H ≤ 2*Fintype.card W-1

/-- A sparse-case argument may use the inductive copies already present in the host. -/
def LongSparseStep (k : ℕ) := ∃ n₀, ∀ (W : Type) [Fintype W] (H : SimpleGraph W)
  [DecidableRel H.Adj] (V : Type) [Fintype V] (G : SimpleGraph V),
  H.Connected → n₀ ≤ Fintype.card W →
  (36*k^2)*H.edgeSet.ncard ≤ (36*k^2+1)*Fintype.card W → 2*Fintype.card W-1 ≤ Fintype.card V →
  (∀ (U : Type) [Fintype U] (J : SimpleGraph U) [DecidableRel J.Adj],
    Fintype.card U ≤ Fintype.card V → J.edgeSet.ncard < H.edgeSet.ncard → J ⊑ Gᶜ) →
  cycleGraph k ⊑ G ∨ H ⊑ Gᶜ

private theorem coarse_base {W : Type} [Fintype W] (H : SimpleGraph W) (k a : ℕ)
    (size : Fintype.card W ≤ a) : graphRamsey (cycleGraph k) H ≤
      graphRamsey (cycleGraph k) (⊤ : SimpleGraph (Fin a)) := by
  apply (graphRamsey_le_iff ..).2
  intro G
  apply (graphRamsey_property (cycleGraph k) (⊤ : SimpleGraph (Fin a)) G).imp_right
  intro b
  obtain ⟨f⟩ : Nonempty (W ↪ Fin a) := Function.Embedding.nonempty_of_card_le (by simpa)
  exact (show H ⊑ (⊤ : SimpleGraph (Fin a)) from ⟨⟨⟨f,fun e => f.injective.ne e.ne⟩,f.injective⟩⟩).trans b

private theorem margins {k m n : ℕ} (_hk : 5 ≤ k)
    (big : (20*(36*k^2+1)*k)^10 ≤ m) (order : m^3 < n^5)
    (gap : (36*k^2+1)*n < (36*k^2)*m) :
    let d := k*(2*m).sqrt
    2*m*d+n^2 ≤ n*m ∧ n+6*d ≤ m := by
  let q := 36*k^2+1
  let d := k*(2*m).sqrt
  have cut := sparse_cutoff big order.le
  have siz : 6*q*d ≤ n := by
    apply le_of_not_gt
    intro h
    have bad := Nat.pow_lt_pow_left h (by decide : 2 ≠ 0)
    have le : (6*q*d)^2 ≤ n^2 := calc
      _ = (6*q*k)^2 * ((2*m).sqrt)^2 := by dsimp [d]; ring
      _ ≤ (6*q*k)^2 * (2*m) := Nat.mul_le_mul_left _ (Nat.sqrt_le' _)
      _ ≤ (20*q*k)^2*m := by ring_nf; omega
      _ ≤ _ := cut
    omega
  have nq : n ≤ m := by
    by_contra! h
    have h' := Nat.mul_le_mul_left (36*k^2) h.le
    nlinarith
  have delta : m ≤ q*(m-n) := by
    rw [Nat.mul_sub]
    dsimp only [q]
    simp only [Nat.add_mul,one_mul] at gap ⊢
    omega
  have sd : 2*q*d ≤ n := by nlinarith
  have l : 2*m*d ≤ n*(m-n) := calc
    _ ≤ 2*(q*(m-n))*d := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ delta)
    _ = (2*q*d)*(m-n) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ sd
  have lim : q*(6*d) ≤ q*(m-n) := by
    calc
      _ = 6*q*d := by ring
      _ ≤ _ := siz.trans (nq.trans delta)
  have qp : 0 < q := by dsimp [q]; omega
  have := (Nat.mul_le_mul_left_iff qp).mp lim
  rw [Nat.mul_sub] at l
  have sq := Nat.mul_le_mul_left n nq
  change 2*m*d+n^2 ≤ n*m ∧ n+6*d ≤ m
  constructor
  · rw [pow_two]; omega
  · omega

private theorem restore_deleted {W V : Type} [Fintype W] [Fintype V] (H : SimpleGraph W)
    [DecidableRel H.Adj] (x : W) (pos : 0 < H.degree x) (G : SimpleGraph V)
    {k t B : ℕ} (nr : ¬ cycleGraph k ⊑ G) (order : Fintype.card W ≤ Fintype.card V)
    (size : longBudget t B H.edgeSet.ncard ≤ Fintype.card V)
    (ih : ∀ (U : Type) [Fintype U] (J : SimpleGraph U) [DecidableRel J.Adj],
      (∀ u, 0 < J.degree u) → J.edgeSet.ncard < H.edgeSet.ncard →
      graphRamsey (cycleGraph k) J ≤ longBudget t B J.edgeSet.ncard) :
    H.induce ({x}ᶜ : Set W) ⊑ Gᶜ := by
  classical
  let J := H.induce ({x}ᶜ : Set W)
  let K := J.induce J.support
  have cardJ : J.edgeSet.ncard = H.edgeSet.ncard - H.degree x := by
    rw [Set.ncard_eq_toFinset_card',Set.ncard_eq_toFinset_card']
    exact (H.card_edgeFinset_induce_compl_singleton x).trans (H.card_edgeFinset_deleteIncidenceSet x)
  have cardK : K.edgeSet.ncard = J.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card',Set.ncard_eq_toFinset_card']
    exact J.card_edgeFinset_induce_support
  have hm : 0 < H.edgeSet.ncard := by
    have h := Finset.card_le_card (H.incidenceFinset_subset x)
    rw [H.card_incidenceFinset_eq_degree] at h
    rw [Set.ncard_eq_toFinset_card']; exact pos.trans_le h
  have lt : K.edgeSet.ncard < H.edgeSet.ncard := by omega
  have bound := ih _ K (fun z => by
    rw [show K.degree z = J.degree z.val from J.degree_induce_support z]
    exact (J.degree_pos_iff_exists_adj _).mpr z.prop) lt
  apply restore_isolates Gᶜ J ((Fintype.card_subtype_le _).trans order)
  exact (graphRamsey_host _ _ G (bound.trans ((longBudget_mono t B lt.le).trans size))).resolve_left nr

/-- All graph-theoretic branches except the sparse connected bound are
discharged here, including the case of disconnected matching targets. -/
theorem long_bound_of_sparse_step (k : ℕ) (hk : 5 ≤ k) (sparse : LongSparseStep k) :
    LargeOrderBound k := by
  classical
  obtain ⟨n₀,sparse⟩ := sparse
  obtain ⟨M,matchB⟩ := long_matching_bound k (by omega)
  let c := 20*(36*k^2+1)*k
  let m₀ := M+n₀^5+c^10+(2*(4*k+4))^10+1
  let R := graphRamsey (cycleGraph k) (⊤ : SimpleGraph (Fin (2*m₀)))
  let t := (k-1)/2
  let B := R + m₀ + t
  have gen (m : ℕ) : ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ w, 0 < H.degree w) → H.edgeSet.ncard = m →
      graphRamsey (cycleGraph k) H ≤ longBudget t B m := by
    induction m using Nat.strong_induction_on with
    | h m prev =>
      intro W _ H _ pos he
      have vert := vertices_le_twice_edges H pos
      by_cases init : m ≤ m₀
      · have h := coarse_base H k (2*m₀) (by omega)
        change graphRamsey (cycleGraph k) H ≤ R at h
        have sq := Nat.sqrt_le_self m
        dsimp only [longBudget,B]
        omega
      have big : 0 < m ∧ n₀^5 < m ∧ c^10 ≤ m ∧ (2*(4*k+4))^10 ≤ m ∧ M ≤ m := by
        dsimp only [m₀] at init; omega
      obtain ⟨hm,hn₀,hc,hd,hmM⟩ := big
      by_cases small : (Fintype.card W)^5 ≤ m^3
      · have h := dense_target H hk hd small
        dsimp only [longBudget]; omega
      have hn₀' : n₀ ≤ Fintype.card W := by
        by_contra! low
        have e := Nat.pow_le_pow_left low.le 5
        have := Nat.le_self_pow (by decide : 3 ≠ 0) m
        omega
      have ih (U : Type) [Fintype U] (J : SimpleGraph U) [DecidableRel J.Adj]
          (p : ∀ u, 0 < J.degree u) (lt : J.edgeSet.ncard < H.edgeSet.ncard) :=
        prev J.edgeSet.ncard (he ▸ lt) U J p rfl
      by_cases matching : ∀ w, H.degree w = 1
      · have h := matchB m hmM W H matching he
        change graphRamsey (cycleGraph k) H ≤ 2*m+t at h
        dsimp only [longBudget]; omega
      apply (graphRamsey_le_iff ..).2
      intro G
      have size : Fintype.card (Fin (longBudget t B m)) = longBudget t B H.edgeSet.ncard := by simp [he]
      by_cases conn : H.Connected
      · have cn := conn.card_vert_le_card_edgeSet_add_one
        rw [Nat.card_coe_set_eq,Nat.card_eq_fintype_card] at cn
        by_cases thin : (36*k^2)*H.edgeSet.ncard ≤ (36*k^2+1)*Fintype.card W
        · by_cases nr : cycleGraph k ⊑ G
          · exact Or.inl nr
          apply sparse W H _ G conn hn₀' thin
          · rw [size]; dsimp only [longBudget,t]; omega
          · intro U _ J _ ord lt
            let E := J.induce J.support
            have ce : E.edgeSet.ncard = J.edgeSet.ncard := by
              rw [Set.ncard_eq_toFinset_card',Set.ncard_eq_toFinset_card']; exact J.card_edgeFinset_induce_support
            have positive (z : J.support) : 0 < E.degree z := by
              rw [show E.degree z = J.degree z.val from J.degree_induce_support z]
              exact (J.degree_pos_iff_exists_adj _).mpr z.prop
            have smaller := ih _ E positive (ce.trans_lt lt)
            apply restore_isolates _ J ord
            exact (graphRamsey_host _ _ G (smaller.trans ((longBudget_mono t B (ce.trans_lt lt).le).trans size.ge))).resolve_left nr
        let d := k*(2*m).sqrt
        obtain ⟨mar₁,mar₂⟩ := margins hk hc (Nat.lt_of_not_ge small) (he ▸ Nat.lt_of_not_ge thin)
        have hd₁ : 0 < d := Nat.mul_pos (by omega) (Nat.sqrt_pos.mpr (by omega))
        have sq : m.sqrt ≤ d := (Nat.sqrt_le_sqrt (by omega : m ≤ 2*m)).trans
          (Nat.le_mul_of_pos_left _ (by omega))
        have : Nonempty W := conn.nonempty
        obtain ⟨x,_,minD⟩ := (Finset.univ : Finset W).exists_min_image (fun w => H.degree w) Finset.univ_nonempty
        have avg : H.degree x * Fintype.card W ≤ 2*H.edgeSet.ncard := calc
          _ = ∑ _ : W, H.degree x := by simp [Nat.mul_comm]
          _ ≤ ∑ w, H.degree w := Finset.sum_le_sum fun w hw => minD w hw
          _ = _ := by rw [Set.ncard_eq_toFinset_card']; exact H.sum_degrees_eq_twice_card_edges
        by_cases nr : cycleGraph k ⊑ G
        · exact Or.inl nr
        have space : 2*H.edgeSet.ncard ≤ Fintype.card (Fin (longBudget t B m)) := by
          rw [size]; simp [longBudget]
        have : Nonempty (Fin (longBudget t B m)) := Fintype.card_pos_iff.mp (by omega)
        have del := restore_deleted H x (pos x) G nr (vert.trans space) size.ge ih
        apply long_middle_step H G hk x del (he ▸ hm) avg (d := d) (B := B) (he ▸ le_rfl) hd₁
          (he ▸ mar₁) (he ▸ mar₂) space
        · rw [size,he]; dsimp only [longBudget]; omega
        · intro U _ J _ p lt
          apply (ih U J p lt).trans
          dsimp only [longBudget,B]; omega
      · apply long_component_step H G pos conn _ size.ge ih
        push Not at matching
        obtain ⟨w,hw⟩ := matching
        exact ⟨w,by have := pos w; omega⟩
  refine ⟨B^2,fun m large W _ H _ pos he _ => ?_⟩
  have h := gen m W H pos he
  have thresh := Nat.le_sqrt'.mpr large
  simpa only [longBudget,Nat.sub_eq_zero_of_le thresh, Nat.zero_max,t] using h

theorem long_bound_of_sparse (k : ℕ) (hk : 5 ≤ k) (sparse : LongSparseBound k) :
    LargeOrderBound k := by
  obtain ⟨n₀,h⟩ := sparse
  apply long_bound_of_sparse_step k hk
  exact ⟨n₀,fun W _ H _ _ _ G conn large thin size _ =>
    graphRamsey_host _ _ G ((h W H conn large thin).trans size)⟩

end OMA

/- Odd cycles forced by repeated common neighborhoods -/

namespace OMA
open SimpleGraph Finset

private theorem close_chain {V : Type*} (G : SimpleGraph V) (L : List V) (ne : L ≠ [])
    (nd : L.Nodup) (ch : L.IsChain G.Adj) (endEdge : G.Adj (L.getLast ne) (L.head ne)) :
    cycleGraph L.length ⊑ G := by
  let f (i : ℕ) := if h : i < L.length then L[i] else L.head ne
  have hp := List.length_pos_iff.mpr ne
  apply cycle_of_sequence f
  · intro i hi j hj eq
    simp only [f,dif_pos hi,dif_pos hj] at eq
    exact congrArg Fin.val (nd.injective_get eq)
  · intro i hi
    simpa only [f,dif_pos hi,dif_pos (by omega : i < L.length)] using
      List.isChain_iff_getElem.mp ch i hi
  · simpa [f,List.getLast_eq_getElem,List.head_eq_getElem, hp,show L.length-1 < L.length by omega] using endEdge

/-- If every consecutive pair in a prescribed list has plenty of common
neighbors outside the list, insert distinct common neighbors in its gaps. -/
private theorem weave {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A Q : Finset V) (disj : Disjoint A Q) (k : ℕ)
    (common : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → k ≤ (Q.filter (fun z => G.Adj x z ∧ G.Adj y z)).card)
    (xs : List V) (ne : xs ≠ []) (nd : xs.Nodup) (inside : ∀ x ∈ xs, x ∈ A)
    (size : 2*xs.length-1 ≤ k) :
    ∃ (p : List V) (hp : p ≠ []), p.Nodup ∧ p.IsChain G.Adj ∧
      p.length = 2*xs.length-1 ∧ p.head hp = xs.head ne ∧ p.getLast hp = xs.getLast ne ∧
      (∀ x ∈ p, x ∈ Q ∨ x ∈ xs) := by
  induction xs with
  | nil => contradiction
  | cons x tail ih =>
    cases tail with
    | nil => exact ⟨[x],by simp,by simp,by simp,rfl,rfl,rfl,by simp⟩
    | cons y ys =>
      have tailIn : ∀ z ∈ y::ys, z ∈ A := fun z hz => inside z (List.mem_cons_of_mem _ hz)
      obtain ⟨p,hp,pnd,pch,pl,ph,pe,pm⟩ := ih (by simp) (List.nodup_cons.mp nd).2 tailIn
        (by simp only [List.length_cons] at size ⊢; omega)
      have hx := inside x List.mem_cons_self
      have hy := tailIn y List.mem_cons_self
      have xnt := (List.nodup_cons.mp nd).1
      have xne : x ≠ y := fun h => xnt (List.mem_cons.mpr (.inl h))
      let S := Q.filter (fun z => G.Adj x z ∧ G.Adj y z)
      have enough : k ≤ S.card := common x hx y hy xne
      have small := List.toFinset_card_le p
      obtain ⟨z,hz,nz⟩ : ∃ z ∈ S, z ∉ p := by
        by_contra! no
        have sub := card_le_card (show S ⊆ p.toFinset from fun z hz => List.mem_toFinset.mpr (no z hz))
        simp only [List.length_cons] at size pl
        omega
      obtain ⟨zQ,xz,yz⟩ := mem_filter.mp hz
      have xp : x ∉ p := fun h => (pm x h).elim (disjoint_left.mp disj hx) xnt
      have xz' := xz.ne
      refine ⟨x::z::p,by simp,by simp [xz',xp,nz,pnd],?_,?_,rfl,?_,?_⟩
      · refine List.isChain_cons_cons.mpr ⟨xz,?_⟩
        cases p with
        | nil => contradiction
        | cons u us =>
          change u = y at ph
          exact List.isChain_cons_cons.mpr ⟨ph ▸ yz.symm,pch⟩
      · simp only [List.length_cons] at pl ⊢; omega
      · simpa [List.getLast_cons hp] using pe
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact Or.inr List.mem_cons_self
        rcases List.mem_cons.mp hw with rfl | hw
        · exact Or.inl zQ
        exact (pm w hw).imp_right (List.mem_cons_of_mem _)

/-- A cycle-free host forces a blue clique on A if every pair in A has k
common red neighbors in a disjoint set Q. -/
theorem long_odd_common_neighbors {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (l : ℕ) (hl : 1 ≤ l) (A Q : Finset V) (dis : Disjoint A Q)
    (size : l+1 ≤ A.card) (free : ¬ cycleGraph (2*l+1) ⊑ G)
    (common : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 2*l+1 ≤ (Q.filter (fun z => G.Adj x z ∧ G.Adj y z)).card) :
    Gᶜ.IsClique (↑A : Set V) := by
  classical
  intro x hx y hy ne
  refine ⟨ne,fun red => free ?_⟩
  have er := card_erase_add_one hx
  have hy' : y ∈ A.erase x := mem_erase.mpr ⟨ne.symm,hy⟩
  have er' := card_erase_add_one hy'
  obtain ⟨T,sub,card⟩ := exists_subset_card_eq (s := (A.erase x).erase y) (show l-1 ≤ _ by omega)
  let xs := x::(T.toList ++ [y])
  have nx : x ∉ T := fun h => notMem_erase x A (mem_of_mem_erase (sub h))
  have ny : y ∉ T := fun h => notMem_erase y _ (sub h)
  have nd : xs.Nodup := by simp [xs,nx,ny,ne,List.nodup_append,T.nodup_toList]
  have inside : ∀ w ∈ xs, w ∈ A := by
    intro w hw
    simp only [xs,List.mem_cons,List.mem_append,mem_toList,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | hw | rfl
    · exact hx
    · exact mem_of_mem_erase (mem_of_mem_erase (sub hw))
    · exact hy
  have length : xs.length = l+1 := by simp [xs,card]; omega
  obtain ⟨p,hp,pnd,pch,pl,ph,pe,_⟩ := weave G A Q dis _ common xs (by simp [xs]) nd inside (by omega)
  have h := close_chain G p hp pnd pch (by simpa [ph,pe,xs] using red.symm)
  rwa [show p.length = 2*l+1 by omega] at h

/-- The common neighborhood of two distinct centers sees the entire first
neighborhood in blue when the centers share sufficiently many red neighbors. -/
theorem long_odd_fan_edges {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z Q : Finset V) {l : ℕ} (_hl : 2 ≤ l) (count : Z.card = l)
    (centers : Gᶜ.IsClique (Z : Set V)) (cross : ∀ z ∈ Z, ∀ q ∈ Q, G.Adj z q)
    (large : 2*l+3 ≤ Q.card) (free : ¬cycleGraph (2*l+1) ⊑ G)
    {a b : V} (ha : a ∈ Z) (hb : b ∈ Z) (ab : a ≠ b) {x y : V}
    (ax : G.Adj a x) (by' : G.Adj b y) (xy : x ≠ y) : Gᶜ.Adj x y := by
  classical
  refine ⟨xy,fun red => free ?_⟩
  let C := (Z.erase a).erase b
  let zs := b::(C.toList ++ [a])
  have bn : b ∈ Z.erase a := mem_erase.mpr ⟨ab.symm,hb⟩
  have card := card_erase_add_one bn
  have card' := card_erase_add_one ha
  have na : a ∉ C := fun h => notMem_erase a Z (mem_of_mem_erase h)
  have nb : b ∉ C := notMem_erase b _
  have zn : zs.Nodup := by simp [zs,na,nb,ab.symm,List.nodup_append,C.nodup_toList]
  have size : zs.length = l := by
    simp only [zs,List.length_cons,List.length_append,length_toList,List.length_nil]
    dsimp only [C]; omega
  have subset (w : V) (hw : w ∈ zs) : w ∈ Z := by
    simp only [zs,List.mem_cons,List.mem_append,mem_toList,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|hw|rfl
    · exact hb
    · exact mem_of_mem_erase (mem_of_mem_erase hw)
    · exact ha
  have notX : x ∉ Z := fun hx => (centers ha hx ax.ne).2 ax
  have notY : y ∉ Z := fun hy => (centers hb hy by'.ne).2 by'
  let D := (Q.erase x).erase y
  have sub : D ⊆ Q := (erase_subset ..).trans (erase_subset ..)
  have dis : Disjoint Z D := Finset.disjoint_left.mpr fun ⦃_⦄ hz hd => (cross _ hz _ (sub hd)).ne rfl
  have avail : 2*l+1 ≤ D.card := by
    have cost (s : Finset V) (u : V) : s.card ≤ (s.erase u).card+1 := by
      by_cases h : u ∈ s
      · exact (card_erase_add_one h).ge
      · simp [erase_eq_of_notMem h]
    have h₁ := cost Q x
    have h₂ := cost (Q.erase x) y
    dsimp only [D]
    omega
  have common (u : V) (hu : u ∈ Z) (v : V) (hv : v ∈ Z) (_ : u ≠ v) :
      2*l+1 ≤ (D.filter (fun q => G.Adj u q ∧ G.Adj v q)).card := by
    rw [filter_eq_self.mpr (fun q hq => ⟨cross _ hu q (sub hq),cross _ hv q (sub hq)⟩)]
    exact avail
  obtain ⟨p,hp,nd,ch,len,head,last,pm⟩ := weave G Z D dis _ common zs (by simp [zs])
    zn subset (by omega)
  have xp : x ∉ p := fun h => (pm _ h).elim
    (fun hd => notMem_erase x Q (mem_of_mem_erase hd)) (fun hz => notX (subset _ hz))
  have yp : y ∉ p := fun h => (pm _ h).elim (notMem_erase y _) (fun hz => notY (subset _ hz))
  have hd : G.Adj y (p.head hp) := by simpa [head,zs] using by'.symm
  have en : G.Adj (p.getLast hp) x := by simpa [last,zs] using ax
  have chain : (x::y::p).IsChain G.Adj := by
    apply List.isChain_cons_cons.mpr ⟨red,?_⟩
    cases p with
    | nil => contradiction
    | cons u us => exact List.isChain_cons_cons.mpr ⟨hd,ch⟩
  have h := close_chain G (x::y::p) (by simp) (by simp [xp,yp,xy,nd]) chain
    (by simpa [List.getLast_cons hp] using en)
  rwa [show (x::y::p).length = 2*l+1 by simp; omega] at h

end OMA

/- Inserting one new vertex into a suspended path -/

namespace OMA
open SimpleGraph

/-- Reverse a segment between two cuts to accommodate a new vertex while
keeping both ends fixed. Only the two cut edges are replaced. -/
theorem long_path_insertion {V : Type*} (B : SimpleGraph V) (p : ℕ → V) (z : V)
    (n a b : ℕ) (ab : a < b) (bn : b+1 < n)
    (inj : ∀ i < n, ∀ j < n, p i = p j → i = j)
    (step : ∀ i, i+1 < n → B.Adj (p i) (p (i+1)))
    (fresh : ∀ i < n, p i ≠ z) (az : B.Adj (p a) z)
    (zb : B.Adj z (p b)) (bridge : B.Adj (p (a+1)) (p (b+1))) :
    ∃ f : ℕ → V, f 0 = p 0 ∧ f n = p (n-1) ∧
      (∀ i ≤ n, f i = z ∨ ∃ j < n, f i = p j) ∧
      (∀ i ≤ n, ∀ j ≤ n, f i = f j → i = j) ∧
      (∀ i < n, B.Adj (f i) (f (i+1))) := by
  let ix (i : ℕ) := if i ≤ a then i else if i ≤ b+1 then b-(i-(a+2)) else i-1
  let f (i : ℕ) := if i = a+1 then z else p (ix i)
  have ok (i : ℕ) (hi : i ≤ n) : ix i < n := by
    dsimp only [ix]; repeat' split
    all_goals omega
  have ii {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (ni : i ≠ a+1) (nj : j ≠ a+1)
      (eq : ix i = ix j) : i = j := by
    dsimp only [ix] at eq
    repeat' split at eq
    all_goals omega
  refine ⟨f,by simp [f,ix],by simp [f,ix, show n ≠ a+1 by omega,show ¬n ≤ a by omega,
    show ¬n ≤ b+1 by omega],?_,?_,?_⟩
  · intro i hi
    by_cases hit : i = a+1
    · exact Or.inl (by simp [f,hit])
    · exact Or.inr ⟨ix i,ok _ hi,by simp [f,hit]⟩
  · intro i hi j hj eq
    dsimp only [f] at eq
    split at eq <;> split at eq
    · omega
    · exact (fresh _ (ok _ hj) eq.symm).elim
    · exact (fresh _ (ok _ hi) eq).elim
    · exact ii hi hj (by assumption) (by assumption) (inj _ (ok _ hi) _ (ok _ hj) eq)
  · intro i hi
    by_cases h₁ : i < a
    · simpa only [f,ix,if_neg (show i ≠ a+1 by omega),if_neg (show i+1 ≠ a+1 by omega),
        if_pos (show i ≤ a by omega),if_pos (show i+1 ≤ a by omega)] using step i (by omega)
    by_cases h₂ : i = a
    · subst i
      simpa [f,ix] using az
    by_cases h₃ : i = a+1
    · subst i
      simpa [f,ix,show a+1+1 ≤ b+1 by omega] using zb
    by_cases h₄ : i ≤ b
    · have adj := (step (ix (i+1)) (by
        dsimp only [ix]; repeat' split
        all_goals omega)).symm
      have idx : ix (i+1)+1 = ix i := by
        dsimp only [ix]; repeat' split
        all_goals omega
      simpa only [f, if_neg (show i ≠ a+1 by omega), if_neg (show i+1 ≠ a+1 by omega),idx] using adj
    by_cases h₅ : i = b+1
    · subst i
      dsimp only [f,ix]
      repeat' split
      all_goals first | omega | convert bridge using 2 <;> omega
    · have idx : ix (i+1) = ix i+1 := by
        dsimp only [ix]; repeat' split
        all_goals omega
      have s := step (ix i) (by rw [← idx]; exact ok _ (by omega))
      simpa only [f,if_neg (show i ≠ a+1 by omega),if_neg (show i+1 ≠ a+1 by omega),idx] using s

end OMA

/- Unused vertices around an unextendible path -/

namespace OMA
open SimpleGraph Finset

/-- If an endpoint-preserving blue path cannot be lengthened by one using
any unused vertex, the unused set must be a blue clique. -/
theorem long_blocked_path_clique {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {l n : ℕ} (hl : 1 ≤ l) (p : ℕ → V)
    (inj : ∀ i < n, ∀ j < n, p i = p j → i = j)
    (step : ∀ i, i+1 < n → Gᶜ.Adj (p i) (p (i+1)))
    (A : Finset V) (fresh : ∀ z ∈ A, ∀ i < n, p i ≠ z)
    (large : 6*(2*l+1) ≤ n) (size : l+1 ≤ A.card) (free : ¬ cycleGraph (2*l+1) ⊑ G)
    (blocked : ∀ z ∈ A, ¬ ∃ f : ℕ → V, f 0 = p 0 ∧ f n = p (n-1) ∧
      (∀ i ≤ n, f i = z ∨ ∃ j < n, f i = p j) ∧
      (∀ i ≤ n, ∀ j ≤ n, f i = f j → i = j) ∧
      (∀ i < n, Gᶜ.Adj (f i) (f (i+1)))) : Gᶜ.IsClique (↑A : Set V) := by
  classical
  let k := 2*l+1
  let I := range (3*k)
  let x (i : ℕ) := p (2*i)
  let y (i : ℕ) := p (2*i+1)
  let Q := I.image x
  have len (i : ℕ) (hi : i ∈ I) : 2*i+1 < n := by
    have := mem_range.mp hi
    dsimp only [k] at this
    omega
  have xi : Set.InjOn x I := fun i hi j hj eq => by
    have h := inj _ (by have := len i hi; omega : 2*i < n) _
      (by have := len j hj; omega : 2*j < n) eq
    omega
  let T (z : V) := I.filter (fun i => ¬ G.Adj z (x i))
  have small (z : V) (hz : z ∈ A) : (T z).card < k := by
    by_contra! big
    obtain ⟨f⟩ : Nonempty (Fin k ↪ T z) := Function.Embedding.nonempty_of_card_le (by simpa using big)
    have red {i j : ℕ} (hi : i ∈ T z) (hj : j ∈ T z) (lt : i < j) : G.Adj (y i) (y j) := by
      have a := (mem_filter.mp hi).1
      have b := (mem_filter.mp hj).1
      have ne : y i ≠ y j := by
        intro eq
        have := inj _ (len _ a) _ (len _ b) eq
        omega
      by_contra no
      apply blocked z hz
      apply long_path_insertion Gᶜ p z n (2*i) (2*j) (by omega) (len _ b) inj step (fresh z hz)
      · exact ⟨fresh z hz _ (by have := len _ a; omega),fun e => (mem_filter.mp hi).2 e.symm⟩
      · exact ⟨(fresh z hz _ (by have := len _ b; omega)).symm,(mem_filter.mp hj).2⟩
      · exact ⟨ne,no⟩
    let F (i : Fin k) := y (f i).val
    have fi : Function.Injective F := by
      intro i j eq
      have e := inj _ (len _ (mem_filter.mp (f i).prop).1) _ (len _ (mem_filter.mp (f j).prop).1) eq
      apply f.injective
      apply Subtype.ext
      omega
    apply free
    refine ⟨⟨⟨F,fun {i j} e => ?_⟩,fi⟩⟩
    have diff : (f i).val ≠ (f j).val := fun h => e.ne (f.injective (Subtype.ext h))
    rcases lt_or_gt_of_ne diff with h|h
    · exact red (f i).prop (f j).prop h
    · exact (red (f j).prop (f i).prop h).symm
  have dis : Disjoint A Q := disjoint_left.mpr fun ⦃_⦄ hz hQ => by
    obtain ⟨i,hi,eq⟩ := mem_image.mp hQ
    exact fresh _ hz _ (by have := len i hi; omega : 2*i < n) eq
  apply long_odd_common_neighbors G l hl A Q dis size free
  intro a ha b hb _
  let S := I \ (T a ∪ T b)
  have sa := small a ha
  have sb := small b hb
  have cnt : k ≤ S.card := by
    have h := card_le_card_sdiff_add_card (s := I) (t := T a ∪ T b)
    have u := card_union_le (T a) (T b)
    change I.card ≤ S.card+(T a ∪ T b).card at h
    rw [show I.card = 3*k from card_range _] at h
    omega
  have sub : S.image x ⊆ Q.filter (fun z => G.Adj a z ∧ G.Adj b z) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    obtain ⟨isin,neither⟩ := mem_sdiff.mp hi
    refine mem_filter.mpr ⟨mem_image_of_mem _ isin,?_,?_⟩
    · by_contra h
      exact neither (mem_union_left _ (mem_filter.mpr ⟨isin,h⟩))
    · by_contra h
      exact neither (mem_union_right _ (mem_filter.mpr ⟨isin,h⟩))
  have eq : (S.image x).card = S.card := card_image_of_injOn (xi.mono (by exact_mod_cast sdiff_subset))
  exact cnt.trans (eq ▸ card_le_card sub)

end OMA

/- Long paths among degree-two vertices of sparse connected targets -/

namespace OMA
open SimpleGraph Finset

private theorem closed_of_reachable {V : Type*} (G : SimpleGraph V) (S : Set V)
    (closed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S)
    {u v : V} (walk : G.Reachable u v) (start : u ∈ S) : v ∈ S := by
  obtain ⟨p⟩ := walk
  induction p with
  | nil => exact start
  | cons e _ ih => exact ih (closed _ start _ e)

/-- Two different neighbors exhaust the neighborhood at a vertex of degree at most two. -/
theorem long_two_neighbors {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    {x a b w : W} (deg : H.degree x ≤ 2) (ha : H.Adj x a) (hb : H.Adj x b) (ne : a ≠ b)
    (hw : H.Adj x w) : w = a ∨ w = b := by
  classical
  have sub : {a,b} ⊆ H.neighborFinset x := insert_subset ((H.mem_neighborFinset _ _).mpr ha)
    (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr hb))
  have eq := eq_of_subset_of_card_le sub (by simpa [ne] using deg)
  have mem := (H.mem_neighborFinset _ _).mpr hw
  rw [← eq] at mem
  simpa using mem

/-- A connected graph of maximum degree two contains paths of every order
up to its own order. -/
theorem long_path_of_degree_two {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected) (deg : ∀ w, H.degree w ≤ 2) {s : ℕ} (hs : s ≤ Fintype.card W) :
    pathGraph s ⊑ H := by
  classical
  have : Nonempty W := conn.nonempty
  obtain ⟨u,v,p,hp,maximal⟩ := Walk.exists_isPath_forall_isPath_length_le_length H
  have closed (a : W) (ha : a ∈ p.support) (b : W) (adj : H.Adj a b) : b ∈ p.support := by
    by_contra outside
    obtain ⟨i,rfl,hi⟩ := Walk.mem_support_iff_exists_getVert.mp ha
    by_cases first : i = 0
    · subst i
      simp only [Walk.getVert_zero] at adj
      have h := maximal _ _ (.cons adj.symm p) (hp.cons outside)
      simp at h
    by_cases last : i = p.length
    · subst i
      simp only [Walk.getVert_length] at adj
      have h := maximal _ _ (p.concat adj) (hp.concat outside adj)
      simp at h
    have pos : 0 < i := by omega
    have left := (p.adj_getVert_succ (show i-1 < p.length by omega)).symm
    rw [show i-1+1=i by omega] at left
    have right := p.adj_getVert_succ (show i < p.length by omega)
    have ne : p.getVert (i-1) ≠ p.getVert (i+1) := by
      intro eq
      have e := hp.getVert_injOn (x₁ := i-1) (x₂ := i+1) (by change i-1 ≤ p.length; omega)
        (by change i+1 ≤ p.length; omega) eq
      omega
    rcases long_two_neighbors H (deg _) left right ne adj with rfl|rfl <;>
      exact outside (p.getVert_mem_support _)
  have all (w : W) : w ∈ p.support := closed_of_reachable H {z | z ∈ p.support} closed
    (conn.preconnected u w) p.start_mem_support
  have univEq : p.support.toFinset = univ := eq_univ_iff_forall.mpr fun w => List.mem_toFinset.mpr (all w)
  have size := List.toFinset_card_le p.support
  rw [univEq,card_univ,Walk.length_support] at size
  let f (i : Fin s) := p.getVert i.val
  refine ⟨⟨⟨f,fun {i j} adj => ?_⟩,fun {i j} eq => Fin.ext (hp.getVert_injOn
    (by change i.val ≤ p.length; omega) (by change j.val ≤ p.length; omega) eq)⟩⟩
  rcases pathGraph_adj.mp adj with h|h
  · have e := p.adj_getVert_succ (show i.val < p.length by omega)
    simpa only [f,h] using e
  · have e := (p.adj_getVert_succ (show j.val < p.length by omega)).symm
    simpa only [f,h] using e

/-- Unless the degree-two part contains a long path, vertices outside it
and their neighbors account for the entire graph. -/
theorem long_degree_two_cover {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (conn : H.Connected) (B : Finset W) (root : B.Nonempty)
    (deg : ∀ z ∉ B, H.degree z ≤ 2) (s : ℕ)
    (no : ¬ pathGraph s ⊑ H.induce (↑Bᶜ : Set W)) :
    Fintype.card W ≤ B.card + s*(∑ x ∈ B, H.degree x) := by
  classical
  let D := Bᶜ
  let J := H.induce (D : Set W)
  let part (u : W) : Finset W := if h : u ∈ D then
    ((J.connectedComponentMk ⟨u,h⟩).supp.toFinset.map (Function.Embedding.subtype (· ∈ D))) else ∅
  have member {u : D} (x : D) (hx : x ∈ (J.connectedComponentMk u).supp) : x.val ∈ part u.val := by
    simp only [part,dif_pos u.prop]
    exact mem_map.mpr ⟨x,Set.mem_toFinset.mpr hx,rfl⟩
  have small (u : W) : (part u).card ≤ s := by
    by_cases hu : u ∈ D
    · let C := J.connectedComponentMk ⟨u,hu⟩
      have size : Fintype.card C.supp < s := by
        by_contra! big
        have path := long_path_of_degree_two (W := ↥C.supp) (J.induce C.supp) C.connected_toSimpleGraph
          (fun z => ((Copy.induce J C.supp).degree_le z).trans
            (((Copy.induce H (D : Set W)).degree_le z.val).trans (deg _ (mem_compl.mp z.val.prop)))) big
        exact no (path.trans ⟨Copy.induce J C.supp⟩)
      simpa only [part,dif_pos hu,card_map,Set.toFinset_card] using size.le
    · simp [part,hu]
  let U := B.biUnion (fun w => H.neighborFinset w)
  have cov : univ ⊆ B ∪ U.biUnion part := by
    intro w _
    by_cases wb : w ∈ B
    · exact mem_union_left _ wb
    apply mem_union_right
    let x : D := ⟨w,mem_compl.mpr wb⟩
    let C := J.connectedComponentMk x
    let E := C.supp.toFinset.map (Function.Embedding.subtype (· ∈ D))
    have inside {u : D} : u.val ∈ E ↔ u ∈ C.supp := by
      simp only [E,mem_map]
      constructor
      · rintro ⟨v,hv,eq⟩
        exact (Subtype.ext eq : v = u) ▸ (Set.mem_toFinset.mp hv)
      · exact fun h => ⟨u,Set.mem_toFinset.mpr h,rfl⟩
    have has : ∃ u : D, u ∈ C.supp ∧ ∃ b ∈ B, H.Adj u.val b := by
      by_contra! away
      have closed (u : W) (hu : u ∈ E) (v : W) (uv : H.Adj u v) : v ∈ E := by
        obtain ⟨z,hz,rfl⟩ := mem_map.mp hu
        have zc := Set.mem_toFinset.mp hz
        have vb : v ∉ B := fun hv => away z zc v hv uv
        let y : D := ⟨v,mem_compl.mpr vb⟩
        exact inside.mpr (C.mem_supp_of_adj_mem_supp zc (show J.Adj z y from uv))
      obtain ⟨b,hb⟩ := root
      have e := closed_of_reachable H (E : Set W) closed (conn.preconnected w b)
        (inside.mpr (show x ∈ C.supp from rfl))
      obtain ⟨v,_,eq⟩ := mem_map.mp e
      change v.val = b at eq
      exact mem_compl.mp v.prop (eq.symm ▸ hb)
    obtain ⟨u,cu,b,hb,ub⟩ := has
    have same : J.connectedComponentMk u = C := cu
    exact mem_biUnion.mpr ⟨u.val,mem_biUnion.mpr ⟨b,hb,(H.mem_neighborFinset _ _).mpr ub.symm⟩,
      member x (by rw [same]; rfl)⟩
  have cU : U.card ≤ ∑ x ∈ B, H.degree x := by
    simpa only [card_neighborFinset_eq_degree] using
      (card_biUnion_le (s := B) (t := fun w => H.neighborFinset w))
  have pU := card_biUnion_le_card_mul U part s (fun x _ => small x)
  have count := (card_le_card cov).trans (card_union_le ..)
  rw [card_univ] at count
  have mul := Nat.mul_le_mul_right s cU
  rw [Nat.mul_comm s]
  omega

/-- If every path on s degree-two vertices is absent, the leaves and the
excess in the edge count bound the order. The extra two permits marking
one vertex even when the entire graph is a cycle. -/
theorem long_leaves_or_thread {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected) (pos : ∀ w, 0 < H.degree w) (s : ℕ) :
    pathGraph s ⊑ H.induce {w | H.degree w = 2} ∨
      Fintype.card W + (s+1)*(6*Fintype.card W) ≤
        (s+1)*(6*H.edgeSet.ncard + 4*(univ.filter (fun w => H.degree w = 1)).card + 2) := by
  classical
  by_cases path : pathGraph s ⊑ H.induce {w | H.degree w = 2}
  · exact Or.inl path
  apply Or.inr
  obtain ⟨r⟩ := conn.nonempty
  let exc := univ.filter (fun w => H.degree w ≠ 2)
  let B := insert r exc
  let L := univ.filter (fun w => H.degree w = 1)
  have outside (w : W) (hw : w ∉ B) : H.degree w = 2 := by
    by_contra h
    exact hw (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _,h⟩))
  let f : (H.induce (↑Bᶜ : Set W)).Copy (H.induce {w | H.degree w = 2}) :=
    ⟨⟨fun z => ⟨z.val,outside z.val (mem_compl.mp z.prop)⟩,fun e => e⟩,
      fun _ _ h => Subtype.ext (congrArg (fun z : {w // H.degree w = 2} => z.val) h)⟩
  have cover := long_degree_two_cover H conn B (insert_nonempty ..) (fun z h => (outside z h).le) s
    (fun p => path (p.trans ⟨f⟩))
  let total := ∑ w ∈ B, H.degree w
  have cardB : B.card ≤ total := by
    simpa [total] using sum_le_sum (s := B) (f := fun _ => 1) (g := fun w => H.degree w) (fun w _ => pos w)
  have degrees : ∑ w, H.degree w = 2*H.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card']; exact H.sum_degrees_eq_twice_card_edges
  have cnt : (∑ w ∈ exc, H.degree w) + 6*Fintype.card W ≤ 6*H.edgeSet.ncard+4*L.card := by
    have pt (w : W) : (if H.degree w ≠ 2 then H.degree w else 0)+6 ≤
        3*H.degree w + (if H.degree w = 1 then 4 else 0) := by
      have := pos w
      repeat' split
      all_goals omega
    have sum := sum_le_sum (s := univ) (fun w _ => pt w)
    rw [sum_add_distrib,sum_add_distrib,← mul_sum,degrees,← sum_filter,← sum_filter] at sum
    simp [exc,L,Nat.mul_comm,Nat.mul_left_comm] at sum ⊢
    omega
  have sumB : total ≤ (∑ w ∈ exc, H.degree w) + 2 := by
    by_cases hr : r ∈ exc
    · simp [total,B,insert_eq_of_mem hr]
    · have dr : H.degree r = 2 := by simpa [exc] using hr
      simp [total,B,sum_insert hr,dr,Nat.add_comm]
  have a : Fintype.card W ≤ (s+1)*total := by
    rw [Nat.add_mul,one_mul]
    change Fintype.card W ≤ B.card+s*total at cover
    omega
  have b : total + 6*Fintype.card W ≤ 6*H.edgeSet.ncard+4*L.card+2 := by omega
  have both := Nat.mul_le_mul_left (s+1) b
  rw [Nat.mul_add] at both
  exact (Nat.add_le_add_right a _).trans both

end OMA

/- Shortening and rebuilding a suspended path -/

namespace OMA
open SimpleGraph Finset

private theorem restore_thread {V W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (B : SimpleGraph V) {n : ℕ} (hn : 2 ≤ n) (p : ℕ → W)
    (pi : ∀ i ≤ n, ∀ j ≤ n, p i = p j → i = j)
    (ps : ∀ i < n, H.Adj (p i) (p (i+1)))
    (pd : ∀ i, 0 < i → i < n → H.degree (p i) ≤ 2)
    (old : (H.induce ({p 1}ᶜ : Set W)).Copy B) (q : ℕ → V)
    (qi : ∀ i ≤ n, ∀ j ≤ n, q i = q j → i = j)
    (qs : ∀ i < n, B.Adj (q i) (q (i+1)))
    (first : ∀ h, q 0 = old ⟨p 0,h⟩) (last : ∀ h, q n = old ⟨p n,h⟩)
    (apart : ∀ (w : ↥({p 1}ᶜ : Set W)), (∀ i ≤ n, p i ≠ w.val) → ∀ j ≤ n, q j ≠ old w) :
    H ⊑ B := by
  classical
  let on (w : W) := ∃ i ≤ n, p i = w
  let F (w : W) := if hw : on w then q hw.choose else old ⟨w,by
    exact fun eq => hw ⟨1,by omega,eq.symm⟩⟩
  have atP (i : ℕ) (hi : i ≤ n) : F (p i) = q i := by
    have h : on (p i) := ⟨i,hi,rfl⟩
    rw [show F (p i) = q h.choose from dif_pos h,pi _ h.choose_spec.1 i hi h.choose_spec.2]
  have atOld (w : ↥({p 1}ᶜ : Set W)) (h : ∀ i, 0 < i → i < n → p i ≠ w.val) :
      F w.val = old w := by
    by_cases t : on w.val
    · obtain ⟨i,hi,eq⟩ := t
      rw [← eq,atP _ hi]
      by_cases zero : i = 0
      · subst i
        obtain ⟨w,hw⟩ := w
        change p 0 = w at eq
        subst w
        exact first _
      · have en : i = n := by by_contra ne; exact h i (by omega) (by omega) eq
        subst i
        obtain ⟨w,hw⟩ := w
        change p n = w at eq
        subst w
        exact last _
    · exact dif_neg t
  have fi : Function.Injective F := by
    intro w v eq
    dsimp only [F] at eq
    split at eq <;> split at eq
    · rename_i a b
      exact a.choose_spec.2.symm.trans ((congrArg p (qi _ a.choose_spec.1 _ b.choose_spec.1 eq)).trans b.choose_spec.2)
    · rename_i a b
      exact (apart ⟨v,_⟩ (fun i hi e => b ⟨i,hi,e⟩) _ a.choose_spec.1 eq).elim
    · rename_i a b
      exact (apart ⟨w,_⟩ (fun i hi e => a ⟨i,hi,e⟩) _ b.choose_spec.1 eq.symm).elim
    · exact congrArg Subtype.val (old.injective eq)
  have middle (i : ℕ) (hp : 0 < i) (hi : i < n) (w : W) (adj : H.Adj (p i) w) :
      B.Adj (F (p i)) (F w) := by
    have back := (ps (i-1) (by omega)).symm
    rw [show i-1+1 = i by omega] at back
    have ne : p (i-1) ≠ p (i+1) := fun eq => by
      have := pi _ (by omega) _ (by omega) eq; omega
    rcases long_two_neighbors H (pd _ hp hi) back (ps i hi) ne adj with rfl | rfl
    · rw [atP _ hi.le,atP _ (by omega)]
      have qadj := (qs (i-1) (by omega)).symm
      rwa [show i-1+1=i by omega] at qadj
    · rw [atP _ hi.le,atP _ (by omega)]; exact qs i hi
  refine ⟨⟨⟨F,fun {w v} e => ?_⟩,fi⟩⟩
  by_cases hw : ∃ i, 0 < i ∧ i < n ∧ p i = w
  · obtain ⟨i,hp,hi,rfl⟩ := hw
    exact middle i hp hi v e
  by_cases hv : ∃ i, 0 < i ∧ i < n ∧ p i = v
  · obtain ⟨i,hp,hi,rfl⟩ := hv
    exact (middle i hp hi w e.symm).symm
  let w' : ↥({p 1}ᶜ : Set W) := ⟨w,fun h => hw ⟨1,by omega,by omega,h.symm⟩⟩
  let v' : ↥({p 1}ᶜ : Set W) := ⟨v,fun h => hv ⟨1,by omega,by omega,h.symm⟩⟩
  rw [atOld w' (fun i hp hi h => hw ⟨i,hp,hi,h⟩),atOld v' (fun i hp hi h => hv ⟨i,hp,hi,h⟩)]
  exact old.toHom.map_rel' e

/-- Suppressing a degree-two vertex preserves connectivity. -/
private theorem connected_bypass {W : Type} (H : SimpleGraph W) (conn : H.Connected)
    (x : W) (A : Set W) (Aeq : A = {x}ᶜ) (a b : A) (ne : a ≠ b)
    (two : ∀ w, H.Adj x w → w = a.val ∨ w = b.val) :
    (H.induce A ⊔ SimpleGraph.edge a b).Connected := by
  classical
  subst A
  let J := H.induce {x}ᶜ ⊔ SimpleGraph.edge a b
  let F (w : W) : ↥({x}ᶜ : Set W) := if h : w = x then a else ⟨w,h⟩
  have fa (w : ↥({x}ᶜ : Set W)) : F w.val = w := by
    simp only [F,dif_neg (show w.val ≠ x from w.prop)]
  have link (w : W) (e : H.Adj x w) : J.Reachable (F x) (F w) := by
    have aedge : J.Adj a b := Or.inr ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl,rfl⟩,ne⟩)
    rcases two w e with rfl | rfl
    · rw [fa]; simp [F]
    · rw [fa]; simpa [F] using aedge.reachable
  have lift {u v : W} (e : H.Adj u v) : J.Reachable (F u) (F v) := by
    by_cases hu : u = x
    · subst u; exact link _ e
    by_cases hv : v = x
    · subst v; exact (link _ e.symm).symm
    apply Adj.reachable
    exact Or.inl (show (H.induce {x}ᶜ).Adj (F u) (F v) by simpa [F,hu,hv] using e)
  have run {u v : W} (p : H.Walk u v) : J.Reachable (F u) (F v) := by
    induction p with
    | nil => exact .rfl
    | cons e _ ih => exact (lift e).trans ih
  exact { preconnected := fun u v => by simpa only [fa] using run (conn.preconnected u.val v.val).some
          nonempty := ⟨a⟩ }

/-- The inductive copy of the shortened graph suffices when the target has
a suspended path with 6k+1 vertices. -/
theorem long_suspended_case {W V : Type} [Fintype W] [Fintype V] (H : SimpleGraph W)
    [DecidableRel H.Adj] (G : SimpleGraph V) {l : ℕ} (hl : 2 ≤ l)
    (conn : H.Connected) (path : pathGraph (6*(2*l+1)+1) ⊑ H.induce {w | H.degree w = 2})
    (space : 2*Fintype.card W-1 ≤ Fintype.card V)
    (ih : ∀ (U : Type) [Fintype U] (J : SimpleGraph U) [DecidableRel J.Adj],
      Fintype.card U = Fintype.card W-1 → J.Connected → J.edgeSet.ncard < H.edgeSet.ncard → J ⊑ Gᶜ) :
    cycleGraph (2*l+1) ⊑ G ∨ H ⊑ Gᶜ := by
  classical
  let n := 6*(2*l+1)
  have hn : 3 ≤ n := by dsimp [n]; omega
  obtain ⟨f⟩ := path
  let p (i : ℕ) := (f ⟨i%(n+1),Nat.mod_lt _ (by omega)⟩).val
  have pi (i : ℕ) (hi : i ≤ n) (j : ℕ) (hj : j ≤ n) (eq : p i = p j) : i = j := by
    have e := congrArg Fin.val (f.injective (Subtype.ext eq))
    simpa only [Nat.mod_eq_of_lt (show i < n+1 by omega),Nat.mod_eq_of_lt (show j < n+1 by omega)] using e
  have ps (i : ℕ) (hi : i < n) : H.Adj (p i) (p (i+1)) := by
    apply f.toHom.map_rel'
    exact pathGraph_adj.mpr (Or.inl (by simp only [Nat.mod_eq_of_lt (show i < n+1 by omega),
      Nat.mod_eq_of_lt (show i+1 < n+1 by omega)]))
  have pd (i : ℕ) : H.degree (p i) = 2 := (f _).prop
  let A : Set W := {p 1}ᶜ
  have mem (i : ℕ) (hi : i ≤ n) (ne : i ≠ 1) : p i ∈ A := fun e => ne (pi _ hi 1 (by omega) e)
  let a : A := ⟨p 0,mem 0 (by omega) (by omega)⟩
  let b : A := ⟨p 2,mem 2 (by omega) (by omega)⟩
  have ab : a ≠ b := fun eq => by
    have h := pi 0 (by omega) 2 (by omega) (congrArg (fun z : A => z.val) eq); omega
  let D := H.induce A
  let J := D ⊔ SimpleGraph.edge a b
  have dj : D.edgeSet.ncard = H.edgeSet.ncard - 2 := by
    rw [Set.ncard_eq_toFinset_card',Set.ncard_eq_toFinset_card']
    change (H.induce ({p 1}ᶜ : Set W)).edgeFinset.card = H.edgeFinset.card - 2
    rw [H.card_edgeFinset_induce_compl_singleton,H.card_edgeFinset_deleteIncidenceSet,pd]
  have ej : J.edgeSet.ncard ≤ D.edgeSet.ncard+1 := by
    by_cases present : D.Adj a b
    · simp [J,D.sup_edge_of_adj present]
    · rw [Set.ncard_eq_toFinset_card',Set.ncard_eq_toFinset_card']
      exact (D.card_edgeFinset_sup_edge present ab).le
  have two : 2 ≤ H.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    exact (pd 1) ▸ H.degree_le_card_edgeFinset (p 1)
  have ca : Fintype.card A = Fintype.card W - 1 := by dsimp [A]; rw [Fintype.card_compl_set]; simp
  have connJ := connected_bypass H conn (p 1) A rfl a b ab (fun w e =>
    long_two_neighbors H (pd 1).le (ps 0 (by omega)).symm (ps 1 (by omega)) (fun hit => ab (Subtype.ext hit)) e)
  obtain ⟨g⟩ := ih _ J ca connJ (by omega)
  let old := g.comp (Copy.ofLE D J le_sup_left)
  let idx (i : ℕ) := if i = 0 ∨ n ≤ i then 0 else i+1
  let pt (i : ℕ) : A := ⟨p (idx i),mem _ (by dsimp [idx]; split <;> omega)
    (by dsimp [idx]; split <;> omega)⟩
  let q (i : ℕ) := g (pt i)
  have qinj (i : ℕ) (hi : i < n) (j : ℕ) (hj : j < n) (eq : q i = q j) : i = j := by
    have ie : idx i ≤ n := by dsimp [idx]; split <;> omega
    have je : idx j ≤ n := by dsimp [idx]; split <;> omega
    have eq' := pi _ ie _ je (congrArg (fun z : A => z.val) (g.injective eq))
    dsimp only [idx] at eq'
    repeat' split at eq'
    all_goals omega
  have step (i : ℕ) (hi : i+1 < n) : Gᶜ.Adj (q i) (q (i+1)) := by
    apply g.toHom.map_rel'
    by_cases zero : i = 0
    · subst i
      apply Or.inr
      change (SimpleGraph.edge a b).Adj (pt 0) (pt 1)
      have ea : pt 0 = a := by apply Subtype.ext; simp [pt,idx,a]
      have eb : pt 1 = b := by apply Subtype.ext; simp [pt,idx,b,show ¬n ≤ 1 by omega]
      rw [ea,eb]; simp [SimpleGraph.edge_adj,ab]
    · apply Or.inl
      change H.Adj (p (idx i)) (p (idx (i+1)))
      simpa [idx,zero,show ¬n ≤ i by omega,show ¬n ≤ i+1 by omega] using ps (i+1) hi
  let U := (univ.map g.toEmbedding)ᶜ
  have cu : U.card = Fintype.card V - Fintype.card A := by simp only [U,card_compl,card_map,card_univ]
  have fresh (z : V) (hz : z ∈ U) (i : ℕ) (_ : i < n) : q i ≠ z :=
    fun eq => mem_compl.mp hz (mem_map.mpr ⟨pt i,mem_univ _,eq⟩)
  by_cases cyc : cycleGraph (2*l+1) ⊑ G
  · exact Or.inl cyc
  apply Or.inr
  by_contra no
  have enough : n+1 ≤ Fintype.card W := by
    have := Fintype.card_le_of_injective _ ((Copy.induce H _).comp f).injective
    simpa only [Fintype.card_fin] using this
  have zu : Fintype.card W ≤ U.card := by omega
  have clique := long_blocked_path_clique G (l := l) (by omega) q qinj step U fresh (by rfl)
    (by dsimp [n] at enough; omega) cyc (fun z hz => ?_)
  · obtain ⟨e⟩ : Nonempty (W ↪ U) := Function.Embedding.nonempty_of_card_le (by simpa using zu)
    let emb := e.trans (Function.Embedding.subtype _)
    exact no ⟨⟨⟨emb,fun {i j} adj => clique (e i).prop (e j).prop (emb.injective.ne adj.ne)⟩,emb.injective⟩⟩
  · rintro ⟨ext,start,finish,used,fi,fs⟩
    apply no
    apply restore_thread H Gᶜ (by omega : 2 ≤ n) p pi ps (fun i _ _ => (pd i).le) old ext fi fs
    · intro h
      rw [start]
      apply congrArg g
      apply Subtype.ext
      simp [pt,idx]
    · intro h
      rw [finish]
      apply congrArg g
      apply Subtype.ext
      simp [pt,idx,show ¬n-1 = 0 by omega,show ¬n ≤ n-1 by omega,show n-1+1 = n by omega]
    · intro w absent i hi eq
      rcases used i hi with e|⟨j,hj,e⟩
      · exact mem_compl.mp hz (mem_map.mpr ⟨w,mem_univ _,eq.symm.trans e⟩)
      · have hit : pt j = w := g.injective (e.symm.trans eq)
        exact absent (idx j) (by dsimp [idx]; split <;> omega) (congrArg (fun z : A => z.val) hit)

end OMA

/- Extending a fixed embedding by leaves -/

namespace OMA
open SimpleGraph Finset

/-- If a fixed copy of the core does not extend to the deleted leaves, some
parent has fewer unused blue neighbors than the number of deleted leaves. -/
theorem long_leaf_obstruction {W V : Type} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (B : SimpleGraph V) [DecidableRel B.Adj] (P : Set W)
    [DecidablePred (· ∈ P)] [DecidablePred (· ∈ Pᶜ)] [DecidableEq V]
    (parent : (↥Pᶜ) → P)
    (leaves : ∀ z : ↥Pᶜ, ∀ w, H.Adj z.val w → w = (parent z).val)
    (f : (H.induce P).Copy B) (no : ¬H ⊑ B) :
    ∃ z : ↥Pᶜ, (((univ.map f.toEmbedding)ᶜ).filter (B.Adj (f (parent z)))).card <
      Fintype.card (↥Pᶜ) := by
  classical
  let S := (univ.map f.toEmbedding)ᶜ
  let T (z : ↥Pᶜ) := S.filter (B.Adj (f (parent z)))
  by_contra! all
  have hall : ∀ D : Finset (↥Pᶜ), D.card ≤ (D.biUnion T).card := by
    intro D
    by_cases empty : D = ∅
    · simp [empty]
    obtain ⟨z,hz⟩ := nonempty_iff_ne_empty.mpr empty
    have sub : T z ⊆ D.biUnion T := fun _ h => mem_biUnion.mpr ⟨z,hz,h⟩
    exact (card_le_univ D).trans ((all z).trans (card_le_card sub))
  obtain ⟨g,gi,gt⟩ := (all_card_le_biUnion_card_iff_existsInjective' T).mp hall
  let h : (H.induce Pᶜ).Copy B :=
    ⟨⟨g,fun {z w} e => False.elim (w.prop ((leaves z w.val e).symm ▸ (parent z).prop))⟩,gi⟩
  apply no (join_copies B H P f h ?_ ?_)
  · intro i j eq
    exact (mem_compl.mp (mem_filter.mp (gt j)).1) (mem_map.mpr ⟨i,mem_univ _,eq⟩)
  · intro i j e
    have eq : i = parent j := Subtype.ext (leaves j i.val e.symm)
    exact eq ▸ (mem_filter.mp (gt j)).2

/-- A clique covering the core, whose vertices see every other usable vertex
in blue, suffices to place all the leaves. -/
theorem long_embed_leaves_on_clique {W V : Type} [Fintype W] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) (B : SimpleGraph V) (P : Set W) [DecidablePred (· ∈ P)]
    (indep : ∀ i j : ↥Pᶜ, ¬H.Adj i.val j.val) (U S : Finset V) (sub : U ⊆ S)
    (blue : ∀ u ∈ U, ∀ s ∈ S, u ≠ s → B.Adj u s)
    (coreSize : Fintype.card P ≤ U.card) (size : Fintype.card W ≤ S.card) : H ⊑ B := by
  classical
  obtain ⟨f⟩ : Nonempty (P ↪ U) := Function.Embedding.nonempty_of_card_le (by simpa using coreSize)
  let F := f.trans (Function.Embedding.subtype _)
  let T := univ.map F
  have inS : T ⊆ S := by
    intro x hx
    obtain ⟨z,_,rfl⟩ := mem_map.mp hx
    exact sub (f z).prop
  have room : Fintype.card (↥Pᶜ) ≤ (S \ T).card := by
    rw [Fintype.card_compl_set,card_sdiff_of_subset inS]
    simpa [T] using Nat.sub_le_sub_right size (Fintype.card P)
  obtain ⟨g⟩ : Nonempty ((↥Pᶜ) ↪ (S \ T : Finset V)) := Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using room)
  let D := g.trans (Function.Embedding.subtype _)
  let left : (H.induce P).Copy B :=
    ⟨⟨F,fun {x y} e => blue _ (f x).prop _ (sub (f y).prop) (F.injective.ne e.ne)⟩,F.injective⟩
  let right : (H.induce Pᶜ).Copy B := ⟨⟨D,fun {i j} e => (indep i j e).elim⟩,D.injective⟩
  have apart (i : P) (j : ↥Pᶜ) : F i ≠ D j := fun h =>
    (mem_sdiff.mp (g j).prop).2 (mem_map.mpr ⟨i,mem_univ _,h⟩)
  exact join_copies B H P left right apart
    (fun i j _ => blue _ (f i).prop _ (mem_sdiff.mp (g j).prop).1 (apart i j))

/-- A path-free region has many distinct possible parents of failed leaf
extensions. Each such parent is red-adjacent to almost the whole opposite
region, and has at least N-n+1 red neighbors in the full host. -/
theorem long_leaf_centers {W V : Type} [Fintype W] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) [DecidableRel G.Adj] (P : Set W)
    [DecidablePred (· ∈ P)] [DecidablePred (· ∈ Pᶜ)]
    (parent : (↥Pᶜ) → P) (leaves : ∀ z : ↥Pᶜ, ∀ w, H.Adj z.val w → w = (parent z).val)
    (S : Finset V) (j R : ℕ) (free : ¬ pathGraph j ⊑ G.induce (S : Set V))
    (no : ¬H ⊑ Gᶜ) (space : R + graphRamsey (pathGraph j) (H.induce P) ≤ S.card) :
    R ≤ (S.filter (fun v => Fintype.card V + 1 - Fintype.card W ≤ G.degree v ∧
      (Sᶜ \ G.neighborFinset v).card < Fintype.card (↥Pᶜ))).card := by
  classical
  let T := S.filter (fun v => Fintype.card V + 1 - Fintype.card W ≤ G.degree v ∧
      (Sᶜ \ G.neighborFinset v).card < Fintype.card (↥Pᶜ))
  by_contra! small
  change T.card < R at small
  let D := S \ T
  have ds : D ⊆ S := sdiff_subset
  have room : graphRamsey (pathGraph j) (H.induce P) ≤ Fintype.card D := by
    rw [Fintype.card_coe]
    have := card_le_card_sdiff_add_card (s := S) (t := T)
    change S.card ≤ D.card+T.card at this
    omega
  let inc : (G.induce (D : Set V)).Copy (G.induce (S : Set V)) :=
    ⟨⟨fun v => ⟨v.val,ds v.prop⟩,fun e => e⟩,fun _ _ h => Subtype.ext (congrArg (fun z : S => z.val) h)⟩
  obtain ⟨f⟩ := (graphRamsey_host _ _ (G.induce (D : Set V)) room).resolve_left
    (fun p => free (p.trans ⟨inc⟩))
  let lift : ((G.induce (D : Set V))ᶜ).Copy Gᶜ :=
    ⟨⟨Subtype.val,fun {_ _} e => ⟨fun h => e.1 (Subtype.ext h),e.2⟩⟩,Subtype.val_injective⟩
  let g := lift.comp f
  obtain ⟨z,hz⟩ := long_leaf_obstruction H Gᶜ P parent leaves g no
  let v := g (parent z)
  let U := (univ.map g.toEmbedding)ᶜ
  let B := U.filter (Gᶜ.Adj v)
  change B.card < Fintype.card (↥Pᶜ) at hz
  have notin (u : V) (hu : u ∈ U) : u ≠ v := fun eq =>
    mem_compl.mp hu (mem_map.mpr ⟨parent z,mem_univ _,eq.symm⟩)
  have cover : U ⊆ G.neighborFinset v ∪ B := by
    intro u hu
    by_cases red : G.Adj v u
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr red)
    · exact mem_union_right _ (mem_filter.mpr ⟨hu,(notin _ hu).symm,red⟩)
  have outside : Sᶜ \ G.neighborFinset v ⊆ B := by
    intro w hw
    obtain ⟨ws,red⟩ := mem_sdiff.mp hw
    have wu : w ∈ U := by
      apply mem_compl.mpr
      rintro h
      obtain ⟨i,_,eq⟩ := mem_map.mp h
      exact mem_compl.mp ws (eq ▸ ds (f i).prop)
    exact mem_filter.mpr ⟨wu,(notin _ wu).symm,fun e => red ((G.mem_neighborFinset _ _).mpr e)⟩
  have cu : U.card = Fintype.card V - Fintype.card P := by
    simp only [U,card_compl,card_map,card_univ]
  have cnt := (card_le_card cover).trans (card_union_le ..)
  rw [cu,card_neighborFinset_eq_degree] at cnt
  have cp := Fintype.card_subtype_le (fun z => z ∈ P)
  have bigV := Fintype.card_le_of_injective _ g.injective
  have comp : Fintype.card (↥Pᶜ) = Fintype.card W - Fintype.card P := Fintype.card_compl_set _
  have high : Fintype.card V+1-Fintype.card W ≤ G.degree v := by omega
  have vd : v ∈ D := (f (parent z)).prop
  exact (mem_sdiff.mp vd).2 (mem_filter.mpr ⟨ds vd,high,(card_le_card outside).trans_lt hz⟩)

end OMA

/- Finishing the odd-cycle case when many leaves are available -/

namespace OMA
open SimpleGraph Finset

/-- A path-free red region embeds the core left by deleting a first batch
of leaves. A larger independent batch can then be placed around a blue clique. -/
theorem long_leaf_case {W V : Type} [Fintype W] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) [DecidableRel G.Adj]
    (P K : Set W) [DecidablePred (· ∈ P)] [DecidablePred (· ∈ Pᶜ)] [DecidablePred (· ∈ K)]
    (parent : (↥Pᶜ) → P) (leaves : ∀ z : ↥Pᶜ, ∀ w, H.Adj z.val w → w = (parent z).val)
    (indep : ∀ i j : ↥Kᶜ, ¬H.Adj i.val j.val)
    (S : Finset V) (l j : ℕ) (hl : 2 ≤ l) (free : ¬ pathGraph j ⊑ G.induce (S : Set V))
    (order : 2*Fintype.card W ≤ Fintype.card V + 1)
    (space : graphRamsey (cycleGraph (2*l+1)) (⊤ : SimpleGraph (Fin l)) +
      graphRamsey (pathGraph j) (H.induce P) ≤ S.card)
    (enough : l*Fintype.card (↥Pᶜ) + 2*l + 3 ≤ Sᶜ.card)
    (coreRoom : Fintype.card K + 2*Fintype.card (↥Pᶜ) ≤ Sᶜ.card) :
    cycleGraph (2*l+1) ⊑ G ∨ H ⊑ Gᶜ := by
  classical
  by_contra fail
  obtain ⟨nr,nb⟩ := not_or.mp fail
  let q := Fintype.card (↥Pᶜ)
  let T := Sᶜ
  let holes (v : V) := T \ G.neighborFinset v
  let D := S.filter fun v => Fintype.card V+1-Fintype.card W ≤ G.degree v ∧ (holes v).card < q
  have room := long_leaf_centers H G P parent leaves S j _ free nb space
  let J : SimpleGraph (Fin l) := ⊤
  obtain ⟨f⟩ := (graphRamsey_host (cycleGraph (2*l+1)) J (G.induce (D : Set V))
    (by rw [show Fintype.card (↥(D : Set V)) = D.card by simp]; exact room)).resolve_left
    (fun c => nr (c.trans ⟨Copy.induce G _⟩))
  let g := f.toEmbedding.trans (Function.Embedding.subtype _)
  let Z := univ.map g
  have zc : Z.card = l := by simp [Z]
  have ds : Z ⊆ D := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := mem_map.mp hz
    exact (f i).prop
  have prop (z : V) (hz : z ∈ Z) : Fintype.card V+1-Fintype.card W ≤ G.degree z ∧ (holes z).card < q :=
    (mem_filter.mp (ds hz)).2
  have clique : Gᶜ.IsClique (Z : Set V) := by
    intro x hx y hy ne
    obtain ⟨i,_,rfl⟩ := mem_map.mp hx
    obtain ⟨j,_,rfl⟩ := mem_map.mp hy
    have e := f.toHom.map_rel' (show J.Adj i j from fun h => ne (congrArg _ h))
    exact ⟨ne,e.2⟩
  let Q := T \ Z.biUnion holes
  have qc : 2*l+3 ≤ Q.card := by
    have cnt := card_biUnion_le_card_mul Z holes q fun z hz => (prop z hz).2.le
    have rem := card_le_card_sdiff_add_card (s := T) (t := Z.biUnion holes)
    change T.card ≤ Q.card + _ at rem
    change l*q+2*l+3 ≤ T.card at enough
    rw [zc] at cnt
    omega
  have cross (z : V) (hz : z ∈ Z) (u : V) (hu : u ∈ Q) : G.Adj z u := by
    by_contra h
    exact (mem_sdiff.mp hu).2 (mem_biUnion.mpr ⟨z,hz,mem_sdiff.mpr ⟨(mem_sdiff.mp hu).1,
      fun e => h ((G.mem_neighborFinset _ _).mp e)⟩⟩)
  let a := g ⟨0,by omega⟩
  let b := g ⟨1,by omega⟩
  have az : a ∈ Z := mem_map.mpr ⟨_,mem_univ _,rfl⟩
  have bz : b ∈ Z := mem_map.mpr ⟨_,mem_univ _,rfl⟩
  have ne : a ≠ b := g.injective.ne (by simp)
  let E := T \ (holes a ∪ holes b)
  have ea {v : V} (hv : v ∈ E) : v ∈ G.neighborFinset a ∧ v ∈ G.neighborFinset b := by
    have := mem_sdiff.mp hv
    simp only [mem_union,not_or] at this
    constructor
    · by_contra h; exact this.2.1 (mem_sdiff.mpr ⟨this.1,h⟩)
    · by_contra h; exact this.2.2 (mem_sdiff.mpr ⟨this.1,h⟩)
  have ec : Fintype.card K ≤ E.card := by
    have h := card_le_card_sdiff_add_card (s := T) (t := holes a ∪ holes b)
    change T.card ≤ E.card+_ at h
    have := card_union_le (holes a) (holes b)
    have ha := (prop a az).2
    have hb := (prop b bz).2
    change Fintype.card K+2*q ≤ T.card at coreRoom
    omega
  apply nb (long_embed_leaves_on_clique H Gᶜ K indep E (G.neighborFinset a)
    (fun _ hv => (ea hv).1) ?_ ec ?_)
  · intro u hu v hv hne
    exact (long_odd_fan_edges G Z Q hl zc clique cross qc nr az bz ne
      ((G.mem_neighborFinset _ _).mp hv) ((G.mem_neighborFinset _ _).mp (ea hu).2) hne.symm).symm
  · rw [card_neighborFinset_eq_degree]
    have := (prop a az).1
    omega

end OMA

/- Numerical slack for the sparse odd-cycle induction -/

namespace OMA

theorem long_leaf_arithmetic {n m R k : ℕ} (hk : 5 ≤ k)
    (large : (4*(1000*(k+1)^2)*(R+k+1))^2 + 3 ≤ n)
    (thin : 18*k^2*m ≤ (18*k^2+1)*n) :
    let q := R+k*(2*m).sqrt+1
    (2*q+1 ≤ n) ∧ (k*q+2*k+4 ≤ n) ∧
    (∀ L : ℕ, n + (6*k+2)*(6*n) ≤ (6*k+2)*(6*m+4*L+2) → 2*q+1 ≤ L) := by
  let C := 1000*(k+1)^2
  change (4*C*(R+k+1))^2+3 ≤ n at large
  let d := (2*m).sqrt
  let q := R+k*d+1
  have np : 0 < n := by omega
  have kpos : 0 < 18*k^2 := by positivity
  have mn : m ≤ 2*n := by
    by_contra! h
    have hi := Nat.mul_lt_mul_of_pos_left h kpos
    have lo := Nat.mul_le_mul_right n (by omega : 1 ≤ 18*k^2)
    nlinarith only [thin,hi,lo]
  have ds : d^2 ≤ 4*n := (Nat.sqrt_le' _).trans (by omega)
  have Q : C*q ≤ n := by
    have q' : q ≤ (R+k+1)*(d+1) := by dsimp only [q]; nlinarith
    have delta : (d+1)^2 ≤ 16*n := by nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) d]
    have mag : (4*C*(R+k+1))^2 ≤ n := by omega
    have square : (C*q)^2 ≤ n^2 := calc
      _ ≤ (C*((R+k+1)*(d+1)))^2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ q') _
      _ = (C*(R+k+1))^2*(d+1)^2 := by ring
      _ ≤ (C*(R+k+1))^2*(16*n) := Nat.mul_le_mul_left _ delta
      _ = (4*C*(R+k+1))^2*n := by ring
      _ ≤ _ := by simpa [pow_two] using Nat.mul_le_mul_right n mag
    exact le_of_not_gt fun h => (Nat.pow_lt_pow_left h (by decide : 2 ≠ 0)).not_ge square
  have qp : 1 ≤ q := by dsimp [q]; omega
  have c₁ : 200*(k+1) ≤ C := by dsimp only [C]; nlinarith
  have limit := (Nat.mul_le_mul_right q c₁).trans Q
  have kp := Nat.mul_le_mul_left k qp
  change 2*q+1 ≤ n ∧ k*q+2*k+4 ≤ n ∧ _
  refine ⟨by nlinarith only [limit,kp,qp],by nlinarith only [limit,kp,qp],?_⟩
  intro L cover
  change 2*q+1 ≤ L
  by_contra! few
  let t := m-n
  have tbound : 18*k^2*t ≤ n := by
    dsimp only [t]; rw [Nat.mul_sub]
    rw [Nat.add_mul,one_mul] at thin
    omega
  have rate : 12*(6*k+2) ≤ 18*k^2 := by nlinarith [Nat.mul_le_mul_right k hk]
  have slack := (Nat.mul_le_mul_right t rate).trans tbound
  have mt : m ≤ n+t := by dsimp only [t]; omega
  have less : 2*(6*k+2)*(4*L+2) < n := by
    have le := Nat.mul_le_mul_left (2*(6*k+2)) (by omega : 4*L+2 ≤ 8*q+2)
    nlinarith only [le,limit,kp,qp,show 0 < k*q by positivity]
  have grow := Nat.mul_le_mul_left (12*(6*k+2)) mt
  nlinarith only [cover,slack,less,grow]

end OMA

/- The inductive step for odd sparse connected targets -/

namespace OMA
open SimpleGraph Finset

private theorem leaves_independent {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected) (size : 3 ≤ Fintype.card W) {a b : W}
    (ha : H.degree a = 1) (hb : H.degree b = 1) : ¬ H.Adj a b := by
  classical
  intro ab
  have closed {u v : W} (h : H.Adj u v) (uIn : u = a ∨ u = b) : v = a ∨ v = b := by
    rcases uIn with rfl | rfl
    · exact Or.inr ((degree_eq_one_iff_existsUnique_adj.mp ha).unique h ab)
    · exact Or.inl ((degree_eq_one_iff_existsUnique_adj.mp hb).unique h ab.symm)
  have walk {u v : W} (p : H.Walk u v) : u = a ∨ u = b → v = a ∨ v = b := by
    induction p with
    | nil => exact id
    | cons e _ ih => exact fun h => ih (closed e h)
  have all : univ ⊆ ({a,b} : Finset W) := by
    intro x _
    have := walk (conn.preconnected a x).some (Or.inl rfl)
    simpa only [mem_insert,mem_singleton] using this
  have := card_le_card all
  simp [ab.ne] at this
  omega

/-- The sparse step only needs connected targets of order one less. -/
theorem long_odd_connected_step (l : ℕ) (hl : 2 ≤ l) :
    ∃ n₀, ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
      (V : Type) [Fintype V] (G : SimpleGraph V), H.Connected → n₀ ≤ Fintype.card W →
      18*(2*l+1)^2*H.edgeSet.ncard ≤ (18*(2*l+1)^2+1)*Fintype.card W →
      2*Fintype.card W-1 ≤ Fintype.card V →
      (∀ (U : Type) [Fintype U] (J : SimpleGraph U) [DecidableRel J.Adj],
        Fintype.card U = Fintype.card W-1 → J.Connected → J.edgeSet.ncard < H.edgeSet.ncard → J ⊑ Gᶜ) →
      cycleGraph (2*l+1) ⊑ G ∨ H ⊑ Gᶜ := by
  classical
  let k := 2*l+1
  let R := graphRamsey (cycleGraph k) (⊤ : SimpleGraph (Fin l))
  let n₀ := (4*(1000*(k+1)^2)*(R+k+1))^2+3
  refine ⟨n₀,fun W _ H _ V _ G conn large thin space ih => ?_⟩
  let n := Fintype.card W
  let m := H.edgeSet.ncard
  let q := R+k*(2*m).sqrt+1
  let L := univ.filter (fun w => H.degree w = 1)
  have hk : 5 ≤ k := by dsimp [k]; omega
  have nbig : 3 ≤ n := by dsimp only [n₀] at large; change _ ≤ n at large; omega
  have pos (w : W) : 0 < H.degree w := by
    have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by change 1 < n; omega)
    exact (H.degree_pos_iff_exists_adj _).mpr (conn.preconnected.exists_adj_of_nontrivial w)
  obtain ⟨num,farRoom,dich⟩ := long_leaf_arithmetic (n := n) (m := m) (R := R) hk large thin
  change 2*q+1 ≤ n at num
  change k*q+2*k+4 ≤ n at farRoom
  rcases long_leaves_or_thread H conn pos (6*k+1) with path | count
  · exact long_suspended_case H G hl conn path space ih
  have many : 2*q+1 ≤ L.card := dich _ count
  obtain ⟨F,hF,cardF⟩ := exists_subset_card_eq many
  obtain ⟨E,hE,cardE⟩ := exists_subset_card_eq (s := F) (show q ≤ F.card by omega)
  let P := (E : Set W)ᶜ
  let K := (F : Set W)ᶜ
  have degF {w : W} (hw : w ∈ F) : H.degree w = 1 := (mem_filter.mp (hF hw)).2
  have indep {u v : W} (hu : u ∈ F) (hv : v ∈ F) := leaves_independent H conn nbig (degF hu) (degF hv)
  have leaf (z : ↥Pᶜ) : z.val ∈ E := by simpa [P] using z.prop
  have parents (z : ↥Pᶜ) : ∃ u : P, ∀ w, H.Adj z.val w → w = u.val := by
    obtain ⟨w,e,only⟩ := degree_eq_one_iff_existsUnique_adj.mp (degF (hE (leaf z)))
    exact ⟨⟨w,fun h => indep (hE (leaf z)) (hE h) e⟩,only⟩
  choose parent leaves using parents
  have cp : Fintype.card P = n-q := by dsimp only [P]; rw [Fintype.card_compl_set]; simp [cardE,n]
  have cq : Fintype.card (↥Pᶜ) = q := by simp [P,cardE]
  have ck : Fintype.card K = n-(2*q+1) := by dsimp only [K]; rw [Fintype.card_compl_set]; simp [cardF,n]
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < F.card by omega)
  have dx := degF hx
  let A : Set W := {x}ᶜ
  let J := H.induce A
  have ja : Fintype.card A = n-1 := by dsimp only [A]; rw [Fintype.card_compl_set]; simp [n]
  have je : J.edgeSet.ncard = m-1 := by
    dsimp only [m]; rw [Set.ncard_eq_toFinset_card',Set.ncard_eq_toFinset_card']
    change (H.induce ({x}ᶜ : Set W)).edgeFinset.card = H.edgeFinset.card-1
    rw [H.card_edgeFinset_induce_compl_singleton,H.card_edgeFinset_deleteIncidenceSet,dx]
  have mp : 0 < m := by
    rw [show m = H.edgeFinset.card by rw [show m = H.edgeSet.ncard by rfl,Set.ncard_eq_toFinset_card']; rfl]
    exact (pos x).trans_le (H.degree_le_card_edgeFinset x)
  have Vsize : 2*n-1 ≤ Fintype.card V := space
  have smaller := ih _ J ja (conn.induce_compl_singleton_of_degree_eq_one dx) (by change J.edgeSet.ncard < m; omega)
  by_cases cyc : cycleGraph k ⊑ G
  · exact Or.inl cyc
  by_cases blue : H ⊑ Gᶜ
  · exact Or.inr blue
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v,hi⟩ := long_degree_witness G H x smaller.some blue
  rw [dx,one_mul] at hi
  obtain ⟨S,subS,sz⟩ := exists_subset_card_eq (s := G.neighborFinset v) (show n ≤ _ by
    rw [card_neighborFinset_eq_degree]; change Fintype.card V+1-n ≤ G.degree v at hi; omega)
  have noPath : ¬ pathGraph (k-1) ⊑ G.induce (S : Set V) := by
    intro h
    let lift : (G.induce (S : Set V)).Copy (G.induce (G.neighborSet v)) :=
      ⟨⟨fun z => ⟨z.val,(G.mem_neighborFinset _ _).mp (subS z.prop)⟩,fun e => e⟩,
        fun _ _ eq => Subtype.ext (congrArg (fun w : G.neighborSet v => w.val) eq)⟩
    exact cyc (cycle_of_neighborhood_path G v k (by omega) (h.trans ⟨lift⟩))
  have ph : (H.induce P).edgeSet.ncard ≤ m := by
    simpa only [m,Set.ncard_eq_toFinset_card',Set.toFinset_card] using
      Fintype.card_le_of_embedding (Copy.induce H P).mapEdgeSet
  have pathCost := (path_ramsey_edges (H.induce P) (k-1)).trans
    (Nat.add_le_add_left (Nat.mul_le_mul (by omega : k-1 ≤ k) (Nat.sqrt_le_sqrt (Nat.mul_le_mul_left 2 ph))) _)
  apply long_leaf_case H G P K parent leaves (fun i j => indep
    (by simpa [K] using i.prop) (by simpa [K] using j.prop)) S l (k-1) hl noPath (by omega)
  · change R + _ ≤ S.card
    rw [cp] at pathCost
    dsimp only [q] at num
    dsimp only [q] at pathCost
    omega
  · rw [cq,card_compl,sz]
    have le := Nat.mul_le_mul_right q (by dsimp only [k]; omega : l ≤ k)
    dsimp only [k] at farRoom le
    omega
  · rw [card_compl,sz,ck,cq]; omega

theorem long_odd_sparse_step (l : ℕ) (hl : 2 ≤ l) : LongSparseStep (2*l+1) := by
  obtain ⟨n₀,h⟩ := long_odd_connected_step l hl
  refine ⟨n₀,fun W _ H _ V _ G conn large thin space ih => ?_⟩
  apply h W H V G conn large _ space (fun U _ J _ card _ e => ih _ J (by omega) e)
  let c := 18*(2*l+1)^2
  rw [show 36*(2*l+1)^2 = 2*c by dsimp [c]; ring] at thin
  change c*H.edgeSet.ncard ≤ (c+1)*Fintype.card W
  simp only [Nat.add_mul,Nat.mul_assoc,one_mul] at thin ⊢
  omega

end OMA

/- Long cycles in the large-order reduction -/

namespace OMA

/-- The sparse connected bound for odd cycles implies the large-order bound. -/
theorem long_cycles_bound_of_odd_sparse
    (sparse : ∀ k ≥ 5, Odd k → LongSparseBound k) : ∀ k ≥ 5, LargeOrderBound k := by
  intro k hk
  rcases Nat.even_or_odd k with ⟨l,eq⟩ | odd
  · have h : k = 2*l := by omega
    exact h ▸ long_even_bound l (by omega)
  · exact long_bound_of_sparse k hk (sparse k hk odd)

/-- The large-order branch for every cycle of length at least five. -/
theorem long_cycles_bound : ∀ k ≥ 5, LargeOrderBound k := by
  intro k hk
  rcases Nat.even_or_odd k with ⟨l,eq⟩ | ⟨l,eq⟩
  · have e : k = 2*l := by omega
    exact e ▸ long_even_bound l (by omega)
  · have e : k = 2*l+1 := by omega
    exact e ▸ long_bound_of_sparse_step (2*l+1) (by omega) (long_odd_sparse_step l (by omega))

end OMA

open OMA SimpleGraph Filter in
theorem OMA.solution : type_of% @Erdos570.erdos_570 := by
  intro k hk
  by_cases h3 : k = 3
  · subst k
    filter_upwards [triangle_forces] with m hm
    exact fun _ _ H _ hn he => bound_of_forces hm H hn he
  by_cases h4 : k = 4
  · subst k
    filter_upwards [square_forces] with m hm
    exact fun _ _ H _ hn he => bound_of_forces hm H hn he
  have h : 5 ≤ k := by omega
  obtain ⟨M, largeOrder⟩ := long_cycles_bound k h
  filter_upwards [eventually_ge_atTop M, eventually_ge_atTop ((2*(4*k+4))^10)] with m hm hbig
  intro W _ H _ hn he
  by_cases small : (Fintype.card W)^5 ≤ m^3
  · exact (dense_target H h hbig small).trans (by omega)
  · exact largeOrder m hm W H hn he (lt_of_not_ge small)
