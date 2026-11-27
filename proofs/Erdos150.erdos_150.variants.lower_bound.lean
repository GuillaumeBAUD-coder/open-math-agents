import FormalConjectures.ErdosProblems.«150»

/-! Minimal cuts in parallel copies of the Gaspers–Mackenzie terminal-port graph. The port
sets are restricted so that every surviving path attaches to a terminal.
See https://www.lirmm.fr/~goncalves/sgt2018/uploads/Enum-15-06.pdf. -/

open Filter Finset SimpleGraph
open scoped Topology

namespace OMA.E150

private theorem cut_of_two_parts {V : Type} (G : SimpleGraph V) (T : Set V)
    (term : Bool → V) (hterm : ∀ b, term b ∉ T) (label : V → Bool)
    (hlab : ∀ b, label (term b) = b)
    (hsep : ∀ {x y}, G.Adj x y → x ∉ T → y ∉ T → label x = label y)
    (hconn : ∀ (x : V) (hx : x ∉ T), (G.induce Tᶜ).Reachable ⟨x,hx⟩
      ⟨term (label x),hterm _⟩)
    (htouch : ∀ x ∈ T, ∀ b, ∃ y ∉ T, label y = b ∧ G.Adj x y) :
    Erdos150.IsMinimalCut G T := by
  refine ⟨?_,?_⟩
  · intro h
    have sameLabel {x y : ↥(Tᶜ : Set V)} (w : (G.induce Tᶜ).Walk x y) :
        label x.1 = label y.1 := by
      induction w with
      | nil => rfl
      | @cons a b c hadj p ih => exact (hsep hadj a.2 b.2).trans ih
    obtain ⟨w⟩ := h ⟨term false,hterm false⟩ ⟨term true,hterm true⟩
    simpa [hlab] using sameLabel w
  · intro S hST
    obtain ⟨z,hzT,hzS⟩ := Set.exists_of_ssubset hST
    let termS (b : Bool) : ↥(Sᶜ : Set V) := ⟨term b,fun h => hterm b (hST.le h)⟩
    let g : G.induce Tᶜ →g G.induce Sᶜ :=
      (SimpleGraph.induceHomOfLE G (Set.compl_subset_compl.mpr hST.le)).toHom
    have connected_if_old (x : V) (hxT : x ∉ T) :
        (G.induce Sᶜ).Reachable ⟨x,fun h => hxT (hST.le h)⟩ (termS (label x)) :=
      (hconn x hxT).map g
    have connected_if_restored (x : V) (hxT : x ∈ T) (hxS : x ∉ S) (b : Bool) :
        (G.induce Sᶜ).Reachable ⟨x,hxS⟩ (termS b) := by
      obtain ⟨y,hy,hl,hxy⟩ := htouch x hxT b
      have hadj : (G.induce Sᶜ).Adj ⟨x,hxS⟩ ⟨y,fun h => hy (hST.le h)⟩ := hxy
      exact hadj.reachable.trans (hl ▸ connected_if_old y hy)
    have hb : (G.induce Sᶜ).Reachable (termS true) (termS false) :=
      (connected_if_restored z hzT hzS true).symm.trans
        (connected_if_restored z hzT hzS false)
    have all (x : ↥(Sᶜ : Set V)) : (G.induce Sᶜ).Reachable x (termS false) := by
      by_cases hx : x.1 ∈ T
      · exact connected_if_restored _ hx x.2 false
      · have hh := connected_if_old x.1 hx
        cases h : label x.1
        · simpa only [h] using hh
        · exact (show (G.induce Sᶜ).Reachable x (termS true) by simpa only [h] using hh).trans hb
    exact fun x y => (all x).trans (all y).symm

abbrev Row := {r : Finset (Fin 9) // r.card = 4}

abbrev Vertex (m : ℕ) := Bool ⊕ (Fin m × (Bool × Fin 9 ⊕ Row × Fin 3))

private def term {m : ℕ} (b : Bool) : Vertex m := Sum.inl b
private def port {m : ℕ} (c : Fin m) (b : Bool) (i : Fin 9) : Vertex m := Sum.inr (c,Sum.inl (b,i))
private def lane {m : ℕ} (c : Fin m) (r : Row) (i : Fin 3) : Vertex m := Sum.inr (c,Sum.inr (r,i))

private def endIndex (b : Bool) : Fin 3 := if b then 2 else 0

private theorem endIndex_order (b : Bool) (i : Fin 3) :
    (if b then i ≤ endIndex b else endIndex b ≤ i) := by
  cases b
  · simp [endIndex]
  · exact Fin.le_last i

private def forward {m : ℕ} : Vertex m → Vertex m → Prop
  | .inl b, .inr (_, .inl (d,_)) => b = d
  | .inr (c,.inl (b,j)), .inr (d,.inr (r,i)) => c = d ∧ j ∈ r.1 ∧ i = endIndex b
  | .inr (c,.inr (r,i)), .inr (d,.inr (s,j)) => c = d ∧ r = s ∧ i.val+1 = j.val
  | _, _ => False

private def graph (m : ℕ) : SimpleGraph (Vertex m) := SimpleGraph.fromRel forward

private theorem forward_irrefl {m : ℕ} (x : Vertex m) : ¬ forward x x := by
  rcases x with b | ⟨c,(⟨b,i⟩ | ⟨r,j⟩)⟩ <;> simp [forward]

private theorem forward_adj {m : ℕ} {x y : Vertex m} (h : forward x y) : (graph m).Adj x y := by
  refine ⟨fun e => forward_irrefl x (e ▸ h),Or.inl h⟩

private theorem term_port {m : ℕ} (c : Fin m) (b : Bool) (i : Fin 9) :
    (graph m).Adj (term b) (port c b i) :=
  forward_adj (by rfl)

private theorem port_lane {m : ℕ} (c : Fin m) (b : Bool) {i : Fin 9} {r : Row}
    (hi : i ∈ r.1) : (graph m).Adj (port c b i) (lane c r (endIndex b)) :=
  forward_adj ⟨rfl,hi,rfl⟩

private theorem lane_step {m : ℕ} (c : Fin m) (r : Row) {i j : Fin 3}
    (h : i.val+1 = j.val) : (graph m).Adj (lane c r i) (lane c r j) :=
  forward_adj ⟨rfl,rfl,h⟩

private def BothOpen (P Q : Finset (Fin 9)) (r : Row) : Prop := ¬ r.1 ⊆ P ∧ ¬ r.1 ⊆ Q

private instance (P Q : Finset (Fin 9)) (r : Row) : Decidable (BothOpen P Q r) := by
  unfold BothOpen
  infer_instance

private structure Pattern where
  left : Finset (Fin 9)
  right : Finset (Fin 9)
  leftSize : left.card = 0 ∨ left.card = 4 ∨ left.card = 5
  rightSize : right.card = 0 ∨ right.card = 4 ∨ right.card = 5
  hInter : (left ∩ right).card < 4
  cutAt : {r : Row // BothOpen left right r} → Fin 3

private def Pattern.ports (P : Pattern) (b : Bool) : Finset (Fin 9) :=
  if b then P.right else P.left

private theorem Pattern.someOpen (P : Pattern) (r : Row) (h : r.1 ⊆ P.left) : ¬ r.1 ⊆ P.right := by
  intro h'
  have hb := Finset.card_le_card (Finset.subset_inter h h')
  have hm := P.hInter
  have hc := r.2
  omega

private def isRemoved {m : ℕ} (F : Fin m → Pattern) : Vertex m → Prop
  | .inl _ => False
  | .inr (c,.inl (b,i)) => i ∈ (F c).ports b
  | .inr (c,.inr (r,i)) =>
    ∃ h : BothOpen (F c).left (F c).right r, i = (F c).cutAt ⟨r,h⟩

private def sideLabel {m : ℕ} (F : Fin m → Pattern) : Vertex m → Bool
  | .inl b => b
  | .inr (_,.inl (b,_)) => b
  | .inr (c,.inr (r,i)) =>
    if h : BothOpen (F c).left (F c).right r then
      decide ((F c).cutAt ⟨r,h⟩ < i)
    else decide (r.1 ⊆ (F c).left)

private theorem label_forward {m : ℕ} (F : Fin m → Pattern) {x y : Vertex m}
    (h : forward x y) (hx : ¬ isRemoved F x) (hy : ¬ isRemoved F y) :
    sideLabel F x = sideLabel F y := by
  rcases x with b | ⟨c,(⟨b,j⟩ | ⟨r,i⟩)⟩
  · rcases y with d | ⟨d,(⟨s,j⟩ | ⟨r,i⟩)⟩
    · contradiction
    · exact h
    · contradiction
  · rcases y with s | ⟨d,(⟨s,k⟩ | ⟨r,i⟩)⟩
    · contradiction
    · contradiction
    · obtain ⟨rfl,hjr,rfl⟩ := h
      have hj : j ∉ (F c).ports b := hx
      change b = sideLabel F (lane c r (endIndex b))
      cases b
      · have hl : ¬ r.1 ⊆ (F c).left := fun hsub => hj (hsub hjr)
        by_cases h : BothOpen (F c).left (F c).right r
        · simp [sideLabel,lane,endIndex,h]
        · simp [sideLabel,lane,endIndex,h,hl]
      · have hr : ¬ r.1 ⊆ (F c).right := fun hsub => hj (hsub hjr)
        by_cases h : BothOpen (F c).left (F c).right r
        · have he : (F c).cutAt ⟨r,h⟩ ≠ 2 :=
            fun e => hy ⟨h,e.symm⟩
          have ht : (F c).cutAt ⟨r,h⟩ < 2 := by omega
          simp [sideLabel,lane,endIndex,h,ht]
        · have ht : r.1 ⊆ (F c).left := by
            by_contra hnot
            exact h ⟨hnot,hr⟩
          simp [sideLabel,lane,endIndex,h,ht]
  · rcases y with b | ⟨d,(⟨b,k⟩ | ⟨s,j⟩)⟩
    · contradiction
    · contradiction
    · obtain ⟨rfl,rfl,hij⟩ := h
      by_cases h : BothOpen (F c).left (F c).right r
      · have hxi : i ≠ (F c).cutAt ⟨r,h⟩ := fun e => hx ⟨h,e⟩
        have hyj : j ≠ (F c).cutAt ⟨r,h⟩ := fun e => hy ⟨h,e⟩
        have he : ((F c).cutAt ⟨r,h⟩ < i) ↔ ((F c).cutAt ⟨r,h⟩ < j) := by omega
        simp [sideLabel,h,he]
      · simp [sideLabel,h]

private def cutSet {m : ℕ} (F : Fin m → Pattern) : Set (Vertex m) := {x | isRemoved F x}

private theorem follow_edge {m : ℕ} (F : Fin m → Pattern) {x y : Vertex m}
    (hx : x ∉ cutSet F) (hy : y ∉ cutSet F) (h : (graph m).Adj x y) :
    ((graph m).induce (cutSet F)ᶜ).Reachable ⟨x,hx⟩ ⟨y,hy⟩ :=
  (show ((graph m).induce (cutSet F)ᶜ).Adj ⟨x,hx⟩ ⟨y,hy⟩ from h).reachable

private theorem intact_lane_port {m : ℕ} (F : Fin m → Pattern) (c : Fin m)
    (r : Row) (b : Bool) (h : ¬ r.1 ⊆ (F c).ports b) :
    ∃ j : Fin 9, j ∈ r.1 ∧ port c b j ∉ cutSet F := by
  simp only [Finset.subset_iff, not_forall] at h
  obtain ⟨j,hj,hj'⟩ := h
  exact ⟨j,hj,hj'⟩

private theorem lane_to_end {m : ℕ} (F : Fin m → Pattern) (c : Fin m)
    (r : Row) (b : Bool) (i : Fin 3)
    (h : ∀ j : Fin 3, (if b then i ≤ j else j ≤ i) → lane c r j ∉ cutSet F) :
    ((graph m).induce (cutSet F)ᶜ).Reachable ⟨lane c r i,h i (by cases b <;> simp)⟩
      ⟨lane c r (endIndex b),h _ (endIndex_order b i)⟩ := by
  have s01 (h0 : lane c r 0 ∉ cutSet F) (h1 : lane c r 1 ∉ cutSet F) :
      ((graph m).induce (cutSet F)ᶜ).Reachable ⟨lane c r 0,h0⟩ ⟨lane c r 1,h1⟩ :=
    follow_edge F h0 h1 (lane_step c r rfl)
  have s12 (h1 : lane c r 1 ∉ cutSet F) (h2 : lane c r 2 ∉ cutSet F) :
      ((graph m).induce (cutSet F)ᶜ).Reachable ⟨lane c r 1,h1⟩ ⟨lane c r 2,h2⟩ :=
    follow_edge F h1 h2 (lane_step c r rfl)
  cases b <;> fin_cases i
  · exact Reachable.rfl
  · exact (s01 (h 0 (by decide)) (h 1 (by decide))).symm
  · exact ((s01 (h 0 (by decide)) (h 1 (by decide))).trans (s12 (h 1 (by decide)) (h 2 (by decide)))).symm
  · exact (s01 (h 0 (by decide)) (h 1 (by decide))).trans (s12 (h 1 (by decide)) (h 2 (by decide)))
  · exact s12 (h 1 (by decide)) (h 2 (by decide))
  · exact Reachable.rfl

private theorem survivor_reaches {m : ℕ} (F : Fin m → Pattern) (x : Vertex m)
    (hx : x ∉ cutSet F) :
    ((graph m).induce (cutSet F)ᶜ).Reachable ⟨x,hx⟩
      ⟨term (sideLabel F x),by simp [term,cutSet,isRemoved]⟩ := by
  rcases x with b | ⟨c,(⟨b,j⟩ | ⟨r,i⟩)⟩
  · exact Reachable.rfl
  · exact follow_edge F hx (by simp [term,cutSet,isRemoved]) (term_port c b j).symm
  · let b := sideLabel F (lane c r i)
    change ((graph m).induce (cutSet F)ᶜ).Reachable ⟨lane c r i,hx⟩ ⟨term b,?_⟩
    have hsafe : ¬ r.1 ⊆ (F c).ports b ∧
        ∀ j : Fin 3, (if b then i ≤ j else j ≤ i) → lane c r j ∉ cutSet F := by
      by_cases h : BothOpen (F c).left (F c).right r
      · have hne : i ≠ (F c).cutAt ⟨r,h⟩ := fun e => hx ⟨h,e⟩
        by_cases hi : (F c).cutAt ⟨r,h⟩ < i
        · have hb : b = true := by simp [b,sideLabel,lane,h,hi]
          rw [hb]
          refine ⟨h.2,?_⟩
          intro j hj ⟨h',he⟩
          change i ≤ j at hj
          omega
        · have hb : b = false := by simp [b,sideLabel,lane,h,hi]
          rw [hb]
          refine ⟨h.1,?_⟩
          intro j hj ⟨h',he⟩
          change j ≤ i at hj
          omega
      · have hs (j : Fin 3) : lane c r j ∉ cutSet F := fun h' => h h'.1
        by_cases hl : r.1 ⊆ (F c).left
        · have hb : b = true := by simp [b,sideLabel,lane,h,hl]
          rw [hb]
          exact ⟨(F c).someOpen r hl,fun j _ => hs j⟩
        · have hb : b = false := by simp [b,sideLabel,lane,h,hl]
          rw [hb]
          exact ⟨hl,fun j _ => hs j⟩
    obtain ⟨j,hjr,hj⟩ := intact_lane_port F c r b hsafe.1
    let hEnd : lane c r (endIndex b) ∉ cutSet F :=
      hsafe.2 _ (endIndex_order b i)
    refine (lane_to_end F c r b i hsafe.2).trans ?_
    exact (follow_edge F hEnd hj (port_lane c b hjr).symm).trans
      (follow_edge F hj (by simp [term,cutSet,isRemoved]) (term_port c b j).symm)

private theorem cut_port_touches_other {m : ℕ} (F : Fin m → Pattern) (c : Fin m)
    (b : Bool) (j : Fin 9) (hj : j ∈ (F c).ports b) :
    ∃ y ∉ cutSet F, sideLabel F y = !b ∧ (graph m).Adj (port c b j) y := by
  have hsize : 4 ≤ ((F c).ports b).card := by
    have hpos := Finset.card_pos.mpr ⟨j,hj⟩
    cases b
    · change 0 < (F c).left.card at hpos
      change 4 ≤ (F c).left.card
      have h := (F c).leftSize
      omega
    · change 0 < (F c).right.card at hpos
      change 4 ≤ (F c).right.card
      have h := (F c).rightSize
      omega
  have hsmall : 3 ≤ (((F c).ports b).erase j).card := by rw [Finset.card_erase_of_mem hj]; omega
  obtain ⟨R,hR,hcard⟩ := Finset.exists_subset_card_eq hsmall
  have hjR : j ∉ R := fun h => (Finset.mem_erase.mp (hR h)).1 rfl
  let r : Row := ⟨insert j R, by rw [Finset.card_insert_of_notMem hjR,hcard]⟩
  have hsub : r.1 ⊆ (F c).ports b :=
    Finset.insert_subset hj (hR.trans (Finset.erase_subset _ _))
  have hadj := port_lane (r:=r) c b (Finset.mem_insert_self j R)
  refine ⟨lane c r (endIndex b),?_,?_,hadj⟩
  · rintro ⟨h,_⟩
    exact (by cases b <;> first | exact h.1 hsub | exact h.2 hsub : False)
  · cases b
    · change r.1 ⊆ (F c).left at hsub
      have hn : ¬ BothOpen (F c).left (F c).right r := fun h => h.1 hsub
      simp [sideLabel,lane,hn,hsub]
    · change r.1 ⊆ (F c).right at hsub
      have hn : ¬ BothOpen (F c).left (F c).right r := fun h => h.2 hsub
      have hl : ¬ r.1 ⊆ (F c).left := fun h => (F c).someOpen r h hsub
      simp [sideLabel,lane,hn,hl]

private theorem cut_lane_touches {m : ℕ} (F : Fin m → Pattern) (c : Fin m) (r : Row)
    (h : BothOpen (F c).left (F c).right r) (b : Bool) :
    ∃ y ∉ cutSet F, sideLabel F y = b ∧ (graph m).Adj
      (lane c r ((F c).cutAt ⟨r,h⟩)) y := by
  let i := (F c).cutAt ⟨r,h⟩
  have portCase (hi : i = endIndex b) :
      ∃ y ∉ cutSet F, sideLabel F y = b ∧ (graph m).Adj (lane c r i) y := by
    have hb : ¬ r.1 ⊆ (F c).ports b := by cases b <;> first | exact h.1 | exact h.2
    obtain ⟨j,hjr,hj⟩ := intact_lane_port F c r b hb
    exact ⟨port c b j,hj,rfl,hi.symm ▸ (port_lane c b hjr).symm⟩
  by_cases hi : i = endIndex b
  · exact portCase hi
  have hleft {j : Fin 3} (hj : j < i) :
      lane c r j ∉ cutSet F ∧ sideLabel F (lane c r j) = false := by
    refine ⟨?_,?_⟩
    · rintro ⟨h',hej⟩
      exact hj.ne hej
    · simp [sideLabel,lane,h,not_lt_of_ge hj.le,i]
  have hright {j : Fin 3} (hj : i < j) :
      lane c r j ∉ cutSet F ∧ sideLabel F (lane c r j) = true := by
    refine ⟨?_,?_⟩
    · rintro ⟨h',hej⟩
      exact hj.ne hej.symm
    · simpa [sideLabel,lane,h,i] using hj
  cases b
  · have hi' : i ≠ 0 := hi
    let j : Fin 3 := ⟨i.val-1, by omega⟩
    have hj : j < i := by
      have : i.val ≠ 0 := fun he => hi' (Fin.ext he)
      change i.val-1 < i.val
      omega
    have he : j.val+1 = i.val := by
      have : i.val ≠ 0 := fun he => hi' (Fin.ext he)
      change i.val-1+1 = i.val
      omega
    exact ⟨lane c r j,(hleft hj).1,(hleft hj).2,(lane_step c r he).symm⟩
  · have hi' : i ≠ 2 := hi
    let j : Fin 3 := ⟨i.val+1, by
      have : i.val ≠ 2 := fun he => hi' (Fin.ext he)
      omega⟩
    have hj : i < j := by change i.val < i.val+1; omega
    exact ⟨lane c r j,(hright hj).1,(hright hj).2,lane_step c r rfl⟩

private theorem graph_cut {m : ℕ} (F : Fin m → Pattern) :
    Erdos150.IsMinimalCut (graph m) (cutSet F) := by
  refine cut_of_two_parts (graph m) (cutSet F) term (by simp [term,cutSet,isRemoved]) (sideLabel F)
    (by intro; rfl) ?_ (survivor_reaches F) ?_
  · intro x y h hx hy
    rcases h.2 with h' | h'
    · exact label_forward F h' hx hy
    · exact (label_forward F h' hy hx).symm
  · rintro (b | ⟨c,(⟨b,j⟩ | ⟨r,i⟩)⟩) hx d
    · contradiction
    · by_cases hd : d = b
      · subst d
        exact ⟨term b,by simp [term,cutSet,isRemoved],rfl,(term_port c b j).symm⟩
      · have he : d = !b := by cases d <;> cases b <;> simp_all
        subst d
        exact cut_port_touches_other F c b j hx
    · obtain ⟨h,rfl⟩ := hx
      exact cut_lane_touches F c r h d

private abbrev PortsOfSize (k : ℕ) := ↥((univ : Finset (Fin 9)).powersetCard k)

private theorem size_of_ports {k : ℕ} (P : PortsOfSize k) : P.1.card = k :=
  (Finset.mem_powersetCard.mp P.2).2

private theorem card_ports (k : ℕ) : Fintype.card (PortsOfSize k) = Nat.choose 9 k := by
  simp [PortsOfSize]

private def sizes (i : Fin 3) : ℕ := ![0,4,5] i

private theorem sizes_allowed (i : Fin 3) : sizes i = 0 ∨ sizes i = 4 ∨ sizes i = 5 := by
  fin_cases i <;> decide

private theorem sizes_inj : Function.Injective sizes := by
  decide +kernel

private abbrev ValidRight (P : Finset (Fin 9)) (q : ℕ) :=
  {Q : PortsOfSize q // (P ∩ Q.1).card < 4}

private def canonicalPorts (p : ℕ) : Finset (Fin 9) := univ.filter (fun i => i.val < p)

private theorem canonical_card (i : Fin 3) : (canonicalPorts (sizes i)).card = sizes i := by
  fin_cases i <;> decide +kernel

private theorem exists_map_of_card_eq (P Q : Finset (Fin 9)) (h : P.card = Q.card) :
    ∃ e : Equiv.Perm (Fin 9), P.map e.toEmbedding = Q := by
  classical
  let s := Finset.equivOfCardEq h
  let f (i : Fin 9) : Fin 9 := if hi : i ∈ P then (s ⟨i,hi⟩).1 else 0
  have hinj : Set.InjOn f P := by
    intro i hi j hj h
    change i ∈ P at hi
    change j ∈ P at hj
    simp only [f,dif_pos hi,dif_pos hj] at h
    exact congrArg Subtype.val (s.injective (Subtype.ext h))
  obtain ⟨e,he⟩ := Finset.exists_equiv_extend_of_card_eq (t := (univ : Finset (Fin 9)))
    (by simp) (subset_univ (P.image f)) hinj
  let u : ↥(univ : Finset (Fin 9)) ≃ Fin 9 :=
    ⟨Subtype.val,fun x => ⟨x,mem_univ _⟩,fun x => Subtype.ext rfl,fun _ => rfl⟩
  let E := e.trans u
  refine ⟨E,Finset.eq_of_subset_of_card_le ?_ (by simp [h])⟩
  intro i hi
  obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
  change (e j).1 ∈ Q
  rw [he _ hj]
  simp [f,hj]

private noncomputable def relabelRight (P Q : Finset (Fin 9)) (q : ℕ)
    (e : Equiv.Perm (Fin 9)) (h : P.map e.toEmbedding = Q) :
    ValidRight P q ≃ ValidRight Q q := by
  have cardMap (X : Finset (Fin 9)) (f : Equiv.Perm (Fin 9)) (hX : X ∈ (univ : Finset (Fin 9)).powersetCard q) :
      X.map f.toEmbedding ∈ (univ : Finset (Fin 9)).powersetCard q :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,by simpa using (Finset.mem_powersetCard.mp hX).2⟩
  have eqMap (X : Finset (Fin 9)) (f : Equiv.Perm (Fin 9)) :
      (X.map f.toEmbedding).map f.symm.toEmbedding = X := by
    rw [Finset.map_map]
    have he : f.toEmbedding.trans f.symm.toEmbedding = Function.Embedding.refl _ := by
      apply Function.Embedding.ext
      intro x
      exact f.symm_apply_apply x
    rw [he,map_refl]
  have h' : Q.map e.symm.toEmbedding = P := by rw [← h,eqMap]
  have valid (f : Equiv.Perm (Fin 9)) (R S X : Finset (Fin 9)) (hRS : R.map f.toEmbedding = S)
      (hX : (R ∩ X).card < 4) : (S ∩ X.map f.toEmbedding).card < 4 := by
    rw [← hRS,← map_inter,card_map]
    exact hX
  refine ⟨fun T => ⟨⟨T.1.1.map e.toEmbedding,cardMap _ _ T.1.2⟩,valid _ _ _ _ h T.2⟩,
    fun T => ⟨⟨T.1.1.map e.symm.toEmbedding,cardMap _ _ T.1.2⟩,valid _ _ _ _ h' T.2⟩,?_,?_⟩
  · intro T
    exact Subtype.ext (Subtype.ext (eqMap _ e))
  · intro T
    exact Subtype.ext (Subtype.ext (eqMap _ e.symm))

private def rightCount (i j : Fin 3) : ℕ :=
  (![![1,126,126],![1,125,121],![1,121,105]] : Fin 3 → Fin 3 → ℕ) i j

private theorem card_right (i j : Fin 3) (P : PortsOfSize (sizes i)) :
    Fintype.card (ValidRight P.1 (sizes j)) = rightCount i j := by
  have h : P.1.card = (canonicalPorts (sizes i)).card :=
    (size_of_ports P).trans (canonical_card i).symm
  obtain ⟨e,he⟩ := exists_map_of_card_eq P.1 _ h
  rw [Fintype.card_congr (relabelRight _ _ _ e he)]
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem card_subsets_for (P : Finset (Fin 9)) :
    Fintype.card {r : Row // r.1 ⊆ P} = P.card.choose 4 := by
  let e : {r : Row // r.1 ⊆ P} ≃ ↥(P.powersetCard 4) :=
    ⟨fun r => ⟨r.1.1, Finset.mem_powersetCard.mpr ⟨r.2,r.1.2⟩⟩,
     fun r => ⟨⟨r.1,(Finset.mem_powersetCard.mp r.2).2⟩,(Finset.mem_powersetCard.mp r.2).1⟩,
     fun _ => rfl,fun _ => rfl⟩
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_powersetCard]

private theorem card_rows : Fintype.card Row = 126 := by
  let e : Row ≃ PortsOfSize 4 :=
    ⟨fun r => ⟨r.1,mem_powersetCard.mpr ⟨subset_univ _,r.2⟩⟩,
     fun r => ⟨r.1,size_of_ports r⟩,fun _ => rfl,fun _ => rfl⟩
  rw [Fintype.card_congr e,card_ports]
  decide

private theorem card_open (P Q : Finset (Fin 9)) (h : (P ∩ Q).card < 4) :
    Fintype.card {r : Row // BothOpen P Q r} = 126 - (P.card.choose 4 + Q.card.choose 4) := by
  let e := Equiv.subtypeEquivRight (fun r : Row =>
    show BothOpen P Q r ↔ ¬ (r.1 ⊆ P ∨ r.1 ⊆ Q) from not_or.symm)
  have hd : Disjoint (fun r : Row => r.1 ⊆ P) (fun r : Row => r.1 ⊆ Q) := by
    intro p hP hQ r hr
    have H := Finset.card_le_card (Finset.subset_inter (hP r hr) (hQ r hr))
    exact (by omega : False)
  rw [Fintype.card_congr e,Fintype.card_subtype_compl,card_rows,
    Fintype.card_subtype_or_disjoint _ _ hd,card_subsets_for,card_subsets_for]

private abbrev Data :=
  Σ i : Fin 3 × Fin 3, Σ P : PortsOfSize (sizes i.1),
    Σ Q : ValidRight P.1 (sizes i.2), {r : Row // BothOpen P.1 Q.1.1 r} → Fin 3

private def fromData (x : Data) : Pattern :=
  ⟨x.2.1.1,x.2.2.1.1.1,
    (size_of_ports x.2.1).symm ▸ sizes_allowed x.1.1,
    (size_of_ports x.2.2.1.1).symm ▸ sizes_allowed x.1.2,x.2.2.1.2,x.2.2.2⟩

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem card_data : Fintype.card Data =
    3^126 + 252 * 3^125 + 252 * 3^121 + 15750 * 3^124 +
      30492 * 3^120 + 13230 * 3^116 := by
  classical
  simp only [Data, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]
  have cardOpen (p q : ℕ) (P : PortsOfSize p) (Q : ValidRight P.1 q) :
      Fintype.card {r : Row // BothOpen P.1 Q.1.1 r} = 126-(p.choose 4+q.choose 4) := by
    rw [card_open _ _ Q.2,size_of_ports P,size_of_ports Q.1]
  simp_rw [cardOpen]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_right,card_ports]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three]
  decide +kernel

private theorem fromData_injective : Function.Injective fromData := by
  rintro ⟨⟨i,j⟩,⟨P,Q,f⟩⟩ ⟨⟨i',j'⟩,⟨P',Q',f'⟩⟩ h
  have hp : P.1 = P'.1 := congrArg Pattern.left h
  have hq : Q.1.1 = Q'.1.1 := congrArg Pattern.right h
  have hi : i = i' := sizes_inj
    ((size_of_ports P).symm.trans ((congrArg Finset.card hp).trans (size_of_ports P')))
  have hj : j = j' := sizes_inj
    ((size_of_ports Q.1).symm.trans ((congrArg Finset.card hq).trans (size_of_ports Q'.1)))
  subst i'
  subst j'
  have hP : P = P' := Subtype.ext hp
  subst P'
  have hQ : Q = Q' := Subtype.ext (Subtype.ext hq)
  subst Q'
  change Pattern.mk P.1 Q.1.1 _ _ _ f = Pattern.mk P.1 Q.1.1 _ _ _ f' at h
  cases h
  rfl

private theorem cutSet_injective (m : ℕ) : Function.Injective (cutSet (m := m)) := by
  intro F H h
  funext c
  have hmem (x : Vertex m) : x ∈ cutSet F ↔ x ∈ cutSet H := Set.ext_iff.mp h x
  have hP : (F c).left = (H c).left := by
    ext i
    exact hmem (port c false i)
  have hQ : (F c).right = (H c).right := by
    ext i
    exact hmem (port c true i)
  generalize hF : F c = p at hP hQ ⊢
  generalize hH : H c = q at hP hQ ⊢
  rcases p with ⟨P,Q,l,r,hi,f⟩
  rcases q with ⟨P',Q',l',r',hi',f'⟩
  change P = P' at hP
  change Q = Q' at hQ
  subst P'
  subst Q'
  suffices hf : f = f' by subst f'; rfl
  funext R
  rcases R with ⟨R,hR⟩
  have hh := hmem (lane c R (f ⟨R,hR⟩))
  let removed (p : Pattern) : Prop :=
    ∃ h : BothOpen p.left p.right R, f ⟨R,hR⟩ = p.cutAt ⟨R,h⟩
  change removed (F c) ↔ removed (H c) at hh
  rw [hF,hH] at hh
  obtain ⟨hX,hFX⟩ := hh.mp ⟨hR,rfl⟩
  exact hFX

private def relabelInduce {V W : Type} (G : SimpleGraph V) (e : W ≃ V) (S : Set V) :
    ((G.comap e).induce (e ⁻¹' S)ᶜ) ≃g G.induce Sᶜ :=
  ⟨e.subtypeEquiv (fun _ => Iff.rfl),by intros; rfl⟩

private theorem relabelCut {V W : Type} {G : SimpleGraph V} (e : W ≃ V) {T : Set V}
    (h : Erdos150.IsMinimalCut G T) :
    Erdos150.IsMinimalCut (G.comap e) (e ⁻¹' T) := by
  refine ⟨fun hconn => h.1 ((relabelInduce G e T).preconnected_iff.mp hconn),?_⟩
  intro S hST
  let T' := e '' S
  have hpre : e ⁻¹' T' = S := Set.preimage_image_eq _ e.injective
  have hss : T' ⊂ T := by
    refine lt_of_le_of_ne (Set.image_subset_iff.mpr hST.le) (fun h' => hST.ne ?_)
    rw [← h',hpre]
  rw [← hpre]
  exact (relabelInduce G e T').preconnected_iff.mpr (h.2 _ hss)

private theorem cut_count (m : ℕ) :
    (Fintype.card Data)^m ≤ Erdos150.maxMinimalCuts (396*m+2) := by
  classical
  let n := 396*m+2
  have hc : Fintype.card (Vertex m) = n := by
    simp [Vertex,Fintype.card_prod,n,show Nat.choose 9 4 = 126 by decide]
    omega
  let e : Fin n ≃ Vertex m := (Fintype.equivFinOfCardEq hc).symm
  let G := (graph m).comap e
  let family : Set (Set (Fin n)) := {T | Erdos150.IsMinimalCut G T}
  let f (F : Fin m → Data) : family :=
    ⟨e ⁻¹' cutSet (fun c => fromData (F c)), relabelCut e (graph_cut _)⟩
  have hinj : Function.Injective f := by
    intro F H h
    have heq : e ⁻¹' cutSet (fun c => fromData (F c)) =
        e ⁻¹' cutSet (fun c => fromData (H c)) := congrArg Subtype.val h
    have hset : cutSet (fun c => fromData (F c)) = cutSet (fun c => fromData (H c)) :=
      Set.preimage_injective.mpr e.surjective heq
    have hf := cutSet_injective m hset
    funext c
    exact fromData_injective (congrFun hf c)
  have hcount : (Fintype.card Data)^m ≤ family.ncard := by
    have hc := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_fun,Nat.card_fin,Nat.card_coe_set_eq,Nat.card_eq_fintype_card] at hc
    exact hc
  refine hcount.trans (le_csSup ?_ ⟨G,rfl⟩)
  refine ⟨Nat.card (Set (Fin n)),?_⟩
  rintro k ⟨H,rfl⟩
  exact Set.ncard_le_card _

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem base_lt : (1.4457 : ℝ) ^ (396 : ℕ) < (Fintype.card Data : ℝ) := by
  rw [card_data]
  rw [show (1.4457 : ℝ) = 14457/10000 by norm_num, div_pow,
    div_lt_iff₀ (by positivity : 0 < (10000 : ℝ)^(396 : ℕ))]
  exact_mod_cast (by decide +kernel : (14457 : ℕ)^396 <
    (3^126 + 252 * 3^125 + 252 * 3^121 + 15750 * 3^124 + 30492 * 3^120 + 13230 * 3^116) * 10000^396)

end OMA.E150

open OMA.E150

theorem OMA.solution : type_of% @Erdos150.erdos_150.variants.lower_bound := by
  intro α hα
  by_contra! hb
  let b : ℝ := 1.4457
  let c : ℝ := (Fintype.card Data : ℝ)
  have hbpos : 0 < b := by norm_num [b]
  have hratio : 1 < c / b^396 := (one_lt_div (by positivity)).mpr base_lt
  let n (m : ℕ) := 396*m+2
  have hn : Tendsto n atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun N => ⟨N,fun m hm => ?_⟩
    dsimp [n]
    omega
  have hnear := (hα.comp hn).eventually (Iio_mem_nhds hb)
  have hfar : ∀ᶠ m : ℕ in atTop, b^2 < (c / b^396)^m :=
    (tendsto_pow_atTop_atTop_of_one_lt hratio).eventually (eventually_gt_atTop (b^2))
  obtain ⟨m,hmNear,hmFar⟩ := (hnear.and hfar).exists
  change (Erdos150.maxMinimalCuts (n m) : ℝ) ^ (1 / (n m : ℝ)) < b at hmNear
  have hpow : (Erdos150.maxMinimalCuts (n m) : ℝ) < b^(n m) := by
    have hnonneg : 0 ≤ (Erdos150.maxMinimalCuts (n m) : ℝ) ^ (1 / (n m : ℝ)) := by positivity
    have hN : n m ≠ 0 := by dsimp [n]; omega
    have hh := pow_lt_pow_left₀ hmNear hnonneg hN
    rw [← Real.rpow_mul_natCast (by positivity),one_div_mul_cancel (by exact_mod_cast hN),
      Real.rpow_one] at hh
    exact hh
  have hcBound : c^m ≤ (Erdos150.maxMinimalCuts (n m) : ℝ) := by
    dsimp [c,n]
    exact_mod_cast cut_count m
  rw [div_pow,lt_div_iff₀ (by positivity : 0 < (b^396)^m)] at hmFar
  have hbBound : b^(n m) < c^m := by
    dsimp [n]
    rw [pow_add,pow_mul,mul_comm]
    exact hmFar
  exact (lt_irrefl _ ((hcBound.trans_lt hpow).trans hbBound))