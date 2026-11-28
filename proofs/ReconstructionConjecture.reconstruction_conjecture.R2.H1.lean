import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_R2

namespace OMA.DisconnRecon

open SimpleGraph Finset Classical

noncomputable section

section counting

variable {α β : Type} [Fintype α] [Fintype β] (A : SimpleGraph α) (B : SimpleGraph β)

def Q {V : Type} (X : SimpleGraph V) (p : Finset V × Finset V) : Prop :=
  Nonempty (X.induce (p.1 : Set V) ≃g A) ∧ Nonempty (X.induce (p.2 : Set V) ≃g B)

def pc {V : Type} [Fintype V] (X : SimpleGraph V) (m : ℕ) : ℕ :=
  #((univ.filter (fun p : Finset V × Finset V => Q A B X p)).filter
    (fun p => #(p.1 ∪ p.2) = m))

def cnt {V : Type} [Fintype V] (X : SimpleGraph V) {γ : Type} (C : SimpleGraph γ) : ℕ :=
  #(univ.filter (fun S : Finset V => Nonempty (X.induce (S : Set V) ≃g C)))

def indIso {X Y : Type} (K : SimpleGraph X) (L : SimpleGraph Y) (g : X ↪ Y)
    (hg : ∀ a b, L.Adj (g a) (g b) ↔ K.Adj a b) (S : Finset X) :
    K.induce (S : Set X) ≃g L.induce (S.map g : Set Y) where
  toEquiv := (Equiv.Set.image g (S : Set X) g.injective).trans
    (Equiv.setCongr (Finset.coe_map g S).symm)
  map_rel_iff' := fun {a b} => hg a b

theorem ind_iff {X Y : Type} (K : SimpleGraph X) (L : SimpleGraph Y) (g : X ↪ Y)
    (hg : ∀ a b, L.Adj (g a) (g b) ↔ K.Adj a b) (S : Finset X) {γ : Type}
    (C : SimpleGraph γ) :
    Nonempty (K.induce (S : Set X) ≃g C) ↔ Nonempty (L.induce (S.map g : Set Y) ≃g C) :=
  ⟨fun ⟨e⟩ => ⟨(indIso K L g hg S).symm.trans e⟩, fun ⟨e⟩ => ⟨(indIso K L g hg S).trans e⟩⟩

theorem transport {X Y : Type} (K : SimpleGraph X) (L : SimpleGraph Y) (g : X ↪ Y)
    (hg : ∀ a b, L.Adj (g a) (g b) ↔ K.Adj a b) (p : Finset X × Finset X) (m : ℕ) :
    (Q A B K p ∧ #(p.1 ∪ p.2) = m) ↔
      (Q A B L (p.1.map g, p.2.map g) ∧ #(p.1.map g ∪ p.2.map g) = m) := by
  unfold Q
  rw [ind_iff K L g hg p.1 A, ind_iff K L g hg p.2 B, ← Finset.map_union, Finset.card_map]

theorem pc_le {X Y : Type} [Fintype X] [Fintype Y] (K : SimpleGraph X) (L : SimpleGraph Y)
    (g : X ↪ Y) (hg : ∀ a b, L.Adj (g a) (g b) ↔ K.Adj a b) (m : ℕ) :
    pc A B K m ≤ pc A B L m := by
  unfold pc
  refine card_le_card_of_injOn (fun p => (p.1.map g, p.2.map g)) ?_ ?_
  · intro p hp
    rw [mem_coe] at hp ⊢
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact (transport A B K L g hg p m).mp hp
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Finset.map_injective g h.1) (Finset.map_injective g h.2)

theorem pc_iso {X Y : Type} [Fintype X] [Fintype Y] {K : SimpleGraph X} {L : SimpleGraph Y}
    (f : K ≃g L) (m : ℕ) : pc A B K m = pc A B L m :=
  le_antisymm (pc_le A B K L f.toEquiv.toEmbedding (fun a b => f.map_rel_iff) m)
    (pc_le A B L K f.symm.toEquiv.toEmbedding (fun a b => f.symm.map_rel_iff) m)

theorem restrict {V : Type} [Fintype V] (X : SimpleGraph V) (v : V) (m : ℕ) :
    pc A B (X.induce ({v}ᶜ : Set V)) m =
      #(((univ.filter (fun p : Finset V × Finset V => Q A B X p)).filter
        (fun p => #(p.1 ∪ p.2) = m)).filter (fun p => v ∉ p.1 ∪ p.2)) := by
  unfold pc
  let e : ({v}ᶜ : Set V) ↪ V := Function.Embedding.subtype _
  have hg : ∀ a b, X.Adj (e a) (e b) ↔ (X.induce ({v}ᶜ : Set V)).Adj a b := fun a b => Iff.rfl
  have hmem : ∀ q : Finset V × Finset V, v ∉ q.1 ∪ q.2 →
      ((q.1.subtype (· ∈ ({v}ᶜ : Set V))).map e, (q.2.subtype (· ∈ ({v}ᶜ : Set V))).map e) = q := by
    intro q hq
    rw [mem_union, not_or] at hq
    refine Prod.ext (subtype_map_of_mem ?_) (subtype_map_of_mem ?_)
    · intro x hx
      rintro rfl
      exact hq.1 hx
    · intro x hx
      rintro rfl
      exact hq.2 hx
  refine card_nbij' (fun p => (p.1.map e, p.2.map e))
    (fun q => (q.1.subtype (· ∈ ({v}ᶜ : Set V)), q.2.subtype (· ∈ ({v}ᶜ : Set V)))) ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_coe] at hp ⊢
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    refine ⟨(transport A B _ X e hg p m).mp hp, ?_⟩
    rw [mem_union, not_or]
    constructor <;>
    · intro h
      obtain ⟨x, _, hx⟩ := mem_map.mp h
      exact x.2 hx
  · intro q hq
    rw [mem_coe] at hq ⊢
    simp only [mem_filter, mem_univ, true_and] at hq ⊢
    have h3 := hmem q hq.2
    rw [Prod.ext_iff] at h3
    simp only at h3
    rw [transport A B _ X e hg _ m]
    simp only [h3.1, h3.2]
    exact hq.1
  · intro p _
    refine Prod.ext (Finset.map_injective e ?_) (Finset.map_injective e ?_)
    · exact subtype_map_of_mem (fun x hx => by
        obtain ⟨y, _, rfl⟩ := mem_map.mp hx
        exact y.2)
    · exact subtype_map_of_mem (fun x hx => by
        obtain ⟨y, _, rfl⟩ := mem_map.mp hx
        exact y.2)
  · intro q hq
    rw [mem_coe] at hq
    simp only [mem_filter, mem_univ, true_and] at hq
    exact hmem q hq.2

theorem kelly {V : Type} [Fintype V] (X : SimpleGraph V) (m : ℕ) :
    ∑ v, pc A B (X.induce ({v}ᶜ : Set V)) m = (Fintype.card V - m) * pc A B X m := by
  simp_rw [restrict, card_filter]
  rw [sum_comm]
  unfold pc
  rw [card_eq_sum_ones, mul_sum]
  refine sum_congr rfl (fun p hp => ?_)
  rw [mem_filter] at hp
  rw [sum_boole]
  have : (univ.filter (fun v => v ∉ p.1 ∪ p.2)) = (p.1 ∪ p.2)ᶜ := by
    ext x
    simp
  rw [this, card_compl, hp.2]
  simp

theorem total {V : Type} [Fintype V] (X : SimpleGraph V) :
    ∑ m ∈ range (Fintype.card V + 1), pc A B X m = cnt X A * cnt X B := by
  unfold pc cnt
  rw [← card_eq_sum_card_fiberwise (f := fun p : Finset V × Finset V => #(p.1 ∪ p.2))]
  · rw [← card_product, ← filter_product, univ_product_univ]
    congr 1
    ext x
    rw [mem_filter, mem_filter]
    simp only [Q, mem_univ, true_and]
  · intro p _
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (card_le_univ _)

theorem card_of_iso {V : Type} [Fintype V] (X : SimpleGraph V) (S : Finset V) {γ : Type}
    [Fintype γ] (C : SimpleGraph γ) (h : Nonempty (X.induce (S : Set V) ≃g C)) :
    #S = Fintype.card γ := by
  obtain ⟨e⟩ := h
  rw [← Fintype.card_congr e.toEquiv]
  simp

theorem pc_top {V : Type} [Fintype V] (X : SimpleGraph V)
    (h : Fintype.card α + Fintype.card β < Fintype.card V) :
    pc A B X (Fintype.card V) = 0 := by
  unfold pc
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p hp hc
  rw [mem_filter] at hp
  have h1 := card_of_iso X p.1 A hp.2.1
  have h2 := card_of_iso X p.2 B hp.2.2
  have := card_union_le p.1 p.2
  omega

end counting

def E : SimpleGraph Empty := ⊥

theorem cnt_E {V : Type} [Fintype V] (X : SimpleGraph V) : cnt X E = 1 := by
  unfold cnt
  rw [card_eq_one]
  refine ⟨∅, ?_⟩
  ext S
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨e⟩
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    exact (e ⟨x, hx⟩).elim
  · rintro rfl
    exact ⟨⟨⟨fun a => absurd a.2 (by simp), fun e => e.elim, fun a => absurd a.2 (by simp),
      fun e => e.elim⟩, fun {a} => absurd a.2 (by simp)⟩⟩

theorem deg_split {X : Type} [Fintype X] (K : SimpleGraph X) (S : Set X) (w : S) :
    (K.induce S).degree w + #(univ.filter (fun u => u ∉ S ∧ K.Adj w u)) = K.degree w := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have h1 : #((K.induce S).neighborFinset w) = #((K.neighborFinset w).filter (· ∈ S)) := by
    refine card_bij (fun a _ => a.val) ?_ ?_ ?_
    · intro a ha
      simp only [mem_neighborFinset, comap_adj, Function.Embedding.coe_subtype] at ha
      simp only [mem_filter, mem_neighborFinset]
      exact ⟨ha, a.2⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro b hb
      simp only [mem_filter, mem_neighborFinset] at hb
      refine ⟨⟨b, hb.2⟩, ?_, rfl⟩
      simp only [mem_neighborFinset, comap_adj, Function.Embedding.coe_subtype]
      exact hb.1
  have h2 : #(univ.filter (fun u => u ∉ S ∧ K.Adj w u)) =
      #((K.neighborFinset w).filter (fun u => ¬ (u ∈ S))) := by
    congr 1
    ext u
    simp [and_comm]
  rw [h1, h2, card_filter_add_card_filter_not]

end

end OMA.DisconnRecon

namespace OMA.DisconnRecon

open SimpleGraph Finset Classical OMA.R_ReconstructionConjecture_reconstruction_conjecture_R2

theorem keyeq {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (σ : V ≃ W) (hc : ∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    {α β : Type} [Fintype α] [Fintype β] (A : SimpleGraph α) (B : SimpleGraph β)
    (m : ℕ) (hm : m < Fintype.card V) : pc A B G m = pc A B H m := by
  have e1 := kelly A B G m
  have e2 := kelly A B H m
  have hW : Fintype.card W = Fintype.card V := (Fintype.card_congr σ).symm
  have e3 : ∑ v, pc A B (G.induce ({v}ᶜ : Set V)) m =
      ∑ v, pc A B (H.induce ({σ v}ᶜ : Set W)) m :=
    sum_congr rfl (fun v _ => by
      obtain ⟨f⟩ := hc v
      exact pc_iso A B f m)
  have e4 : ∑ v, pc A B (H.induce ({σ v}ᶜ : Set W)) m =
      ∑ w, pc A B (H.induce ({w}ᶜ : Set W)) m :=
    Equiv.sum_comp σ (fun w => pc A B (H.induce ({w}ᶜ : Set W)) m)
  rw [hW] at e2
  have : (Fintype.card V - m) * pc A B G m = (Fintype.card V - m) * pc A B H m := by
    rw [← e1, ← e2, e3, e4]
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

theorem cnteq {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (σ : V ≃ W) (hc : ∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    {γ : Type} [Fintype γ] (C : SimpleGraph γ) (h : Fintype.card γ < Fintype.card V) :
    cnt G C = cnt H C := by
  have hW : Fintype.card W = Fintype.card V := (Fintype.card_congr σ).symm
  have t1 := total C E G
  have t2 := total C E H
  rw [cnt_E, mul_one] at t1 t2
  rw [← t1, ← t2, sum_range_succ, sum_range_succ, pc_top C E G (by simp; omega),
    pc_top C E H (by simp; omega), hW]
  congr 1
  exact sum_congr rfl (fun m hm => keyeq G H σ hc C E m (mem_range.mp hm))

theorem sum_split {X : Type} [Fintype X] (S : Set X) (f : X → ℕ) :
    ∑ x, f x = ∑ x : S, f x + ∑ x : ↥Sᶜ, f x :=
  (Fintype.sum_subtype_add_sum_subtype (· ∈ S) f).symm

theorem glue {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (hcard : Fintype.card V = Fintype.card W) (C : Set V) (S : Set W)
    (noC : ∀ x y, x ∈ C → y ∉ C → ¬ G.Adj x y) (noH : ∀ x y, x ∈ S → y ∉ S → ¬ H.Adj x y)
    (α : G.induce C ≃g H.induce S) (β : G.induce Cᶜ ≃g H.induce Sᶜ) : Nonempty (G ≃g H) := by
  let f : V → W := fun x => if hx : x ∈ C then (α ⟨x, hx⟩ : W) else (β ⟨x, hx⟩ : W)
  have f1 : ∀ x (hx : x ∈ C), f x = α ⟨x, hx⟩ := fun x hx => by simp [f, hx]
  have f2 : ∀ x (hx : x ∉ C), f x = β ⟨x, hx⟩ := fun x hx => by simp [f, hx]
  have m1 : ∀ x (hx : x ∈ C), f x ∈ S := fun x hx => by
    rw [f1 x hx]
    exact (α ⟨x, hx⟩).2
  have m2 : ∀ x (hx : x ∉ C), f x ∉ S := fun x hx => by
    rw [f2 x hx]
    exact (β ⟨x, hx⟩).2
  have adj : ∀ a b, H.Adj (f a) (f b) ↔ G.Adj a b := by
    intro a b
    by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
    · rw [f1 a ha, f1 b hb]
      exact α.map_rel_iff
    · exact iff_of_false (noH _ _ (m1 a ha) (m2 b hb)) (noC a b ha hb)
    · exact iff_of_false (fun h => noH _ _ (m1 b hb) (m2 a ha) h.symm)
        (fun h => noC b a hb ha h.symm)
    · rw [f2 a ha, f2 b hb]
      exact β.map_rel_iff
  have finj : Function.Injective f := by
    intro a b h
    by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
    · rw [f1 a ha, f1 b hb] at h
      exact congrArg Subtype.val (α.injective (Subtype.ext h))
    · exact absurd (h ▸ m1 a ha) (m2 b hb)
    · exact absurd (h ▸ m2 a ha) (not_not.mpr (m1 b hb))
    · rw [f2 a ha, f2 b hb] at h
      exact congrArg Subtype.val (β.injective (Subtype.ext h))
  have hbij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨finj, hcard⟩
  exact ⟨⟨Equiv.ofBijective f hbij, fun {a b} => adj a b⟩⟩

theorem cross_zero {X : Type} [Fintype X] (K : SimpleGraph X) (S : Set X)
    (h : ∀ x y, x ∈ S → y ∉ S → ¬ K.Adj x y) (w : S) :
    #(univ.filter (fun u => u ∉ S ∧ K.Adj w u)) = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro u - ⟨hu, ha⟩
  exact h w u w.2 hu ha

theorem main_H1 : H1 := by
  intro V W _ _ hV G H hG hyp
  obtain ⟨σ, hc⟩ := hyp
  have hW : Fintype.card W = Fintype.card V := (Fintype.card_congr σ).symm
  obtain ⟨u, w, huw⟩ : ∃ u w, ¬ G.Reachable u w := by
    by_contra hcon
    push_neg at hcon
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact hG ⟨hcon⟩
  obtain ⟨C, hCdef⟩ : ∃ C : Set V, C = {x | G.Reachable u x} := ⟨_, rfl⟩
  have noC : ∀ x y, x ∈ C → y ∉ C → ¬ G.Adj x y := by
    intro x y hx hy ha
    rw [hCdef] at hx hy
    exact hy (Reachable.trans hx ha.reachable)
  have noC' : ∀ x y, x ∈ Cᶜ → y ∉ Cᶜ → ¬ G.Adj x y := fun x y hx hy ha =>
    noC y x (not_not.mp hy) hx ha.symm
  have huC : u ∈ C := by
    rw [hCdef]
    exact Reachable.refl u
  have hwC : w ∉ C := by
    rw [hCdef]
    exact huw
  have ha : Fintype.card C < Fintype.card V := Fintype.card_subtype_lt hwC
  have hb : Fintype.card ↥Cᶜ < Fintype.card V :=
    Fintype.card_subtype_lt (p := (· ∈ Cᶜ)) (not_not.mpr huC)
  have hab : Fintype.card C + Fintype.card ↥Cᶜ = Fintype.card V := by
    rw [Fintype.card_compl_set]
    omega
  let A := G.induce C
  let B := G.induce Cᶜ
  have hA := cnteq G H σ hc A ha
  have hB := cnteq G H σ hc B hb
  have htop : pc A B G (Fintype.card V) = pc A B H (Fintype.card V) := by
    have t1 := total A B G
    have t2 := total A B H
    rw [hA, hB, ← t2, hW, sum_range_succ, sum_range_succ] at t1
    have : ∑ m ∈ range (Fintype.card V), pc A B G m = ∑ m ∈ range (Fintype.card V), pc A B H m :=
      sum_congr rfl (fun m hm => keyeq G H σ hc A B m (mem_range.mp hm))
    omega
  have hpos : 0 < pc A B G (Fintype.card V) := by
    unfold pc
    apply card_pos.mpr
    refine ⟨(C.toFinset, Cᶜ.toFinset), ?_⟩
    rw [mem_filter, mem_filter]
    refine ⟨⟨mem_univ _, ?_, ?_⟩, ?_⟩
    · rw [Set.coe_toFinset]
      exact ⟨Iso.refl⟩
    · rw [Set.coe_toFinset]
      exact ⟨Iso.refl⟩
    · have : C.toFinset ∪ Cᶜ.toFinset = univ := by
        ext x
        simp only [mem_union, Set.mem_toFinset, Set.mem_compl_iff, mem_univ, iff_true]
        exact Classical.em _
      rw [this, card_univ]
  rw [htop] at hpos
  unfold pc at hpos
  obtain ⟨p, hp⟩ := card_pos.mp hpos
  rw [mem_filter, mem_filter] at hp
  obtain ⟨⟨-, ⟨e1⟩, he2⟩, hcard⟩ := hp
  have c1 := card_of_iso H p.1 A ⟨e1⟩
  have c2 := card_of_iso H p.2 B he2
  have hi := card_union_add_card_inter p.1 p.2
  have hdisj : p.1 ∩ p.2 = ∅ := by
    rw [← card_eq_zero]
    omega
  have huniv : p.1 ∪ p.2 = univ := eq_univ_of_card _ (by rw [hcard, hW])
  have hT : (p.2 : Set W) = (p.1 : Set W)ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, mem_coe]
    constructor
    · intro h2 h1
      have : x ∈ p.1 ∩ p.2 := mem_inter.mpr ⟨h1, h2⟩
      rw [hdisj] at this
      exact absurd this (notMem_empty x)
    · intro h1
      have : x ∈ p.1 ∪ p.2 := by rw [huniv]; exact mem_univ x
      rcases mem_union.mp this with h | h
      · exact absurd h h1
      · exact h
  rw [hT] at he2
  obtain ⟨e2⟩ := he2
  generalize (p.1 : Set W) = S at e1 e2
  have noH : ∀ x y, x ∈ S → y ∉ S → ¬ H.Adj x y := by
    have dsum : ∑ x, H.degree x = ∑ x, G.degree x := by
      rw [← Equiv.sum_comp σ (fun x => H.degree x)]
      exact sum_congr rfl (fun v _ => deg_hyp hV G H σ hc v)
    have sG : ∑ x, G.degree x = ∑ x : C, (G.induce C).degree x +
        ∑ x : ↥Cᶜ, (G.induce Cᶜ).degree x := by
      rw [sum_split C]
      congr 1
      · refine sum_congr rfl (fun x _ => ?_)
        rw [← deg_split G C x, cross_zero G C noC x, add_zero]
        try convert rfl
      · refine sum_congr rfl (fun x _ => ?_)
        rw [← deg_split G Cᶜ x, cross_zero G Cᶜ noC' x, add_zero]
        try convert rfl
    have sH : ∑ x, H.degree x = ∑ x : S, ((H.induce S).degree x +
          #(univ.filter (fun u => u ∉ S ∧ H.Adj x u))) +
        ∑ x : ↥Sᶜ, ((H.induce Sᶜ).degree x +
          #(univ.filter (fun u => u ∉ Sᶜ ∧ H.Adj x u))) := by
      rw [sum_split S]
      congr 1
      · exact sum_congr rfl (fun x _ => by convert (deg_split H S x).symm using 3)
      · exact sum_congr rfl (fun x _ => by convert (deg_split H Sᶜ x).symm using 3; convert rfl)
    have i1 : ∑ x : C, (G.induce C).degree x = ∑ x : S, (H.induce S).degree x := by
      convert iso_sum e1
    have i2 : ∑ x : ↥Cᶜ, (G.induce Cᶜ).degree x = ∑ x : ↥Sᶜ, (H.induce Sᶜ).degree x := by
      convert iso_sum e2
    rw [sum_add_distrib, sum_add_distrib] at sH
    have z : ∑ x : S, #(univ.filter (fun u => u ∉ S ∧ H.Adj x u)) = 0 := by omega
    rw [sum_eq_zero_iff] at z
    intro x y hx hy hadj
    have z1 := z ⟨x, hx⟩ (mem_univ _)
    rw [card_eq_zero, filter_eq_empty_iff] at z1
    exact z1 (mem_univ y) ⟨hy, hadj⟩
  exact glue G H hW.symm C S noC noH e1.symm e2.symm

end OMA.DisconnRecon

theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_R2.H1 :=
  OMA.DisconnRecon.main_H1
