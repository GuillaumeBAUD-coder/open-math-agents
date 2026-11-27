import OMAReductions.R_Erdos917_erdos_917_variants_lower_construction_R1

/-! Toft's four-critical graph. The transport and critical deletion lemmas below
are adapted from the proof of Erdős 917 part (i) by @mattdorman. -/
namespace ToftFour
open Finset SimpleGraph
lemma isKCritical_of_edge_critical {V : Type*} (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hcol : G.Colorable k) (hnot : ¬ G.Colorable (k - 1))
    (hdeg : ∀ v : V, ∃ w : V, G.Adj v w)
    (hedge : ∀ u w : V, G.Adj u w → (G.deleteEdges {s(u, w)}).Colorable (k - 1)) :
    Erdos917.IsKCritical G k := by
  have hle_chi : (k : ℕ∞) ≤ G.chromaticNumber := by
    rw [le_chromaticNumber_iff_not_colorable (by omega)]
    exact hnot
  have hchi : G.chromaticNumber = (k : ℕ∞) :=
    le_antisymm hcol.chromaticNumber_le hle_chi
  refine ⟨⟨hchi, ?_⟩, ?_⟩
  · intro v
    unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts
    obtain ⟨w, hvw⟩ := hdeg v
    obtain ⟨C⟩ := hedge v w hvw
    have hdel : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
      refine ⟨Coloring.mk (fun a => C a.val) ?_⟩
      intro a b hab
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hab
      obtain ⟨_, ha, _, hb, hab⟩ := hab
      rw [Subgraph.top_adj] at hab
      apply C.valid
      rw [deleteEdges_adj]
      refine ⟨hab, ?_⟩
      rw [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact ha (Set.mem_singleton_iff.mpr h1)
      · exact hb (Set.mem_singleton_iff.mpr h2)
    have htop_le : (k : ℕ∞) ≤ (⊤ : G.Subgraph).coe.chromaticNumber := by
      rw [le_chromaticNumber_iff_not_colorable (by omega)]
      rintro ⟨C'⟩
      exact hnot ⟨Coloring.mk (fun x => C' ⟨x, trivial⟩) (fun h => C'.valid (by simpa using h))⟩
    exact lt_of_le_of_lt hdel.chromaticNumber_le
      (lt_of_lt_of_le (by exact_mod_cast (by omega : k - 1 < k)) htop_le)
  · intro e he
    unfold IsCriticalEdge IsCriticalEdges
    revert he
    refine Sym2.ind (fun u w huw => ?_) e
    rw [mem_edgeSet] at huw
    exact lt_of_le_of_lt (hedge u w huw).chromaticNumber_le
      (lt_of_lt_of_le (by exact_mod_cast (by omega : k - 1 < k)) hle_chi)

lemma isKCritical_transport {V W : Type*} (G : SimpleGraph V) (e : V ≃ W) {k : ℕ} (hk : 1 ≤ k)
    (hcol : G.Colorable k) (hnot : ¬ G.Colorable (k - 1))
    (hdeg : ∀ v : V, ∃ w : V, G.Adj v w)
    (hedge : ∀ u w : V, G.Adj u w → (G.deleteEdges {s(u, w)}).Colorable (k - 1)) :
    Erdos917.IsKCritical (G.map e.toEmbedding) k := by
  refine isKCritical_of_edge_critical _ hk ?_ ?_ ?_ ?_
  · obtain ⟨C⟩ := hcol
    refine ⟨Coloring.mk (fun w => C (e.symm w)) ?_⟩
    intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
    simpa using C.valid huv
  · rintro ⟨C⟩
    exact hnot ⟨Coloring.mk (fun v => C (e v)) fun {u v} huv =>
      C.valid (by rw [map_adj]; exact ⟨u, v, huv, rfl, rfl⟩)⟩
  · intro w
    obtain ⟨u, hu⟩ := hdeg (e.symm w)
    refine ⟨e u, ?_⟩
    rw [map_adj]
    exact ⟨e.symm w, u, hu, e.apply_symm_apply w, rfl⟩
  · intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
    obtain ⟨C⟩ := hedge u v huv
    refine ⟨Coloring.mk (fun w => C (e.symm w)) ?_⟩
    intro a b hab
    rw [deleteEdges_adj, map_adj] at hab
    obtain ⟨⟨u', v', huv', rfl, rfl⟩, hne⟩ := hab
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
    apply C.valid
    rw [deleteEdges_adj]
    refine ⟨huv', ?_⟩
    intro heq
    apply hne
    rw [Set.mem_singleton_iff] at heq ⊢
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

lemma isKCritical_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hG : Erdos917.IsKCritical G k) : G.Colorable k :=
  chromaticNumber_le_iff_colorable.mp hG.1.1.le

lemma isKCritical_not_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) : ¬ G.Colorable (k - 1) := by
  intro hc
  have hlt : (k - 1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast (by omega : k - 1 < k)
  exact not_le_of_gt hlt (hG.1.1.symm.trans_le hc.chromaticNumber_le)

lemma isKCritical_nonempty {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) : Nonempty V := by
  by_contra hemp
  rw [not_nonempty_iff] at hemp
  exact isKCritical_not_colorable hk hG
    ⟨Coloring.mk (fun v => (IsEmpty.false v).elim) (fun {v} => (IsEmpty.false v).elim)⟩

lemma isKCritical_del_edge_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) {u w : V} (huw : G.Adj u w) :
    (G.deleteEdges {s(u, w)}).Colorable (k - 1) := by
  have he : s(u, w) ∈ G.edgeSet := huw
  have hlt := hG.2 _ he
  unfold IsCriticalEdge IsCriticalEdges at hlt
  rw [hG.1.1] at hlt
  by_contra hnc
  exact not_lt_of_ge ((le_chromaticNumber_iff_not_colorable (by omega)).mpr hnc) hlt

lemma isKCritical_del_vert_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) (v : V) :
    ∃ col : V → ℕ, (∀ x, x ≠ v → col x < k - 1) ∧
      ∀ x y, x ≠ v → y ≠ v → G.Adj x y → col x ≠ col y := by
  classical
  have hlt := hG.1.2 v
  unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts at hlt
  have htop_le : (⊤ : G.Subgraph).coe.chromaticNumber ≤ G.chromaticNumber := by
    obtain ⟨C⟩ := isKCritical_colorable hG
    rw [hG.1.1]
    exact (Colorable.chromaticNumber_le
      ⟨Coloring.mk (fun x => C x.val) (fun {a b} h => C.valid (by simpa using h))⟩)
  have hlt' : ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber < (k : ℕ∞) :=
    lt_of_lt_of_le hlt (htop_le.trans_eq hG.1.1)
  have hcol : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
    by_contra hnc
    exact not_lt_of_ge ((le_chromaticNumber_iff_not_colorable (by omega)).mpr hnc) hlt'
  obtain ⟨C⟩ := hcol
  refine ⟨fun x => if hx : x ≠ v then (C ⟨x, by simp [hx]⟩).val else 0, ?_, ?_⟩
  · intro x hx
    dsimp only
    rw [dif_pos hx]
    exact (C _).isLt
  · intro x y hx hy hadj heq
    dsimp only at heq
    rw [dif_pos hx, dif_pos hy] at heq
    have hadj' : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Adj ⟨x, by simp [hx]⟩ ⟨y, by simp [hy]⟩ := by
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
      exact ⟨trivial, by simp [hx], trivial, by simp [hy], hadj⟩
    exact C.valid hadj' (Fin.ext heq)

abbrev V (X Y : Type*) := X ⊕ (X ⊕ (Y ⊕ Y))
abbrev a {X Y : Type*} (x : X) : V X Y := .inl x
abbrev b {X Y : Type*} (x : X) : V X Y := .inr (.inl x)
abbrev c {X Y : Type*} (y : Y) : V X Y := .inr (.inr (.inl y))
abbrev d {X Y : Type*} (y : Y) : V X Y := .inr (.inr (.inr y))

variable {X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y)

def rel : V X Y → V X Y → Prop
  | .inl x, .inl t => G.Adj x t
  | .inl x, .inr (.inl t) => x = t
  | .inr (.inl t), .inl x => x = t
  | .inr (.inl _), .inr (.inr (.inl _)) => True
  | .inr (.inr (.inl _)), .inr (.inl _) => True
  | .inr (.inr (.inl y)), .inr (.inr (.inr t)) => y = t
  | .inr (.inr (.inr t)), .inr (.inr (.inl y)) => y = t
  | .inr (.inr (.inr y)), .inr (.inr (.inr t)) => H.Adj y t
  | _, _ => False

def graph : SimpleGraph (V X Y) where
  Adj := rel G H
  symm := ⟨by
    rintro (x|x|y|y) (t|t|s|s) h <;> simp only [rel] at * <;> first | assumption | exact h.symm⟩
  loopless := ⟨by rintro (x|x|y|y) <;> simp [rel]⟩

lemma coloring {k : ℕ} (D : Set (Sym2 (V X Y))) (f g : X → Fin k) (h i : Y → Fin k)
    (ha : ∀ x t, G.Adj x t → f x = f t → s(a x,a t) ∈ D)
    (hd : ∀ y t, H.Adj y t → i y = i t → s(d y,d t) ∈ D)
    (hm : ∀ x, f x = g x → s(a x,b x) ∈ D)
    (hn : ∀ y, i y = h y → s(c y,d y) ∈ D)
    (hb : ∀ x y, g x = h y → s(b x,c y) ∈ D) :
    ((graph G H).deleteEdges D).Colorable k := by
  refine ⟨Coloring.mk (Sum.elim f (Sum.elim g (Sum.elim h i))) ?_⟩
  intro v w had he
  rw [deleteEdges_adj] at had
  obtain ⟨hadj, hne⟩ := had
  apply hne
  rcases v with x|x|y|y <;> rcases w with t|t|u|u <;>
    simp only [graph, rel] at hadj <;> simp only [Sum.elim_inl, Sum.elim_inr] at he
  · exact ha _ _ hadj he
  · subst t; exact hm _ he
  · subst t; rw [Sym2.eq_swap]; exact hm _ he.symm
  · exact hb _ _ he
  · rw [Sym2.eq_swap]; exact hb _ _ he.symm
  · subst u; exact hn _ he.symm
  · subst u; rw [Sym2.eq_swap]; exact hn _ he
  · exact hd _ _ hadj he
lemma unique_color {k : ℕ} {G : SimpleGraph X} (hG : Erdos917.IsKCritical G (k+1)) (v : X) :
    ∃ f : G.Coloring (Fin (k+1)), ∀ x, f x = Fin.last k ↔ x = v := by
  classical
  obtain ⟨col, hb, hp⟩ := isKCritical_del_vert_colorable (by omega) hG v
  let f (x : X) : Fin (k+1) := if hx : x = v then Fin.last k else
    ⟨col x, by have := hb x hx; omega⟩
  have hf (x : X) : f x = Fin.last k ↔ x = v := by
    by_cases h : x = v
    · simp [f, h]
    · simp only [f, dif_neg h, h, iff_false]
      intro he
      have := congrArg Fin.val he
      have := hb x h
      simp only [Fin.val_last] at *
      omega
  refine ⟨Coloring.mk f ?_, hf⟩
  intro x y h he
  by_cases hx : x = v
  · exact h.ne (hx.trans ((hf y).mp (he ▸ (hf x).mpr hx)).symm)
  by_cases hy : y = v
  · exact hx ((hf x).mp (he.trans ((hf y).mpr hy)))
  apply hp _ _ hx hy h
  simpa [f, hx, hy] using congrArg Fin.val he

lemma same_deleted_edge {k : ℕ} {G : SimpleGraph X} {v w x t : X}
    (f : (G.deleteEdges {s(v,w)}).Coloring (Fin k)) (h : G.Adj x t) (he : f x = f t) :
    s(x,t) = s(v,w) := by
  by_contra hn
  exact f.valid (deleteEdges_adj.mpr ⟨h, by simpa using hn⟩) he


lemma full (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3) :
    (graph G H).Colorable 4 := by
  obtain ⟨f⟩ := isKCritical_colorable hG
  obtain ⟨i⟩ := isKCritical_colorable hH
  have hcol := coloring G H (∅ : Set _) (fun x => (f x).castSucc) (fun _ => (3 : Fin 4))
    (fun y => if i y = 0 then 1 else 0) (fun y => (i y).castSucc)
    (by intro x t hx he; exact (f.valid hx (Fin.castSucc_injective _ he)).elim)
    (by intro y t hy he; exact (i.valid hy (Fin.castSucc_injective _ he)).elim)
    (by intro x he; have := congrArg Fin.val he; simp at this; omega)
    (by intro y he; split at he <;> have := congrArg Fin.val he <;> simp at this <;> omega)
    (by intro x y he; split at he <;> contradiction)
  simpa using hcol

lemma shadow_pair {G : SimpleGraph X} (hG : Erdos917.IsKCritical G 3) (f : G.Coloring (Fin 3))
    (g : X → Fin 3) (hg : ∀ x, f x ≠ g x) : ∃ x t, g x ≠ g t := by
  obtain ⟨v⟩ := isKCritical_nonempty (by decide) hG
  obtain ⟨x, hx⟩ := (chromaticNumber_eq_iff_forall_surjective (isKCritical_colorable hG)).mp
    hG.1.1 f (g v)
  exact ⟨x, v, fun h => hg x (hx.trans h.symm)⟩

lemma not_three (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3) :
    ¬(graph G H).Colorable 3 := by
  rintro ⟨F⟩
  let f : G.Coloring (Fin 3) := Coloring.mk (fun x => F (a x))
    (fun {x t} hp => F.valid (show (graph G H).Adj (a x) (a t) from hp))
  let i : H.Coloring (Fin 3) := Coloring.mk (fun y => F (d y))
    (fun {y t} hp => F.valid (show (graph G H).Adj (d y) (d t) from hp))
  obtain ⟨x,t,hx⟩ := shadow_pair hG f (fun x => F (b x))
    (fun x => F.valid (show (graph G H).Adj (a x) (b x) from rfl))
  obtain ⟨y,u,hy⟩ := shadow_pair hH i (fun y => F (c y))
    (fun y => F.valid (show (graph G H).Adj (d y) (c y) from rfl))
  have cross (x : X) (y : Y) : F (b x) ≠ F (c y) := F.valid (show (graph G H).Adj _ _ from trivial)
  have pigeon : ∀ i j k l : Fin 3, i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l → False := by
    intro i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide
  exact pigeon _ _ _ _ hx hy (cross x y) (cross x u) (cross t y) (cross t u)

lemma del_l_edge (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3)
    {v w : X} (hvw : G.Adj v w) : ((graph G H).deleteEdges {s(a v,a w)}).Colorable 3 := by
  obtain ⟨f⟩ := isKCritical_del_edge_colorable (by decide) hG hvw
  obtain ⟨i⟩ := isKCritical_colorable hH
  apply coloring G H _ (fun x => (f x).castSucc) (fun _ => (2 : Fin 3)) (fun t => if i t = 0 then 1 else 0) i
  · intro x t hx he
    exact congrArg (Sym2.map a) (same_deleted_edge f hx (Fin.castSucc_injective _ he))
  · intro y t hy he; exact (i.valid hy he).elim
  · intro x he; have := congrArg Fin.val he; simp at this; omega
  · intro y he; exact (show ∀ z : Fin 3, z ≠ (if z = 0 then 1 else 0) by decide) (i y) he |>.elim
  · intro x y he; split at he <;> contradiction

lemma del_l_match (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3)
    (v : X) : ((graph G H).deleteEdges {s(a v,b v)}).Colorable 3 := by
  obtain ⟨f, hf⟩ := unique_color (k := 2) hG v
  obtain ⟨i⟩ := isKCritical_colorable hH
  apply coloring G H _ f (fun _ => (2 : Fin 3)) (fun t => if i t = 0 then 1 else 0) i
  · intro x t hx he; exact (f.valid hx he).elim
  · intro y t hy he; exact (i.valid hy he).elim
  · intro x he; rw [(hf x).mp he]; rfl
  · intro y he; exact (show ∀ z : Fin 3, z ≠ (if z = 0 then 1 else 0) by decide) (i y) he |>.elim
  · intro x y he; split at he <;> contradiction

lemma del_r_edge (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3)
    {v w : Y} (hvw : H.Adj v w) : ((graph G H).deleteEdges {s(d v,d w)}).Colorable 3 := by
  obtain ⟨f⟩ := isKCritical_del_edge_colorable (by decide) hH hvw
  obtain ⟨i⟩ := isKCritical_colorable hG
  apply coloring G H _ i (fun t => if i t = 0 then 1 else 0) (fun _ => (2 : Fin 3)) (fun x => (f x).castSucc)
  · intro y t hy he; exact (i.valid hy he).elim
  · intro x t hx he
    exact congrArg (Sym2.map d) (same_deleted_edge f hx (Fin.castSucc_injective _ he))
  · intro y he; exact (show ∀ z : Fin 3, z ≠ (if z = 0 then 1 else 0) by decide) (i y) he |>.elim
  · intro x he; have := congrArg Fin.val he; simp at this; omega
  · intro x y he; split at he <;> contradiction

lemma del_r_match (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3)
    (v : Y) : ((graph G H).deleteEdges {s(c v,d v)}).Colorable 3 := by
  obtain ⟨f, hf⟩ := unique_color (k := 2) hH v
  obtain ⟨i⟩ := isKCritical_colorable hG
  apply coloring G H _ i (fun t => if i t = 0 then 1 else 0) (fun _ => (2 : Fin 3)) f
  · intro y t hy he; exact (i.valid hy he).elim
  · intro x t hx he; exact (f.valid hx he).elim
  · intro y he; exact (show ∀ z : Fin 3, z ≠ (if z = 0 then 1 else 0) by decide) (i y) he |>.elim
  · intro x he; rw [(hf x).mp he]; rfl
  · intro x y he; split at he <;> contradiction

lemma named_color {G : SimpleGraph X} (hG : Erdos917.IsKCritical G 3) (v : X) (k : Fin 3) :
    ∃ f : G.Coloring (Fin 3), ∀ x, f x = k ↔ x = v := by
  classical
  obtain ⟨f,hf⟩ := unique_color (k := 2) hG v
  let e := Equiv.swap (Fin.last 2) k
  have he : e (Fin.last 2) = k := Equiv.swap_apply_left _ _
  refine ⟨Coloring.mk (fun x => e (f x)) (fun {x t} h hh => f.valid h (e.injective hh)), ?_⟩
  intro x
  change e (f x) = k ↔ x = v
  rw [← he, e.injective.eq_iff, hf]

lemma del_cross [DecidableEq X] [DecidableEq Y] (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3)
    (v : X) (w : Y) : ((graph G H).deleteEdges {s(b v,c w)}).Colorable 3 := by
  obtain ⟨f,hf⟩ := named_color hG v 0
  obtain ⟨i,hi⟩ := named_color hH w 1
  apply coloring G H _ f (fun x => if x = v then 2 else 0) (fun y => if y = w then 2 else 1) i
  · intro x t hx he; exact (f.valid hx he).elim
  · intro y t hy he; exact (i.valid hy he).elim
  · intro x he; split at he
    · rename_i hx; have hh := (hf x).mpr hx; omega
    · rename_i hx; exact (hx ((hf x).mp he)).elim
  · intro y he; split at he
    · rename_i hy; have hh := (hi y).mpr hy; omega
    · rename_i hy; exact (hy ((hi y).mp he)).elim
  · intro x y he
    by_cases hx : x = v <;> by_cases hy : y = w <;> simp_all

lemma del [DecidableEq X] [DecidableEq Y] (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3) :
    ∀ v w, (graph G H).Adj v w → ((graph G H).deleteEdges {s(v,w)}).Colorable 3 := by
  rintro (x|x|y|y) (t|t|s|s) hadj <;> simp only [graph, rel] at hadj
  · exact del_l_edge G H hG hH hadj
  · subst t; exact del_l_match G H hG hH x
  · subst t; rw [Sym2.eq_swap]; exact del_l_match G H hG hH x
  · exact del_cross G H hG hH x s
  · rw [Sym2.eq_swap]; exact del_cross G H hG hH t y
  · subst s; exact del_r_match G H hG hH y
  · subst s; rw [Sym2.eq_swap]; exact del_r_match G H hG hH y
  · exact del_r_edge G H hG hH hadj
lemma degree_sum [Fintype X] (G : SimpleGraph X) [DecidableRel G.Adj] (v : X) :
    G.degree v = ∑ w : X, if G.Adj v w then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.sum_boole]
  rfl


lemma edge_count {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) :
    (graph G H).edgeSet.ncard = G.edgeSet.ncard + H.edgeSet.ncard + n + m + n*m := by
  classical
  let T := graph G H
  have da (x : Fin n) : T.degree (a x) = G.degree x + 1 := by
    rw [degree_sum, degree_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [T, graph, rel, a]
  have db (x : Fin n) : T.degree (b x) = 1 + m := by
    rw [degree_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [T, graph, rel, b]
  have dc (y : Fin m) : T.degree (c y) = n + 1 := by
    rw [degree_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [T, graph, rel, c]
  have dd (y : Fin m) : T.degree (d y) = H.degree y + 1 := by
    rw [degree_sum, degree_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [T, graph, rel, d, add_comm]
  have hs := sum_degrees_eq_twice_card_edges T
  change (∑ v : Fin n ⊕ (Fin n ⊕ (Fin m ⊕ Fin m)), T.degree v) = _ at hs
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hs
  change (∑ x, T.degree (a x)) + ((∑ x, T.degree (b x)) + ((∑ y, T.degree (c y)) + ∑ y, T.degree (d y))) = _ at hs
  simp only [da, db, dc, dd, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hs
  have hg := sum_degrees_eq_twice_card_edges G
  have hh := sum_degrees_eq_twice_card_edges H
  change T.edgeSet.ncard = _
  rw [← coe_edgeFinset, ← coe_edgeFinset, ← coe_edgeFinset]
  simp only [Set.ncard_coe_finset]
  nlinarith

end ToftFour
open ToftFour in
theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_lower_construction_R1.H3 := by
  classical
  rintro n m _ _ ⟨G, hG, rfl⟩ ⟨H, hH, rfl⟩
  let e : V (Fin n) (Fin m) ≃ Fin (2*n+2*m) := Fintype.equivOfCardEq (by simp [V]; omega)
  refine ⟨(graph G H).map e.toEmbedding, ?_, ?_⟩
  · apply isKCritical_transport _ e (by decide : 1 ≤ 4) (full _ _ hG hH) (not_three _ _ hG hH)
    · rintro (x|x|y|y)
      · exact ⟨b x, rfl⟩
      · exact ⟨a x, rfl⟩
      · exact ⟨d y, rfl⟩
      · exact ⟨c y, rfl⟩
    · exact del G H hG hH
  · rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, SimpleGraph.card_edgeFinset_map]
    simpa only [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using edge_count G H
