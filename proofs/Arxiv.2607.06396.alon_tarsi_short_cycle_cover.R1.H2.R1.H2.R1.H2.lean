import OMAReductions.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H2_R1

/-! Fleischner splitting lemma, via edge cuts: splitting off `vu`, `vw` creates a bridge only if some
vertex set avoiding `v` and containing `u`, `w` has exactly three edges leaving it. -/

open Finset SimpleGraph

namespace FleischnerAux

open Classical

noncomputable def cnt {W : Type} [Fintype W] (H : SimpleGraph W) (R : W → W → Prop) : ℕ :=
  ∑ p : W × W, if H.Adj p.1 p.2 ∧ R p.1 p.2 then 1 else 0

lemma cnt_congr {W : Type} [Fintype W] (H : SimpleGraph W) (R R' : W → W → Prop)
    (h : ∀ a b, H.Adj a b → (R a b ↔ R' a b)) : cnt H R = cnt H R' := by
  unfold cnt
  refine sum_congr rfl fun p _ => ?_
  by_cases hA : H.Adj p.1 p.2
  · simp [hA, h p.1 p.2 hA]
  · simp [hA]

lemma cnt_le {W : Type} [Fintype W] (H : SimpleGraph W) (R R' : W → W → Prop)
    (h : ∀ a b, H.Adj a b → R a b → R' a b) : cnt H R ≤ cnt H R' := by
  unfold cnt
  refine sum_le_sum fun p _ => ?_
  by_cases hA : H.Adj p.1 p.2 ∧ R p.1 p.2
  · simp [hA, h p.1 p.2 hA.1 hA.2]
  · simp [hA]

lemma cnt_add {W : Type} [Fintype W] (H : SimpleGraph W) (R1 R2 R3 R4 : W → W → Prop)
    (h : ∀ a b, H.Adj a b → (if R1 a b then 1 else 0) + (if R2 a b then 1 else 0) =
      (if R3 a b then 1 else 0) + (if R4 a b then (1 : ℕ) else 0)) :
    cnt H R1 + cnt H R2 = cnt H R3 + cnt H R4 := by
  unfold cnt
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  by_cases hA : H.Adj p.1 p.2
  · simpa [hA] using h p.1 p.2 hA
  · simp [hA]

lemma cnt_swap {W : Type} [Fintype W] (H : SimpleGraph W) (R : W → W → Prop) :
    cnt H (fun a b => R b a) = cnt H R := by
  unfold cnt
  refine Fintype.sum_equiv (Equiv.prodComm W W) _ _ fun p => ?_
  simp [H.adj_comm]

lemma one_le_cnt {W : Type} [Fintype W] (H : SimpleGraph W) (R : W → W → Prop) (a b : W)
    (hab : H.Adj a b) (h : R a b) : 1 ≤ cnt H R := by
  unfold cnt
  have := Finset.single_le_sum (f := fun p : W × W => if H.Adj p.1 p.2 ∧ R p.1 p.2 then 1 else 0)
    (fun _ _ => Nat.zero_le _) (mem_univ (a, b))
  simpa [hab, h] using this

lemma two_le_cnt {W : Type} [Fintype W] (H : SimpleGraph W) (R : W → W → Prop) (p q : W × W)
    (hpq : p ≠ q) (hp : H.Adj p.1 p.2 ∧ R p.1 p.2) (hq : H.Adj q.1 q.2 ∧ R q.1 q.2) :
    2 ≤ cnt H R := by
  unfold cnt
  have := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ {p, q})
    (f := fun p : W × W => if H.Adj p.1 p.2 ∧ R p.1 p.2 then 1 else 0) (fun _ _ _ => Nat.zero_le _)
  rw [sum_pair hpq] at this
  simpa [hp, hq] using this

lemma exists_of_cnt {W : Type} [Fintype W] (H : SimpleGraph W) (R : W → W → Prop)
    (h : cnt H R ≠ 0) : ∃ a b, H.Adj a b ∧ R a b := by
  by_contra hno
  push Not at hno
  apply h
  unfold cnt
  refine sum_eq_zero fun p _ => ?_
  have := hno p.1 p.2
  by_cases hA : H.Adj p.1 p.2
  · simp [hA, this hA]
  · simp [hA]

/-- Cut of `S`: ordered adjacent pairs leaving `S`. -/
noncomputable def dc {W : Type} [Fintype W] (H : SimpleGraph W) (S : W → Prop) : ℕ :=
  cnt H (fun a b => S a ∧ ¬ S b)

lemma dc_compl {W : Type} [Fintype W] (H : SimpleGraph W) (S : W → Prop) :
    dc H (fun x => ¬ S x) = dc H S := by
  unfold dc
  rw [← cnt_swap]
  exact cnt_congr _ _ _ fun a b _ => by tauto

lemma dc_ne_one {W : Type} [Fintype W] (H : SimpleGraph W) (hb : H.IsBridgeless) (S : W → Prop) :
    dc H S ≠ 1 := by
  intro h1
  obtain ⟨a, b, hab, ha, hb'⟩ := exists_of_cnt H (fun a b => S a ∧ ¬ S b) (by unfold dc at h1; omega)
  have hnb : ¬ H.IsBridge s(a, b) := hb _ hab
  rw [isBridge_iff, not_not] at hnb
  obtain ⟨p⟩ := hnb
  obtain ⟨d, _, hd1, hd2⟩ := p.exists_boundary_dart {x | S x} ha hb'
  have hadj := d.adj
  rw [deleteEdges_adj, Set.mem_singleton_iff] at hadj
  have hne : (d.fst, d.snd) ≠ (a, b) := by
    intro h
    apply hadj.2
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2]
  have := two_le_cnt H (fun a b => S a ∧ ¬ S b) _ _ hne ⟨hadj.1, hd1, hd2⟩ ⟨hab, ha, hb'⟩
  unfold dc at h1
  omega

lemma exists_dc_one {W : Type} [Fintype W] (H : SimpleGraph W) (hb : ¬ H.IsBridgeless) :
    ∃ S : W → Prop, dc H S = 1 := by
  unfold IsBridgeless at hb
  push Not at hb
  obtain ⟨e, he, hbr⟩ := hb
  induction e using Sym2.ind with
  | _ x y =>
  rw [isBridge_iff] at hbr
  refine ⟨fun z => (H.deleteEdges {s(x, y)}).Reachable x z, ?_⟩
  unfold dc cnt
  rw [Fintype.sum_eq_single (x, y)]
  · simp only [mem_edgeSet] at he
    simp [he, hbr]
  · rintro ⟨p, q⟩ hpq
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    rintro ⟨hadj, hp, hq⟩
    apply hq
    by_cases he' : s(p, q) = s(x, y)
    · rcases Sym2.eq_iff.mp he' with h | h
      · exact absurd (by rw [h.1, h.2]) hpq
      · rw [h.1] at hp; exact absurd hp hbr
    · exact hp.trans (Adj.reachable (by simp [hadj, he']))

end FleischnerAux

namespace FleischnerAux

open Classical

lemma ite_congr' {c : Prop} (i1 i2 : Decidable c) (a b : ℕ) :
    @ite _ c i1 a b = @ite _ c i2 a b := by
  congr

lemma cnt_region {W : Type} [Fintype W] (H : SimpleGraph W) {k : ℕ} (L : W → Fin k)
    (P Q : Fin k → Prop) :
    cnt H (fun a b => P (L a) ∧ Q (L b)) =
      ∑ i, ∑ j, if P i ∧ Q j then cnt H (fun a b => L a = i ∧ L b = j) else 0 := by
  have e1 : cnt H (fun a b => P (L a) ∧ Q (L b)) =
      ∑ p : W × W, if H.Adj p.1 p.2 ∧ P (L p.1) ∧ Q (L p.2) then 1 else 0 :=
    sum_congr rfl fun p _ => ite_congr' _ _ _ _
  have e2 : ∀ i j, cnt H (fun a b => L a = i ∧ L b = j) =
      ∑ p : W × W, if H.Adj p.1 p.2 ∧ (L p.1 = i ∧ L p.2 = j) then 1 else 0 :=
    fun i j => sum_congr rfl fun p _ => ite_congr' _ _ _ _
  rw [e1]
  simp only [e2]
  have hp : ∀ p : W × W, (if H.Adj p.1 p.2 ∧ P (L p.1) ∧ Q (L p.2) then 1 else 0) =
      ∑ i, ∑ j, if (H.Adj p.1 p.2 ∧ P (L p.1) ∧ Q (L p.2)) ∧ (L p.1 = i ∧ L p.2 = j)
        then 1 else 0 := by
    intro p
    rw [Fintype.sum_eq_single (L p.1), Fintype.sum_eq_single (L p.2)]
    · simp
    · intro j hj
      rw [if_neg]
      rintro ⟨_, _, h⟩
      exact hj h.symm
    · intro i hi
      refine sum_eq_zero fun j _ => ?_
      rw [if_neg]
      rintro ⟨_, h, _⟩
      exact hi h.symm
  have hq : ∀ i j, (∑ p : W × W, if (H.Adj p.1 p.2 ∧ P (L p.1) ∧ Q (L p.2)) ∧
      (L p.1 = i ∧ L p.2 = j) then 1 else 0) =
      if P i ∧ Q j then ∑ p : W × W, (if H.Adj p.1 p.2 ∧ (L p.1 = i ∧ L p.2 = j) then 1 else 0)
        else 0 := by
    intro i j
    split_ifs with h
    · refine sum_congr rfl fun p _ => ?_
      by_cases h' : L p.1 = i ∧ L p.2 = j
      · obtain ⟨h1, h2⟩ := h'
        subst h1 h2
        simp [h]
      · simp [h']
    · refine sum_eq_zero fun p _ => ?_
      rw [if_neg]
      rintro ⟨⟨_, hp, hq⟩, h1, h2⟩
      subst h1 h2
      exact h ⟨hp, hq⟩
  calc _ = ∑ p : W × W, ∑ i, ∑ j, if (H.Adj p.1 p.2 ∧ P (L p.1) ∧ Q (L p.2)) ∧
        (L p.1 = i ∧ L p.2 = j) then 1 else 0 := sum_congr rfl fun p _ => hp p
    _ = ∑ i, ∑ p : W × W, ∑ j, if (H.Adj p.1 p.2 ∧ P (L p.1) ∧ Q (L p.2)) ∧
        (L p.1 = i ∧ L p.2 = j) then 1 else 0 := sum_comm
    _ = ∑ i, ∑ j, ∑ p : W × W, if (H.Adj p.1 p.2 ∧ P (L p.1) ∧ Q (L p.2)) ∧
        (L p.1 = i ∧ L p.2 = j) then 1 else 0 := sum_congr rfl fun i _ => sum_comm
    _ = _ := sum_congr rfl fun i _ => sum_congr rfl fun j _ => hq i j

/-- Ordered adjacent pairs from `S` to `v`, that is the number of neighbours of `v` in `S`. -/
noncomputable def nb {W : Type} [Fintype W] (H : SimpleGraph W) (v : W) (S : W → Prop) : ℕ :=
  cnt H (fun a b => S a ∧ b = v)

lemma key {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v u x : V)
    (X Y : V → Prop) (hXv : ¬ X v) (hYv : ¬ Y v) (huX : X u) (huY : Y u) (hxX : ¬ X x)
    (hxY : Y x) (hu : G.Adj u v) (hx : G.Adj x v) (hbr : ∀ S, dc G S ≠ 1) (hY3 : dc G Y = 3)
    (hcase : (dc G X ≤ 3 ∧ 3 ≤ nb G v X) ∨ (dc G X = 3 ∧ 2 ≤ nb G v X ∧
      ∀ T : V → Prop, ¬ T v → dc G T ≤ 3 → nb G v T < 3)) : False := by
  let L : V → Fin 5 := fun z => if z = v then 4 else
    if X z then (if Y z then 1 else 0) else (if Y z then 2 else 3)
  have hL4 : ∀ z, L z = 4 ↔ z = v := by
    intro z
    by_cases hz : z = v
    · simp [L, hz]
    · simp only [L, hz, if_false, iff_false]
      split_ifs <;> simp
  have hLX : ∀ z, X z ↔ (L z = 0 ∨ L z = 1) := by
    intro z
    by_cases hz : z = v
    · subst hz; simp [L, hXv]
    · simp only [L, hz, if_false]
      split_ifs <;> simp_all
  have hLY : ∀ z, Y z ↔ (L z = 1 ∨ L z = 2) := by
    intro z
    by_cases hz : z = v
    · subst hz; simp [L, hYv]
    · simp only [L, hz, if_false]
      split_ifs <;> simp_all
  have hd : ∀ P : Fin 5 → Prop, dc G (fun z => P (L z)) =
      ∑ i, ∑ j, if P i ∧ ¬ P j then cnt G (fun a b => L a = i ∧ L b = j) else 0 :=
    fun P => (cnt_region G L P (fun j => ¬ P j)).trans
      (sum_congr rfl fun i _ => sum_congr rfl fun j _ => ite_congr' _ _ _ _)
  have hn : ∀ P : Fin 5 → Prop, nb G v (fun z => P (L z)) =
      ∑ i, ∑ j, if P i ∧ j = 4 then cnt G (fun a b => L a = i ∧ L b = j) else 0 := by
    intro P
    rw [nb, cnt_congr G _ (fun a b => P (L a) ∧ L b = 4) (fun a b _ => by rw [hL4])]
    exact (cnt_region G L P (fun j => j = 4)).trans
      (sum_congr rfl fun i _ => sum_congr rfl fun j _ => ite_congr' _ _ _ _)
  have hsym : ∀ i j, cnt G (fun a b => L a = i ∧ L b = j) = cnt G (fun a b => L a = j ∧ L b = i) := by
    intro i j
    rw [← cnt_swap G (fun a b => L a = j ∧ L b = i)]
    exact cnt_congr _ _ _ fun a b _ => and_comm
  have eX : dc G X = dc G (fun z => L z = 0 ∨ L z = 1) :=
    cnt_congr _ _ _ fun a b _ => by rw [hLX a, hLX b]
  have eY : dc G Y = dc G (fun z => L z = 1 ∨ L z = 2) :=
    cnt_congr _ _ _ fun a b _ => by rw [hLY a, hLY b]
  have eXY : dc G (fun z => X z ∨ Y z) = dc G (fun z => L z = 0 ∨ L z = 1 ∨ L z = 2) :=
    cnt_congr _ _ _ fun a b _ => by simp only [hLX, hLY]; tauto
  have fX : nb G v X = nb G v (fun z => L z = 0 ∨ L z = 1) :=
    cnt_congr _ _ _ fun a b _ => by rw [hLX a]
  have fY : nb G v Y = nb G v (fun z => L z = 1 ∨ L z = 2) :=
    cnt_congr _ _ _ fun a b _ => by rw [hLY a]
  have fXY : nb G v (fun z => X z ∨ Y z) = nb G v (fun z => L z = 0 ∨ L z = 1 ∨ L z = 2) :=
    cnt_congr _ _ _ fun a b _ => by simp only [hLX, hLY]; tauto
  have hA := hbr (fun z => L z = 0)
  have hB := hbr (fun z => L z = 1)
  have hC := hbr (fun z => L z = 2)
  have h14 : 1 ≤ cnt G (fun a b => L a = 1 ∧ L b = 4) :=
    one_le_cnt G _ u v hu ⟨by simp [L, huX, huY, (hu.ne : u ≠ v)], (hL4 v).mpr rfl⟩
  have h24 : 1 ≤ cnt G (fun a b => L a = 2 ∧ L b = 4) :=
    one_le_cnt G _ x v hx ⟨by simp [L, hxX, hxY, (hx.ne : x ≠ v)], (hL4 v).mpr rfl⟩
  rw [hd (fun i => i = 0)] at hA
  rw [hd (fun i => i = 1)] at hB
  rw [hd (fun i => i = 2)] at hC
  rw [eY, hd (fun i => i = 1 ∨ i = 2)] at hY3
  simp [Fin.sum_univ_five] at hA hB hC hY3
  have s01 := hsym 0 1
  have s02 := hsym 0 2
  have s03 := hsym 0 3
  have s04 := hsym 0 4
  have s12 := hsym 1 2
  have s13 := hsym 1 3
  have s14 := hsym 1 4
  have s23 := hsym 2 3
  have s24 := hsym 2 4
  have s34 := hsym 3 4
  rcases hcase with ⟨hX3, hnbX⟩ | ⟨hX3, hnbX, hT⟩
  · rw [eX, hd (fun i => i = 0 ∨ i = 1)] at hX3
    rw [fX, hn (fun i => i = 0 ∨ i = 1)] at hnbX
    simp [Fin.sum_univ_five] at hX3 hnbX
    omega
  · have hTY := hT Y hYv
    have hTX := hT X hXv
    have hTXY := hT (fun z => X z ∨ Y z) (by simp [hXv, hYv])
    rw [eX, hd (fun i => i = 0 ∨ i = 1)] at hX3 hTX
    rw [fX, hn (fun i => i = 0 ∨ i = 1)] at hnbX hTX
    rw [eY, hd (fun i => i = 1 ∨ i = 2), fY, hn (fun i => i = 1 ∨ i = 2)] at hTY
    rw [eXY, hd (fun i => i = 0 ∨ i = 1 ∨ i = 2), fXY, hn (fun i => i = 0 ∨ i = 1 ∨ i = 2)] at hTXY
    simp [Fin.sum_univ_five] at hX3 hnbX hTX hTY hTXY
    omega

end FleischnerAux

namespace FleischnerAux

open Classical

lemma nb_true {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : nb G v (fun _ => True) = G.degree v := by
  unfold nb cnt
  rw [Fintype.sum_prod_type, ← card_neighborFinset_eq_degree]
  calc _ = ∑ a, if G.Adj a v then 1 else 0 := by
        refine sum_congr rfl fun a _ => ?_
        rw [Fintype.sum_eq_single v]
        · simp
        · intro b hb
          simp [hb]
    _ = (univ.filter fun a => G.Adj a v).card := (card_filter _ _).symm
    _ = _ := by
        congr 1
        ext a
        simp [G.adj_comm]

lemma exists_out {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : V → Prop) (h : nb G v S < G.degree v) : ∃ x, G.Adj x v ∧ ¬ S x := by
  by_contra hno
  push Not at hno
  have : nb G v S = nb G v (fun _ => True) := by
    refine cnt_congr _ _ _ fun a b hab => ?_
    constructor
    · rintro ⟨_, hb⟩; exact ⟨trivial, hb⟩
    · rintro ⟨_, rfl⟩; exact ⟨hno a hab, rfl⟩
  rw [this, nb_true] at h
  omega

lemma nb_le_dc {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) (S : V → Prop) (hv : ¬ S v) :
    nb G v S ≤ dc G S :=
  cnt_le _ _ _ fun a b _ h => ⟨h.1, by rw [h.2]; exact hv⟩

lemma exists_in {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) (S : V → Prop)
    (h : 1 ≤ nb G v S) : ∃ x, G.Adj x v ∧ S x := by
  obtain ⟨a, b, hab, ha, rfl⟩ := exists_of_cnt G (fun a b => S a ∧ b = v) (by unfold nb at h; omega)
  exact ⟨a, hab, ha⟩

lemma cnt_transfer {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v u w : V)
    (G' : SimpleGraph (Option V))
    (hss : ∀ a b, G'.Adj (some a) (some b) ↔ G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w))
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) (R : V → V → Prop) :
    cnt G' (fun p q => R (p.getD v) (q.getD v)) = cnt G R := by
  unfold cnt
  rw [← card_filter, ← card_filter]
  apply Finset.card_bij (fun p _ => (p.1.getD v, p.2.getD v))
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H2_R1.sp_adj_map
      G v u w G' hss hns hu hw hp.1, hp.2⟩
  · rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq h
    simp only [mem_filter, mem_univ, true_and] at hp hq
    simp only [Prod.mk.injEq] at h ⊢
    have hm := OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H2_R1.sp_map_injOn
      G v u w G' hss hns huw s(p1, p2) hp.1 s(q1, q2) hq.1 (by simp [h.1, h.2])
    rcases Sym2.eq_iff.mp hm with h' | h'
    · exact h'
    · exfalso
      have hq' := OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H2_R1.sp_adj_map
        G v u w G' hss hns hu hw hq.1
      apply hq'.ne
      rw [← h.1, h'.1]
  · rintro ⟨b1, b2⟩ hb
    simp only [mem_filter, mem_univ, true_and] at hb
    obtain ⟨e', he', hmap⟩ :=
      OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H2_R1.sp_map_surj
        G v u w G' hss hns s(b1, b2) hb.1
    induction e' using Sym2.ind with
    | _ p q =>
    rw [Sym2.map_mk] at hmap
    rcases Sym2.eq_iff.mp hmap with h' | h'
    · refine ⟨(p, q), ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        rw [h'.1, h'.2]
        exact ⟨he', hb.2⟩
      · simp [h'.1, h'.2]
    · refine ⟨(q, p), ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        rw [h'.1, h'.2]
        exact ⟨he'.symm, hb.2⟩
      · simp [h'.1, h'.2]

lemma none_cnt {V : Type} [Fintype V] (u w : V) (G' : SimpleGraph (Option V))
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (huw : u ≠ w) (Q : Option V → Prop) :
    cnt G' (fun a b => a = none ∧ Q b) =
      (if Q (some u) then 1 else 0) + (if Q (some w) then 1 else 0) := by
  unfold cnt
  rw [Fintype.sum_eq_add (none, some u) (none, some w) (by simp [huw])]
  · simp [hns]
  · rintro ⟨a, b⟩ hp
    rcases a with _ | a
    · rcases b with _ | b
      · simp
      · rw [if_neg]
        rintro ⟨hadj, -, -⟩
        rcases (hns b).mp hadj with rfl | rfl
        · exact hp.1 rfl
        · exact hp.2 rfl
    · simp

lemma split_good {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v u w : V)
    (huw : u ≠ w) (hu : G.Adj v u) (hw : G.Adj v w) (hbr : ∀ S, dc G S ≠ 1)
    (hgood : ∀ Y : V → Prop, ¬ Y v → Y u → Y w → dc G Y ≠ 3) :
    (SimpleGraph.fromRel (fun x y : Option V => match x, y with
          | some a, some b => G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w)
          | none, some b => b = u ∨ b = w
          | _, _ => False)).IsBridgeless := by
  set G' : SimpleGraph (Option V) := SimpleGraph.fromRel (fun x y : Option V => match x, y with
          | some a, some b => G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w)
          | none, some b => b = u ∨ b = w
          | _, _ => False) with hG'
  have hss : ∀ a b, G'.Adj (some a) (some b) ↔
      G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w) := by
    intro a b
    rw [hG', fromRel_adj]
    simp only [ne_eq, Option.some.injEq]
    constructor
    · rintro ⟨_, h | h⟩
      · exact h
      · refine ⟨h.1.symm, ?_, ?_⟩
        · rw [Sym2.eq_swap]; exact h.2.1
        · rw [Sym2.eq_swap]; exact h.2.2
    · intro h
      exact ⟨h.1.ne, Or.inl h⟩
  have hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w := by
    intro b
    rw [hG', fromRel_adj]
    simp
  by_contra hnb
  obtain ⟨S', hS'⟩ := exists_dc_one G' hnb
  by_cases h1 : (S' none ↔ S' (some v))
  · have e : dc G' S' = cnt G' (fun p q => (fun a b => S' (some a) ∧ ¬ S' (some b))
        (p.getD v) (q.getD v)) := by
      refine cnt_congr _ _ _ fun p q _ => ?_
      rcases p with _ | p <;> rcases q with _ | q <;> simp [h1]
    have e2 := e.trans (cnt_transfer G v u w G' hss hns hu hw huw
      (fun a b => S' (some a) ∧ ¬ S' (some b)))
    exact hbr (fun a => S' (some a)) (e2.symm.trans hS')
  obtain ⟨S'', hS'', hn, hv⟩ : ∃ S'' : Option V → Prop, dc G' S'' = 1 ∧ S'' none ∧
      ¬ S'' (some v) := by
    by_cases h2 : S' none
    · exact ⟨S', hS', h2, by tauto⟩
    · exact ⟨fun z => ¬ S' z, by rw [dc_compl]; exact hS', h2, by tauto⟩
  have eT : dc G' (fun z => z ≠ none ∧ S'' z) = dc G (fun a => S'' (some a)) := by
    unfold dc
    refine (cnt_congr G' _ (fun p q => (fun a b => S'' (some a) ∧ ¬ S'' (some b))
      (p.getD v) (q.getD v)) fun p q _ => ?_).trans
      (cnt_transfer G v u w G' hss hns hu hw huw (fun a b => S'' (some a) ∧ ¬ S'' (some b)))
    rcases p with _ | p <;> rcases q with _ | q <;> simp [hv]
  have tog := cnt_add G' (fun a b => S'' a ∧ ¬ S'' b)
    (fun a b => (a ≠ none ∧ S'' a) ∧ b = none)
    (fun a b => (a ≠ none ∧ S'' a) ∧ ¬ (b ≠ none ∧ S'' b))
    (fun a b => a = none ∧ ¬ (b ≠ none ∧ S'' b)) (by
      intro a b hab
      rcases a with _ | a <;> rcases b with _ | b
      · exact absurd hab (G'.irrefl)
      · simp [hn]
      · simp [hn]
      · simp)
  rw [← cnt_swap G' (fun a b => (a ≠ none ∧ S'' a) ∧ b = none)] at tog
  have e1 := none_cnt u w G' hns huw (fun b => b ≠ none ∧ S'' b)
  have e2 := none_cnt u w G' hns huw (fun b => ¬ (b ≠ none ∧ S'' b))
  have e3 : cnt G' (fun a b => (b ≠ none ∧ S'' b) ∧ a = none) =
      cnt G' (fun a b => a = none ∧ (b ≠ none ∧ S'' b)) :=
    cnt_congr _ _ _ fun a b _ => and_comm
  unfold dc at hS'' eT
  rw [e3, e1, e2, hS''] at tog
  rw [eT] at tog
  have hb1 := hbr (fun a => S'' (some a))
  have hg := hgood (fun a => S'' (some a)) hv
  unfold dc at hb1 hg
  by_cases hsu : S'' (some u) <;> by_cases hsw : S'' (some w) <;> simp [hsu, hsw] at tog hg hb1 <;> omega

end FleischnerAux

theorem OMA.solution : OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H2_R1.H2 := by
  intro V _ _ G _ hb v hdeg
  have hbr : ∀ S, FleischnerAux.dc G S ≠ 1 := FleischnerAux.dc_ne_one G hb
  by_cases hB : ∃ S : V → Prop, ¬ S v ∧ FleischnerAux.dc G S ≤ 3 ∧ 3 ≤ FleischnerAux.nb G v S
  · obtain ⟨S, hSv, hS3, hSn⟩ := hB
    obtain ⟨u, hu, huS⟩ := FleischnerAux.exists_in G v S (by omega)
    obtain ⟨x, hx, hxS⟩ := FleischnerAux.exists_out G v S
      (by have := FleischnerAux.nb_le_dc G v S hSv; omega)
    have hux : u ≠ x := fun h => hxS (h ▸ huS)
    refine ⟨u, x, hux, hu.symm, hx.symm,
      FleischnerAux.split_good G v u x hux hu.symm hx.symm hbr ?_⟩
    intro Y hYv huY hxY hY3
    exact FleischnerAux.key G v u x S Y hSv hYv huS huY hxS hxY hu hx hbr hY3
      (Or.inl ⟨hS3, hSn⟩)
  · push Not at hB
    by_cases hC : ∃ X : V → Prop, ¬ X v ∧ FleischnerAux.dc G X = 3 ∧ 2 ≤ FleischnerAux.nb G v X
    · obtain ⟨X, hXv, hX3, hXn⟩ := hC
      have hlt := hB X hXv (by omega)
      obtain ⟨u, hu, huX⟩ := FleischnerAux.exists_in G v X (by omega)
      obtain ⟨x, hx, hxX⟩ := FleischnerAux.exists_out G v X (by omega)
      have hux : u ≠ x := fun h => hxX (h ▸ huX)
      refine ⟨u, x, hux, hu.symm, hx.symm,
        FleischnerAux.split_good G v u x hux hu.symm hx.symm hbr ?_⟩
      intro Y hYv huY hxY hY3
      exact FleischnerAux.key G v u x X Y hXv hYv huX huY hxX hxY hu hx hbr hY3
        (Or.inr ⟨hX3, hXn, hB⟩)
    · push Not at hC
      have h2 : 1 < (G.neighborFinset v).card := by
        rw [card_neighborFinset_eq_degree]; omega
      obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp h2
      rw [mem_neighborFinset] at hu hw
      refine ⟨u, w, huw, hu, hw, FleischnerAux.split_good G v u w huw hu hw hbr ?_⟩
      intro Y hYv huY hwY hY3
      have h2 : 2 ≤ FleischnerAux.nb G v Y :=
        FleischnerAux.two_le_cnt G _ (u, v) (w, v) (by simp [huw])
          ⟨hu.symm, huY, rfl⟩ ⟨hw.symm, hwY, rfl⟩
      have := hC Y hYv hY3
      omega
