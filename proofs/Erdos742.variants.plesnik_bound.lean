import FormalConjectures.ErdosProblems.«742»
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! A counting proof of Plesník’s upper bound for diameter-two-critical graphs. -/

open SimpleGraph Finset
open scoped BigOperators

namespace PlesnikBound

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem degree_sum_le_card_of_unique {a b x : V} (hab : ¬ G.Adj a b)
    (hu : ∀ y, G.Adj a y → G.Adj b y → y = x) :
    G.degree a + G.degree b ≤ Fintype.card V := by
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  have hU : A ∪ B ⊆ univ.erase a := by
    intro y hy
    simp only [mem_erase, mem_univ, and_true]
    intro hya
    subst y
    rcases mem_union.mp hy with h | h
    · exact G.irrefl ((G.mem_neighborFinset a a).mp h)
    · exact hab ((G.mem_neighborFinset b a).mp h).symm
  have hI : A ∩ B ⊆ {x} := by
    intro y hy
    exact mem_singleton.mpr (hu y ((G.mem_neighborFinset a y).mp (mem_inter.mp hy).1)
      ((G.mem_neighborFinset b y).mp (mem_inter.mp hy).2))
  have hcU := card_le_card hU
  have hcI := card_le_card hI
  rw [card_erase_of_mem (mem_univ a), card_univ] at hcU
  rw [card_singleton] at hcI
  have habc := card_union_add_card_inter A B
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
  change G.degree a + G.degree b ≤ _
  rw [← G.card_neighborFinset_eq_degree a, ← G.card_neighborFinset_eq_degree b]
  change A.card + B.card ≤ _
  omega

private theorem common_of_large_degree {u v : V}
    (hu : Fintype.card V < 2 * G.degree u)
    (hv : Fintype.card V < 2 * G.degree v) :
    ∃ t, G.Adj u t ∧ G.Adj v t := by
  let A := G.neighborFinset u
  let B := G.neighborFinset v
  have hU : (A ∪ B).card ≤ Fintype.card V := card_le_univ _
  have hEq := card_union_add_card_inter A B
  change _ < 2 * A.card at hu
  change _ < 2 * B.card at hv
  have hi : 0 < (A ∩ B).card := by omega
  obtain ⟨t, ht⟩ := card_pos.mp hi
  exact ⟨t, (G.mem_neighborFinset u t).mp (mem_inter.mp ht).1,
    (G.mem_neighborFinset v t).mp (mem_inter.mp ht).2⟩

private theorem ediam_two (hd : G.diam = 2) : G.ediam = 2 := by
  have h : G.ediam.toNat = 2 := hd
  exact (ENat.toNat_eq_iff (by decide : (2 : ℕ) ≠ 0)).mp h

private theorem failed_pair (hG : Erdos742.IsDiameter2Critical G) {u v : V}
    (huv : G.Adj u v) :
    ∃ a b, a ≠ b ∧ ¬ (G.deleteEdges {s(u, v)}).Adj a b ∧
      (G.deleteEdges {s(u, v)}).commonNeighbors a b = ∅ := by
  letI : Nonempty V := ⟨u⟩
  let D := G.deleteEdges {s(u, v)}
  have he : s(u, v) ∈ G.edgeSet := huv
  have hneq : D.diam ≠ 2 := hG.2 _ he
  have hmono : G.ediam ≤ D.ediam := ediam_anti (deleteEdges_le (G := G) _)
  rw [ediam_two G hG.1] at hmono
  have hlt : 2 < D.ediam := lt_of_le_of_ne hmono (fun h => hneq (by simp [diam, ← h]))
  obtain ⟨a, b, hab⟩ := D.exists_edist_eq_ediam_of_finite
  have hab' : 2 < D.edist a b := hab ▸ hlt
  exact ⟨a, b, two_lt_edist_iff.mp hab'⟩

private theorem keep_edge {u v a b : V} (h : G.Adj a b) (hne : s(a, b) ≠ s(u, v)) :
    (G.deleteEdges {s(u, v)}).Adj a b :=
  deleteEdges_adj.mpr ⟨h, by simpa using hne⟩

private theorem two_step_uses_edge {u v a b z : V}
    (h : (G.deleteEdges {s(u, v)}).commonNeighbors a b = ∅)
    (haz : G.Adj a z) (hbz : G.Adj b z) :
    s(a, z) = s(u, v) ∨ s(b, z) = s(u, v) := by
  by_contra! he
  have hz : z ∈ (G.deleteEdges {s(u, v)}).commonNeighbors a b :=
    (mem_commonNeighbors _).mpr ⟨keep_edge G haz he.1, keep_edge G hbz he.2⟩
  simpa [h] using hz

private theorem deleted_pair_nonadj {u v a b : V}
    (hdel : ¬ (G.deleteEdges {s(u, v)}).Adj a b)
    (hcommon : (G.deleteEdges {s(u, v)}).commonNeighbors a b = ∅)
    (h : ∃ t, G.Adj u t ∧ G.Adj v t) : ¬ G.Adj a b := by
  intro hab
  have e : s(a, b) = s(u, v) := by
    by_contra he
    exact hdel (keep_edge G hab he)
  obtain ⟨t, hut, hvt⟩ := h
  rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases two_step_uses_edge G hcommon hut hvt with hh | hh
    · simpa [Sym2.eq_iff, hut.ne.symm, hvt.ne.symm] using hh
    · simpa [Sym2.eq_iff, hut.ne.symm, hvt.ne.symm, hab.ne, hab.ne.symm] using hh
  · rcases two_step_uses_edge G hcommon hvt hut with hh | hh
    · simpa [Sym2.eq_iff, hut.ne.symm, hvt.ne.symm, hab.ne, hab.ne.symm] using hh
    · simpa [Sym2.eq_iff, hut.ne.symm, hvt.ne.symm] using hh

private theorem common_unique_of_first {u v a b x : V}
    (hab : a ≠ b) (hc : (G.deleteEdges {s(u, v)}).commonNeighbors a b = ∅)
    (he : s(a, x) = s(u, v)) :
    ∀ y, G.Adj a y → G.Adj b y → y = x := by
  intro y hay hby
  rcases two_step_uses_edge G hc hay hby with h | h
  · simpa [Sym2.eq_iff, hay.ne.symm] using h.trans he.symm
  · have hm : a ∈ s(b, y) := by rw [h, ← he]; simp
    exact False.elim (by simpa [hab, hay.ne] using hm)

private theorem unique_pair_through_high_edge (hG : Erdos742.IsDiameter2Critical G)
    {u v : V} (huv : G.Adj u v)
    (hu : Fintype.card V < 2 * G.degree u)
    (hv : Fintype.card V < 2 * G.degree v) :
    (∃ w, 2 * G.degree w ≤ Fintype.card V ∧ ¬ G.Adj u w ∧ G.Adj w v ∧
      ∀ x, G.Adj u x → G.Adj w x → x = v) ∨
    (∃ w, 2 * G.degree w ≤ Fintype.card V ∧ ¬ G.Adj v w ∧ G.Adj w u ∧
      ∀ x, G.Adj v x → G.Adj w x → x = u) := by
  obtain ⟨a, b, hab, hdel, hc⟩ := failed_pair G hG huv
  have hn := deleted_pair_nonadj G hdel hc (common_of_large_degree G hu hv)
  have hle : G.edist a b ≤ 2 := (G.edist_le_ediam).trans_eq (ediam_two G hG.1)
  have hd : G.edist a b = 2 := le_antisymm hle (by
    by_contra! hlt
    exact (edist_le_one_iff_adj_or_eq.mp (Order.le_of_lt_add_one hlt)).elim hn hab)
  obtain ⟨x, hx⟩ := (edist_eq_two_iff.mp hd).2.2
  obtain ⟨hax, hbx⟩ := (G.mem_commonNeighbors).mp hx
  have forward (a b x : V) (hab : a ≠ b) (hn : ¬ G.Adj a b) (hbx : G.Adj b x)
      (hc : (G.deleteEdges {s(u, v)}).commonNeighbors a b = ∅)
      (he : s(a, x) = s(u, v)) :
      (∃ w, 2 * G.degree w ≤ Fintype.card V ∧ ¬ G.Adj u w ∧ G.Adj w v ∧
        ∀ x, G.Adj u x → G.Adj w x → x = v) ∨
      (∃ w, 2 * G.degree w ≤ Fintype.card V ∧ ¬ G.Adj v w ∧ G.Adj w u ∧
        ∀ x, G.Adj v x → G.Adj w x → x = u) := by
    have huniq := common_unique_of_first G hab hc he
    have hbd := degree_sum_le_card_of_unique G hn huniq
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨b, by omega, hn, hbx, huniq⟩
    · exact Or.inr ⟨b, by omega, hn, hbx, huniq⟩
  rcases two_step_uses_edge G hc hax hbx with he | he
  · exact forward a b x hab hn hbx hc he
  · exact forward b a x hab.symm (fun h => hn h.symm) hax
      (by rwa [commonNeighbors_symm]) he

end PlesnikBound

namespace PlesnikBound

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem edge_partition_count (P : V → Prop) [DecidablePred P] :
    2 * G.edgeFinset.card =
      2 * (G.induce {v | P v}).edgeFinset.card +
        Fintype.card {p : {v // P v} × {v // ¬ P v} // G.Adj p.1.val p.2.val} +
        ∑ v : {v // ¬ P v}, G.degree v.val := by
  let H := {v // P v}
  let L := {v // ¬ P v}
  let K := G.induce {v | P v}
  let C := {p : H × L // G.Adj p.1.val p.2.val}
  let DH := {d : G.Dart // P d.fst}
  let DL := {d : G.Dart // ¬ P d.fst}
  let DHH := {d : DH // P d.val.snd}
  let DHL := {d : DH // ¬ P d.val.snd}
  let highEquiv : DHH ≃ K.Dart :=
    { toFun := fun d => ⟨(⟨d.val.val.fst, d.val.property⟩, ⟨d.val.val.snd, d.property⟩), d.val.val.adj⟩
      invFun := fun d => ⟨⟨⟨(d.fst.val, d.snd.val), d.adj⟩, d.fst.property⟩, d.snd.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let crossEquiv : DHL ≃ C :=
    { toFun := fun d => ⟨(⟨d.val.val.fst, d.val.property⟩, ⟨d.val.val.snd, d.property⟩), d.val.val.adj⟩
      invFun := fun d => ⟨⟨⟨(d.val.1.val, d.val.2.val), d.property⟩, d.val.1.property⟩, d.val.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let lowEquiv : DL ≃ Σ v : L, G.neighborSet v.val :=
    { toFun := fun d => ⟨⟨d.val.fst, d.property⟩, ⟨d.val.snd, d.val.adj⟩⟩
      invFun := fun d => ⟨⟨(d.fst.val, d.snd.val), d.snd.property⟩, d.fst.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc₁ : Fintype.card DH + Fintype.card DL = Fintype.card G.Dart := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun d : G.Dart => P d.fst))
  have hc₂ : Fintype.card DHH + Fintype.card DHL = Fintype.card DH := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun d : DH => P d.val.snd))
  have hlow : Fintype.card DL = ∑ v : L, G.degree v.val := by
    rw [Fintype.card_congr lowEquiv, Fintype.card_sigma]
    simp_rw [G.card_neighborSet_eq_degree]
  have h := calc
    2 * G.edgeFinset.card = Fintype.card G.Dart := G.dart_card_eq_twice_card_edges.symm
    _ = (Fintype.card DHH + Fintype.card DHL) + Fintype.card DL := by rw [hc₂, hc₁]
    _ = 2 * K.edgeFinset.card + Fintype.card C + ∑ v : L, G.degree v.val := by
      rw [Fintype.card_congr highEquiv, Fintype.card_congr crossEquiv, K.dart_card_eq_twice_card_edges, hlow]
  exact h

private theorem dart_diagonal_count {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] :
    2 * K.edgeFinset.card + Fintype.card W ≤ Fintype.card W * Fintype.card W := by
  let f : K.Dart ⊕ W → W × W := Sum.elim Dart.toProd (fun w => (w, w))
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Dart.toProd_injective hab)
      | inr b =>
        have h₁ : a.fst = b := congrArg Prod.fst hab
        have h₂ : a.snd = b := congrArg Prod.snd hab
        exact (a.fst_ne_snd (h₁.trans h₂.symm)).elim
    | inr a =>
      cases b with
      | inl b =>
        have h₁ : a = b.fst := congrArg Prod.fst hab
        have h₂ : a = b.snd := congrArg Prod.snd hab
        exact (b.fst_ne_snd (h₁.symm.trans h₂)).elim
      | inr b => exact congrArg Sum.inr (congrArg Prod.fst hab)
  simpa only [Fintype.card_sum, Fintype.card_prod, K.dart_card_eq_twice_card_edges] using
    Fintype.card_le_of_injective f hf

private theorem two_high_count (hG : Erdos742.IsDiameter2Critical G) :
    let P := fun v => Fintype.card V < 2 * G.degree v
    let H := {v // P v}
    let L := {v // ¬ P v}
    (G.induce {v | P v}).edgeFinset.card +
      Fintype.card {p : H × L // G.Adj p.1.val p.2.val} ≤ Fintype.card H * Fintype.card L := by
  let P := fun v => Fintype.card V < 2 * G.degree v
  let H := {v // P v}
  let L := {v // ¬ P v}
  let K := G.induce {v | P v}
  let C := {p : H × L // G.Adj p.1.val p.2.val}
  change K.edgeFinset.card + Fintype.card C ≤ Fintype.card H * Fintype.card L
  have hw (e : K.edgeSet) :
      ∃ p : H × L, ¬ G.Adj p.1.val p.2.val ∧
        ∃ z : H, e.val = s(p.1, z) ∧ G.Adj p.1.val z.val ∧ G.Adj p.2.val z.val ∧
          ∀ x, G.Adj p.1.val x → G.Adj p.2.val x → x = z.val := by
    obtain ⟨e, he⟩ := e
    obtain ⟨u, v⟩ := e
    change G.Adj u.val v.val at he
    rcases unique_pair_through_high_edge G hG he u.property v.property with h | h
    · obtain ⟨w, hw, hn, hwv, hu⟩ := h
      exact ⟨(u, ⟨w, not_lt.mpr hw⟩), hn, v, rfl, he, hwv, hu⟩
    · obtain ⟨w, hw, hn, hwu, hu⟩ := h
      exact ⟨(v, ⟨w, not_lt.mpr hw⟩), hn, u, Sym2.eq_swap, he.symm, hwu, hu⟩
  classical
  choose f hf using hw
  have hinj : Function.Injective f := by
    intro e e' h
    obtain ⟨_, z, he, _, _, hz⟩ := hf e
    obtain ⟨_, z', he', ha', hb', _⟩ := hf e'
    have hz' : z' = z := Subtype.ext (hz z'.val (by simpa only [h] using ha')
      (by simpa only [h] using hb'))
    exact Subtype.ext (he.trans (by rw [h]; simpa only [hz'] using he'.symm))
  let g : K.edgeSet ⊕ C → H × L := Sum.elim f Subtype.val
  have hg : Function.Injective g := by
    intro e e' h
    cases e with
    | inl e =>
      cases e' with
      | inl e' => exact congrArg Sum.inl (hinj h)
      | inr e' =>
        exact ((hf e).1 (by simpa only [show f e = e'.val from h] using e'.property)).elim
    | inr e =>
      cases e' with
      | inl e' =>
        exact ((hf e').1 (by simpa only [show f e' = e.val from h.symm] using e.property)).elim
      | inr e' => exact congrArg Sum.inr (Subtype.ext h)
  simpa only [Fintype.card_sum, Fintype.card_prod, K.card_edgeSet] using
    Fintype.card_le_of_injective g hg

private theorem three_le_order (hd : G.diam = 2) : 3 ≤ Fintype.card V := by
  letI : Nontrivial V := G.nontrivial_of_diam_ne_zero (by omega)
  obtain ⟨a, b, hab⟩ := G.exists_edist_eq_ediam_of_finite
  obtain ⟨hne, _, ⟨z, hz⟩⟩ := edist_eq_two_iff.mp (hab.trans (ediam_two G hd))
  obtain ⟨ha, hb⟩ := (G.mem_commonNeighbors).mp hz
  simpa [hne, ha.ne, hb.ne] using (card_le_univ ({a, b, z} : Finset V))

private theorem numeric_bound (n h l e : ℕ) (hn : 3 ≤ n) (hp : h + l = n)
    (hb : 4 * e + n ≤ n * n + h * l + l) :
    (e : ℝ) < 3 * (n : ℝ) * ((n : ℝ) - 1) / 8 := by
  have hle : h ≤ n := by omega
  by_cases hn5 : 5 ≤ n
  · have hb' : 4 * (e : ℝ) + n ≤ (n : ℝ) * n + (h : ℝ) * l + l := by exact_mod_cast hb
    have hp' : (h : ℝ) + l = n := by exact_mod_cast hp
    have hn5' : (5 : ℝ) ≤ n := by exact_mod_cast hn5
    have hmul : 4 * ((h : ℝ) * l + l) ≤ ((n : ℝ) + 1)^2 := by
      rw [← hp']
      nlinarith [sq_nonneg ((h : ℝ) + 1 - l)]
    have hstrict : ((n : ℝ) + 1)^2 < 2 * (n : ℝ) * ((n : ℝ) - 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn5') (show (0 : ℝ) ≤ n by positivity)]
    linarith
  · interval_cases n
    · have he : e ≤ 2 := by interval_cases h <;> omega
      have he' : (e : ℝ) ≤ 2 := by exact_mod_cast he
      norm_num
      linarith
    · have he : e ≤ 4 := by interval_cases h <;> omega
      have he' : (e : ℝ) ≤ 4 := by exact_mod_cast he
      norm_num
      linarith

end PlesnikBound

theorem OMA.solution : type_of% @Erdos742.variants.plesnik_bound := by
  intro V instV decV G decG hG
  let n := Fintype.card V
  let P := fun v => n < 2 * G.degree v
  let H := {v // P v}
  let L := {v // ¬ P v}
  let K := G.induce {v | P v}
  let C := {p : H × L // G.Adj p.1.val p.2.val}
  let h := Fintype.card H
  let l := Fintype.card L
  let e := G.edgeFinset.card
  let a := K.edgeFinset.card
  let c := Fintype.card C
  let low := ∑ v : L, G.degree v.val
  have hp : h + l = n := by
    change Fintype.card H + Fintype.card L = _
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl P)
  have hc : 2 * e = 2 * a + c + low := PlesnikBound.edge_partition_count G P
  have hh : a + c ≤ h * l := PlesnikBound.two_high_count G hG
  have hd : 2 * a + h ≤ h * h := PlesnikBound.dart_diagonal_count K
  have hlow : 2 * low ≤ l * n := by
    change 2 * (∑ v : L, G.degree v.val) ≤ _
    rw [mul_sum]
    calc
      _ ≤ ∑ _ : L, n := sum_le_sum (fun v _ => Nat.le_of_not_lt v.property)
      _ = l * n := by simp [l, Nat.mul_comm]
  have ha : 4 * e + h ≤ 2 * (h * l) + h * h + l * n := by omega
  have hiden : 2 * (h * l) + h * h + l * n = n * n + h * l := by
    rw [← hp]
    ring
  rw [hiden] at ha
  exact PlesnikBound.numeric_bound n h l e (PlesnikBound.three_le_order G hG.1) hp (by omega)
