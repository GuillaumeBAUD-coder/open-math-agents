import FormalConjectures.ErdosProblems.«639»
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-! The extremal result is due to Peter Keevash and Benny Sudakov,
“On the number of edges not covered by monochromatic copies of a fixed graph,”
J. Combin. Theory Ser. B 90 (2004), 41–53.
https://people.maths.ox.ac.uk/keevash/papers/nim-edges-journal.pdf

The induction below uses their observation about the colors from the apex
of an uncovered triangle. It counts the remaining edges using a four-vertex core.
-/

open Finset SimpleGraph
open scoped Sym2

namespace OMA

private def ClearEdge {V : Type} (C : Sym2 V → Fin 2) (a b : V) : Prop :=
  a ≠ b ∧ ¬ ∃ t, t ≠ a ∧ t ≠ b ∧ C s(a, t) = C s(a, b) ∧ C s(b, t) = C s(a, b)

private lemma clear_symm {V : Type} {C : Sym2 V → Fin 2} {a b : V}
    (h : ClearEdge C a b) : ClearEdge C b a := by
  refine ⟨h.1.symm, ?_⟩
  rintro ⟨t, htb, hta, hbt, hat⟩
  have hswap : C s(b, a) = C s(a, b) := congrArg C Sym2.eq_swap
  exact h.2 ⟨t, hta, htb, hat.trans hswap, hbt.trans hswap⟩

private def uncoveredGraph {V : Type} (C : Sym2 V → Fin 2) : SimpleGraph V where
  Adj := ClearEdge C
  symm.symm _ _ := clear_symm
  loopless := ⟨fun _ h => h.1 rfl⟩

private noncomputable instance {V : Type} (C : Sym2 V → Fin 2) :
    DecidableRel (uncoveredGraph C).Adj := Classical.decRel _

private lemma color_symm {V : Type} (C : Sym2 V → Fin 2) (a b : V) :
    C s(a, b) = C s(b, a) := congrArg C Sym2.eq_swap

private lemma color_eq_of_ne (r b c : Fin 2) (hrb : r ≠ b) (hcr : c ≠ r) : c = b :=
  (by decide : ∀ r b c : Fin 2, r ≠ b → c ≠ r → c = b) r b c hrb hcr

private lemma color_eq_or_eq (r b c : Fin 2) (hrb : r ≠ b) : c = r ∨ c = b :=
  (by decide : ∀ r b c : Fin 2, r ≠ b → c = r ∨ c = b) r b c hrb

private lemma no_clear_of_mono {V : Type} {C : Sym2 V → Fin 2} {a b t : V}
    {k : Fin 2} (hta : t ≠ a) (htb : t ≠ b) (hab : C s(a, b) = k)
    (hat : C s(a, t) = k) (hbt : C s(b, t) = k) : ¬ ClearEdge C a b :=
  fun h => h.2 ⟨t, hta, htb, hat.trans hab.symm, hbt.trans hab.symm⟩

private lemma clear_forces_color {V : Type} {C : Sym2 V → Fin 2} {a b t : V}
    {r k : Fin 2} (h : ClearEdge C a b) (hta : t ≠ a) (htb : t ≠ b)
    (hab : C s(a, b) = r) (hat : C s(a, t) = r) (hrk : r ≠ k) : C s(b, t) = k :=
  color_eq_of_ne r k _ hrk fun hbt => no_clear_of_mono hta htb hab hat hbt h

private theorem clearEdge_iff_mem {n : ℕ} {C : Sym2 (Fin n) → Fin 2} {a b : Fin n} :
    ClearEdge C a b ↔ s(a, b) ∈ Erdos639.uncoveredEdges C := by
  change ClearEdge C a b ↔ ¬s(a, b).IsDiag ∧ ∀ x y, s(a, b) = s(x, y) →
    ¬ ∃ t, t ≠ x ∧ t ≠ y ∧ C s(x, t) = C s(a, b) ∧ C s(y, t) = C s(a, b)
  rw [Sym2.mk_isDiag_iff]
  constructor
  · intro h
    refine ⟨h.1, fun x y hxy => ?_⟩
    rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.2
    · exact fun ⟨t, htb, hta, hbt, hat⟩ => h.2 ⟨t, hta, htb, hat, hbt⟩
  · exact fun h => ⟨h.1, h.2 a b rfl⟩

private lemma uncovered_ncard {n : ℕ} (C : Sym2 (Fin n) → Fin 2) :
    (Erdos639.uncoveredEdges C).ncard = (uncoveredGraph C).edgeFinset.card := by
  have h : Erdos639.uncoveredEdges C = (uncoveredGraph C).edgeSet := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b => exact clearEdge_iff_mem.symm
  rw [h, ← coe_edgeFinset, Set.ncard_coe_finset]

private lemma clear_pull {V W : Type} {C : Sym2 V → Fin 2} (f : W ↪ V) {a b : W}
    (h : ClearEdge C (f a) (f b)) : ClearEdge (C ∘ Sym2.map f) a b := by
  refine ⟨fun hab => h.1 (congrArg f hab), ?_⟩
  rintro ⟨t, hta, htb, hat, hbt⟩
  exact h.2 ⟨f t, fun ht => hta (f.injective ht), fun ht => htb (f.injective ht), hat, hbt⟩

private def cycleFiveColor (e : Sym2 (Fin 5)) : Fin 2 :=
  if e ∈ ({s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0)} : Finset _) then 0 else 1

private instance {V : Type} [Fintype V] [DecidableEq V] (C : Sym2 V → Fin 2) (a b : V) :
    Decidable (ClearEdge C a b) := inferInstanceAs (Decidable (_ ∧ ¬ ∃ _t : V, _))

private lemma cycleFive_clear (a b : Fin 5) (h : a ≠ b) : ClearEdge cycleFiveColor a b :=
  (by decide : ∀ a b : Fin 5, a ≠ b → ClearEdge cycleFiveColor a b) a b h

private theorem small_attained (n : ℕ) (hn : n ≤ 5) :
    ∃ C : Sym2 (Fin n) → Fin 2, (Erdos639.uncoveredEdges C).ncard = n.choose 2 := by
  classical
  let f : Fin n ↪ Fin 5 := Fin.castLEEmb hn
  let C := cycleFiveColor ∘ Sym2.map f
  refine ⟨C, ?_⟩
  rw [uncovered_ncard]
  have h : uncoveredGraph C = ⊤ := by
    ext a b
    change ClearEdge C a b ↔ a ≠ b
    exact ⟨fun h => h.1, fun hn => clear_pull f (cycleFive_clear _ _ (f.injective.ne hn))⟩
  have he : (uncoveredGraph C).edgeFinset = (⊤ : SimpleGraph (Fin n)).edgeFinset :=
    edgeFinset_inj.mpr h
  rw [he, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

private theorem mantel_bound {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.CliqueFree 3) : G.edgeFinset.card ≤ Fintype.card V ^ 2 / 4 := by
  have hb := h.card_edgeFinset_le (r := 2)
  have hm : Fintype.card V % 2 ≤ 1 := by omega
  have hz : (Fintype.card V % 2).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp only [Nat.reduceSub, Nat.mul_one, Nat.reduceMul, hz, Nat.add_zero] at hb
  exact hb.trans (Nat.div_le_div_right (Nat.sub_le _ _))

/-- At the vertex incident to the two red edges, every edge leaving the triangle is blue. -/
private lemma apex_color {V : Type} {C : Sym2 V → Fin 2} {x y z v : V} {r b : Fin 2}
    (hxy : ClearEdge C x y) (hxz : ClearEdge C x z) (hyz : ClearEdge C y z)
    (cxy : C s(x, y) = r) (cxz : C s(x, z) = r) (cyz : C s(y, z) = b)
    (hrb : r ≠ b) (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) :
    C s(x, v) = b := by
  apply color_eq_of_ne r b _ hrb
  intro cxv
  have cyv := clear_forces_color hxy hvx hvy cxy cxv hrb
  have czv := clear_forces_color hxz hvx hvz cxz cxv hrb
  exact no_clear_of_mono hvy hvz cyz cyv czv hyz

private lemma card_core_edges {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (G.edgeFinset ∩ S.sym2).card ≤ S.card.choose 2 := by
  rw [← G.filter_edgeFinset_toFinset_subset S,
    G.card_filter_edgeFinset_toFinset_subset S]
  rw [← Fintype.card_coe S]
  exact card_edgeFinset_le_card_choose_two

private lemma card_core_edges_strict {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (hn : ¬ G.Adj a b) :
    (G.edgeFinset ∩ S.sym2).card < S.card.choose 2 := by
  rw [← G.filter_edgeFinset_toFinset_subset S, G.card_filter_edgeFinset_toFinset_subset S,
    ← Fintype.card_coe S, ← card_edgeFinset_top_eq_card_choose_two]
  apply Finset.card_lt_card
  rw [edgeFinset_ssubset_edgeFinset, lt_top_iff_ne_top]
  intro h
  apply hn
  have h' : (G.induce (S : Set V)).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
    rw [h]
    exact fun he => hab (congrArg Subtype.val he)
  exact h'

private lemma card_edges_of_cut {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h : ∀ a ∈ Sᶜ, ∀ b ∈ Sᶜ, ¬ G.Adj a b) :
    G.edgeFinset.card ≤ (G.edgeFinset ∩ S.sym2).card +
      ∑ a ∈ Sᶜ, (G.neighborFinset a ∩ S).card := by
  let crossing (a : V) := (G.neighborFinset a ∩ S).image fun b => s(a, b)
  have hs : G.edgeFinset ⊆ (G.edgeFinset ∩ S.sym2) ∪ Sᶜ.biUnion crossing := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : G.Adj a b := mem_edgeFinset.mp he
      by_cases ha : a ∈ S
      · by_cases hb : b ∈ S
        · exact mem_union_left _ (mem_inter.mpr ⟨he, Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩⟩)
        · apply mem_union_right
          refine mem_biUnion.mpr ⟨b, mem_compl.mpr hb, ?_⟩
          exact mem_image.mpr ⟨a, mem_inter.mpr ⟨(G.mem_neighborFinset b a).mpr hab.symm, ha⟩,
            Sym2.eq_swap⟩
      · have hb : b ∈ S := by
          by_contra hb
          exact h a (mem_compl.mpr ha) b (mem_compl.mpr hb) hab
        apply mem_union_right
        exact mem_biUnion.mpr ⟨a, mem_compl.mpr ha, mem_image.mpr
          ⟨b, mem_inter.mpr ⟨(G.mem_neighborFinset a b).mpr hab, hb⟩, rfl⟩⟩
  calc
    _ ≤ ((G.edgeFinset ∩ S.sym2) ∪ Sᶜ.biUnion crossing).card := card_le_card hs
    _ ≤ (G.edgeFinset ∩ S.sym2).card + (Sᶜ.biUnion crossing).card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le)) _

private lemma outside_at_most_one_of_same_pair {V : Type} {C : Sym2 V → Fin 2}
    {a b u v : V} {r k : Fin 2} (hrk : r ≠ k)
    (hva : v ≠ a) (hvb : v ≠ b) (huv : u ≠ v)
    (cau : C s(a, u) = r) (cav : C s(a, v) = r)
    (cbu : C s(b, u) = k) (cbv : C s(b, v) = k) :
    ¬ (ClearEdge C a u ∧ ClearEdge C b u) := by
  rintro ⟨hau, hbu⟩
  rcases color_eq_or_eq r k _ hrk with c | c
  · exact no_clear_of_mono hva huv.symm cau cav c hau
  · exact no_clear_of_mono hvb huv.symm cbu cbv c hbu

/-- An additional uncovered edge at the apex leaves at most two edges per outside vertex,
with a possible extra edge offset by a missing edge inside the core. -/
private lemma four_core_bound_oriented {V : Type} [Fintype V] {C : Sym2 V → Fin 2}
    {x y z t : V} {r b : Fin 2} (hn : 6 ≤ Fintype.card V)
    (hxy : ClearEdge C x y) (hxz : ClearEdge C x z) (hyz : ClearEdge C y z)
    (hxt : ClearEdge C x t) (hty : t ≠ y) (htz : t ≠ z)
    (cxy : C s(x, y) = r) (cxz : C s(x, z) = r) (cyz : C s(y, z) = b)
    (cyt : C s(y, t) = r) (hrb : r ≠ b) :
    (uncoveredGraph C).edgeFinset.card ≤ 2 * (Fintype.card V - 4) + 6 := by
  classical
  let G := uncoveredGraph C
  let S : Finset V := {x, y, z, t}
  let U : Finset V := Sᶜ
  have hS : S.card = 4 := by
    simp [S, card_insert_of_notMem, hxy.1, hxz.1, hyz.1, hxt.1, hty.symm, htz.symm]
  have hU : U.card = Fintype.card V - 4 := by rw [show U = Sᶜ from rfl, Finset.card_compl, hS]
  have hU₂ : 2 ≤ U.card := by omega
  have outside (s : V) (hs : s ∈ U) : s ≠ x ∧ s ≠ y ∧ s ≠ z ∧ s ≠ t := by
    simpa [U, S] using hs
  have cxt := apex_color hxy hxz hyz cxy cxz cyz hrb hxt.1.symm hty htz
  have colors (s : V) (hs : s ∈ U) : C s(x, s) = b ∧ C s(t, s) = r := by
    obtain ⟨hsx, hsy, hsz, hst⟩ := outside s hs
    have cxs := apex_color hxy hxz hyz cxy cxz cyz hrb hsx hsy hsz
    exact ⟨cxs, clear_forces_color hxt hsx hst cxt cxs hrb.symm⟩
  have no_inside (s : V) (hs : s ∈ U) (v : V) (hv : v ∈ U) : ¬ G.Adj s v := by
    obtain ⟨hsx, _, _, hst⟩ := outside s hs
    obtain ⟨hvx, _, _, hvt⟩ := outside v hv
    obtain ⟨cxs, cts⟩ := colors s hs
    obtain ⟨cxv, ctv⟩ := colors v hv
    rcases color_eq_or_eq r b _ hrb with c | c
    · exact no_clear_of_mono hst.symm hvt.symm c
        ((color_symm C s t).trans cts) ((color_symm C v t).trans ctv)
    · exact no_clear_of_mono hsx.symm hvx.symm c
        ((color_symm C s x).trans cxs) ((color_symm C v x).trans cxv)
  have other (s : V) : ∃ u ∈ U, s ≠ u := by
    by_contra! h
    have hsub : U ⊆ {s} := fun u hu => mem_singleton.mpr (h u hu).symm
    have hle := card_le_card hsub
    simp at hle
    omega
  have max_one_xt (s : V) (hs : s ∈ U) : ¬ (ClearEdge C x s ∧ ClearEdge C t s) := by
    obtain ⟨u, hu, hsu⟩ := other s
    exact outside_at_most_one_of_same_pair hrb.symm
      (outside u hu).1 (outside u hu).2.2.2 hsu
      (colors s hs).1 (colors u hu).1 (colors s hs).2 (colors u hu).2
  let exceptional (s : V) := ClearEdge C y s ∧ ClearEdge C z s
  let E := U.filter exceptional
  have exceptional_colors (s : V) (hs : s ∈ U) (he : exceptional s) :
      C s(y, s) = b ∧ C s(z, s) = r := by
    obtain ⟨_, hsy, hsz, hst⟩ := outside s hs
    have cys : C s(y, s) = b := by
      apply color_eq_of_ne r b _ hrb
      intro cys
      exact no_clear_of_mono hty hst.symm cys cyt
        ((color_symm C s t).trans (colors s hs).2) he.1
    exact ⟨cys, clear_forces_color hyz hsy hsz cyz cys hrb.symm⟩
  have exceptional_forces_red (s : V) (hs : s ∈ U) (he : exceptional s)
      (u : V) (hu : u ∈ U) (hsu : s ≠ u) : C s(y, u) = r := by
    obtain ⟨_, huy, huz, _⟩ := outside u hu
    obtain ⟨cys, czs⟩ := exceptional_colors s hs he
    apply color_eq_of_ne b r _ hrb.symm
    intro cyu
    have czu := clear_forces_color hyz huy huz cyz cyu hrb.symm
    exact outside_at_most_one_of_same_pair hrb.symm huy huz hsu cys cyu czs czu he
  have hE : E.card ≤ 1 := by
    rw [card_le_one]
    intro s hs u hu
    by_contra hsu
    obtain ⟨hs, he⟩ := mem_filter.mp hs
    obtain ⟨hu, he'⟩ := mem_filter.mp hu
    exact hrb ((exceptional_forces_red s hs he u hu hsu).symm.trans
      (exceptional_colors u hu he').1)
  have hcore := card_core_edges G S
  rw [hS] at hcore
  change (G.edgeFinset ∩ S.sym2).card ≤ 6 at hcore
  have hcore_sum : (G.edgeFinset ∩ S.sym2).card + E.card ≤ 6 := by
    by_cases he : E.Nonempty
    · obtain ⟨s, hs⟩ := he
      obtain ⟨hs, hes⟩ := mem_filter.mp hs
      obtain ⟨u, hu, hsu⟩ := other s
      have ht : ¬ G.Adj y t := no_clear_of_mono (outside u hu).2.1 (outside u hu).2.2.2
        cyt (exceptional_forces_red s hs hes u hu hsu) (colors u hu).2
      have hcore' := card_core_edges_strict G S (a := y) (b := t)
        (by simp [S]) (by simp [S]) hty.symm ht
      rw [hS] at hcore'
      change (G.edgeFinset ∩ S.sym2).card < 6 at hcore'
      omega
    · rw [not_nonempty_iff_eq_empty.mp he, card_empty, Nat.add_zero]
      exact hcore
  have hdeg (s : V) (hs : s ∈ U) :
      (G.neighborFinset s ∩ S).card ≤ 2 + if exceptional s then 1 else 0 := by
    have hf : G.neighborFinset s ∩ S = S.filter fun a => ClearEdge C a s := by
      ext a
      simp only [mem_inter, mem_neighborFinset, mem_filter]
      constructor
      · exact fun h => ⟨h.2, clear_symm h.1⟩
      · exact fun h => ⟨clear_symm h.2, h.1⟩
    rw [hf, card_filter]
    simp only [S, sum_insert (show x ∉ ({y, z, t} : Finset V) by simp [hxy.1, hxz.1, hxt.1]),
      sum_insert (show y ∉ ({z, t} : Finset V) by simp [hyz.1, hty.symm]),
      sum_insert (show z ∉ ({t} : Finset V) by simp [htz.symm]), sum_singleton]
    have hxt' := max_one_xt s hs
    by_cases a : ClearEdge C x s <;> by_cases b : ClearEdge C t s <;>
      by_cases c : ClearEdge C y s <;> by_cases d : ClearEdge C z s <;>
      simp [a, b, c, d, exceptional] at hxt' ⊢
  have hsum :
      (∑ s ∈ U, (G.neighborFinset s ∩ S).card) ≤ 2 * U.card + E.card := by
    calc
      _ ≤ ∑ s ∈ U, (2 + if exceptional s then 1 else 0) := sum_le_sum hdeg
      _ = _ := by rw [sum_add_distrib, ← card_filter]; simp [E, Nat.mul_comm]
  have htotal := card_edges_of_cut G S no_inside
  change G.edgeFinset.card ≤ (G.edgeFinset ∩ S.sym2).card +
    ∑ s ∈ U, (G.neighborFinset s ∩ S).card at htotal
  rw [hU] at hsum
  change G.edgeFinset.card ≤ 2 * (Fintype.card V - 4) + 6
  omega

private lemma four_core_bound {V : Type} [Fintype V] {C : Sym2 V → Fin 2}
    {x y z t : V} {r b : Fin 2} (hn : 6 ≤ Fintype.card V)
    (hxy : ClearEdge C x y) (hxz : ClearEdge C x z) (hyz : ClearEdge C y z)
    (hxt : ClearEdge C x t) (hty : t ≠ y) (htz : t ≠ z)
    (cxy : C s(x, y) = r) (cxz : C s(x, z) = r) (cyz : C s(y, z) = b)
    (hrb : r ≠ b) :
    (uncoveredGraph C).edgeFinset.card ≤ 2 * (Fintype.card V - 4) + 6 := by
  by_cases c : C s(y, t) = r
  · exact four_core_bound_oriented hn hxy hxz hyz hxt hty htz cxy cxz cyz c hrb
  · have cyt := color_eq_of_ne r b _ hrb c
    have czt := clear_forces_color hyz hty htz cyz cyt hrb.symm
    exact four_core_bound_oriented hn hxz hxy (clear_symm hyz) hxt htz hty cxz cxy
      ((color_symm C z y).trans cyz) czt hrb

private def MonoTriangle {V : Type} (C : Sym2 V → Fin 2) (a b c : V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∃ k, C s(a, b) = k ∧ C s(a, c) = k ∧ C s(b, c) = k

private lemma one_triangle_six {V : Type} [Fintype V] (hV : Fintype.card V = 6)
    (C : Sym2 V → Fin 2) : ∃ a b c, MonoTriangle C a b c := by
  classical
  have hn : 0 < Fintype.card V := by omega
  let x : V := Classical.choice (Fintype.card_pos_iff.mp hn)
  let U : Set V := {x}ᶜ
  have hU : Fintype.card U = 5 := by
    change Fintype.card ↥(({x} : Set V)ᶜ) = 5
    rw [Fintype.card_compl_set, hV, Fintype.card_unique]
  let f : Fin 5 ≃ U := Fintype.equivOfCardEq (by rw [Fintype.card_fin, hU])
  have hp : ∀ k : Fin 5 → Fin 2, ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      k a = k b ∧ k a = k c := by decide
  obtain ⟨i, j, l, hij, hil, hjl, cij, cil⟩ := hp fun i => C s(x, (f i : V))
  let a : V := f i
  let b : V := f j
  let c : V := f l
  have hxy (i : Fin 5) : x ≠ (f i : V) := Ne.symm (f i).property
  have hne {i j : Fin 5} (hne : i ≠ j) : (f i : V) ≠ (f j : V) :=
    fun h => hne (f.injective (Subtype.ext h))
  let r := C s(x, a)
  have cxb : C s(x, b) = r := cij.symm
  have cxc : C s(x, c) = r := cil.symm
  by_cases cab : C s(a, b) = r
  · exact ⟨x, a, b, hxy i, hxy j, hne hij, r, rfl, cxb, cab⟩
  by_cases cac : C s(a, c) = r
  · exact ⟨x, a, c, hxy i, hxy l, hne hil, r, rfl, cxc, cac⟩
  by_cases cbc : C s(b, c) = r
  · exact ⟨x, b, c, hxy j, hxy l, hne hjl, r, cxb, cxc, cbc⟩
  let k := C s(a, b)
  exact ⟨a, b, c, hne hij, hne hil, hne hjl, k, rfl,
    color_eq_of_ne r k _ (Ne.symm cab) cac, color_eq_of_ne r k _ (Ne.symm cab) cbc⟩

private lemma shared_opposite : ∀ r a b c a' b' c' : Fin 2,
      ((¬ (a = r ∧ b = r)) ∧ (¬ (a = r ∧ c = r)) ∧ (¬ (b = r ∧ c = r))) →
      ((¬ (a' = r ∧ b' = r)) ∧ (¬ (a' = r ∧ c' = r)) ∧ (¬ (b' = r ∧ c' = r))) →
      (a ≠ r ∧ a' ≠ r) ∨ (b ≠ r ∧ b' ≠ r) ∨ (c ≠ r ∧ c' ≠ r) := by
  intro r a b c a' b' c' ha hb
  tauto

/-- If the first triangle were unique, every outside vertex would have at least two links
of the other color to it. The three outside vertices would then form a second triangle. -/
private lemma two_triangles_six {V : Type} [Fintype V] (hV : Fintype.card V = 6)
    (C : Sym2 V → Fin 2) {a b c : V} (hTriangle : MonoTriangle C a b c) :
    ∃ d e f, d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ MonoTriangle C d e f := by
  classical
  obtain ⟨hab, hac, hbc, r, cab, cac, cbc⟩ := hTriangle
  let U : Finset V := ({a, b, c} : Finset V)ᶜ
  have hU : U.card = 3 := by
    rw [show U = ({a, b, c} : Finset V)ᶜ from rfl, Finset.card_compl, hV]
    simp [card_insert_of_notMem, hab, hac, hbc]
  have hout (d : V) (hd : d ∈ U) : d ≠ a ∧ d ≠ b ∧ d ≠ c := by simpa [U] using hd
  by_contra hnone
  have hno (d e f : V) (hd : d ∈ U) : ¬ MonoTriangle C d e f := by
    intro ht
    obtain ⟨hda, hdb, hdc⟩ := hout d hd
    exact hnone ⟨d, e, f, hda, hdb, hdc, ht⟩
  have at_most_one (d : V) (hd : d ∈ U) :
      (¬ (C s(d, a) = r ∧ C s(d, b) = r)) ∧
      (¬ (C s(d, a) = r ∧ C s(d, c) = r)) ∧
      (¬ (C s(d, b) = r ∧ C s(d, c) = r)) := by
    obtain ⟨hda, hdb, hdc⟩ := hout d hd
    refine ⟨?_, ?_, ?_⟩
    · exact fun ⟨cda, cdb⟩ => hno d a b hd ⟨hda, hdb, hab, r, cda, cdb, cab⟩
    · exact fun ⟨cda, cdc⟩ => hno d a c hd ⟨hda, hdc, hac, r, cda, cdc, cac⟩
    · exact fun ⟨cdb, cdc⟩ => hno d b c hd ⟨hdb, hdc, hbc, r, cdb, cdc, cbc⟩
  have cout (d e : V) (hd : d ∈ U) (he : e ∈ U) (hne : d ≠ e) : C s(d, e) = r := by
    by_contra hk
    obtain ⟨hda, hdb, hdc⟩ := hout d hd
    obtain ⟨hea, heb, hec⟩ := hout e he
    have hcommon (v : V) (hdv : d ≠ v) (hev : e ≠ v)
        (cdv : C s(d, v) ≠ r) (cev : C s(e, v) ≠ r) : False :=
      hno d e v hd ⟨hne, hdv, hev, C s(d, e), rfl,
        color_eq_of_ne r _ _ (Ne.symm hk) cdv, color_eq_of_ne r _ _ (Ne.symm hk) cev⟩
    rcases shared_opposite r _ _ _ _ _ _ (at_most_one d hd) (at_most_one e he) with ha | hb | hc
    · exact hcommon a hda hea ha.1 ha.2
    · exact hcommon b hdb heb hb.1 hb.2
    · exact hcommon c hdc hec hc.1 hc.2
  obtain ⟨d, e, f, hde, hdf, hef, hUE⟩ := Finset.card_eq_three.mp hU
  have hd : d ∈ U := by simp [hUE]
  have he : e ∈ U := by simp [hUE]
  have hf : f ∈ U := by simp [hUE]
  exact hno d e f hd ⟨hde, hdf, hef, r, cout d e hd he hde, cout d f hd hf hdf,
    cout e f he hf hef⟩

private lemma six_upper {V : Type} [Fintype V] (hV : Fintype.card V = 6)
    (C : Sym2 V → Fin 2) : (uncoveredGraph C).edgeFinset.card ≤ 10 := by
  classical
  obtain ⟨a, b, c, ht⟩ := one_triangle_six hV C
  obtain ⟨d, e, f, hda, hdb, hdc, ht'⟩ := two_triangles_six hV C ht
  obtain ⟨hab, hac, hbc, r, cab, cac, cbc⟩ := ht
  obtain ⟨hde, hdf, hef, k, cde, cdf, cef⟩ := ht'
  let D : Finset (Sym2 V) := {s(a, b), s(a, c), s(b, c), s(d, e), s(d, f)}
  let G := uncoveredGraph C
  have hD : D.card = 5 := by
    simp [D, card_insert_of_notMem, hab, hac, hbc, hda.symm, hdb.symm, hdc.symm, hdf, hef]
  have hDsub : D ⊆ (⊤ : SimpleGraph V).edgeFinset := by
    intro g hg
    simp only [D, mem_insert, mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;>
      simp [hab, hac, hbc, hde, hdf]
  have hdisj : Disjoint G.edgeFinset D := by
    refine Finset.disjoint_left.mpr fun g hg hDg => ?_
    simp only [D, mem_insert, mem_singleton] at hDg
    rcases hDg with rfl | rfl | rfl | rfl | rfl
    · exact no_clear_of_mono hac.symm hbc.symm cab cac cbc (mem_edgeFinset.mp hg)
    · exact no_clear_of_mono hab.symm hbc cac cab ((color_symm C c b).trans cbc)
        (mem_edgeFinset.mp hg)
    · exact no_clear_of_mono hab hac cbc ((color_symm C b a).trans cab)
        ((color_symm C c a).trans cac) (mem_edgeFinset.mp hg)
    · exact no_clear_of_mono hdf.symm hef.symm cde cdf cef (mem_edgeFinset.mp hg)
    · exact no_clear_of_mono hde.symm hef cdf cde ((color_symm C f e).trans cef)
        (mem_edgeFinset.mp hg)
  have hle := card_le_card (union_subset (edgeFinset_mono (show G ≤ ⊤ from le_top)) hDsub)
  rw [card_union_of_disjoint hdisj, hD, card_edgeFinset_top_eq_card_choose_two, hV] at hle
  change G.edgeFinset.card + 5 ≤ 15 at hle
  change G.edgeFinset.card ≤ 10
  omega

private lemma mixed_triangle_colors : ∀ p q r : Fin 2, ¬ (p = q ∧ p = r) →
      (p = q ∧ p ≠ r) ∨ (p = r ∧ p ≠ q) ∨ (q = r ∧ q ≠ p) := by decide

private lemma uncovered_triangle {V : Type} {C : Sym2 V → Fin 2}
    (h : ¬ (uncoveredGraph C).CliqueFree 3) :
    ∃ x y z, ClearEdge C x y ∧ ClearEdge C x z ∧ ClearEdge C y z ∧
      C s(x, y) = C s(x, z) ∧ C s(x, y) ≠ C s(y, z) := by
  classical
  unfold SimpleGraph.CliqueFree at h
  push Not at h
  obtain ⟨T, hT⟩ := h
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ := is3Clique_iff.mp hT
  change ClearEdge C a b at hab
  change ClearEdge C a c at hac
  change ClearEdge C b c at hbc
  have hnot : ¬ (C s(a, b) = C s(a, c) ∧ C s(a, b) = C s(b, c)) := by
    rintro ⟨habc, habc'⟩
    exact no_clear_of_mono hac.1.symm hbc.1.symm rfl habc.symm habc'.symm hab
  rcases mixed_triangle_colors _ _ _ hnot with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨a, b, c, hab, hac, hbc, h₁, h₂⟩
  · refine ⟨b, a, c, clear_symm hab, hbc, hac, (color_symm C b a).trans h₁, ?_⟩
    exact fun he => h₂ ((color_symm C a b).trans he)
  · refine ⟨c, a, b, clear_symm hac, clear_symm hbc, hab, ?_, ?_⟩
    · exact (color_symm C c a).trans (h₁.trans (color_symm C b c))
    · exact fun he => h₂ ((color_symm C a c).trans he)

private lemma floor_step (m : ℕ) (hm : 4 ≤ m) :
    m ^ 2 / 4 + 2 ≤ (m + 1) ^ 2 / 4 := by
  have h : m ^ 2 + 8 ≤ (m + 1) ^ 2 := by nlinarith
  omega

private lemma floor_core (m : ℕ) (hm : 3 ≤ m) :
    2 * m + 6 ≤ (m + 4) ^ 2 / 4 := by
  have h : 4 * (2 * m + 6) ≤ (m + 4) ^ 2 := by
    nlinarith [Nat.mul_le_mul hm hm]
  omega

private theorem upper_from_six (n : ℕ) :
    6 ≤ n → ∀ (V : Type) [Fintype V], Fintype.card V = n → ∀ C : Sym2 V → Fin 2,
    (uncoveredGraph C).edgeFinset.card ≤ if n = 6 then 10 else n ^ 2 / 4 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn V inst hV C
    by_cases h6 : n = 6
    · simpa only [h6, if_true] using six_upper (hV.trans h6) C
    rw [if_neg h6]
    let G := uncoveredGraph C
    by_cases hf : G.CliqueFree 3
    · exact (mantel_bound G hf).trans_eq (by rw [hV])
    obtain ⟨x, y, z, hxy, hxz, hyz, hsame, hdiff⟩ := uncovered_triangle hf
    by_cases he : ∃ t, ClearEdge C x t ∧ t ≠ y ∧ t ≠ z
    · obtain ⟨t, hxt, hty, htz⟩ := he
      have h := four_core_bound (hn := by rw [hV]; exact hn)
        hxy hxz hyz hxt hty htz rfl hsame.symm rfl hdiff
      rw [hV] at h
      exact h.trans (by
        have hnum : n - 4 + 4 = n := Nat.sub_add_cancel (by omega)
        simpa only [hnum] using floor_core (n - 4) (by omega))
    · -- Deleting the apex loses at most two edges. The smaller coloring may uncover more.
      have hdegree : G.degree x ≤ 2 := by
        rw [← G.card_neighborFinset_eq_degree]
        have hsub : G.neighborFinset x ⊆ {y, z} := by
          intro t ht
          have ht' : ClearEdge C x t := (G.mem_neighborFinset x t).mp ht
          by_contra h
          have h' : t ≠ y ∧ t ≠ z := by simpa using h
          exact he ⟨t, ht', h'⟩
        exact (card_le_card hsub).trans (by simp [card_insert_of_notMem, hyz.1])
      let S : Set V := {x}ᶜ
      let f : S ↪ V := Function.Embedding.subtype _
      let D : Sym2 S → Fin 2 := C ∘ Sym2.map f
      have hS : Fintype.card S = n - 1 := by
        change Fintype.card ↥(({x} : Set V)ᶜ) = n - 1
        rw [Fintype.card_compl_set, hV, Fintype.card_unique]
      have hrestrict : G.induce S ≤ uncoveredGraph D := by
        intro a b hab
        exact clear_pull f hab
      have hle := card_le_card (edgeFinset_mono hrestrict)
      have hdel := G.card_edgeFinset_induce_compl_singleton x
      rw [G.card_edgeFinset_deleteIncidenceSet] at hdel
      change (G.induce S).edgeFinset.card = G.edgeFinset.card - G.degree x at hdel
      have hprev := ih (n - 1) (by omega) (by omega) S hS D
      have henough : (if n - 1 = 6 then 10 else (n - 1) ^ 2 / 4) + 2 ≤ n ^ 2 / 4 := by
        by_cases h7 : n - 1 = 6
        · have hn7 : n = 7 := by omega
          norm_num [hn7]
        · rw [if_neg h7]
          have hnum : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
          simpa only [hnum] using floor_step (n - 1) (by omega)
      change G.edgeFinset.card ≤ n ^ 2 / 4
      omega

private lemma splitSize (n : ℕ) :
    n ^ 2 / 4 = (n / 2) * (n - n / 2) := by
  have h : ∃ m : ℕ, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
  obtain ⟨m, hm | hm⟩ := h
  · subst n
    rw [show 2 * m / 2 = m by omega, show 2 * m - m = m by omega]
    have hh : (2 * m) ^ 2 = 4 * (m * m) := by ring
    omega
  · subst n
    rw [show (2 * m + 1) / 2 = m by omega, show 2 * m + 1 - m = m + 1 by omega]
    have hh : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega

private lemma split_attained_lower (n : ℕ) :
    ∃ C : Sym2 (Fin n) → Fin 2, n ^ 2 / 4 ≤ (Erdos639.uncoveredEdges C).ncard := by
  classical
  let left (a : Fin n) : Prop := a.val < n / 2
  let color (a b : Fin n) : Fin 2 := if (left a ↔ left b) then 0 else 1
  have hsymm (a b : Fin n) : color a b = color b a := by
    by_cases h : left a ↔ left b
    · exact (if_pos h).trans (if_pos h.symm).symm
    · have h' : ¬ (left b ↔ left a) := fun he => h he.symm
      exact (if_neg h).trans (if_neg h').symm
  let C := Sym2.lift ⟨color, hsymm⟩
  refine ⟨C, ?_⟩
  rw [uncovered_ncard, splitSize]
  have hclear (a b : Fin n) (ha : left a) (hb : ¬ left b) : ClearEdge C a b := by
    refine ⟨fun h => hb (h ▸ ha), ?_⟩
    rintro ⟨t, _, _, hat, hbt⟩
    change color a t = color a b at hat
    change color b t = color a b at hbt
    have hab : ¬ (left a ↔ left b) := fun h => hb (h.mp ha)
    by_cases ht : left t
    · have h : left a ↔ left t := ⟨fun _ => ht, fun _ => ha⟩
      unfold color at hat
      rw [if_pos h, if_neg hab] at hat
      exact (by decide : (0 : Fin 2) ≠ 1) hat
    · have h : left b ↔ left t := ⟨fun hh => (hb hh).elim, fun hh => (ht hh).elim⟩
      unfold color at hbt
      rw [if_pos h, if_neg hab] at hbt
      exact (by decide : (0 : Fin 2) ≠ 1) hbt
  let L (a : Fin (n / 2)) : Fin n := ⟨a.val, by have := a.isLt; omega⟩
  let R (b : Fin (n - n / 2)) : Fin n := ⟨n / 2 + b.val, by have := b.isLt; omega⟩
  have hL (a : Fin (n / 2)) : left (L a) := a.isLt
  have hR (b : Fin (n - n / 2)) : ¬ left (R b) := by
    change ¬ n / 2 + b.val < n / 2
    omega
  let f : Fin (n / 2) × Fin (n - n / 2) ↪ (uncoveredGraph C).edgeFinset :=
    ⟨fun p => ⟨s(L p.1, R p.2), mem_edgeFinset.mpr (hclear _ _ (hL _) (hR _))⟩, by
      intro p q he
      have he' : s(L p.1, R p.2) = s(L q.1, R q.2) := congrArg Subtype.val he
      rcases Sym2.eq_iff.mp he' with ⟨hl, hr⟩ | ⟨hl, _⟩
      · apply Prod.ext
        · have hv : (L p.1).val = (L q.1).val := congrArg Fin.val hl
          exact Fin.ext hv
        · have hh : n / 2 + p.2.val = n / 2 + q.2.val := congrArg Fin.val hr
          exact Fin.ext (by omega)
      · exact (hR q.2 (hl ▸ hL p.1)).elim⟩
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using
    Fintype.card_le_of_embedding f

end OMA

theorem OMA.solution : type_of% @Erdos639.erdos_639.variants.exact := by
  classical
  intro n
  by_cases hsmall : n ≤ 5
  · rw [if_pos hsmall]
    obtain ⟨C, hC⟩ := OMA.small_attained n hsmall
    refine ⟨⟨C, hC⟩, ?_⟩
    rintro _ ⟨D, rfl⟩
    change (Erdos639.uncoveredEdges D).ncard ≤ n.choose 2
    rw [OMA.uncovered_ncard]
    simpa only [Fintype.card_fin] using
      (card_edgeFinset_le_card_choose_two (G := OMA.uncoveredGraph D))
  rw [if_neg hsmall]
  have hUpper (C : Sym2 (Fin n) → Fin 2) :
      (Erdos639.uncoveredEdges C).ncard ≤ if n = 6 then 10 else n ^ 2 / 4 := by
    rw [OMA.uncovered_ncard]
    exact OMA.upper_from_six n (by omega) (Fin n) (Fintype.card_fin n) C
  refine ⟨?_, ?_⟩
  · by_cases hn : n = 6
    · subst n
      obtain ⟨C, hC, _⟩ := Erdos639.erdos_639.variants.six_vertices
      exact ⟨C, hC⟩
    · obtain ⟨C, hC⟩ := OMA.split_attained_lower n
      exact ⟨C, (hUpper C).antisymm (by simpa only [if_neg hn] using hC)⟩
  · rintro _ ⟨D, rfl⟩
    exact hUpper D