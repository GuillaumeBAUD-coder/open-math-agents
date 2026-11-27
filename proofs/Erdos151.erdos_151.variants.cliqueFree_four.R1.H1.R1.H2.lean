import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1
import Mathlib

/-!
# Bikov's 7-vertex link extension lemma for Erdos 151 (K_4-free)

Step `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H2`: for any triangle-free simple graph
`L` on `k ≤ 7` vertices and any symmetric 2-edge-coloring `c : Fin k → Fin k → Bool`, there exists
a vertex 2-coloring `d : Fin k → Bool` such that no edge `(x, y)` has `d x = c x y` and
`d y = c x y`.
-/

namespace Erdos151Link7

open Finset SimpleGraph
open scoped Classical

private lemma indep_of_adj {k : ℕ} {L : SimpleGraph (Fin k)} (hL : L.CliqueFree 3)
    {v x y : Fin k} (hvx : L.Adj v x) (hvy : L.Adj v y) : ¬ L.Adj x y := by
  intro hxy
  exact hL {v, x, y} (is3Clique_triple_iff.mpr ⟨hvx, hvy, hxy⟩)

private lemma two_color_of_one_degenerate {k : ℕ} (L : SimpleGraph (Fin k))
    (S : Finset (Fin k))
    (hdeg : ∀ T : Finset (Fin k), T ⊆ S → T.Nonempty → ∃ v ∈ T, (T.filter (L.Adj v)).card ≤ 1) :
    ∃ d : Fin k → Bool, ∀ x ∈ S, ∀ y ∈ S, L.Adj x y → d x ≠ d y := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨v, hvS, hvdeg⟩ := hdeg S Subset.rfl hS
      obtain ⟨d0, hd0⟩ := ih (S.erase v) (erase_ssubset hvS)
        (fun T hT hTne => hdeg T (hT.trans (erase_subset _ _)) hTne)
      let Nv := (S.erase v).filter (L.Adj v)
      have hNv_card : Nv.card ≤ 1 := by
        exact (card_le_card (filter_subset_filter _ (erase_subset _ _))).trans hvdeg
      let bv : Bool :=
        if h : Nv.Nonempty then !(d0 (Classical.choose h)) else false
      let d : Fin k → Bool := fun x => if x = v then bv else d0 x
      refine ⟨d, fun x hx y hy hxy => ?_⟩
      by_cases hxv : x = v
      · subst hxv
        have hyv : y ≠ x := hxy.ne.symm
        have hyN : y ∈ Nv := mem_filter.mpr ⟨mem_erase.mpr ⟨hyv, hy⟩, hxy⟩
        have hne : Nv.Nonempty := ⟨y, hyN⟩
        have hch_mem : Classical.choose hne ∈ Nv := Classical.choose_spec hne
        have huniq : Classical.choose hne = y :=
          Finset.card_le_one.mp hNv_card _ hch_mem _ hyN
        simp only [d, if_pos rfl, if_neg hyv, bv, dif_pos hne, huniq]
        cases d0 y <;> decide
      · by_cases hyv : y = v
        · subst hyv
          have hxN : x ∈ Nv := mem_filter.mpr ⟨mem_erase.mpr ⟨hxv, hx⟩, hxy.symm⟩
          have hne : Nv.Nonempty := ⟨x, hxN⟩
          have hch_mem : Classical.choose hne ∈ Nv := Classical.choose_spec hne
          have huniq : Classical.choose hne = x :=
            Finset.card_le_one.mp hNv_card _ hch_mem _ hxN
          simp only [d, if_neg hxv, if_pos rfl, bv, dif_pos hne, huniq]
          cases d0 x <;> decide
        · simp only [d, if_neg hxv, if_neg hyv]
          exact hd0 x (mem_erase.mpr ⟨hxv, hx⟩) y (mem_erase.mpr ⟨hyv, hy⟩) hxy
    · refine ⟨fun _ => false, fun x hx => (hS ⟨x, hx⟩).elim⟩

private lemma two_regular_card_ge_four {k : ℕ} {L : SimpleGraph (Fin k)} (hL : L.CliqueFree 3)
    {T : Finset (Fin k)} (hTne : T.Nonempty) (hreg : ∀ v ∈ T, 2 ≤ (T.filter (L.Adj v)).card) :
    4 ≤ T.card := by
  classical
  obtain ⟨v, hvT⟩ := hTne
  have hv2 := hreg v hvT
  obtain ⟨u₁, hu₁, u₂, hu₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (T.filter (L.Adj v)).card)
  simp only [mem_filter] at hu₁ hu₂
  have hu1_deg := hreg u₁ hu₁.1
  obtain ⟨w₁, hw₁, w₂, hw₂, hw12⟩ := Finset.one_lt_card.mp (by omega : 1 < (T.filter (L.Adj u₁)).card)
  simp only [mem_filter] at hw₁ hw₂
  have hex_w : ∃ w ∈ T, L.Adj u₁ w ∧ w ≠ v := by
    by_cases h1 : w₁ = v
    · exact ⟨w₂, hw₂.1, hw₂.2, fun h2 => hw12 (h1.trans h2.symm)⟩
    · exact ⟨w₁, hw₁.1, hw₁.2, h1⟩
  obtain ⟨w, hwT, hu1w, hwv⟩ := hex_w
  have hvu1 : v ≠ u₁ := hu₁.2.ne
  have hvu2 : v ≠ u₂ := hu₂.2.ne
  have hwu1 : w ≠ u₁ := hu1w.ne.symm
  have hwu2 : w ≠ u₂ := by
    intro h; subst h
    exact indep_of_adj hL hu₁.2 hu₂.2 hu1w
  have hsub : ({v, u₁, u₂, w} : Finset (Fin k)) ⊆ T := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hvT
    · exact hu₁.1
    · exact hu₂.1
    · exact hwT
  have hcard4 : ({v, u₁, u₂, w} : Finset (Fin k)).card = 4 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp [hwu2.symm]
    · simp [h12, hwu1.symm]
    · simp [hvu1, hvu2, hwv.symm]
  exact hcard4 ▸ Finset.card_le_card hsub

private lemma even_card_of_one_regular {k : ℕ} (S : Finset (Fin k))
    (R : Fin k → Fin k → Prop) [DecidableRel R]
    (hsym : ∀ x y, R x y → R y x) (hirr : ∀ x, ¬ R x x)
    (h1 : ∀ x ∈ S, (S.filter (R x)).card = 1) : Even S.card := by
  classical
  let E : Finset (Fin k × Fin k) := (S ×ˢ S).filter fun p => R p.1 p.2
  have hE_card : E.card = S.card := by
    have hsum : E.card = ∑ x ∈ S, (S.filter (R x)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.card_filter]
    rw [hsum]
    simpa using Finset.sum_congr rfl fun x hx => h1 x hx
  let Elt : Finset (Fin k × Fin k) := E.filter fun p => p.1 < p.2
  let Egt : Finset (Fin k × Fin k) := E.filter fun p => p.2 < p.1
  have hdisj : Disjoint Elt Egt := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Elt, Egt, mem_filter] at h1 h2
    exact lt_asymm h1.2 h2.2
  have hunion : E = Elt ∪ Egt := by
    ext ⟨x, y⟩
    simp only [Elt, Egt, mem_union, mem_filter]
    constructor
    · intro h
      have hxy : x ≠ y := fun heq => by
        subst heq
        simp only [E, mem_filter] at h
        exact hirr x h.2
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr ⟨h, hgt⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hswap : Elt.card = Egt.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · rintro ⟨x, y⟩ h
      simp only [Elt, Egt, E, mem_filter, mem_product] at h ⊢
      exact ⟨⟨⟨h.1.1.2, h.1.1.1⟩, hsym x y h.1.2⟩, h.2⟩
    · rintro ⟨x₁, y₁⟩ _ ⟨x₂, y₂⟩ _ h
      cases h; rfl
    · rintro ⟨x, y⟩ h
      refine ⟨(y, x), ?_, rfl⟩
      simp only [Elt, Egt, E, mem_filter, mem_product] at h ⊢
      exact ⟨⟨⟨h.1.1.2, h.1.1.1⟩, hsym x y h.1.2⟩, h.2⟩
  rw [← hE_card, hunion, Finset.card_union_of_disjoint hdisj, hswap]
  exact ⟨Egt.card, by ring⟩

private lemma solve_two_regular {k : ℕ} (L : SimpleGraph (Fin k)) (hL : L.CliqueFree 3)
    (S : Finset (Fin k)) (hScard : S.card ≤ 7)
    (hreg : ∀ v ∈ S, (S.filter (L.Adj v)).card = 2)
    (c : Fin k → Fin k → Bool) (hcs : ∀ x y, c x y = c y x) :
    ∃ d : Fin k → Bool, ∀ x ∈ S, ∀ y ∈ S, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y) := by
  classical
  by_cases hS : S.Nonempty
  swap
  · exact ⟨fun _ => false, fun x hx => (hS ⟨x, hx⟩).elim⟩
  -- Deleting any vertex v ∈ S leaves S.erase v 1-degenerate
  have hdel_1deg : ∀ v ∈ S,
      ∀ T : Finset (Fin k), T ⊆ S.erase v → T.Nonempty → ∃ w ∈ T, (T.filter (L.Adj w)).card ≤ 1 := by
    intro v hvS T hT hTne
    by_contra hno
    push_neg at hno
    have hT2 : ∀ w ∈ T, 2 ≤ (T.filter (L.Adj w)).card := fun w hw => hno w hw
    have hT4 : 4 ≤ T.card := two_regular_card_ge_four hL hTne hT2
    -- Every w ∈ T already has 2 neighbors in T ⊆ S, so w cannot be adjacent to v
    have hno_adj_v : ∀ w ∈ T, ¬ L.Adj v w := by
      intro w hw hadj
      have hvT : v ∉ T := fun hv => (mem_erase.mp (hT hv)).1 rfl
      have hsub : insert v (T.filter (L.Adj w)) ⊆ S.filter (L.Adj w) := by
        intro x hx
        simp only [mem_insert, mem_filter] at hx ⊢
        rcases hx with rfl | ⟨hxT, hxadj⟩
        · exact ⟨hvS, hadj.symm⟩
        · exact ⟨(mem_erase.mp (hT hxT)).2, hxadj⟩
      have hcard_le := Finset.card_le_card hsub
      rw [card_insert_of_notMem (fun h => hvT (mem_filter.mp h).1),
        hreg w (mem_erase.mp (hT hw)).2] at hcard_le
      have := hT2 w hw
      omega
    -- So T is disjoint from {v} ∪ N(v), which has size 3
    let Nv := S.filter (L.Adj v)
    have hNv2 : Nv.card = 2 := hreg v hvS
    have hdisj : Disjoint T (insert v Nv) := by
      rw [Finset.disjoint_left]
      intro w hwT hw2
      simp only [mem_insert, Nv, mem_filter] at hw2
      rcases hw2 with rfl | ⟨_, hadj⟩
      · exact (mem_erase.mp (hT hwT)).1 rfl
      · exact hno_adj_v w hwT hadj
    have hunion_sub : T ∪ insert v Nv ⊆ S := by
      intro w hw
      rcases mem_union.mp hw with hwT | hw2
      · exact (mem_erase.mp (hT hwT)).2
      · simp only [mem_insert, Nv, mem_filter] at hw2
        rcases hw2 with rfl | ⟨hwS, _⟩ <;> assumption
    have hcard_u := Finset.card_le_card hunion_sub
    rw [card_union_of_disjoint hdisj,
      card_insert_of_notMem (fun h => L.loopless.irrefl v (mem_filter.mp h).2), hNv2] at hcard_u
    -- Therefore T.card = 4 and S = T ∪ {v} ∪ Nv
    have hT_eq4 : T.card = 4 := by omega
    have hS_eq : T ∪ insert v Nv = S := Finset.eq_of_subset_of_card_le hunion_sub (by
      rw [card_union_of_disjoint hdisj,
        card_insert_of_notMem (fun h => L.loopless.irrefl v (mem_filter.mp h).2), hNv2]
      omega)
    -- Any u ∈ Nv has 2 neighbors in S, none in T, and u ≠ u; so u must be adjacent to the other vertex in Nv!
    obtain ⟨u₁, hu₁, u₂, hu₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < Nv.card)
    have hu₁S : u₁ ∈ S := (mem_filter.mp hu₁).1
    have hvu₁ : L.Adj v u₁ := (mem_filter.mp hu₁).2
    have hvu₂ : L.Adj v u₂ := (mem_filter.mp hu₂).2
    have hNu1_sub : S.filter (L.Adj u₁) ⊆ insert v Nv := by
      intro x hx
      rw [← hS_eq] at hx
      simp only [mem_filter, mem_union] at hx
      rcases hx.1 with hxT | hx2
      · -- x ∈ T and u₁ ∈ Nv cannot be adjacent because x already has 2 neighbors in T ⊆ S
        exfalso
        have hu1T : u₁ ∉ T := Finset.disjoint_right.mp hdisj (mem_insert_of_mem hu₁)
        have hsub' : insert u₁ (T.filter (L.Adj x)) ⊆ S.filter (L.Adj x) := by
          intro y hy
          simp only [mem_insert, mem_filter] at hy ⊢
          rcases hy with rfl | ⟨hyT, hyadj⟩
          · exact ⟨hu₁S, hx.2.symm⟩
          · exact ⟨(mem_erase.mp (hT hyT)).2, hyadj⟩
        have hc := Finset.card_le_card hsub'
        rw [card_insert_of_notMem (fun h => hu1T (mem_filter.mp h).1),
          hreg x (mem_erase.mp (hT hxT)).2] at hc
        have := hT2 x hxT
        omega
      · exact hx2
    -- Since Nv has card 2 and contains u₁ ≠ u₂, Nv = {u₁, u₂}
    have hNv_eq : Nv = {u₁, u₂} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · rw [card_insert_of_notMem (by simp [h12]), card_singleton, hNv2]
    have hNu1_sub2 : S.filter (L.Adj u₁) ⊆ {v, u₂} := by
      intro x hx
      have hx' := hNu1_sub hx
      rw [hNv_eq] at hx'
      simp only [mem_insert, mem_singleton] at hx' ⊢
      rcases hx' with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd (mem_filter.mp hx).2 (L.loopless.irrefl _)
      · exact Or.inr rfl
    have hNu1_eq : S.filter (L.Adj u₁) = {v, u₂} := by
      refine Finset.eq_of_subset_of_card_le hNu1_sub2 ?_
      rw [hreg u₁ hu₁S]
      exact Finset.card_le_two
    have hu1u2 : L.Adj u₁ u₂ := by
      have : u₂ ∈ S.filter (L.Adj u₁) := by rw [hNu1_eq]; simp
      exact (mem_filter.mp this).2
    exact indep_of_adj hL hvu₁ hvu₂ hu1u2
  -- Case 1: some vertex v ∈ S has two incident edges of the same color
  by_cases hsame : ∃ v ∈ S, ∃ b : Bool, ∀ u ∈ S, L.Adj v u → c v u = b
  · obtain ⟨v, hvS, b, hvb⟩ := hsame
    obtain ⟨d0, hd0⟩ := two_color_of_one_degenerate L (S.erase v) (hdel_1deg v hvS)
    let d : Fin k → Bool := fun x => if x = v then !b else d0 x
    refine ⟨d, fun x hx y hy hxy => ?_⟩
    by_cases hxv : x = v
    · subst hxv
      have hcvy : c x y = b := hvb y hy hxy
      rintro ⟨h1, _⟩
      simp only [d, if_pos rfl, hcvy] at h1
      cases b <;> simp at h1
    · by_cases hyv : y = v
      · subst hyv
        have hcyx : c x y = b := (hcs x y).trans (hvb x hx hxy.symm)
        rintro ⟨_, h2⟩
        simp only [d, if_pos rfl, hcyx] at h2
        cases b <;> simp at h2
      · rintro ⟨h1, h2⟩
        simp only [d, if_neg hxv, if_neg hyv] at h1 h2
        exact hd0 x (mem_erase.mpr ⟨hxv, hx⟩) y (mem_erase.mpr ⟨hyv, hy⟩) hxy (h1.trans h2.symm)
  · -- Case 2: every vertex v ∈ S has one true-edge and one false-edge
    push_neg at hsame
    have htrue_1reg : ∀ v ∈ S, (S.filter fun u => L.Adj v u ∧ c v u = true).card = 1 := by
      intro v hvS
      have hnv2 := hreg v hvS
      obtain ⟨u₁, hu₁, u₂, hu₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (S.filter (L.Adj v)).card)
      have hNv_eq : S.filter (L.Adj v) = {u₁, u₂} := by
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        · rw [card_insert_of_notMem (by simp [h12]), card_singleton, hnv2]
      have hdiff : c v u₁ ≠ c v u₂ := by
        intro heq
        obtain ⟨u, huS, hvu, hne⟩ := hsame v hvS (c v u₁)
        have hu_mem : u ∈ ({u₁, u₂} : Finset (Fin k)) := by
          rw [← hNv_eq]; exact mem_filter.mpr ⟨huS, hvu⟩
        simp only [mem_insert, mem_singleton] at hu_mem
        rcases hu_mem with rfl | rfl
        · exact hne rfl
        · exact hne heq.symm
      have hfilt_eq : (S.filter fun u => L.Adj v u ∧ c v u = true) =
          ({u₁, u₂} : Finset (Fin k)).filter (fun u => c v u = true) := by
        ext u
        simp only [mem_filter]
        constructor
        · rintro ⟨huS, hvu, hct⟩
          exact ⟨by rw [← hNv_eq]; exact mem_filter.mpr ⟨huS, hvu⟩, hct⟩
        · rintro ⟨hu12, hct⟩
          rw [← hNv_eq, mem_filter] at hu12
          exact ⟨hu12.1, hu12.2, hct⟩
      rw [hfilt_eq]
      cases h1 : c v u₁ <;> cases h2 : c v u₂
      · exact absurd (h1.trans h2.symm) hdiff
      · have : ({u₁, u₂} : Finset (Fin k)).filter (fun u => c v u = true) = {u₂} := by
          ext u; simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, ht⟩
            · simp [h1] at ht
            · rfl
          · rintro rfl; exact ⟨Or.inr rfl, h2⟩
        rw [this, card_singleton]
      · have : ({u₁, u₂} : Finset (Fin k)).filter (fun u => c v u = true) = {u₁} := by
          ext u; simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, ht⟩
            · rfl
            · simp [h2] at ht
          · rintro rfl; exact ⟨Or.inl rfl, h1⟩
        rw [this, card_singleton]
      · exact absurd (h1.trans h2.symm) hdiff
    have hSeven : Even S.card :=
      even_card_of_one_regular S (fun x y => L.Adj x y ∧ c x y = true)
        (fun x y h => ⟨h.1.symm, (hcs y x).trans h.2⟩)
        (fun x h => L.loopless.irrefl x h.1) htrue_1reg
    obtain ⟨v, hvS⟩ := hS
    obtain ⟨d0, hd0⟩ := two_color_of_one_degenerate L (S.erase v) (hdel_1deg v hvS)
    have hnv2 := hreg v hvS
    obtain ⟨u₁, hu₁, u₂, hu₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (S.filter (L.Adj v)).card)
    have hNv_eq : S.filter (L.Adj v) = {u₁, u₂} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · rw [card_insert_of_notMem (by simp [h12]), card_singleton, hnv2]
    -- Show d0 u₁ = d0 u₂ by bipartite degree-sum parity on S.erase v
    have hd0_eq : d0 u₁ = d0 u₂ := by
      by_contra hne
      let S' := S.erase v
      let A := S'.filter fun x => d0 x = true
      let B := S'.filter fun x => d0 x = false
      have hAB_sum : ∑ x ∈ A, (S'.filter (L.Adj x)).card = ∑ y ∈ B, (S'.filter (L.Adj y)).card := by
        have hLHS : ∑ x ∈ A, (S'.filter (L.Adj x)).card =
            ((A ×ˢ B).filter fun p => L.Adj p.1 p.2).card := by
          rw [Finset.card_filter, Finset.sum_product]
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [Finset.card_filter]
          have hsub : S'.filter (L.Adj x) = B.filter (L.Adj x) := by
            ext y
            simp only [mem_filter, B]
            constructor
            · rintro ⟨hyS', hxy⟩
              have hxA := mem_filter.mp hx
              have hdy : d0 y ≠ d0 x := (hd0 x hxA.1 y hyS' hxy).symm
              rw [hxA.2] at hdy
              exact ⟨⟨hyS', Bool.eq_false_iff.mpr hdy⟩, hxy⟩
            · rintro ⟨⟨hyS', _⟩, hxy⟩
              exact ⟨hyS', hxy⟩
          rw [← Finset.card_filter, hsub, Finset.card_filter]
        have hRHS : ∑ y ∈ B, (S'.filter (L.Adj y)).card =
            ((A ×ˢ B).filter fun p => L.Adj p.1 p.2).card := by
          rw [Finset.card_filter, Finset.sum_product_right]
          refine Finset.sum_congr rfl fun y hy => ?_
          rw [Finset.card_filter]
          have hsub : S'.filter (L.Adj y) = A.filter (fun x => L.Adj x y) := by
            ext x
            simp only [mem_filter, A]
            constructor
            · rintro ⟨hxS', hyx⟩
              have hyB := mem_filter.mp hy
              have hdx : d0 x ≠ d0 y := hd0 x hxS' y hyB.1 hyx.symm
              rw [hyB.2] at hdx
              exact ⟨⟨hxS', Bool.eq_true_of_not_eq_false hdx⟩, hyx.symm⟩
            · rintro ⟨⟨hxS', _⟩, hxy⟩
              exact ⟨hxS', hxy.symm⟩
          rw [← Finset.card_filter, hsub, Finset.card_filter]
        exact hLHS.trans hRHS.symm
      have hdegS' : ∀ x ∈ S', (S'.filter (L.Adj x)).card = if x = u₁ ∨ x = u₂ then 1 else 2 := by
        intro x hxS'
        have hxS : x ∈ S := (mem_erase.mp hxS').2
        have hxv : x ≠ v := (mem_erase.mp hxS').1
        by_cases hxu : x = u₁ ∨ x = u₂
        · rw [if_pos hxu]
          have hvx : L.Adj x v := by
            rcases hxu with rfl | rfl
            · exact (mem_filter.mp hu₁).2.symm
            · exact (mem_filter.mp hu₂).2.symm
          have h1 : S'.filter (L.Adj x) = (S.filter (L.Adj x)).erase v := by
            ext y; simp only [S', mem_filter, mem_erase]; tauto
          rw [h1, card_erase_of_mem (mem_filter.mpr ⟨hvS, hvx⟩), hreg x hxS]
        · rw [if_neg hxu]
          have hnvx : ¬ L.Adj x v := by
            intro hvx
            have hxN : x ∈ ({u₁, u₂} : Finset (Fin k)) := by
              rw [← hNv_eq]; exact mem_filter.mpr ⟨hxS, hvx.symm⟩
            simp only [mem_insert, mem_singleton] at hxN
            exact hxu hxN
          have h1 : S'.filter (L.Adj x) = S.filter (L.Adj x) := by
            ext y; simp only [S', mem_filter, mem_erase]
            refine ⟨fun ⟨⟨_, hyS⟩, hxy⟩ => ⟨hyS, hxy⟩, fun ⟨hyS, hxy⟩ => ⟨⟨?_, hyS⟩, hxy⟩⟩
            rintro rfl; exact hnvx hxy
          rw [h1, hreg x hxS]
      have hu1S' : u₁ ∈ S' := mem_erase.mpr ⟨(mem_filter.mp hu₁).2.ne.symm, (mem_filter.mp hu₁).1⟩
      have hu2S' : u₂ ∈ S' := mem_erase.mpr ⟨(mem_filter.mp hu₂).2.ne.symm, (mem_filter.mp hu₂).1⟩
      have hsum_A_B : A.card + B.card = S'.card := by
        have hdisj : Disjoint A B := by
          rw [Finset.disjoint_left]; intro x h1 h2
          simp only [A, B, mem_filter] at h1 h2; rw [h1.2] at h2; cases h2.2
        have hunion : A ∪ B = S' := by
          ext x; simp only [A, B, mem_union, mem_filter]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro h; cases hx : d0 x
            · exact Or.inr ⟨h, rfl⟩
            · exact Or.inl ⟨h, rfl⟩
        rw [← card_union_of_disjoint hdisj, hunion]
      have hS'_card : S'.card + 1 = S.card := by
        rw [card_erase_of_mem hvS]; have := Finset.card_pos.mpr ⟨v, hvS⟩; omega
      -- One of u₁, u₂ is in A and the other is in B
      have hsum_single : ∀ (X : Finset (Fin k)) (u : Fin k), X ⊆ S' → u ∈ X →
          (∀ w ∈ X, (w = u₁ ∨ w = u₂) ↔ w = u) →
          ∑ x ∈ X, (S'.filter (L.Adj x)).card = 2 * X.card - 1 := by
        intro X u hXS' huX huniq
        rw [← Finset.add_sum_erase _ _ huX]
        have hu_val : (S'.filter (L.Adj u)).card = 1 := by
          rw [hdegS' u (hXS' huX), if_pos ((huniq u huX).mpr rfl)]
        have hrest : ∑ x ∈ X.erase u, (S'.filter (L.Adj x)).card = 2 * (X.card - 1) := by
          calc ∑ x ∈ X.erase u, (S'.filter (L.Adj x)).card
              = ∑ _x ∈ X.erase u, 2 := by
                refine Finset.sum_congr rfl fun x hx => ?_
                have hxX : x ∈ X := (mem_erase.mp hx).2
                have hxu : x ≠ u := (mem_erase.mp hx).1
                rw [hdegS' x (hXS' hxX), if_neg (fun h => hxu ((huniq x hxX).mp h))]
            _ = 2 * (X.erase u).card := by simp [mul_comm]
            _ = 2 * (X.card - 1) := by rw [card_erase_of_mem huX]
        have hXpos : 1 ≤ X.card := Finset.card_pos.mpr ⟨u, huX⟩
        omega
      cases h1 : d0 u₁ <;> cases h2 : d0 u₂
      · exact hne (h1.trans h2.symm)
      · have hAeq := hsum_single A u₂ (filter_subset _ _) (mem_filter.mpr ⟨hu2S', h2⟩) (fun w hw => by
          simp only [A, mem_filter] at hw
          constructor
          · rintro (rfl | rfl)
            · rw [h1] at hw; cases hw.2
            · rfl
          · rintro rfl; exact Or.inr rfl)
        have hBeq := hsum_single B u₁ (filter_subset _ _) (mem_filter.mpr ⟨hu1S', h1⟩) (fun w hw => by
          simp only [B, mem_filter] at hw
          constructor
          · rintro (rfl | rfl)
            · rfl
            · rw [h2] at hw; cases hw.2
          · rintro rfl; exact Or.inl rfl)
        have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨u₂, mem_filter.mpr ⟨hu2S', h2⟩⟩
        have hBpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨u₁, mem_filter.mpr ⟨hu1S', h1⟩⟩
        obtain ⟨m, hm⟩ := hSeven
        omega
      · have hAeq := hsum_single A u₁ (filter_subset _ _) (mem_filter.mpr ⟨hu1S', h1⟩) (fun w hw => by
          simp only [A, mem_filter] at hw
          constructor
          · rintro (rfl | rfl)
            · rfl
            · rw [h2] at hw; cases hw.2
          · rintro rfl; exact Or.inl rfl)
        have hBeq := hsum_single B u₂ (filter_subset _ _) (mem_filter.mpr ⟨hu2S', h2⟩) (fun w hw => by
          simp only [B, mem_filter] at hw
          constructor
          · rintro (rfl | rfl)
            · rw [h1] at hw; cases hw.2
            · rfl
          · rintro rfl; exact Or.inr rfl)
        have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨u₁, mem_filter.mpr ⟨hu1S', h1⟩⟩
        have hBpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨u₂, mem_filter.mpr ⟨hu2S', h2⟩⟩
        obtain ⟨m, hm⟩ := hSeven
        omega
      · exact hne (h1.trans h2.symm)
    -- Proper 2-coloring of S by setting d v = !d0 u₁
    let d : Fin k → Bool := fun x => if x = v then !(d0 u₁) else d0 x
    refine ⟨d, fun x hx y hy hxy ⟨h1, h2⟩ => ?_⟩
    have hdx_eq : d x = d y := h1.trans h2.symm
    by_cases hxv : x = v
    · subst hxv
      have hyN : y ∈ ({u₁, u₂} : Finset (Fin k)) := by
        rw [← hNv_eq]; exact mem_filter.mpr ⟨hy, hxy⟩
      simp only [mem_insert, mem_singleton] at hyN
      have hyv : y ≠ x := hxy.ne.symm
      simp only [d, if_pos rfl, if_neg hyv] at hdx_eq
      rcases hyN with rfl | rfl
      · cases d0 y <;> simp at hdx_eq
      · rw [hd0_eq] at hdx_eq; cases d0 y <;> simp at hdx_eq
    · by_cases hyv : y = v
      · subst hyv
        have hxN : x ∈ ({u₁, u₂} : Finset (Fin k)) := by
          rw [← hNv_eq]; exact mem_filter.mpr ⟨hx, hxy.symm⟩
        simp only [mem_insert, mem_singleton] at hxN
        simp only [d, if_neg hxv, if_pos rfl] at hdx_eq
        rcases hxN with rfl | rfl
        · cases d0 x <;> simp at hdx_eq
        · rw [hd0_eq] at hdx_eq; cases d0 x <;> simp at hdx_eq
      · simp only [d, if_neg hxv, if_neg hyv] at hdx_eq
        exact hd0 x (mem_erase.mpr ⟨hxv, hx⟩) y (mem_erase.mpr ⟨hyv, hy⟩) hxy hdx_eq

private lemma solve_finset {k : ℕ} (L : SimpleGraph (Fin k)) (hL : L.CliqueFree 3)
    (c : Fin k → Fin k → Bool) (hcs : ∀ x y, c x y = c y x) :
    ∀ S : Finset (Fin k), S.card ≤ 7 →
      ∃ d : Fin k → Bool, ∀ x ∈ S, ∀ y ∈ S, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y) := by
  classical
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hScard
    by_cases hS : S.Nonempty
    swap
    · exact ⟨fun _ => false, fun x hx => (hS ⟨x, hx⟩).elim⟩
    -- Case A: some vertex has degree ≤ 1 in S
    by_cases hlow : ∃ v ∈ S, (S.filter (L.Adj v)).card ≤ 1
    · obtain ⟨v, hvS, hvdeg⟩ := hlow
      have hsub_card : (S.erase v).card ≤ 7 := (card_le_card (erase_subset _ _)).trans hScard
      obtain ⟨d0, hd0⟩ := ih (S.erase v) (erase_ssubset hvS) hsub_card
      let Nv := (S.erase v).filter (L.Adj v)
      have hNv_card : Nv.card ≤ 1 :=
        (card_le_card (filter_subset_filter _ (erase_subset _ _))).trans hvdeg
      let bv : Bool := if h : Nv.Nonempty then !(d0 (Classical.choose h)) else false
      let d : Fin k → Bool := fun x => if x = v then bv else d0 x
      refine ⟨d, fun x hx y hy hxy => ?_⟩
      by_cases hxv : x = v
      · subst hxv
        have hyv : y ≠ x := hxy.ne.symm
        have hyN : y ∈ Nv := mem_filter.mpr ⟨mem_erase.mpr ⟨hyv, hy⟩, hxy⟩
        have hne : Nv.Nonempty := ⟨y, hyN⟩
        have huniq : Classical.choose hne = y :=
          Finset.card_le_one.mp hNv_card _ (Classical.choose_spec hne) _ hyN
        rintro ⟨h1, h2⟩
        have hEq : d x = d y := h1.trans h2.symm
        simp only [d, if_pos rfl, if_neg hyv, bv, dif_pos hne, huniq] at hEq
        cases d0 y <;> simp at hEq
      · by_cases hyv : y = v
        · subst hyv
          have hxN : x ∈ Nv := mem_filter.mpr ⟨mem_erase.mpr ⟨hxv, hx⟩, hxy.symm⟩
          have hne : Nv.Nonempty := ⟨x, hxN⟩
          have huniq : Classical.choose hne = x :=
            Finset.card_le_one.mp hNv_card _ (Classical.choose_spec hne) _ hxN
          rintro ⟨h1, h2⟩
          have hEq : d x = d y := h1.trans h2.symm
          simp only [d, if_neg hxv, if_pos rfl, bv, dif_pos hne, huniq] at hEq
          cases d0 x <;> simp at hEq
        · simp only [d, if_neg hxv, if_neg hyv]
          exact hd0 x (mem_erase.mpr ⟨hxv, hx⟩) y (mem_erase.mpr ⟨hyv, hy⟩) hxy
    · -- Every vertex in S has degree ≥ 2
      push_neg at hlow
      -- Case B: every vertex has degree = 2
      by_cases hall2 : ∀ v ∈ S, (S.filter (L.Adj v)).card = 2
      · exact solve_two_regular L hL S hScard hall2 c hcs
      · -- Case C: maximum degree Δ ≥ 3
        obtain ⟨v, hvS, hvmax⟩ := Finset.exists_max_image S (fun x => (S.filter (L.Adj x)).card) hS
        have hv3 : 3 ≤ (S.filter (L.Adj v)).card := by
          by_contra hlt
          apply hall2
          intro w hw
          have h1 := hlow w hw
          have h2 := hvmax w hw
          omega
        let N := S.filter (L.Adj v)
        let R := (S.erase v) \ N
        -- Partition S into N and S \ N (= insert v R)
        have hR_card : R.card ≤ 3 := by
          have hN_ge3 : 3 ≤ N.card := hv3
          have hN_sub : N ⊆ S.erase v := fun x hx =>
            mem_erase.mpr ⟨(mem_filter.mp hx).2.ne.symm, (mem_filter.mp hx).1⟩
          have h1 := Finset.card_sdiff_add_card_eq_card hN_sub
          rw [card_erase_of_mem hvS] at h1
          change R.card + N.card = S.card - 1 at h1
          have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hvS⟩
          omega
        -- Subcase C1: all edges inside R have the same color b
        by_cases hmonoR : ∃ b : Bool, ∀ x ∈ R, ∀ y ∈ R, L.Adj x y → c x y = b
        · obtain ⟨b, hb⟩ := hmonoR
          let d : Fin k → Bool := fun x => if x ∈ N then b else !b
          refine ⟨d, fun x hx y hy hxy => ?_⟩
          by_cases hxN : x ∈ N
          · by_cases hyN : y ∈ N
            · exact absurd hxy (indep_of_adj hL (mem_filter.mp hxN).2 (mem_filter.mp hyN).2)
            · rintro ⟨h1, h2⟩
              have hEq : d x = d y := h1.trans h2.symm
              simp only [d, if_pos hxN, if_neg hyN] at hEq
              cases b <;> simp at hEq
          · by_cases hyN : y ∈ N
            · rintro ⟨h1, h2⟩
              have hEq : d x = d y := h1.trans h2.symm
              simp only [d, if_neg hxN, if_pos hyN] at hEq
              cases b <;> simp at hEq
            · have hxR : x ∈ R := by
                refine mem_sdiff.mpr ⟨mem_erase.mpr ⟨?_, hx⟩, hxN⟩
                rintro rfl
                exact hyN (mem_filter.mpr ⟨hy, hxy⟩)
              have hyR : y ∈ R := by
                refine mem_sdiff.mpr ⟨mem_erase.mpr ⟨?_, hy⟩, hyN⟩
                rintro rfl
                exact hxN (mem_filter.mpr ⟨hx, hxy.symm⟩)
              have hcxy : c x y = b := hb x hxR y hyR hxy
              rintro ⟨h1, _⟩
              simp only [d, if_neg hxN, hcxy] at h1
              cases b <;> simp at h1
        · -- Subcase C2: R has edges of both colors, so R = {w₁, w₂, w₃} is a P₃ centered at w₂, and Δ = 3
          push_neg at hmonoR
          obtain ⟨a₁, ha₁, a₂, ha₂, ha12, hca⟩ := hmonoR false
          obtain ⟨b₁, hb₁, b₂, hb₂, hb12, hcb⟩ := hmonoR true
          -- Since R.card ≤ 3, the two edges {a₁, a₂} and {b₁, b₂} must share a vertex w₂
          have hex_shared : ∃ w₂ ∈ R, ∃ w₁ ∈ R, ∃ w₃ ∈ R,
              w₁ ≠ w₂ ∧ w₃ ≠ w₂ ∧ w₁ ≠ w₃ ∧ L.Adj w₂ w₁ ∧ L.Adj w₂ w₃ := by
            have hne_a : a₁ ≠ a₂ := ha12.ne
            have hne_b : b₁ ≠ b₂ := hb12.ne
            have hne_pair : ¬ ((a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁)) := by
              rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
              · cases h1 : c a₁ a₂ <;> simp [h1] at hca hcb
              · rw [hcs a₁ a₂] at hca; cases h1 : c a₂ a₁ <;> simp [h1] at hca hcb
            by_cases h11 : a₁ = b₁
            · subst h11
              have hne2 : a₂ ≠ b₂ := fun h => hne_pair (Or.inl ⟨rfl, h⟩)
              exact ⟨a₁, ha₁, a₂, ha₂, b₂, hb₂, hne_a.symm, hne_b.symm, hne2, ha12, hb12⟩
            · by_cases h12 : a₁ = b₂
              · subst h12
                have hne2 : a₂ ≠ b₁ := fun h => hne_pair (Or.inr ⟨rfl, h⟩)
                exact ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, hne_a.symm, hne_b, hne2, ha12, hb12.symm⟩
              · by_cases h21 : a₂ = b₁
                · subst h21
                  have hne2 : a₁ ≠ b₂ := fun h => hne_pair (Or.inr ⟨h, rfl⟩)
                  exact ⟨a₂, ha₂, a₁, ha₁, b₂, hb₂, hne_a, hne_b.symm, hne2, ha12.symm, hb12⟩
                · by_cases h22 : a₂ = b₂
                  · subst h22
                    have hne2 : a₁ ≠ b₁ := fun h => hne_pair (Or.inl ⟨h, rfl⟩)
                    exact ⟨a₂, ha₂, a₁, ha₁, b₁, hb₁, hne_a, hne_b, hne2, ha12.symm, hb12.symm⟩
                  · exfalso
                    have hsub : ({a₁, a₂, b₁, b₂} : Finset (Fin k)) ⊆ R := by
                      intro x hx; simp only [mem_insert, mem_singleton] at hx
                      rcases hx with rfl | rfl | rfl | rfl <;> assumption
                    have hc4 : ({a₁, a₂, b₁, b₂} : Finset (Fin k)).card = 4 := by
                      rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
                      · simp [hne_b]
                      · simp [h21, h22]
                      · simp [hne_a, h11, h12]
                    have := Finset.card_le_card hsub
                    omega
          obtain ⟨w₂, hw₂R, w₁, hw₁R, w₃, hw₃R, h12, h32, h13, hw21, hw23⟩ := hex_shared
          have hR_eq : R = {w₁, w₂, w₃} := by
            refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
            · intro x hx; simp only [mem_insert, mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> assumption
            · rw [card_insert_of_notMem (by simp [h12, h13]),
                card_insert_of_notMem (by simp [h32.symm]), card_singleton]
              exact hR_card
          have hR3 : R.card = 3 := by
            rw [hR_eq, card_insert_of_notMem (by simp [h12, h13]),
              card_insert_of_notMem (by simp [h32.symm]), card_singleton]
          -- Hence N.card = 3 (maximum degree is 3!)
          have hN3 : N.card = 3 := by
            have hN_ge3 : 3 ≤ N.card := hv3
            have hN_sub : N ⊆ S.erase v := fun x hx =>
              mem_erase.mpr ⟨(mem_filter.mp hx).2.ne.symm, (mem_filter.mp hx).1⟩
            have h1 := Finset.card_sdiff_add_card_eq_card hN_sub
            rw [card_erase_of_mem hvS] at h1
            change R.card + N.card = S.card - 1 at h1
            have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hvS⟩
            omega
          -- w₂ has degree ≤ 3 in S and already 2 neighbors {w₁, w₃} in R, so at most 1 neighbor in N
          have hw₂S : w₂ ∈ S := (mem_erase.mp (mem_sdiff.mp hw₂R).1).2
          have hw₂_deg : (S.filter (L.Adj w₂)).card ≤ 3 := by
            have := hvmax w₂ hw₂S
            change (S.filter (L.Adj w₂)).card ≤ N.card at this
            omega
          let Nw2 := N.filter (L.Adj w₂)
          have hNw2_card : Nw2.card ≤ 1 := by
            have hdisj : Disjoint Nw2 {w₁, w₃} := by
              rw [Finset.disjoint_left]
              intro x hx1 hx2
              have hxN : x ∈ N := (mem_filter.mp hx1).1
              simp only [mem_insert, mem_singleton] at hx2
              rcases hx2 with rfl | rfl
              · exact (mem_sdiff.mp hw₁R).2 hxN
              · exact (mem_sdiff.mp hw₃R).2 hxN
            have hsub : Nw2 ∪ {w₁, w₃} ⊆ S.filter (L.Adj w₂) := by
              intro x hx
              rcases mem_union.mp hx with hx1 | hx2
              · exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hx1).1).1, (mem_filter.mp hx1).2⟩
              · simp only [mem_insert, mem_singleton] at hx2
                rcases hx2 with rfl | rfl
                · exact mem_filter.mpr ⟨(mem_erase.mp (mem_sdiff.mp hw₁R).1).2, hw21⟩
                · exact mem_filter.mpr ⟨(mem_erase.mp (mem_sdiff.mp hw₃R).1).2, hw23⟩
            have hc := Finset.card_le_card hsub
            rw [card_union_of_disjoint hdisj, card_insert_of_notMem (by simp [h13]), card_singleton] at hc
            omega
          let b : Bool := if h : Nw2.Nonempty then c w₂ (Classical.choose h) else false
          -- Color N ∪ {w₂} with !b and {v, w₁, w₃} with b
          let Bset : Finset (Fin k) := insert w₂ N
          let d : Fin k → Bool := fun x => if x ∈ Bset then !b else b
          refine ⟨d, fun x hx y hy hxy => ?_⟩
          by_cases hxB : x ∈ Bset
          · by_cases hyB : y ∈ Bset
            · -- Both x, y ∈ insert w₂ N: since N is independent, one is w₂ and the other is in Nw2
              have hnotbothN : ¬ (x ∈ N ∧ y ∈ N) := fun ⟨hxN, hyN⟩ =>
                indep_of_adj hL (mem_filter.mp hxN).2 (mem_filter.mp hyN).2 hxy
              simp only [Bset, mem_insert] at hxB hyB
              have hcxy : c x y = b := by
                rcases hxB with rfl | hxN <;> rcases hyB with rfl | hyN
                · exact absurd hxy (L.loopless.irrefl _)
                · have hyNw2 : y ∈ Nw2 := mem_filter.mpr ⟨hyN, hxy⟩
                  have hne : Nw2.Nonempty := ⟨y, hyNw2⟩
                  have huniq : Classical.choose hne = y :=
                    Finset.card_le_one.mp hNw2_card _ (Classical.choose_spec hne) _ hyNw2
                  simp [b, dif_pos hne, huniq]
                · have hxNw2 : x ∈ Nw2 := mem_filter.mpr ⟨hxN, hxy.symm⟩
                  have hne : Nw2.Nonempty := ⟨x, hxNw2⟩
                  have huniq : Classical.choose hne = x :=
                    Finset.card_le_one.mp hNw2_card _ (Classical.choose_spec hne) _ hxNw2
                  rw [hcs x y]
                  simp [b, dif_pos hne, huniq]
                · exact absurd ⟨hxN, hyN⟩ hnotbothN
              rintro ⟨h1, _⟩
              have hxB' : x ∈ Bset := by simp only [Bset, mem_insert]; exact hxB
              simp only [d, if_pos hxB', hcxy] at h1
              cases b <;> simp at h1
            · rintro ⟨h1, h2⟩
              have hEq : d x = d y := h1.trans h2.symm
              simp only [d, if_pos hxB, if_neg hyB] at hEq
              cases b <;> simp at hEq
          · by_cases hyB : y ∈ Bset
            · rintro ⟨h1, h2⟩
              have hEq : d x = d y := h1.trans h2.symm
              simp only [d, if_neg hxB, if_pos hyB] at hEq
              cases b <;> simp at hEq
            · -- Both x, y ∈ S \ (insert w₂ N) = {v, w₁, w₃}, which is an independent set!
              exfalso
              have hmemA : ∀ z ∈ S, z ∉ Bset → z = v ∨ z = w₁ ∨ z = w₃ := by
                intro z hzS hzB
                by_cases hzv : z = v
                · exact Or.inl hzv
                · have hzN : z ∉ N := fun h => hzB (mem_insert_of_mem h)
                  have hzR : z ∈ R := mem_sdiff.mpr ⟨mem_erase.mpr ⟨hzv, hzS⟩, hzN⟩
                  rw [hR_eq] at hzR
                  simp only [mem_insert, mem_singleton] at hzR
                  rcases hzR with rfl | rfl | rfl
                  · exact Or.inr (Or.inl rfl)
                  · exact absurd (mem_insert_self _ N) hzB
                  · exact Or.inr (Or.inr rfl)
              rcases hmemA x hx hxB with rfl | rfl | rfl <;>
                rcases hmemA y hy hyB with rfl | rfl | rfl
              · exact L.loopless.irrefl _ hxy
              · exact (mem_sdiff.mp hw₁R).2 (mem_filter.mpr ⟨hy, hxy⟩)
              · exact (mem_sdiff.mp hw₃R).2 (mem_filter.mpr ⟨hy, hxy⟩)
              · exact (mem_sdiff.mp hw₁R).2 (mem_filter.mpr ⟨hx, hxy.symm⟩)
              · exact L.loopless.irrefl _ hxy
              · exact indep_of_adj hL hw21 hw23 hxy
              · exact (mem_sdiff.mp hw₃R).2 (mem_filter.mpr ⟨hx, hxy.symm⟩)
              · exact indep_of_adj hL hw23 hw21 hxy
              · exact L.loopless.irrefl _ hxy

theorem link_extension_7 : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1.H2 := by
  intro k L hk hL c hcs
  obtain ⟨d, hd⟩ := solve_finset L hL c hcs Finset.univ (by simpa using hk)
  exact ⟨d, fun x y hxy => hd x (Finset.mem_univ x) y (Finset.mem_univ y) hxy⟩

end Erdos151Link7

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1.H2 :=
  Erdos151Link7.link_extension_7
