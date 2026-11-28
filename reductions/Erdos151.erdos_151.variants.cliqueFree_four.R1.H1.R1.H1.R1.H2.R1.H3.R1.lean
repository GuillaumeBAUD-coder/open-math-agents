import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1
import Mathlib

/-! Graver-Yackel / McKay-Min averaging reduction for the min-degree >= 6 branch of
R(3,8) <= 28 (R1.H1.R1.H1.R1.H2.R1.H3): using the triangle-free non-neighborhood edge
sum identity `sum_v 2|E(B_v)| = 96 n_6 + 98 n_7` together with the minimum edge counts
e(3,7;21) >= 51 (H1) and e(3,7;20) >= 44 (H2), every counterexample satisfies
`12 <= n_7` and `Even n_7` (eliminating 6-regular and all `n_7 <= 10`). -/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1_H3_R1

/-- Minimum edge count e(3,7;21) >= 51: every triangle-free 21-vertex graph with
degree sum < 102 (< 51 edges) has an independent set of size 7. -/
def H1 : Prop :=
  ∀ Q : SimpleGraph (Fin 21), Q.CliqueFree 3 →
    (∑ x : Fin 21, (univ.filter (Q.Adj x)).card) < 102 →
    ∃ s, Q.IsNIndepSet 7 s

/-- Minimum edge count e(3,7;20) >= 44: every triangle-free 20-vertex graph with
degree sum < 88 (< 44 edges) has an independent set of size 7. -/
def H2 : Prop :=
  ∀ Q : SimpleGraph (Fin 20), Q.CliqueFree 3 →
    (∑ x : Fin 20, (univ.filter (Q.Adj x)).card) < 88 →
    ∃ s, Q.IsNIndepSet 7 s

/-- Remaining branch: no triangle-free 28-vertex graph with all degrees in {6,7}
and at least 12 (and an even number of) vertices of degree 7 avoids an independent 8-set. -/
def H3 : Prop :=
  ∀ G : SimpleGraph (Fin 28), G.CliqueFree 3 →
    (∀ v : Fin 28, 6 ≤ (univ.filter (G.Adj v)).card ∧ (univ.filter (G.Adj v)).card ≤ 7) →
    12 ≤ (univ.filter (fun v : Fin 28 => (univ.filter (G.Adj v)).card = 7)).card →
    Even (univ.filter (fun v : Fin 28 => (univ.filter (G.Adj v)).card = 7)).card →
    ∃ s, G.IsNIndepSet 8 s

section Proof

private lemma nonnbr_edge_sum_eq (G : SimpleGraph (Fin 28)) (hG : G.CliqueFree 3) (v : Fin 28) :
    let N := univ.filter (G.Adj v)
    let B := univ.filter (fun x => x ≠ v ∧ ¬ G.Adj v x)
    (∑ x ∈ B, (B.filter (G.Adj x)).card) + 2 * (∑ u ∈ N, (univ.filter (G.Adj u)).card) =
      ∑ x : Fin 28, (univ.filter (G.Adj x)).card := by
  classical
  intro N B
  have hdisj_vN : Disjoint ({v} : Finset (Fin 28)) N := by
    rw [Finset.disjoint_singleton_left]
    simp [N]
  have hdisj_vNB : Disjoint ({v} ∪ N) B := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h2 := (Finset.mem_filter.mp hx2).2
    rcases Finset.mem_union.mp hx1 with hv | hn
    · exact h2.1 (Finset.mem_singleton.mp hv)
    · exact h2.2 (Finset.mem_filter.mp hn).2
  have huniv : ({v} : Finset (Fin 28)) ∪ N ∪ B = univ := by
    ext x
    simp only [N, B, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    by_cases hxv : x = v
    · exact Or.inl (Or.inl hxv)
    · by_cases hadj : G.Adj v x
      · exact Or.inl (Or.inr hadj)
      · exact Or.inr ⟨hxv, hadj⟩
  have hsum_all :
      (∑ x : Fin 28, (univ.filter (G.Adj x)).card) =
        (univ.filter (G.Adj v)).card +
        (∑ u ∈ N, (univ.filter (G.Adj u)).card) +
        (∑ x ∈ B, (univ.filter (G.Adj x)).card) := by
    rw [← huniv, Finset.sum_union hdisj_vNB, Finset.sum_union hdisj_vN, Finset.sum_singleton]
  have hB_split : ∀ x ∈ B,
      (univ.filter (G.Adj x)).card =
        (B.filter (G.Adj x)).card + (N.filter (G.Adj x)).card := by
    intro x hx
    have hxB := (Finset.mem_filter.mp hx).2
    have hdisj : Disjoint (B.filter (G.Adj x)) (N.filter (G.Adj x)) := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy1).1).2.2
        (Finset.mem_filter.mp (Finset.mem_filter.mp hy2).1).2
    have heq : univ.filter (G.Adj x) = B.filter (G.Adj x) ∪ N.filter (G.Adj x) := by
      ext y
      simp only [B, N, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hxy
        by_cases hyv : y = v
        · subst hyv
          exact (hxB.2 (G.symm.symm _ _ hxy)).elim
        · by_cases hvy : G.Adj v y
          · exact Or.inr ⟨hvy, hxy⟩
          · exact Or.inl ⟨⟨hyv, hvy⟩, hxy⟩
      · rintro (⟨_, hxy⟩ | ⟨_, hxy⟩) <;> exact hxy
    rw [heq, Finset.card_union_of_disjoint hdisj]
  have hsum_B :
      (∑ x ∈ B, (univ.filter (G.Adj x)).card) =
        (∑ x ∈ B, (B.filter (G.Adj x)).card) + (∑ x ∈ B, (N.filter (G.Adj x)).card) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hB_split
  have hN_split : ∀ u ∈ N,
      (univ.filter (G.Adj u)).card = 1 + (B.filter (G.Adj u)).card := by
    intro u hu
    have hvu : G.Adj v u := (Finset.mem_filter.mp hu).2
    have hv_notB : v ∉ B.filter (G.Adj u) := by
      intro h
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1 rfl
    have heq : univ.filter (G.Adj u) = insert v (B.filter (G.Adj u)) := by
      ext y
      simp only [B, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro huy
        by_cases hyv : y = v
        · exact Or.inl hyv
        · refine Or.inr ⟨⟨hyv, ?_⟩, huy⟩
          intro hvy
          have hcl : G.IsNClique 3 ({v, u, y} : Finset (Fin 28)) := by
            have hvu_ne : v ≠ u := hvu.ne
            have hvy_ne : v ≠ y := hvy.ne
            have huy_ne : u ≠ y := huy.ne
            refine ⟨?_, by simp [hvu_ne, hvy_ne, huy_ne]⟩
            intro a ha b hb hab
            simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
            rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
            · exact (hab rfl).elim
            · exact hvu
            · exact hvy
            · exact hvu.symm
            · exact (hab rfl).elim
            · exact huy
            · exact hvy.symm
            · exact huy.symm
            · exact (hab rfl).elim
          exact hG {v, u, y} hcl
      · rintro (rfl | ⟨_, huy⟩)
        · exact hvu.symm
        · exact huy
    rw [heq, Finset.card_insert_of_notMem hv_notB]
    omega
  have hcross : (∑ x ∈ B, (N.filter (G.Adj x)).card) = ∑ u ∈ N, (B.filter (G.Adj u)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => ?_
    by_cases h : G.Adj u x
    · simp [h, G.symm.symm _ _ h]
    · have h' : ¬ G.Adj x u := fun hxu => h (G.symm.symm _ _ hxu)
      simp [h, h']
  have hsum_N :
      (∑ u ∈ N, (univ.filter (G.Adj u)).card) =
        N.card + ∑ u ∈ N, (B.filter (G.Adj u)).card := by
    calc (∑ u ∈ N, (univ.filter (G.Adj u)).card)
        = ∑ u ∈ N, (1 + (B.filter (G.Adj u)).card) := Finset.sum_congr rfl hN_split
      _ = (∑ _u ∈ N, 1) + ∑ u ∈ N, (B.filter (G.Adj u)).card := Finset.sum_add_distrib
      _ = N.card + ∑ u ∈ N, (B.filter (G.Adj u)).card := by simp
  have hNcard : N.card = (univ.filter (G.Adj v)).card := rfl
  omega

private lemma nonnbr_card (G : SimpleGraph (Fin 28)) (v : Fin 28) :
    (univ.filter (fun x : Fin 28 => x ≠ v ∧ ¬ G.Adj v x)).card +
      (univ.filter (G.Adj v)).card + 1 = 28 := by
  classical
  let N := univ.filter (G.Adj v)
  let B := univ.filter (fun x : Fin 28 => x ≠ v ∧ ¬ G.Adj v x)
  have hdisj1 : Disjoint B N := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp hx1).2.2 (Finset.mem_filter.mp hx2).2
  have hv_not : v ∉ B ∪ N := by
    intro h
    rcases Finset.mem_union.mp h with hB | hN
    · exact (Finset.mem_filter.mp hB).2.1 rfl
    · exact G.irrefl (Finset.mem_filter.mp hN).2
  have huniv : insert v (B ∪ N) = univ := by
    ext x
    simp only [B, N, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    by_cases hxv : x = v
    · exact Or.inl hxv
    · by_cases hadj : G.Adj v x
      · exact Or.inr (Or.inr hadj)
      · exact Or.inr (Or.inl ⟨hxv, hadj⟩)
  have hcard : (insert v (B ∪ N)).card = 28 := by
    rw [huniv]
    simp
  rw [Finset.card_insert_of_notMem hv_not, Finset.card_union_of_disjoint hdisj1] at hcard
  exact hcard

private lemma nonnbr_deg_sum_ge {m : ℕ} (G : SimpleGraph (Fin 28)) (hG : G.CliqueFree 3)
    (hno : ¬ ∃ s, G.IsNIndepSet 8 s) (v : Fin 28) (t : ℕ)
    (hbound : ∀ Q : SimpleGraph (Fin m), Q.CliqueFree 3 →
      (∑ x : Fin m, (univ.filter (Q.Adj x)).card) < t → ∃ s, Q.IsNIndepSet 7 s)
    (hcard : (univ.filter (fun x : Fin 28 => x ≠ v ∧ ¬ G.Adj v x)).card = m) :
    t ≤ ∑ x ∈ univ.filter (fun x : Fin 28 => x ≠ v ∧ ¬ G.Adj v x),
      ((univ.filter (fun x : Fin 28 => x ≠ v ∧ ¬ G.Adj v x)).filter (G.Adj x)).card := by
  classical
  let B := univ.filter (fun x : Fin 28 => x ≠ v ∧ ¬ G.Adj v x)
  have hBeq : Fintype.card B = m := by simpa [Fintype.card_coe] using hcard
  let e : Fin m ≃ B := (Fintype.equivFinOfCardEq hBeq).symm
  let Q : SimpleGraph (Fin m) := {
    Adj := fun i j => G.Adj (e i).val (e j).val
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨fun _ h => G.irrefl h⟩
  }
  have hQtf : Q.CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp hs
    have hcl : G.IsNClique 3 ({(e a).val, (e b).val, (e c).val} : Finset (Fin 28)) := by
      have hne1 : (e a).val ≠ (e b).val := G.ne_of_adj hab
      have hne2 : (e a).val ≠ (e c).val := G.ne_of_adj hac
      have hne3 : (e b).val ≠ (e c).val := G.ne_of_adj hbc
      refine ⟨?_, by simp [hne1, hne2, hne3]⟩
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact (hxy rfl).elim
      · exact hab
      · exact hac
      · exact hab.symm
      · exact (hxy rfl).elim
      · exact hbc
      · exact hac.symm
      · exact hbc.symm
      · exact (hxy rfl).elim
    exact hG _ hcl
  have hsum_eq :
      (∑ i : Fin m, (univ.filter (Q.Adj i)).card) =
        ∑ x ∈ B, (B.filter (G.Adj x)).card := by
    have h1 : ∀ i : Fin m, (univ.filter (Q.Adj i)).card = (B.filter (G.Adj (e i).val)).card := by
      intro i
      refine Finset.card_bij (fun j _ => (e j).val) ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_filter.mpr ⟨(e j).property, (Finset.mem_filter.mp hj).2⟩
      · intro j₁ _ j₂ _ heq
        exact e.injective (Subtype.ext heq)
      · intro y hy
        obtain ⟨hyB, hadj⟩ := Finset.mem_filter.mp hy
        refine ⟨e.symm ⟨y, hyB⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [Q] using hadj
        · simp
    calc (∑ i : Fin m, (univ.filter (Q.Adj i)).card)
        = ∑ i : Fin m, (B.filter (G.Adj (e i).val)).card := Finset.sum_congr rfl (fun i _ => h1 i)
      _ = ∑ x : B, (B.filter (G.Adj x.val)).card := Equiv.sum_comp e (fun x : B => (B.filter (G.Adj x.val)).card)
      _ = ∑ x ∈ B, (B.filter (G.Adj x)).card :=
            Finset.sum_coe_sort B (fun x => (B.filter (G.Adj x)).card)
  by_contra hlt
  push Not at hlt
  rw [← hsum_eq] at hlt
  obtain ⟨s, hs⟩ := hbound Q hQtf hlt
  let S : Finset (Fin 28) := s.image (fun i => (e i).val)
  have hScard : S.card = 7 := by
    rw [Finset.card_image_of_injective s (fun i j hij => e.injective (Subtype.ext hij))]
    exact hs.card_eq
  have hv_notS : v ∉ S := by
    intro hvS
    rcases Finset.mem_image.mp hvS with ⟨i, _, hi⟩
    exact (Finset.mem_filter.mp (e i).property).2.1 hi
  apply hno
  refine ⟨insert v S, ?_, ?_⟩
  · intro x hx y hy hxy hadj
    simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
    rcases hx with rfl | hxS <;> rcases hy with rfl | hyS
    · exact hxy rfl
    · rcases Finset.mem_image.mp hyS with ⟨j, _, rfl⟩
      exact (Finset.mem_filter.mp (e j).property).2.2 hadj
    · rcases Finset.mem_image.mp hxS with ⟨i, _, rfl⟩
      exact (Finset.mem_filter.mp (e i).property).2.2 hadj.symm
    · rcases Finset.mem_image.mp hxS with ⟨i, hi, rfl⟩
      rcases Finset.mem_image.mp hyS with ⟨j, hj, rfl⟩
      have hij : i ≠ j := fun h => hxy (by rw [h])
      exact hs.isIndepSet hi hj hij hadj
  · rw [Finset.card_insert_of_notMem hv_notS, hScard]

private lemma sum_deg_even (G : SimpleGraph (Fin 28)) :
    Even (∑ x : Fin 28, (univ.filter (G.Adj x)).card) := by
  classical
  let E := univ.filter (fun p : Fin 28 × Fin 28 => p.1 < p.2 ∧ G.Adj p.1 p.2)
  let D := univ.filter (fun p : Fin 28 × Fin 28 => G.Adj p.1 p.2)
  have hD1 : D.card = ∑ x : Fin 28, (univ.filter (G.Adj x)).card := by
    simp only [D, Finset.card_filter, Fintype.sum_prod_type]
  have hD2 : D = E ∪ E.image Prod.swap := by
    ext ⟨u, v⟩
    simp only [D, E, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · intro huv
      rcases lt_trichotomy u v with h | rfl | h
      · exact Or.inl ⟨h, huv⟩
      · exact (G.irrefl huv).elim
      · exact Or.inr ⟨v, u, ⟨h, huv.symm⟩, rfl, rfl⟩
    · rintro (⟨_, huv⟩ | ⟨a, b, ⟨_, hab⟩, rfl, rfl⟩)
      · exact huv
      · exact hab.symm
  have hdisj : Disjoint E (E.image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro ⟨u, v⟩ h1 h2
    have hlt1 := (Finset.mem_filter.mp h1).2.1
    rcases Finset.mem_image.mp h2 with ⟨⟨a, b⟩, hab, heq⟩
    have hlt2 := (Finset.mem_filter.mp hab).2.1
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact lt_asymm hlt1 hlt2
  refine ⟨E.card, ?_⟩
  rw [← hD1, hD2, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective E Prod.swap_injective]

theorem main : H1 → H2 → H3 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1.H3 := by
  classical
  intro h1 h2 h3 G hG hdeg
  by_contra hno
  let d : Fin 28 → ℕ := fun v => (univ.filter (G.Adj v)).card
  let S6 := univ.filter (fun v : Fin 28 => d v = 6)
  let S7 := univ.filter (fun v : Fin 28 => d v = 7)
  have hdisj67 : Disjoint S6 S7 := by
    rw [Finset.disjoint_left]
    intro v h6 h7
    have := (Finset.mem_filter.mp h6).2
    have := (Finset.mem_filter.mp h7).2
    omega
  have hunion67 : S6 ∪ S7 = univ := by
    ext v
    simp only [S6, S7, d, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have := hdeg v
    omega
  have hcard67 : S6.card + S7.card = 28 := by
    have h := congrArg Finset.card hunion67
    rw [Finset.card_union_of_disjoint hdisj67] at h
    simpa using h
  have hsum_d : (∑ v : Fin 28, d v) = 6 * S6.card + 7 * S7.card := by
    rw [← hunion67, Finset.sum_union hdisj67]
    have h6 : ∑ v ∈ S6, d v = 6 * S6.card := by
      calc ∑ v ∈ S6, d v = ∑ _v ∈ S6, 6 := Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
        _ = 6 * S6.card := by simp [mul_comm]
    have h7 : ∑ v ∈ S7, d v = 7 * S7.card := by
      calc ∑ v ∈ S7, d v = ∑ _v ∈ S7, 7 := Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
        _ = 7 * S7.card := by simp [mul_comm]
    rw [h6, h7]
  have hsum_d2 : (∑ v : Fin 28, d v * d v) = 36 * S6.card + 49 * S7.card := by
    rw [← hunion67, Finset.sum_union hdisj67]
    have h6 : ∑ v ∈ S6, d v * d v = 36 * S6.card := by
      calc ∑ v ∈ S6, d v * d v = ∑ _v ∈ S6, 36 := Finset.sum_congr rfl (fun v hv => by
            have := (Finset.mem_filter.mp hv).2; rw [this])
        _ = 36 * S6.card := by simp [mul_comm]
    have h7 : ∑ v ∈ S7, d v * d v = 49 * S7.card := by
      calc ∑ v ∈ S7, d v * d v = ∑ _v ∈ S7, 49 := Finset.sum_congr rfl (fun v hv => by
            have := (Finset.mem_filter.mp hv).2; rw [this])
        _ = 49 * S7.card := by simp [mul_comm]
    rw [h6, h7]
  have hsum_Q :
      (∑ v : Fin 28, ∑ u ∈ univ.filter (G.Adj v), d u) = ∑ u : Fin 28, d u * d u := by
    calc (∑ v : Fin 28, ∑ u ∈ univ.filter (G.Adj v), d u)
        = ∑ v : Fin 28, ∑ u : Fin 28, if G.Adj v u then d u else 0 := by
            refine Finset.sum_congr rfl fun v _ => Finset.sum_filter _ _
      _ = ∑ u : Fin 28, ∑ v : Fin 28, if G.Adj v u then d u else 0 := Finset.sum_comm
      _ = ∑ u : Fin 28, ∑ v : Fin 28, if G.Adj u v then d u else 0 := by
            refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
            by_cases h : G.Adj v u
            · simp [h, G.symm.symm _ _ h]
            · have h' : ¬ G.Adj u v := fun huv => h (G.symm.symm _ _ huv)
              simp [h, h']
      _ = ∑ u : Fin 28, (univ.filter (G.Adj u)).card * d u := by
            refine Finset.sum_congr rfl fun u _ => by
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      _ = ∑ u : Fin 28, d u * d u := rfl
  let B : Fin 28 → Finset (Fin 28) := fun v => univ.filter (fun x => x ≠ v ∧ ¬ G.Adj v x)
  have hsum_id :
      (∑ v : Fin 28, ∑ x ∈ B v, ((B v).filter (G.Adj x)).card) +
        2 * (∑ v : Fin 28, ∑ u ∈ univ.filter (G.Adj v), d u) =
        28 * (∑ x : Fin 28, d x) := by
    have hpt : ∀ v : Fin 28,
        (∑ x ∈ B v, ((B v).filter (G.Adj x)).card) +
          2 * (∑ u ∈ univ.filter (G.Adj v), d u) = ∑ x : Fin 28, d x :=
      fun v => nonnbr_edge_sum_eq G hG v
    calc (∑ v : Fin 28, ∑ x ∈ B v, ((B v).filter (G.Adj x)).card) +
          2 * (∑ v : Fin 28, ∑ u ∈ univ.filter (G.Adj v), d u)
        = ∑ v : Fin 28, ((∑ x ∈ B v, ((B v).filter (G.Adj x)).card) +
            2 * (∑ u ∈ univ.filter (G.Adj v), d u)) := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = ∑ _v : Fin 28, (∑ x : Fin 28, d x) := Finset.sum_congr rfl (fun v _ => hpt v)
      _ = 28 * (∑ x : Fin 28, d x) := by simp
  have hlb : 102 * S6.card + 88 * S7.card ≤
      ∑ v : Fin 28, ∑ x ∈ B v, ((B v).filter (G.Adj x)).card := by
    rw [← hunion67, Finset.sum_union hdisj67]
    have hlb6 : 102 * S6.card ≤ ∑ v ∈ S6, ∑ x ∈ B v, ((B v).filter (G.Adj x)).card := by
      calc 102 * S6.card = ∑ _v ∈ S6, 102 := by simp [mul_comm]
        _ ≤ ∑ v ∈ S6, ∑ x ∈ B v, ((B v).filter (G.Adj x)).card := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hd6 : d v = 6 := (Finset.mem_filter.mp hv).2
          have hBc : (B v).card = 21 := by have := nonnbr_card G v; dsimp [B, d] at *; omega
          exact nonnbr_deg_sum_ge G hG hno v 102 h1 hBc
    have hlb7 : 88 * S7.card ≤ ∑ v ∈ S7, ∑ x ∈ B v, ((B v).filter (G.Adj x)).card := by
      calc 88 * S7.card = ∑ _v ∈ S7, 88 := by simp [mul_comm]
        _ ≤ ∑ v ∈ S7, ∑ x ∈ B v, ((B v).filter (G.Adj x)).card := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hd7 : d v = 7 := (Finset.mem_filter.mp hv).2
          have hBc : (B v).card = 20 := by have := nonnbr_card G v; dsimp [B, d] at *; omega
          exact nonnbr_deg_sum_ge G hG hno v 88 h2 hBc
    omega
  have heven_S7 : Even S7.card := by
    obtain ⟨k, hk⟩ := sum_deg_even G
    change ∑ x : Fin 28, d x = k + k at hk
    rw [hsum_d] at hk
    refine ⟨k - 3 * S6.card - 3 * S7.card, ?_⟩
    omega
  have hge12 : 12 ≤ S7.card := by
    rw [hsum_Q, hsum_d2, hsum_d] at hsum_id
    obtain ⟨m, hm⟩ := heven_S7
    omega
  exact hno (h3 G hG hdeg hge12 heven_S7)

end Proof

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1_H3_R1
