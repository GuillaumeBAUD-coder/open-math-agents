import OMAStatements.S_oeis_a095338
import Mathlib

open Finset
/- Double counting, as in the argument recorded in the OEIS entry (Bertran Steinsky): the total
   number of leaves is the sum over vertices v of the number of graphs in which v has degree 1.
   Such a graph is determined by the unique neighbour u of v (n - 1 choices) and an arbitrary
   simple graph on the other n - 1 vertices (2^C(n-1,2) choices). -/

theorem oma_card_graphs (V : Type) [Fintype V] [DecidableEq V] :
    Fintype.card (SimpleGraph V) = 2 ^ (Fintype.card V).choose 2 := by
  classical
  let e : SimpleGraph V ≃ Set {x : Sym2 V // ¬ x.IsDiag} :=
    { toFun := fun G => {x | x.1 ∈ G.edgeSet}
      invFun := fun S => SimpleGraph.fromEdgeSet (Subtype.val '' S)
      left_inv := by
        intro G
        conv_rhs => rw [← SimpleGraph.fromEdgeSet_edgeSet G]
        ext a b
        simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_image, Set.mem_ofPred_eq,
          SimpleGraph.mem_edgeSet]
        constructor
        · rintro ⟨⟨x, hx, hxe⟩, hne⟩; rw [hxe] at hx; exact ⟨hx, hne⟩
        · rintro ⟨hx, hne⟩; exact ⟨⟨⟨s(a, b), by simpa using hne⟩, hx, rfl⟩, hne⟩
      right_inv := by
        intro S
        ext ⟨x, hx⟩
        simp only [Set.mem_ofPred_eq, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
          Set.mem_image, Sym2.mem_diagSet]
        constructor
        · rintro ⟨⟨y, hy, hyx⟩, _⟩
          have : y = ⟨x, hx⟩ := Subtype.ext hyx
          rw [← this]; exact hy
        · intro h; exact ⟨⟨⟨x, hx⟩, h, rfl⟩, hx⟩ }
  rw [Fintype.card_congr e, Fintype.card_set, Sym2.card_subtype_not_diag]

section
open Classical

def oma_build {n : ℕ} (v u : Fin n) (H : SimpleGraph {w : Fin n // w ≠ v}) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => (a = v ∧ b = u) ∨ ∃ (ha : a ≠ v) (hb : b ≠ v), H.Adj ⟨a, ha⟩ ⟨b, hb⟩

theorem oma_build_adj_v {n : ℕ} (v u : Fin n) (hu : u ≠ v) (H : SimpleGraph {w : Fin n // w ≠ v})
    (b : Fin n) : (oma_build v u H).Adj v b ↔ b = u := by
  unfold oma_build
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hvb, (⟨_, h⟩ | ⟨ha, _, _⟩) | (⟨h, _⟩ | ⟨_, hb, _⟩)⟩
    · exact h
    · exact absurd rfl ha
    · exact absurd h.symm hvb
    · exact absurd rfl hb
  · rintro rfl
    exact ⟨hu.symm, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩

theorem oma_build_adj_sub {n : ℕ} (v u : Fin n) (H : SimpleGraph {w : Fin n // w ≠ v})
    (x y : {w : Fin n // w ≠ v}) : (oma_build v u H).Adj x.1 y.1 ↔ H.Adj x y := by
  unfold oma_build
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, (⟨h, _⟩ | ⟨_, _, h⟩) | (⟨h, _⟩ | ⟨_, _, h⟩)⟩
    · exact absurd h x.2
    · exact h
    · exact absurd h y.2
    · exact h.symm
  · intro h
    refine ⟨fun e => H.ne_of_adj h (Subtype.ext e), Or.inl (Or.inr ⟨x.2, y.2, h⟩)⟩

theorem oma_count (n : ℕ) (v : Fin n) :
    (univ.filter fun G : SimpleGraph (Fin n) => G.degree v = 1).card =
      (n - 1) * 2 ^ (n - 1).choose 2 := by
  have hsub : Fintype.card {w : Fin n // w ≠ v} = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  have hfil : (univ.filter fun w : Fin n => w ≠ v).card = n - 1 := by
    rw [filter_ne' univ v, card_erase_of_mem (mem_univ v),
      card_univ, Fintype.card_fin]
  have hprod : ((univ.filter fun w : Fin n => w ≠ v) ×ˢ
      (univ : Finset (SimpleGraph {w : Fin n // w ≠ v}))).card =
      (n - 1) * 2 ^ (n - 1).choose 2 := by
    rw [card_product, hfil, card_univ, oma_card_graphs, hsub]
  rw [← hprod]
  symm
  refine card_bij (fun p _ => oma_build v p.1 p.2) ?_ ?_ ?_
  · rintro ⟨u, H⟩ hp
    simp only [mem_product, mem_filter, mem_univ, true_and] at hp
    simp only [mem_filter, mem_univ, true_and]
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    exact ⟨u, (oma_build_adj_v v u hp.1 H u).mpr rfl,
      fun b hb => (oma_build_adj_v v u hp.1 H b).mp hb⟩
  · rintro ⟨u, H⟩ hp ⟨u', H'⟩ hp' heq
    simp only [mem_product, mem_filter, mem_univ, true_and] at hp hp'
    simp only at heq
    have huu : u = u' := by
      have h1 := (oma_build_adj_v v u hp.1 H u).mpr rfl
      rw [heq] at h1
      exact (oma_build_adj_v v u' hp'.1 H' u).mp h1
    subst huu
    have hH : H = H' := by
      ext x y
      rw [← oma_build_adj_sub v u H x y, ← oma_build_adj_sub v u H' x y, heq]
    rw [hH]
  · intro G hG
    simp only [mem_filter, mem_univ, true_and] at hG
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hG
    obtain ⟨u, hu, huniq⟩ := hG
    have huv : u ≠ v := (G.ne_of_adj hu).symm
    refine ⟨(u, G.comap Subtype.val), ?_, ?_⟩
    · simp only [mem_product, mem_filter, mem_univ, true_and, and_true]
      exact huv
    · ext a b
      simp only
      by_cases ha : a = v
      · subst ha
        rw [oma_build_adj_v a u huv]
        exact ⟨fun h => h ▸ hu, fun h => huniq b h⟩
      by_cases hb : b = v
      · subst hb
        rw [SimpleGraph.adj_comm, oma_build_adj_v b u huv, G.adj_comm]
        exact ⟨fun h => h ▸ hu, fun h => huniq a h⟩
      · have := oma_build_adj_sub v u (G.comap Subtype.val) ⟨a, ha⟩ ⟨b, hb⟩
        simp only [SimpleGraph.comap_adj] at this
        exact this

theorem OMA.solution : type_of% @OMA.S_oeis_a095338.main := by
  intro n _
  unfold OMA.S_oeis_a095338.a OMA.S_oeis_a095338.leaves
  simp only [card_filter]
  rw [sum_comm]
  simp only [← card_filter]
  simp only [oma_count, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end
