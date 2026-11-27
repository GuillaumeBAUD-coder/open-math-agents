import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1
import Mathlib.Tactic

/-!
# Vertex Cover vs Total Domination on Trees

Every tree of order at least two has vertex cover number at most twice its total domination number.
-/

open SimpleGraph

namespace Graph372H2Aux

def isChild {α : Type*} (T : SimpleGraph α) (r u v : α) : Prop :=
  T.Adj u v ∧ T.dist r v = T.dist r u + 1

lemma adj_child_or_symm {α : Type*} {T : SimpleGraph α} (hT : T.IsTree) (r u v : α)
    (hadj : T.Adj u v) :
    isChild T r u v ∨ isChild T r v u := by
  rcases hT.dist_eq_dist_add_one_of_adj r hadj with hd | hd
  · exact Or.inr ⟨hadj.symm, hd⟩
  · exact Or.inl ⟨hadj, hd⟩

lemma eq_penultimate_of_isChild {α : Type*} {T : SimpleGraph α} (hT : T.IsTree)
    {r u v : α} {q : T.Walk r v} (hq : q.IsPath) (hq_len : q.length = T.dist r v)
    (hchild : isChild T r u v) :
    u = q.penultimate := by
  rcases hchild with ⟨hadj, hd⟩
  obtain ⟨p, hp, hp_len⟩ := hT.connected.exists_path_of_dist r u
  have hu_mem : u ∈ q.support := by
    by_contra hu
    have hv_mem : v ∈ p.support :=
      hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hadj hu
    have hpq : p = q.concat hadj.symm :=
      hT.isAcyclic.path_concat hq hp hadj.symm hv_mem
    have hlen : p.length = q.length + 1 := by
      rw [hpq, Walk.length_concat]
    omega
  exact hT.isAcyclic.eq_penultimate_of_adj_end hq hadj.symm hu_mem

lemma parent_unique {α : Type*} {T : SimpleGraph α} (hT : T.IsTree)
    {r u₁ u₂ v : α} (h₁ : isChild T r u₁ v) (h₂ : isChild T r u₂ v) :
    u₁ = u₂ := by
  obtain ⟨q, hq, hq_len⟩ := hT.connected.exists_path_of_dist r v
  rw [eq_penultimate_of_isChild hT hq hq_len h₁, eq_penultimate_of_isChild hT hq hq_len h₂]

lemma exists_min_totalDominating {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    ∃ D : Finset α, T.IsTotalDominating (D : Set α) ∧ D.card = T.totalDominationNumber := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have huniv : T.IsTotalDominating (Finset.univ : Finset α) := by
    intro v
    obtain ⟨u, huv⟩ := exists_ne v
    obtain ⟨p⟩ := hT.connected v u
    cases p with
    | nil => exact absurd rfl huv
    | @cons _ w _ hadj _ => exact ⟨w, Finset.mem_coe.mpr (Finset.mem_univ w), hadj⟩
  have hne : {n | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨Fintype.card α, Finset.univ, huniv, Finset.card_univ⟩
  obtain ⟨D, hD_dom, hD_card⟩ := Nat.sInf_mem hne
  exact ⟨D, hD_dom, hD_card⟩

end Graph372H2Aux

theorem prove_Graph372_H2 :
    ∀ (α : Type) [Fintype α] [DecidableEq α] (T : SimpleGraph α), T.IsTree →
      2 ≤ Fintype.card α →
      T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber := by
  classical
  intro α _ _ T hT hn
  obtain ⟨D, hD_dom, hD_card⟩ := Graph372H2Aux.exists_min_totalDominating T hT hn
  let r : α := hT.connected.nonempty.some
  let P : Finset α :=
    Finset.univ.filter fun u => u ∉ D ∧ ∃ v, v ∉ D ∧ Graph372H2Aux.isChild T r u v
  have hcov : T.IsVertexCover ((D ∪ P : Finset α) : Set α) := by
    intro x y hadj
    by_cases hx : x ∈ D
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_union_left P hx))
    · by_cases hy : y ∈ D
      · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_union_left P hy))
      · rcases Graph372H2Aux.adj_child_or_symm hT r x y hadj with hxy | hyx
        · have hxP : x ∈ P :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, y, hy, hxy⟩
          exact Or.inl (Finset.mem_coe.mpr (Finset.mem_union_right D hxP))
        · have hyP : y ∈ P :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy, x, hx, hyx⟩
          exact Or.inr (Finset.mem_coe.mpr (Finset.mem_union_right D hyP))
  have hw_exists : ∀ u : {u // u ∈ P},
      ∃ w : {w // w ∈ D}, ∃ v : α,
        Graph372H2Aux.isChild T r u.1 v ∧ Graph372H2Aux.isChild T r v w.1 := by
    intro u
    obtain ⟨_, hu_not_D, v, _hv_not_D, huv⟩ := Finset.mem_filter.mp u.2
    obtain ⟨w, hw_coe, hvw_adj⟩ := hD_dom v
    have hw_D : w ∈ D := Finset.mem_coe.mp hw_coe
    rcases Graph372H2Aux.adj_child_or_symm hT r v w hvw_adj with hvw | hwv
    · exact ⟨⟨w, hw_D⟩, v, huv, hvw⟩
    · have hwu : w = u.1 := Graph372H2Aux.parent_unique hT hwv huv
      exact absurd (hwu ▸ hw_D) hu_not_D
  choose g hg using hw_exists
  have hg_inj : Function.Injective g := by
    intro u₁ u₂ hge
    obtain ⟨v₁, hu₁v₁, hv₁w⟩ := hg u₁
    obtain ⟨v₂, hu₂v₂, hv₂w⟩ := hg u₂
    have hw_eq : (g u₁).1 = (g u₂).1 := congrArg Subtype.val hge
    rw [← hw_eq] at hv₂w
    have hv_eq : v₁ = v₂ := Graph372H2Aux.parent_unique hT hv₁w hv₂w
    rw [← hv_eq] at hu₂v₂
    exact Subtype.ext (Graph372H2Aux.parent_unique hT hu₁v₁ hu₂v₂)
  have hP_le_D : P.card ≤ D.card := by
    simpa using Fintype.card_le_of_injective g hg_inj
  have hvc_enat : T.vertexCoverNum ≤ ((D ∪ P).card : ℕ∞) := by
    rw [← Set.encard_coe_eq_coe_finsetCard (D ∪ P)]
    exact hcov.vertexCoverNum_le
  have hvc_nat : T.vertexCoverNum.toNat ≤ (D ∪ P).card :=
    ENat.toNat_le_of_le_natCast hvc_enat
  have hunion : (D ∪ P).card ≤ D.card + P.card := Finset.card_union_le D P
  omega

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H2 :=
  prove_Graph372_H2
