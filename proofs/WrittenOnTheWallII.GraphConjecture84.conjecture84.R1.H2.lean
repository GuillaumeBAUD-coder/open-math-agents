import OMAReductions.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1
import Mathlib.Tactic

open SimpleGraph

theorem prove_Graph84_H2 :
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α)
      [DecidableRel G.Adj], G.Connected → 0 < G.minDegree → 2 ≤ G.minDegree →
      2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
  intro α _ _ _ G _ hc hδpos hδ2
  obtain ⟨u⟩ : Nonempty α := inferInstance
  have hrad_eq : G.radius.toNat = computable_radius G := by
    rw [radius_eq_computable G hc]
    rfl
  have hrad_le_ecc : computable_radius G ≤ computable_eccent G u :=
    Finset.inf'_le (computable_eccent G) (Finset.mem_univ u)
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset α) Finset.univ_nonempty
    (fun v => computable_dist G u v)
  have hecc_eq : computable_eccent G u = G.dist u v := by
    change Finset.univ.sup (fun w => computable_dist G u w) = G.dist u v
    rw [hv, dist_eq_computable G u v]
  obtain ⟨p, hpath, hp⟩ := hc.exists_path_of_dist u v
  have htree : (G.induce (p.support.toFinset : Set α)).IsTree :=
    p.induce_support_isTree_of_length_eq_dist hp
  have hcard : p.support.toFinset.card = G.dist u v + 1 := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup, p.length_support, hp]
  have hdist_le_tree : G.dist u v + 1 ≤ largestInducedTreeSize G :=
    hcard ▸ card_le_largestInducedTreeSize htree
  have hrad_le_tree : G.radius.toNat ≤ largestInducedTreeSize G := by
    omega
  have hradR : (G.radius.toNat : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
    exact_mod_cast hrad_le_tree
  have hδposR : (0 : ℝ) < (G.minDegree : ℝ) := by
    exact_mod_cast hδpos
  have hδ2R : (2 : ℝ) ≤ (G.minDegree : ℝ) := by
    exact_mod_cast hδ2
  have hrad_nn : (0 : ℝ) ≤ (G.radius.toNat : ℝ) := Nat.cast_nonneg _
  have hdiv_le : 2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (G.radius.toNat : ℝ) :=
    (div_le_iff₀ hδposR).mpr (by nlinarith)
  exact hdiv_le.trans hradR

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1.H2 :=
  prove_Graph84_H2
