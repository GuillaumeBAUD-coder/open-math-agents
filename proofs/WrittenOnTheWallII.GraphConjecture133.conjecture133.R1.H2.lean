import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1
import Mathlib.Tactic

/-!
# Proof of H2 for Written on the Wall II Conjecture 133
-/

open SimpleGraph

private lemma isInducedPath_support_of_length_eq_dist {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {u v : α} (p : G.Walk u v) (hpath : p.IsPath)
    (hp : p.length = G.dist u v) :
    G.isInducedPath p.support := by
  refine ⟨hpath.support_nodup, ?_⟩
  have hlen : p.support.length = p.length + 1 := p.length_support
  have hno_chord : ∀ a b : ℕ, a < b → b ≤ p.length →
      G.Adj (p.getVert a) (p.getVert b) → a + 1 = b := by
    intro a b hab hble hadj
    let r : G.Walk u v := (p.take a).append ((p.drop b).cons hadj)
    have hdist : G.dist u v ≤ r.length := G.dist_le r
    simp only [r, Walk.length_append, Walk.take_length, Walk.length_cons, Walk.drop_length,
      ← hp] at hdist
    omega
  intro i j
  have hi_get : p.support.get i = p.getVert i.val := by
    rw [List.get_eq_getElem, p.support_getElem_eq_getVert i.isLt]
  have hj_get : p.support.get j = p.getVert j.val := by
    rw [List.get_eq_getElem, p.support_getElem_eq_getVert j.isLt]
  rw [hi_get, hj_get]
  have hi_le : i.val ≤ p.length := by omega
  have hj_le : j.val ≤ p.length := by omega
  constructor
  · intro hadj
    have hne : i.val ≠ j.val := fun heq => hadj.ne (congrArg p.getVert heq)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (hno_chord i.val j.val hlt hj_le hadj)
    · exact Or.inr (hno_chord j.val i.val hgt hi_le hadj.symm)
  · rintro (hij | hji)
    · have hi_lt : i.val < p.length := by omega
      simpa only [hij] using p.adj_getVert_succ hi_lt
    · have hj_lt : j.val < p.length := by omega
      simpa only [hji] using (p.adj_getVert_succ hj_lt).symm

theorem prove_Graph133_H2 :
    ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
      (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
      (G.radius.toNat : ℝ) + 1 ≤ (SimpleGraph.path G : ℝ) := by
  intro α _ _ _ G hc _hC4
  classical
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
  have hind : G.isInducedPath p.support :=
    isInducedPath_support_of_length_eq_dist p hpath hp
  have hlen_le : p.support.length ≤ SimpleGraph.path G :=
    length_le_path_of_isInducedPath G p.support hind
  have hsupp_len : p.support.length = G.dist u v + 1 := by
    rw [p.length_support, hp]
  have hnat : G.radius.toNat + 1 ≤ SimpleGraph.path G := by
    omega
  exact_mod_cast hnat

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H2 :=
  prove_Graph133_H2
