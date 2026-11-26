import FormalConjectures.ErdosProblems.«739»

-- Problem: Erdős Problem 739 — aleph zero
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/739.lean:75 (declaration Erdos739.erdos_739.variants.aleph_zero)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Cardinal SimpleGraph

universe u

namespace OMA

/-- A coloring with `C` colors bounds the chromatic cardinal. -/
lemma chromCard_le {V C : Type u} (G : SimpleGraph V) (c : G.Coloring C) :
    G.chromaticCardinal ≤ #C :=
  csInf_le' ⟨C, rfl, ⟨c⟩⟩

/-- A finite coloring gives a finite bound. -/
lemma chromCard_lt_of_colorable {V : Type u} (G : SimpleGraph V) (n : ℕ)
    (h : G.Colorable n) : G.chromaticCardinal < ℵ₀ := by
  obtain ⟨c⟩ := h
  let c' : G.Coloring (ULift.{u} (Fin n)) :=
    Coloring.mk (fun v => ULift.up (c v)) (by
      intro v w hvw he
      exact c.valid hvw (congrArg ULift.down he))
  refine (chromCard_le G c').trans_lt ?_
  simp

/-- The chromatic cardinal is attained. -/
lemma chromCard_attained {V : Type u} (G : SimpleGraph V) :
    ∃ (C : Type u), #C = G.chromaticCardinal ∧ Nonempty (G.Coloring C) := by
  have hne : {κ : Cardinal | ∃ (C : Type u) (_ : Cardinal.mk C = κ),
      Nonempty (G.Coloring C)}.Nonempty :=
    ⟨#V, V, rfl, ⟨Coloring.mk id (fun h => G.ne_of_adj h)⟩⟩
  obtain ⟨C, hC, hc⟩ := csInf_mem hne
  exact ⟨C, hC, hc⟩

end OMA

theorem OMA.solution : type_of% @Erdos739.erdos_739.variants.aleph_zero := by
  intro V G hG
  -- for each n, a finite subgraph that is not n-colorable
  have hfin : ∀ n : ℕ, ∃ G' : G.Subgraph, G'.verts.Finite ∧ ¬ G'.coe.Colorable n := by
    intro n
    by_contra hcon
    push_neg at hcon
    have hcol : G.Colorable n := by
      apply nonempty_hom_of_forall_finite_subgraph_hom
      intro G' hG'
      exact (hcon G' hG').some
    exact absurd (OMA.chromCard_lt_of_colorable G n hcol) (not_lt.mpr hG.le)
  choose S hSfin hScol using hfin
  refine ⟨⨆ n, S n, le_antisymm ?_ ?_⟩
  · -- countable vertex set
    have hcount : (⨆ n, S n).verts.Countable := by
      rw [Subgraph.verts_iSup]
      exact Set.countable_iUnion fun n => (hSfin n).countable
    haveI : Countable (⨆ n, S n).verts := hcount.to_subtype
    obtain ⟨f, hf⟩ := exists_injective_nat (⨆ n, S n).verts
    let c : (⨆ n, S n).coe.Coloring (ULift ℕ) :=
      Coloring.mk (fun v => ULift.up (f v)) (by
        intro v w hvw he
        exact (⨆ n, S n).coe.ne_of_adj hvw (hf (congrArg ULift.down he)))
    refine (OMA.chromCard_le _ c).trans ?_
    simp
  · by_contra hlt
    push_neg at hlt
    obtain ⟨C, hC, ⟨c⟩⟩ := OMA.chromCard_attained (⨆ n, S n).coe
    rw [← hC] at hlt
    haveI : Finite C := Cardinal.lt_aleph0_iff_finite.mp hlt
    haveI := Fintype.ofFinite C
    apply hScol (Fintype.card C)
    have e := Fintype.equivFin C
    have hle : S (Fintype.card C) ≤ ⨆ n, S n := le_iSup S _
    exact ⟨(Coloring.mk (fun v => e (c (Subgraph.inclusion hle v))) (by
      intro v w hvw he
      exact c.valid ((Subgraph.inclusion hle).map_adj hvw) (e.injective he)))⟩
