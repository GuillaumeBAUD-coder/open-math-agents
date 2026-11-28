import OMAStatements.S_opg_chords_of_longest_cycles
import Mathlib.Tactic

/-!
# Reduction R3 of Thomassen's chord conjecture (opg-chords-of-longest-cycles)

A second axis on the same target: every longest cycle of a 3-connected finite simple graph has a
chord (C. Thomassen, Open Problem Garden). The strong form, quantified over EVERY longest cycle,
is still open: Thomassen, JCTB 179 (2026) 90-117, proves only that some longest cycle has a chord,
and the classes where the strong form is known are cubic graphs (Thomassen, JCTB 129 (2018)
148-157), planar graphs of minimum degree 4 (Zhang 1987), the projective plane (Li-Zhang 2003),
the torus and Klein bottle at connectivity 4 (Li-Zhang 2003), and graphs of large minimum degree
(Harvey, EJC 2017). Those results are organised by minimum degree: 3-connected graphs are what
3-connectivity gives, cubic is the smallest case, and delta >= 4 is the dense regime.

`main` splits the target by whether the minimum degree is exactly 3 somewhere:

* `min_degree` (proved here): a 3-connected graph has minimum degree at least 3. So the two
  hypotheses below are exhaustive: either some vertex has degree exactly 3, or every vertex has
  degree at least 4.
* `H1` is the remaining gap of the literature: minimum degree 3 (the case that is not covered by
  the delta >= 4 results and only partially by the cubic ones).
* `H2` is the dense regime delta >= 4.

They are incomparable restrictions of the target, each strictly weaker than it, and each is a
statement the published proofs of the special cases attack with their own methods.
-/

namespace OMA.R_opg_chords_of_longest_cycles_R3

open OMA.S_opg_chords_of_longest_cycles

/-- The chord conjecture in the minimum-degree-3 case: some vertex has degree exactly 3. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], IsKConnected G 3 →
    (∃ v : V, G.degree v = 3) →
      ∀ (u : V) (c : G.Walk u u), IsLongestCycle c → HasChord c

/-- The chord conjecture in the dense regime: every vertex has degree at least 4. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], IsKConnected G 3 →
    (∀ v : V, 4 ≤ G.degree v) →
      ∀ (u : V) (c : G.Walk u u), IsLongestCycle c → HasChord c

variable {V : Type} [Fintype V]

/-- A 3-connected graph has minimum degree at least 3. -/
lemma min_degree {G : SimpleGraph V} [DecidableRel G.Adj] (hG : IsKConnected G 3) (v : V) :
    3 ≤ G.degree v := by
  classical
  by_contra hlt
  have hle : G.degree v ≤ 2 := by omega
  have hdeg : G.degree v = (G.neighborFinset v).card := rfl
  have hScard : (G.neighborFinset v).card < 3 := by omega
  have hconn : (G.induce (↑(G.neighborFinset v) : Set V)ᶜ).Connected := hG.2 _ hScard
  have hvS : v ∉ G.neighborFinset v := by simp
  have hv' : v ∈ (↑(G.neighborFinset v) : Set V)ᶜ := by simpa using hvS
  have hiso : (G.induce (↑(G.neighborFinset v) : Set V)ᶜ).neighborSet ⟨v, hv'⟩ = ∅ := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
    intro hadj
    have hmem : (x : V) ∈ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.induce_adj.mp hadj
    exact x.2 hmem
  have hall : ∀ w : V, w ∉ G.neighborFinset v → w = v := by
    intro w hw
    by_contra hne
    have hw' : w ∈ (↑(G.neighborFinset v) : Set V)ᶜ := by simpa using hw
    have hne' : (⟨v, hv'⟩ : ↥((↑(G.neighborFinset v) : Set V)ᶜ)) ≠ ⟨w, hw'⟩ := by
      intro h
      exact hne (congrArg Subtype.val h).symm
    exact (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hne' hiso)
      (hconn.preconnected ⟨v, hv'⟩ ⟨w, hw'⟩)
  have hsub : (Finset.univ : Finset V) ⊆ insert v (G.neighborFinset v) := by
    intro w _
    by_cases hw : w ∈ G.neighborFinset v
    · exact Finset.mem_insert_of_mem hw
    · rw [hall w hw]
      exact Finset.mem_insert_self v _
  have h1 : Fintype.card V ≤ (insert v (G.neighborFinset v)).card := Finset.card_le_card hsub
  have h2 : (insert v (G.neighborFinset v)).card ≤ (G.neighborFinset v).card + 1 :=
    Finset.card_insert_le v _
  have h3 := hG.1
  omega

theorem main : H1 → H2 → type_of% @OMA.S_opg_chords_of_longest_cycles.main := by
  intro h1 h2 V _ G hG u c hc
  classical
  by_cases hex : ∃ v : V, G.degree v = 3
  · exact h1 V G hG hex u c hc
  · have h4 : ∀ v : V, 4 ≤ G.degree v := by
      intro v
      have h3 := min_degree hG v
      by_contra hv
      exact hex ⟨v, by omega⟩
    exact h2 V G hG h4 u c hc

end OMA.R_opg_chords_of_longest_cycles_R3
