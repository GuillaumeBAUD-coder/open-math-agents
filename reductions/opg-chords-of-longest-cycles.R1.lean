import OMAStatements.S_opg_chords_of_longest_cycles
import Mathlib.Tactic

/-!
# Reduction of Thomassen's chord conjecture (opg-chords-of-longest-cycles)

Target: every longest cycle of a 3-connected finite simple graph has a chord
(Open Problem Garden, C. Thomassen; still open, known for cubic graphs (Thomassen 1997), for
planar graphs of minimum degree 4 (Zhang 1987), for the projective plane (Li-Zhang 2003), for the
torus and Klein bottle at connectivity 4 (Li-Zhang 2003) and for locally planar 4-connected
graphs (Kawarabayashi-Niu-Zhang 2007)).

The published work on this conjecture is organised by how the longest cycle `C` sits in `G`:

* `C` spans every vertex (G is Hamiltonian). This case is the trivial one: a spanning cycle uses
  only two edges at each vertex, and 3-connectivity forces minimum degree at least 3, so an edge
  leaving `C` at a vertex exists and is a chord. The Open Problem Garden page says explicitly that
  in Hamiltonian graphs the conjecture is easy.
* `C` does not span, and the graph induced by the vertices outside `C` is connected: there is a
  single bridge of `C` to attack, all the standard rerouting/fan arguments apply to one component.
* `C` does not span, and the vertices outside `C` induce a disconnected graph: several bridges of
  `C` interleave, and the relative positions of their attachments on `C` are what has to be
  controlled.

`main` proves that these three cases exhaust the target (the third split is a plain `by_cases` on
the induced graph being connected, and the first split is a plain `by_cases` on `C` spanning all
vertices). The three hypotheses are strictly weaker than the target: each one is the target
restricted to one of the structural cases, so each can be attacked separately.
-/

namespace OMA.R_opg_chords_of_longest_cycles_R1

open OMA.S_opg_chords_of_longest_cycles

/-- The Hamiltonian case of the chord conjecture: a longest cycle that visits every vertex has a
chord. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsKConnected G 3 →
    ∀ (u : V) (c : G.Walk u u), IsLongestCycle c → (∀ v : V, v ∈ c.support) → HasChord c

/-- The chord conjecture when the longest cycle is not spanning and the vertices off the cycle
induce a connected graph (one bridge). -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsKConnected G 3 →
    ∀ (u : V) (c : G.Walk u u), IsLongestCycle c → (∃ v : V, v ∉ c.support) →
      (G.induce {v : V | v ∉ c.support}).Connected → HasChord c

/-- The chord conjecture when the longest cycle is not spanning and the vertices off the cycle
induce a disconnected graph (at least two bridges). -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsKConnected G 3 →
    ∀ (u : V) (c : G.Walk u u), IsLongestCycle c → (∃ v : V, v ∉ c.support) →
      ¬ (G.induce {v : V | v ∉ c.support}).Connected → HasChord c

theorem main : H1 → H2 → H3 → type_of% @OMA.S_opg_chords_of_longest_cycles.main := by
  intro h1 h2 h3 V _ G hG u c hc
  by_cases hspan : ∀ v : V, v ∈ c.support
  · exact h1 V G hG u c hc hspan
  · have hoff : ∃ v : V, v ∉ c.support := by
      by_contra hcon
      exact hspan fun v => by
        by_contra hv
        exact hcon ⟨v, hv⟩
    by_cases hconn : (G.induce {v : V | v ∉ c.support}).Connected
    · exact h2 V G hG u c hc hoff hconn
    · exact h3 V G hG u c hc hoff hconn

end OMA.R_opg_chords_of_longest_cycles_R1
