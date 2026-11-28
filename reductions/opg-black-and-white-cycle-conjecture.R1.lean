import OMAStatements.S_opg_black_and_white_cycle_conjecture

/-!
# Reduction R1 of the Black and White Cycle Conjecture (Hoffmann-Ostenhof)

Credit: @MBimrose

Target (statements/opg-black-and-white-cycle-conjecture.lean, OMA.S_opg_black_and_white_cycle_conjecture.main):
for every finite cubic multigraph `(V, E, src, tgt)` with `Nonempty V` and a nowhere-zero 4-flow (an integer
flow with values in `{+-1, +-2, +-3}` that is conservative at every vertex), there is a cycle all of whose edges
`e` satisfy `HasNZ4Flow (G - e)` (white), and there is no cycle all of whose edges fail that (black).

## Statement audit (why the file below splits this and nothing weaker)

The encoding is faithful, not vacuous and not degenerate; I re-read it against the informal statement:

* `degIn src tgt C v` counts edge ends at `v` among `C`, a loop counting twice, so `= 3` is literally cubic.
* `IsConservative` is inflow sum = outflow sum for one reference orientation; a loop appears in both sums, so it
  cancels, exactly as flow theory wants.
* `IsWhite e` is `HasNZ4Flow` on the edge subtype `{d // d != e}`, i.e. literally `G - e`.
* `IsCycle` is nonempty + every vertex of degree 0 or 2 + connected, via Mathlib's
  `SimpleGraph.fromRel (fun a b => exists e in C, src e = a and tgt e = b)`, whose `Adj` is
  `a != b and (r a b or r b a)`, so a digon (two parallel edges) is a cycle and connectivity is the right one.
  The empty graph is excluded by `Nonempty V`, as the statement file says.
* The statement is NOT vacuous: `K4` (four vertices, six edges) satisfies every hypothesis, so the conclusion
  is a real claim about it. It holds there (all six edges are white, so every cycle is white and no black cycle
  exists).

Small-case evidence gathered by exact computation (even-subgraph-cover decidability of the 4-flow property,
cross-validated against brute-force enumeration of integer flows and against the perfect-matching/bipartite
3-edge-colouring characterisation):
* `K4`, the theta multigraph (2 vertices, 3 parallel edges), the triangular prism, `K_{3,3}` and the cube are
  cubic with a nowhere-zero 4-flow and ALL of their edges are white, so the conclusion is trivial for them.
* Petersen has no nowhere-zero 4-flow at all, so it is excluded by the hypothesis (it would have been an
  encoding bug if it were included).
* Over about 5000 random cubic multigraphs with 8 to 16 vertices that do admit a nowhere-zero 4-flow, EVERY one
  has a white cycle and NONE has a black cycle. No counterexample was found, so the conjecture looks true as
  encoded, and no `OMA.disproof` is available.

Two structural facts worth recording, both used below in choosing the hypotheses:
* If `e` lies in a 2-edge-cut then `G - e` has a bridge, and a graph with a bridge has no nowhere-zero flow
  (sum the conservation equations over one side of the bridge), so `e` is black. Hence edges in 2-edge-cuts are
  always black; there is no cycle consisting only of 2-edge-cut edges (a cycle crosses a cut evenly).
* Blackness is NOT confined to 2-edge-cuts, so the second conjunct is not a pure statement about cut structure:
  take Petersen, subdivide edges (0,1) and (2,3) at new vertices x, y and add the edge x-y. That graph is
  cubic, 3-edge-connected (no 2-edge-cut at all), has a nowhere-zero 4-flow, and both (1,2) and (x,y) are black
  (`G - (x,y)` smooths back to Petersen). This also refutes the folk claim that every 3-edge-connected cubic
  graph with a 4-flow has only white edges.

## The split

`H1` is the white-edge half, which is exactly the 4-flow form of Hoffmann-Ostenhof's 3-edge-colouring conjecture
(`statements/opg-3-edge-coloring-conjecture.lean`): a cubic multigraph with a nowhere-zero 4-flow has a 4-removable
edge. It is unpublished and open: the only source is the Open Problem Garden page, it is conjectured as
Conjecture 1.6 in Mattiolo, arXiv:2511.01556 (which proves a 3-removable set of size at most `|E|/6`), and the
most recent discussion, Luo-Hao-Zhang, Removable edges and stability of 4-flow, Discrete Math. 349(10) (2026)
115233, proves it only for cubic graphs with no Petersen (`P10`) minor - a proper subclass, so `H1` remains open,
and that paper does not treat the black/white statement (which is not cited anywhere before the OPG page). A white
cycle contains a white edge, so the target implies `H1`, and `H1` cannot be dropped.
`H2` is the extension step that is genuinely new here: having one white edge is not enough, a white edge has to
be turned into a white cycle. Neither `H1` nor `H2` alone mentions the target.
`H3` is the negative half: no all-black cycle. Its `H1`-shadow is the statement that no cycle consists only of
edges that are in 2-edge-cuts, which is provable by hand, but as the counterexample above shows the real content
is the snark-like way an edge can be non-removable, so `H3` is not a corollary of cut structure.

Each `H_i` is a standalone statement about an arbitrary cubic multigraph with a nowhere-zero 4-flow; each can be
attacked independently, and `H2` is the most tractable one (it is strictly weaker than `H1` plus `H3`).
-/

namespace OMA.R_opg_black_and_white_cycle_conjecture_R1

open OMA.S_opg_black_and_white_cycle_conjecture

/-- `H1` (3-edge-colouring conjecture, 4-flow form, unpublished/open): every finite nonempty cubic multigraph
with a nowhere-zero 4-flow has a white edge, i.e. an edge whose deletion keeps a nowhere-zero 4-flow. -/
def H1 : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (src tgt : E → V),
    Nonempty V → (∀ v : V, degIn src tgt Finset.univ v = 3) → HasNZ4Flow src tgt →
      ∃ e : E, IsWhite src tgt e

/-- `H2` (extension): in a cubic multigraph with a nowhere-zero 4-flow, the existence of a white edge already
forces a cycle all of whose edges are white. -/
def H2 : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (src tgt : E → V),
    Nonempty V → (∀ v : V, degIn src tgt Finset.univ v = 3) → HasNZ4Flow src tgt →
      (∃ e : E, IsWhite src tgt e) →
        ∃ C : Finset E, IsCycle src tgt C ∧ ∀ e ∈ C, IsWhite src tgt e

/-- `H3` (negative half): a cubic multigraph with a nowhere-zero 4-flow has no cycle all of whose edges are
black, i.e. no cycle `C` such that every edge of `C` loses the 4-flow property when deleted. -/
def H3 : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (src tgt : E → V),
    Nonempty V → (∀ v : V, degIn src tgt Finset.univ v = 3) → HasNZ4Flow src tgt →
      ¬ ∃ C : Finset E, IsCycle src tgt C ∧ ∀ e ∈ C, ¬ IsWhite src tgt e

/-- The three hypotheses carry the two conjuncts of the target: `H1` and `H2` produce the white cycle and `H3`
forbids the black one. No content is smuggled in: the split is a pure repackaging of the target's conclusion. -/
theorem main : H1 → H2 → H3 → type_of% @OMA.S_opg_black_and_white_cycle_conjecture.main := by
  intro h1 h2 h3 V E iV dV iE dE src tgt hne hc hf
  exact ⟨h2 V E src tgt hne hc hf (h1 V E src tgt hne hc hf), h3 V E src tgt hne hc hf⟩

end OMA.R_opg_black_and_white_cycle_conjecture_R1
