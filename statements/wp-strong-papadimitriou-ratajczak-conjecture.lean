import Mathlib

/-!
# Strong Papadimitriou–Ratajczak conjecture

Source: https://en.wikipedia.org/wiki/Greedy_embedding#Planar_graphs
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

Source sentence: "The strong Papadimitriou–Ratajczak conjecture, that every polyhedral graph
has a planar greedy embedding in which all faces are convex, remains unproven."
The source glosses "polyhedral graph" as "a 3-vertex-connected planar graph", and defines a
greedy embedding as an embedding such that "for every two nodes x and t, there exists a neighbor
y of x such that d(x, t) > d(y, t)".

Mathlib v4.33.1 has no planarity and no k-connectivity for `SimpleGraph`, so we define:
* `planar G`: existence of a crossing-free straight-line drawing in the plane (equivalent to
  topological planarity for finite graphs by Fáry's theorem);
* `kVertexConnected k G`: `card V ≥ k + 1` and deleting fewer than `k` vertices leaves a
  connected graph;
* faces of a drawing via the rotation system induced by the drawing (neighbours sorted by
  polar angle): the dart-successor map sends the dart `(u, v)` to `(v, w)` where `w` is the
  neighbour of `v` immediately clockwise from `u`, and faces are the orbits of this map;
* a face is convex when its facial walk has length at least `3`, visits pairwise distinct
  vertices, and every consecutive triple makes a non-negative left turn (cross product `≥ 0`),
  i.e. the face boundary is a convex polygon.
-/

namespace OMA.S_wp_strong_papadimitriou_ratajczak_conjecture

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The darts (directed edges) of `G`. -/
abbrev Dart (G : SimpleGraph V) := {d : V × V // G.Adj d.1 d.2}

/-- The closed line segment from `a` to `b` in the complex plane. -/
def seg (a b : ℂ) : Set ℂ :=
  {z | ∃ t ∈ Set.Icc (0 : ℝ) 1, z = (1 - t) • a + t • b}

/-- The polar angle of the direction from `v` to `u` in the drawing `p : V → ℂ`. -/
noncomputable def angAt (p : V → ℂ) (v u : V) : ℝ := Complex.arg (p u - p v)

/-- Clockwise angular distance from the direction `v → u` to the direction `v → w`. -/
noncomputable def cwDist (p : V → ℂ) (v u w : V) : ℝ :=
  let a := angAt p v u
  let b := angAt p v w
  if b < a then a - b else a - b + 2 * Real.pi

/-- The neighbours of `v` as a `Finset` (Mathlib's `neighborFinset` needs an extra
    `Fintype (G.neighborSet v)` instance, so we build it directly). -/
noncomputable def nbhd {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => G.Adj v u)

/-- The neighbour of `v` immediately clockwise from `u` around `v`
    (returns `u` itself when `u` is the only neighbour of `v`). -/
noncomputable def nextNbhd (G : SimpleGraph V) (p : V → ℂ) (u v : V) : V :=
  if h : (nbhd G v \ {u}).Nonempty then
    Classical.choose
      (Finset.exists_min_image (nbhd G v \ {u}) (fun w => cwDist p v u w) h)
  else u

noncomputable instance (G : SimpleGraph V) : Fintype (Dart G) := by
  classical
  exact inferInstance

/-- The dart-successor permutation of the rotation system induced by the drawing `p`:
    the dart `(u, v)` maps to `(v, w)`, where `w` is the neighbour of `v`
    immediately clockwise from `u`. -/
noncomputable def dartSucc (G : SimpleGraph V) (p : V → ℂ) (d : Dart G) : Dart G := by
  classical
  refine ⟨⟨d.1.2, nextNbhd G p d.1.1 d.1.2⟩, ?_⟩
  unfold nextNbhd
  split
  · rename_i h
    have hspec := Classical.choose_spec
      (Finset.exists_min_image (nbhd G d.1.2 \ {d.1.1}) (fun w => cwDist p d.1.2 d.1.1 w) h)
    obtain ⟨hw, _⟩ := hspec
    have hmem' := (Finset.mem_sdiff.mp hw).1
    have key : ∀ x ∈ nbhd G d.1.2, G.Adj d.1.2 x := by
      intro x hx
      unfold nbhd at hx
      exact (Finset.mem_filter.mp hx).2
    exact key _ hmem'
  · exact d.2.symm

/-- The face (orbit of darts) of the drawing `p` containing the dart `d`. -/
noncomputable def dartOrbit (G : SimpleGraph V) (p : V → ℂ) (d : Dart G) : Finset (Dart G) :=
  Finset.image (fun k : Fin (Fintype.card (Dart G)) => (dartSucc G p)^[k.1] d) Finset.univ

/-- The length of the facial walk of the face containing `d`. -/
noncomputable def faceLen (G : SimpleGraph V) (p : V → ℂ) (d : Dart G) : ℕ :=
  (dartOrbit G p d).card

/-- The `i`-th vertex of the facial walk of the face containing `d`
    (indices taken modulo the face length). -/
noncomputable def faceVertex (G : SimpleGraph V) (p : V → ℂ) (d : Dart G)
    (i : ZMod (faceLen G p d)) : V :=
  (((dartSucc G p)^[ZMod.val i] d).1).1

/-- Signed turn (cross product) of the triple of points `a, b, c` in the plane. -/
def turn (a b c : ℂ) : ℝ := ((b - a) * (c - b)).im

/-- The face of the drawing `p` containing the dart `d` is a convex polygon:
    its facial walk has length at least `3`, visits pairwise distinct vertices,
    and every consecutive triple makes a non-negative left turn. -/
def faceConvex (G : SimpleGraph V) (p : V → ℂ) (d : Dart G) : Prop :=
  3 ≤ faceLen G p d ∧
  (∀ i j : ZMod (faceLen G p d), i ≠ j → faceVertex G p d i ≠ faceVertex G p d j) ∧
  (∀ i : ZMod (faceLen G p d),
    0 ≤ turn (p (faceVertex G p d i)) (p (faceVertex G p d (i + 1)))
      (p (faceVertex G p d (i + 2))))

/-- A straight-line drawing `p` of `G` in the Euclidean plane with no crossings:
    positions are injective, edges with no common endpoint have disjoint closed segments,
    and no vertex lies on a non-incident edge. -/
def planarDrawing (G : SimpleGraph V) (p : V → ℂ) : Prop :=
  Function.Injective p ∧
  (∀ a b c d : V, G.Adj a b → G.Adj c d →
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    Disjoint (seg (p a) (p b)) (seg (p c) (p d))) ∧
  (∀ a b c : V, G.Adj a b → c ≠ a → c ≠ b → ¬G.Adj a c → ¬G.Adj b c →
    p c ∉ seg (p a) (p b))

/-- The greedy property of the drawing `p` (source, Definitions section): for every two
    (distinct) nodes `x` and `t` there exists a neighbour `y` of `x` with
    `d(x, t) > d(y, t)`, where `d` is the distance in the embedded (Euclidean) plane. -/
def greedy (G : SimpleGraph V) (p : V → ℂ) : Prop :=
  ∀ x t : V, x ≠ t → ∃ y, G.Adj x y ∧ dist (p y) (p t) < dist (p x) (p t)

/-- `G` is planar: it admits a crossing-free straight-line drawing in the Euclidean plane
    (equivalent to topological planarity for finite graphs by Fáry's theorem). -/
def planar (G : SimpleGraph V) : Prop :=
  ∃ p : V → ℂ, planarDrawing G p

/-- `G` is `k`-vertex-connected: it has at least `k + 1` vertices, and deleting any set of
    fewer than `k` vertices leaves a connected graph. -/
def kVertexConnected (k : ℕ) (G : SimpleGraph V) : Prop :=
  k + 1 ≤ Fintype.card V ∧
  ∀ s : Finset V, s.card < k → Connected (G.induce (Set.univ \ (s : Set V)))

/-- A polyhedral graph, as glossed by the source: a 3-vertex-connected planar graph. -/
def polyhedral (G : SimpleGraph V) : Prop :=
  kVertexConnected 3 G ∧ planar G

/--
The strong Papadimitriou–Ratajczak conjecture (Papadimitriou & Ratajczak 2005, stated as
open in the source): every polyhedral graph (3-vertex-connected planar graph) has a planar
greedy embedding in the Euclidean plane in which all faces are convex.
-/
theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      polyhedral G →
      ∃ p : V → ℂ, planarDrawing G p ∧ greedy G p ∧
        ∀ d : Dart G, faceConvex G p d := by
  sorry

end OMA.S_wp_strong_papadimitriou_ratajczak_conjecture
