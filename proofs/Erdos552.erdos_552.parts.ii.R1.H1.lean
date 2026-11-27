import OMAReductions.R_Erdos552_erdos_552_parts_ii_R1
import Mathlib
section
/-
# Quadrilateral–star Ramsey numbers at finite-field orders

The exact values at q² and q² + 1 are due to T. D. Parsons,
“Ramsey Graphs and Block Designs, I” (1975), https://doi.org/10.2307/1997368.
The formalization below combines finite polarity graphs with a spectral
argument for an excess-one graph and a signed quotient obstruction at degree six.
It also includes the characteristic-two interval and the prime-gap condition
for a witness to part (ii) of Erdős problem 552.
Formalization for Left to Solve by @Deldor14. Credits for the underlying
friendship theorem and Chen's inequality are retained in the corresponding sections.
-/
/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller
-/

/-
# The Friendship Theorem

## Definitions and Statement
- A `Friendship` graph is one in which any two distinct vertices have exactly one neighbor in common
- A `Politician`, at least in the context of this problem, is a vertex in a graph which is adjacent
  to every other vertex.
- The friendship theorem (Erdős, Rényi, Sós 1966) states that every finite friendship graph has a
  politician.

## Proof outline
The proof revolves around the theory of adjacency matrices, although some steps could equivalently
be phrased in terms of counting walks.
- Assume `G` is a finite friendship graph.
- First we show that any two nonadjacent vertices have the same degree
- Assume for contradiction that `G` does not have a politician.
- Conclude from the last two points that `G` is `d`-regular for some `d : ℕ`.
- Show that `G` has `d ^ 2 - d + 1` vertices.
- By casework, show that if `d = 0, 1, 2`, then `G` has a politician.
- If `3 ≤ d`, let `p` be a prime factor of `d - 1`.
- If `A` is the adjacency matrix of `G` with entries in `ℤ/pℤ`, we show that `A ^ p` has trace `1`.
- This gives a contradiction, as `A` has trace `0`, and thus `A ^ p` has trace `0`.

## References
- [P. Erdős, A. Rényi, V. Sós, *On A Problem of Graph Theory*][erdosrenyisos]
- [C. Huneke, *The Friendship Theorem*][huneke2002]

-/

namespace Deldor14.FriendshipProof

noncomputable section

open Finset SimpleGraph Matrix

universe u v

variable {V : Type u} {R : Type v} [Semiring R]

section FriendshipDef

variable (G : SimpleGraph V)

open scoped Classical in
/-- This property of a graph is the hypothesis of the friendship theorem:
every pair of nonadjacent vertices has exactly one common friend,
a vertex to which both are adjacent.
-/
def Friendship [Fintype V] : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1

/-- A politician is a vertex that is adjacent to all other vertices.
-/
def ExistsPolitician : Prop :=
  ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w

end FriendshipDef

variable [Fintype V] {G : SimpleGraph V} {d : ℕ} (hG : Friendship G)

namespace Friendship

variable (R)

open scoped Classical in
include hG in
/-- One characterization of a friendship graph is that there is exactly one walk of length 2
  between distinct vertices. These walks are counted in off-diagonal entries of the square of
  the adjacency matrix, so for a friendship graph, those entries are all 1. -/
theorem adjMatrix_sq_of_ne {v w : V} (hvw : v ≠ w) :
    (G.adjMatrix R ^ 2 : Matrix V V R) v w = 1 := by
  rw [sq, ← Nat.cast_one, ← hG hvw]
  simp only [mul_adjMatrix_apply, neighborFinset_eq_filter, adjMatrix_apply,
    sum_boole, filter_filter, and_comm]
  congr 1
  refine (Fintype.card_coe _).symm.trans (Fintype.card_congr ?_)
  exact Equiv.subtypeEquivRight (fun x => by simp [commonNeighbors, and_comm])

open scoped Classical in
include hG in
/-- This calculation amounts to counting the number of length 3 walks between nonadjacent vertices.
  We use it to show that nonadjacent vertices have equal degrees. -/
theorem adjMatrix_pow_three_of_not_adj {v w : V} (non_adj : ¬G.Adj v w) :
    (G.adjMatrix R ^ 3 : Matrix V V R) v w = degree G v := by
  rw [pow_succ', adjMatrix_mul_apply, degree, card_eq_sum_ones, Nat.cast_sum]
  apply sum_congr rfl
  intro x hx
  rw [adjMatrix_sq_of_ne _ hG, Nat.cast_one]
  rintro ⟨rfl⟩
  rw [mem_neighborFinset] at hx
  exact non_adj hx

variable {R}

open scoped Classical in
include hG in
/-- As `v` and `w` not being adjacent implies
  `degree G v = ((G.adjMatrix R) ^ 3) v w` and `degree G w = ((G.adjMatrix R) ^ 3) v w`,
  the degrees are equal if `((G.adjMatrix R) ^ 3) v w = ((G.adjMatrix R) ^ 3) w v`

  This is true as the adjacency matrix is symmetric. -/
theorem degree_eq_of_not_adj {v w : V} (hvw : ¬G.Adj v w) : degree G v = degree G w := by
  rw [← Nat.cast_id (G.degree v), ← Nat.cast_id (G.degree w),
    ← adjMatrix_pow_three_of_not_adj ℕ hG hvw,
    ← adjMatrix_pow_three_of_not_adj ℕ hG fun h ↦ hvw h.symm]
  conv_lhs => rw [← transpose_adjMatrix]
  simp only [pow_succ _ 2, sq, ← transpose_mul, transpose_apply]
  simp only [mul_assoc]

open scoped Classical in
include hG in
/-- Let `A` be the adjacency matrix of a graph `G`.
  If `G` is a friendship graph, then all of the off-diagonal entries of `A^2` are 1.
  If `G` is `d`-regular, then all of the diagonal entries of `A^2` are `d`.
  Putting these together determines `A^2` exactly for a `d`-regular friendship graph. -/
theorem adjMatrix_sq_of_regular (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R ^ 2 = of fun v w => if v = w then (d : R) else (1 : R) := by
  ext (v w); by_cases h : v = w
  · rw [h, sq, adjMatrix_mul_self_apply_self, hd]; simp
  · rw [adjMatrix_sq_of_ne R hG h, of_apply, if_neg h]

open scoped Classical in
include hG in
theorem adjMatrix_sq_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : G.adjMatrix (ZMod p) ^ 2 = of fun _ _ => 1 := by
  simp [adjMatrix_sq_of_regular hG hd, dmod]

section Nonempty

variable [Nonempty V]

open scoped Classical in
include hG in
/-- If `G` is a friendship graph without a politician (a vertex adjacent to all others), then
  it is regular. We have shown that nonadjacent vertices of a friendship graph have the same degree,
  and if there isn't a politician, we can show this for adjacent vertices by finding a vertex
  neither is adjacent to, and then using transitivity. -/
theorem isRegularOf_not_existsPolitician (hG' : ¬ExistsPolitician G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  use G.degree v
  intro x
  by_cases hvx : G.Adj v x; swap; · exact (degree_eq_of_not_adj hG hvx).symm
  dsimp only [Deldor14.FriendshipProof.ExistsPolitician] at hG'
  push Not at hG'
  rcases hG' v with ⟨w, hvw', hvw⟩
  rcases hG' x with ⟨y, hxy', hxy⟩
  by_cases hxw : G.Adj x w
  swap; · rw [degree_eq_of_not_adj hG hvw]; exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v y
  swap; · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  apply degree_eq_of_not_adj hG
  intro hcontra
  rcases Finset.card_eq_one.mp (hG hvw') with ⟨⟨a, ha⟩, h⟩
  have key : ∀ {x}, x ∈ G.commonNeighbors v w → x = a := by
    intro x hx
    have h' : ⟨x, hx⟩ ∈ (univ : Finset (G.commonNeighbors v w)) := mem_univ (Subtype.mk x hx)
    rw [h, mem_singleton] at h'
    injection h'
  apply hxy'
  rw [key ((mem_commonNeighbors G).mpr ⟨hvx, hxw.symm⟩),
    key ((mem_commonNeighbors G).mpr ⟨hvy, hcontra.symm⟩)]

open scoped Classical in
include hG in
/-- Let `A` be the adjacency matrix of a `d`-regular friendship graph, and let `v` be a vector
  all of whose components are `1`. Then `v` is an eigenvector of `A ^ 2`, and we can compute
  the eigenvalue to be `d * d`, or as `d + (Fintype.card V - 1)`, so those quantities must be equal.

  This essentially means that the graph has `d ^ 2 - d + 1` vertices. -/
theorem card_of_regular (hd : G.IsRegularOfDegree d) : d + (Fintype.card V - 1) = d * d := by
  have v := Classical.arbitrary V
  trans ((G.adjMatrix ℕ ^ 2) *ᵥ (fun _ => 1)) v
  · rw [adjMatrix_sq_of_regular hG hd, mulVec, dotProduct, ← insert_erase (mem_univ v)]
    simp only [sum_insert, mul_one, if_true, Nat.cast_id, mem_erase, not_true,
      Ne, not_false_iff, add_right_inj, false_and, of_apply]
    rw [Finset.sum_const_nat, card_erase_of_mem (mem_univ v), mul_one]; · rfl
    intro x hx; simp [(ne_of_mem_erase hx).symm]
  · rw [sq, ← mulVec_mulVec]
    simp only [adjMatrix_mulVec_const_apply_of_regular hd, neighborFinset,
      card_neighborSet_eq_degree, hd v, Function.const_def, adjMatrix_mulVec_apply _ _ (mulVec _ _),
      mul_one, sum_const, Set.toFinset_card, smul_eq_mul, Nat.cast_id]
    change (∑ _ ∈ (G.neighborSet v).toFinset, d) = d*d
    rw [Finset.sum_const,Set.toFinset_card,card_neighborSet_eq_degree,hd]
    simp

open scoped Classical in
include hG in
/-- The size of a `d`-regular friendship graph is `1 mod (d-1)`, and thus `1 mod p` for a
  factor `p ∣ d-1`. -/
theorem card_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1) (hd : G.IsRegularOfDegree d) :
    (Fintype.card V : ZMod p) = 1 := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  rw [← Nat.succ_pred_eq_of_pos hpos, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
  simp only [add_eq_right, Nat.cast_add, Nat.cast_one]
  have h := congr_arg (fun n : ℕ => (n : ZMod p)) (card_of_regular hG hd)
  revert h; simp [dmod]

end Nonempty

open scoped Classical in
theorem adjMatrix_sq_mul_const_one_of_regular (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R * of (fun _ _ => 1) = of (fun _ _ => (d : R)) := by
  ext x
  simp only [← hd x, degree, adjMatrix_mul_apply, sum_const, Nat.smul_one_eq_cast,
    of_apply]

open scoped Classical in
theorem adjMatrix_mul_const_one_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) :
    G.adjMatrix (ZMod p) * of (fun _ _ => 1) = of (fun _ _ => 1) := by
  rw [adjMatrix_sq_mul_const_one_of_regular hd, dmod]

open scoped Classical in
include hG in
/-- Modulo a factor of `d-1`, the square and all higher powers of the adjacency matrix
  of a `d`-regular friendship graph reduce to the matrix whose entries are all 1. -/
theorem adjMatrix_pow_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) {k : ℕ} (hk : 2 ≤ k) :
    G.adjMatrix (ZMod p) ^ k = of (fun _ _ => 1) := by
  match k with
  | 0 | 1 => exfalso; linarith
  | k + 2 =>
    induction k with
    | zero => exact adjMatrix_sq_mod_p_of_regular hG dmod hd
    | succ k hind =>
      rw [pow_succ', hind (Nat.le_add_left 2 k)]
      exact adjMatrix_mul_const_one_mod_p_of_regular dmod hd

variable [Nonempty V]

open scoped Classical in
include hG in
/-- This is the main proof. Assuming that `3 ≤ d`, we take `p` to be a prime factor of `d-1`.
  Then the `p`th power of the adjacency matrix of a `d`-regular friendship graph must have trace 1
  mod `p`, but we can also show that the trace must be the `p`th power of the trace of the original
  adjacency matrix, which is 0, a contradiction.
-/
theorem false_of_three_le_degree (hd : G.IsRegularOfDegree d) (h : 3 ≤ d) : False := by
  -- get a prime factor of d - 1
  let p : ℕ := (d - 1).minFac
  have p_dvd_d_pred := (ZMod.natCast_eq_zero_iff _ _).mpr (d - 1).minFac_dvd
  have dpos : 1 ≤ d := by lia
  have d_cast : ↑(d - 1) = (d : ℤ) - 1 := by norm_cast
  have : Fact p.Prime := ⟨Nat.minFac_prime (by lia)⟩
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have dmod : (d : ZMod p) = 1 := by
    rw [← Nat.succ_pred_eq_of_pos dpos, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
    simp only [add_eq_right, Nat.cast_add, Nat.cast_one]
    exact p_dvd_d_pred
  have Vmod := card_mod_p_of_regular hG dmod hd
  -- now we reduce to a trace calculation
  have := ZMod.trace_pow_card (G.adjMatrix (ZMod p))
  contrapose! this; clear this
  -- the trace is 0 mod p when computed one way
  rw [trace_adjMatrix, zero_pow this.out.ne_zero]
  -- but the trace is 1 mod p when computed the other way
  rw [adjMatrix_pow_mod_p_of_regular hG dmod hd hp2]
  dsimp only [Fintype.card] at Vmod
  simp only [Matrix.trace, Matrix.diag, mul_one, nsmul_eq_mul, sum_const,
    of_apply, Ne]
  rw [Vmod, ← Nat.cast_one (R := ZMod (Nat.minFac (d - 1))), ZMod.natCast_eq_zero_iff,
    Nat.dvd_one, Nat.minFac_eq_one_iff]
  lia

open scoped Classical in
include hG in
/-- If `d ≤ 1`, a `d`-regular friendship graph has at most one vertex, which is
  trivially a politician. -/
theorem existsPolitician_of_degree_le_one (hd : G.IsRegularOfDegree d) (hd1 : d ≤ 1) :
    ExistsPolitician G := by
  have h := card_of_regular hG hd
  have : Fintype.card V ≤ 1 := by interval_cases d <;> lia
  exact ⟨Classical.arbitrary V, fun w h ↦ (h <| Fintype.card_le_one_iff.mp this ..).elim⟩

open scoped Classical in
include hG in
/-- If `d = 2`, a `d`-regular friendship graph has 3 vertices, so it must be complete graph,
  and all the vertices are politicians. -/
theorem neighborFinset_eq_of_degree_eq_two (hd : G.IsRegularOfDegree 2) (v : V) :
    G.neighborFinset v = Finset.univ.erase v := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.subset_iff]
    intro x
    rw [mem_neighborFinset, Finset.mem_erase]
    exact fun h => ⟨(G.ne_of_adj h).symm, Finset.mem_univ _⟩
  convert_to 2 ≤ _
  · convert_to _ = Fintype.card V - 1
    · have hfr := card_of_regular hG hd
      lia
    · exact Finset.card_erase_of_mem (Finset.mem_univ _)
  · dsimp only [IsRegularOfDegree, degree] at hd
    rw [hd]

open scoped Classical in
include hG in
theorem existsPolitician_of_degree_eq_two (hd : G.IsRegularOfDegree 2) : ExistsPolitician G := by
  have v := Classical.arbitrary V
  use v
  intro w hvw
  rw [← mem_neighborFinset, neighborFinset_eq_of_degree_eq_two hG hd v, Finset.mem_erase]
  exact ⟨hvw.symm, Finset.mem_univ _⟩

open scoped Classical in
include hG in
theorem existsPolitician_of_degree_le_two (hd : G.IsRegularOfDegree d) (h : d ≤ 2) :
    ExistsPolitician G := by
  interval_cases d
  iterate 2 apply existsPolitician_of_degree_le_one hG hd; norm_num
  exact existsPolitician_of_degree_eq_two hG hd

end Friendship

include hG in
/-- **Friendship theorem**: We wish to show that a friendship graph has a politician (a vertex
  adjacent to all others). We proceed by contradiction, and assume the graph has no politician.
  We have already proven that a friendship graph with no politician is `d`-regular for some `d`,
  and now we do casework on `d`.
  If the degree is at most 2, we observe by casework that it has a politician anyway.
  If the degree is at least 3, the graph cannot exist. -/
theorem friendship_theorem [Nonempty V] : ExistsPolitician G := by
  by_contra npG
  rcases hG.isRegularOf_not_existsPolitician npG with ⟨d, dreg⟩
  rcases lt_or_ge d 3 with dle2 | dge3
  · exact npG (hG.existsPolitician_of_degree_le_two dreg (Nat.lt_succ_iff.mp dle2))
  · exact hG.false_of_three_le_degree dreg dge3

end

end Deldor14.FriendshipProof


/-
Port to the pinned Formal Conjectures environment by @Deldor14. The mathematical
proof is Chen's (1997). The Lean proof is adapted from the Apache-2.0
formalization of agnt-gg/erdos-lean, commit 8e5972f4e6787049b168e5350b1a2badc9eb8bcd,
Erdos/Erdos552.lean.

# Erdős Problem 552: $R(C_4, K_{1,n+1}) \le R(C_4, K_{1,n}) + 2$

Burr, Erdős, Faudree, Rousseau and Schelp asked whether $f(n+1) \le f(n) + 2$ for all $n$, where
$f(n) = R(C_4, K_{1,n})$ (erdosproblems.com/552). Chen Guantao proved it
(*A result on $C_4$-star Ramsey numbers*, Discrete Math. 163 (1997), 243–246). This file gives a
formal proof for every $n \ge 1$, stated with `SimpleGraph.graphRamsey` of formal-conjectures.

Proof. Let $N = f(n)$ and let $H$ be a $C_4$-free graph on $N + 2$ vertices. Two distinct vertices
of $H$ have at most one common neighbour.
* If some pair $x \ne y$ has no common neighbour, delete it. The remaining $N$ vertices contain a
  vertex $w$ with at least $n$ non-neighbours. Since $w$ is not adjacent to both $x$ and $y$, it has
  at least $n + 1$ non-neighbours in $H$.
* Otherwise every pair has exactly one common neighbour, so $H$ has a vertex $p$ adjacent to all
  others (friendship theorem). Any other vertex $u$ is adjacent only to $p$ and to the common
  neighbour of $u$ and $p$, so it has at least $N - 1 \ge n + 1$ non-neighbours, as $N \ge n + 2$.
-/

open Finset SimpleGraph

namespace OMA.ChenStar

section Lemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A vertex of degree at least `n` gives a copy of the star `K_{1,n}`. -/
lemma star_isContained_of_le_degree (D : SimpleGraph V) [DecidableRel D.Adj] {n : ℕ} {v : V}
    (hv : n ≤ D.degree v) : (completeBipartiteGraph (Fin 1) (Fin n)).IsContained D := by
  rw [← card_neighborFinset_eq_degree] at hv
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hv
  let e : Fin n ≃ s := (s.equivFinOfCardEq hcard).symm
  have hmem : ∀ i, D.Adj v (e i) := fun i => (mem_neighborFinset _ _ _).mp (hs (e i).2)
  let g : Fin 1 ⊕ Fin n → V := Sum.elim (fun _ => v) (fun i => (e i : V))
  have hg : Function.Injective g := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [g, Sum.elim_inl, Sum.elim_inr] at hab
    · exact congrArg Sum.inl (Subsingleton.elim a b)
    · have h := hmem b
      rw [← hab] at h
      exact (h.ne rfl).elim
    · have h := hmem a
      rw [hab] at h
      exact (h.ne rfl).elim
    · exact congrArg Sum.inr (e.injective (Subtype.ext hab))
  refine ⟨⟨⟨g, ?_⟩, hg⟩⟩
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;> simp [g, completeBipartiteGraph] at hab ⊢
  · exact hmem b
  · exact (hmem a).symm

omit [DecidableEq V] in
/-- A copy of the star `K_{1,n}` has a centre of degree at least `n`. -/
lemma exists_le_degree_of_star_isContained (D : SimpleGraph V) [DecidableRel D.Adj] {n : ℕ}
    (h : (completeBipartiteGraph (Fin 1) (Fin n)).IsContained D) : ∃ v, n ≤ D.degree v := by
  obtain ⟨f⟩ := h
  refine ⟨f (Sum.inl 0), ?_⟩
  rw [← card_neighborFinset_eq_degree]
  have key := Finset.card_le_card_of_injOn (s := (univ : Finset (Fin n)))
    (t := D.neighborFinset (f (Sum.inl 0))) (fun i => f (Sum.inr i)) ?_ ?_
  · simpa using key
  · intro i _
    rw [Finset.mem_coe, mem_neighborFinset]
    exact f.toHom.map_adj (by simp [completeBipartiteGraph])
  · intro i _ j _ hij
    exact Sum.inr_injective (f.injective hij)

omit [Fintype V] [DecidableEq V] in
/-- Two distinct vertices with two distinct common neighbours span a 4-cycle. -/
lemma cycle_isContained_of_two_common (C : SimpleGraph V) {a b x y : V} (hab : a ≠ b)
    (hxy : x ≠ y) (hax : C.Adj a x) (hbx : C.Adj b x) (hay : C.Adj a y) (hby : C.Adj b y) :
    (cycleGraph 4).IsContained C := by
  let f : Fin 4 → V := ![a, x, b, y]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    have hedge : ∀ i j : Fin 4, (cycleGraph 4).Adj i j →
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
        (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3) := by
      intro i j h
      rw [cycleGraph_adj] at h
      revert h
      fin_cases i <;> fin_cases j <;> decide
    rcases hedge i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hax
    · exact hax.symm
    · exact hbx.symm
    · exact hbx
    · exact hby
    · exact hby.symm
    · exact hay.symm
    · exact hay
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, hab, hab.symm, hxy, hxy.symm, hax.ne, hax.ne.symm, hbx.ne, hbx.ne.symm,
        hay.ne, hay.ne.symm, hby.ne, hby.ne.symm] at hij ⊢

end Lemmas

/-- The set whose infimum is `R(C₄, K_{1,n})`. -/
abbrev ramseySet (n : ℕ) : Set ℕ :=
  { m : ℕ | ∀ (C : SimpleGraph (Fin m)),
    (cycleGraph 4).IsContained C ∨ (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Cᶜ }

/-- On `2n + 2` vertices there is a `C₄` or a `K_{1,n}` in the complement: if every vertex has
fewer than `n` non-neighbours, two vertices of degree at least `n + 2` share two neighbours. -/
lemma two_mul_add_two_mem (n : ℕ) : 2 * n + 2 ∈ ramseySet n := by
  intro C
  classical
  by_cases h : ∃ v, n ≤ Cᶜ.degree v
  · obtain ⟨v, hv⟩ := h
    exact Or.inr (star_isContained_of_le_degree _ hv)
  · push Not at h
    left
    have hdeg : ∀ v, n + 2 ≤ C.degree v := by
      intro v
      have hv := h v
      rw [degree_compl, Fintype.card_fin] at hv
      have := C.degree_lt_card_verts v
      rw [Fintype.card_fin] at this
      omega
    let a : Fin (2 * n + 2) := ⟨0, by omega⟩
    let b : Fin (2 * n + 2) := ⟨1, by omega⟩
    have hab : a ≠ b := Fin.ne_of_val_ne (by simp [a, b])
    have hu := Finset.card_union_add_card_inter (C.neighborFinset a) (C.neighborFinset b)
    have hle : (C.neighborFinset a ∪ C.neighborFinset b).card ≤ 2 * n + 2 := by
      simpa using Finset.card_le_univ (C.neighborFinset a ∪ C.neighborFinset b)
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hu
    have hI : 1 < (C.neighborFinset a ∩ C.neighborFinset b).card := by
      have := hdeg a
      have := hdeg b
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hI
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hx hy
    exact cycle_isContained_of_two_common C hab hxy hx.1 hx.2 hy.1 hy.2

lemma ramseySet_nonempty (n : ℕ) : (ramseySet n).Nonempty :=
  ⟨_, two_mul_add_two_mem n⟩

/-- The star centred at vertex `0` of `Fin m`. -/
def centreStar (m : ℕ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun u _ => u.val = 0

/-- The star has no 4-cycle: each edge of a 4-cycle needs the centre, and two disjoint edges
cannot both use it. -/
lemma not_cycle_isContained_centreStar (m : ℕ) : ¬ (cycleGraph 4).IsContained (centreStar m) := by
  rintro ⟨f⟩
  have hadj : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → (f i).val = 0 ∨ (f j).val = 0 := by
    intro i j hij
    have h := f.toHom.map_adj hij
    simp only [centreStar, fromRel_adj] at h
    rcases h.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h01 := hadj 0 1 (by simp [cycleGraph_adj'])
  have h23 := hadj 2 3 (by simp [cycleGraph_adj'])
  have hinj : ∀ i j : Fin 4, (f i).val = 0 → (f j).val = 0 → i = j := fun i j hi hj =>
    f.injective (Fin.ext (hi.trans hj.symm))
  rcases h01 with h0 | h1 <;> rcases h23 with h2 | h3
  · exact absurd (hinj 0 2 h0 h2) (by decide)
  · exact absurd (hinj 0 3 h0 h3) (by decide)
  · exact absurd (hinj 1 2 h1 h2) (by decide)
  · exact absurd (hinj 1 3 h1 h3) (by decide)

/-- `R(C₄, K_{1,n}) ≥ n + 2` for `n ≥ 1`: on `m ≤ n + 1` vertices the centred star has no `C₄`,
and in its complement every vertex has degree less than `n`. -/
lemma add_two_le_ramsey (n : ℕ) (hn : 1 ≤ n) :
    n + 2 ≤ graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) := by
  apply le_csInf (ramseySet_nonempty n)
  intro m hm
  by_contra hlt
  push Not at hlt
  classical
  rcases hm (centreStar m) with h4 | hs
  · exact not_cycle_isContained_centreStar m h4
  · obtain ⟨v, hv⟩ := exists_le_degree_of_star_isContained _ hs
    rw [degree_compl, Fintype.card_fin] at hv
    rcases Nat.lt_or_ge m (n + 1) with hsmall | hbig
    · omega
    · -- m = n + 1 ≥ 2, so every vertex of the star has a neighbour
      have hm2 : 2 ≤ m := by omega
      have hpos : 0 < (centreStar m).degree v := by
        rw [(centreStar m).degree_pos_iff_exists_adj]
        by_cases hv0 : v.val = 0
        · refine ⟨⟨1, by omega⟩, ?_⟩
          simp only [centreStar, fromRel_adj]
          exact ⟨Fin.ne_of_val_ne (by simp [hv0]), Or.inl hv0⟩
        · refine ⟨⟨0, by omega⟩, ?_⟩
          simp only [centreStar, fromRel_adj]
          exact ⟨Fin.ne_of_val_ne (by simpa using hv0), by simp⟩
      omega

/-- The main step: `R(C₄, K_{1,n}) + 2` vertices suffice for `K_{1,n+1}`. -/
lemma ramsey_add_two_mem (n : ℕ) (hn : 1 ≤ n) :
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) + 2 ∈ ramseySet (n + 1) := by
  set N := graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) with hN_def
  have hNmem : N ∈ ramseySet n := Nat.sInf_mem (ramseySet_nonempty n)
  have hNge : n + 2 ≤ N := add_two_le_ramsey n hn
  intro H
  classical
  by_cases hc : (cycleGraph 4).IsContained H
  · exact Or.inl hc
  right
  -- In a C₄-free graph two distinct vertices have at most one common neighbour.
  have hcommon : ∀ x y, x ≠ y → ∀ a b, H.Adj x a → H.Adj y a → H.Adj x b → H.Adj y b →
      a = b := by
    intro x y hxy a b hxa hya hxb hyb
    by_contra hab
    exact hc (cycle_isContained_of_two_common H hxy hab hxa hya hxb hyb)
  by_cases hpair : ∃ x y, x ≠ y ∧ ∀ v, ¬ (H.Adj x v ∧ H.Adj y v)
  · obtain ⟨x, y, hxy, hno⟩ := hpair
    have hT : Fintype.card {v : Fin (N + 2) // v ≠ x ∧ v ≠ y} = N := by
      rw [Fintype.card_subtype]
      have hfilter : (univ.filter fun v : Fin (N + 2) => v ≠ x ∧ v ≠ y) =
          (univ.erase x).erase y := by
        ext v
        simp [and_comm]
      rw [hfilter, Finset.card_erase_of_mem (by simp [Ne.symm hxy]),
        Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
      omega
    let e : Fin N ≃ {v : Fin (N + 2) // v ≠ x ∧ v ≠ y} := (Fintype.equivFinOfCardEq hT).symm
    let ι : Fin N → Fin (N + 2) := fun i => (e i).1
    have hι : Function.Injective ι := fun i j h => e.injective (Subtype.ext h)
    rcases hNmem (H.comap ι) with h4 | hs
    · exact absurd (h4.trans ⟨⟨⟨ι, fun h => h⟩, hι⟩⟩) hc
    · obtain ⟨w, hw⟩ := exists_le_degree_of_star_isContained _ hs
      apply star_isContained_of_le_degree Hᶜ (v := ι w)
      -- `ι w` misses `x` or `y`.
      obtain ⟨z, hz, hzxy⟩ : ∃ z, ¬ H.Adj (ι w) z ∧ (z = x ∨ z = y) := by
        by_cases hx : H.Adj (ι w) x
        · exact ⟨y, fun hy => hno (ι w) ⟨hx.symm, hy.symm⟩, Or.inr rfl⟩
        · exact ⟨x, hx, Or.inl rfl⟩
      have hzι : ∀ i, ι i ≠ z := by
        intro i hi
        rcases hzxy with rfl | rfl
        · exact (e i).2.1 hi
        · exact (e i).2.2 hi
      let A := ((H.comap ι)ᶜ.neighborFinset w).map ⟨ι, hι⟩
      have hA : A ⊆ Hᶜ.neighborFinset (ι w) := by
        intro u hu
        simp only [A, Finset.mem_map, mem_neighborFinset, compl_adj, comap_adj,
          Function.Embedding.coeFn_mk] at hu
        obtain ⟨u', ⟨hne, hnadj⟩, rfl⟩ := hu
        rw [mem_neighborFinset, compl_adj]
        exact ⟨fun h => hne (hι h), hnadj⟩
      have hzA : z ∉ A := by
        simp only [A, Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
        exact fun i _ => hzι i
      have hzN : z ∈ Hᶜ.neighborFinset (ι w) := by
        rw [mem_neighborFinset, compl_adj]
        exact ⟨fun h => hzι w h, hz⟩
      have hcard : (insert z A).card ≤ Hᶜ.degree (ι w) := by
        rw [← card_neighborFinset_eq_degree]
        exact Finset.card_le_card (Finset.insert_subset hzN hA)
      rw [Finset.card_insert_of_notMem hzA, Finset.card_map,
        card_neighborFinset_eq_degree] at hcard
      omega
  · push Not at hpair
    -- Every pair has exactly one common neighbour: a friendship graph.
    have hfr : Deldor14.FriendshipProof.Friendship H := by
      intro v w hvw
      rw [Fintype.card_eq_one_iff]
      obtain ⟨c, hvc, hwc⟩ := hpair v w hvw
      refine ⟨⟨c, H.mem_commonNeighbors.mpr ⟨hvc, hwc⟩⟩, ?_⟩
      rintro ⟨d, hd⟩
      rw [H.mem_commonNeighbors] at hd
      exact Subtype.ext (hcommon v w hvw d c hd.1 hd.2 hvc hwc)
    obtain ⟨p, hp⟩ := Deldor14.FriendshipProof.friendship_theorem hfr
    obtain ⟨u, hup⟩ := exists_ne p
    obtain ⟨c, huc, hpc⟩ := hpair u p hup
    have hdeg : H.degree u ≤ 2 := by
      rw [← card_neighborFinset_eq_degree]
      calc (H.neighborFinset u).card ≤ ({p, c} : Finset (Fin (N + 2))).card := by
            apply Finset.card_le_card
            intro t ht
            rw [mem_neighborFinset] at ht
            by_cases htp : t = p
            · simp [htp]
            · have hpt : H.Adj p t := hp t (fun h => htp h.symm)
              have htc : t = c := hcommon u p hup t c ht hpt huc hpc
              simp [htc]
        _ ≤ 2 := Finset.card_le_two
    apply star_isContained_of_le_degree Hᶜ (v := u)
    rw [degree_compl, Fintype.card_fin]
    omega

/-- **Chen (1997).** For every `n ≥ 1`, `R(C₄, K_{1,n+1}) ≤ R(C₄, K_{1,n}) + 2`. -/
theorem erdos_552.variants.succ_le_add_two (n : ℕ) (hn : 1 ≤ n) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin (n + 1))) ≤
      SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin n)) + 2 :=
  Nat.sInf_le (ramsey_add_two_mem n hn)

end OMA.ChenStar


namespace Deldor14.Star.Packing
open Finset SimpleGraph OMA.ChenStar

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The endpoints of two-step walks from a fixed vertex, excluding that vertex.
In a four-cycle-free graph every endpoint has a unique intermediate vertex. -/
def endpoints (v : V) : Finset V :=
  (G.neighborFinset v).biUnion (fun u => (G.neighborFinset u).erase v)

theorem mem_endpoints {v z : V} :
    z ∈ endpoints G v ↔ z ≠ v ∧ ∃ u, G.Adj v u ∧ G.Adj z u := by
  simp only [endpoints,mem_biUnion,mem_erase,mem_neighborFinset]
  constructor
  · rintro ⟨u,vu,zv,uz⟩
    exact ⟨zv,u,vu,uz.symm⟩
  · rintro ⟨zv,u,vu,zu⟩
    exact ⟨u,vu,zv,zu.symm⟩

theorem card_endpoints (h : ¬(cycleGraph 4).IsContained G) (v : V) :
    (endpoints G v).card = ∑ u ∈ G.neighborFinset v, (G.degree u - 1) := by
  unfold endpoints
  rw [card_biUnion]
  · apply sum_congr rfl
    intro u hu
    rw [card_erase_of_mem,card_neighborFinset_eq_degree]
    exact (mem_neighborFinset _ _ _).mpr ((mem_neighborFinset _ _ _).mp hu).symm
  · intro a ha b hb ne
    apply Finset.disjoint_left.mpr
    intro z za zb
    rw [mem_erase,mem_neighborFinset] at za zb
    have va := (mem_neighborFinset _ _ _).mp ha
    have vb := (mem_neighborFinset _ _ _).mp hb
    exact h (cycle_isContained_of_two_common G ne za.1.symm va.symm vb.symm za.2 zb.2)

theorem local_bound (h : ¬(cycleGraph 4).IsContained G) (d : ℕ)
    (minimum : ∀ v, d ≤ G.degree v) (v : V) :
    G.degree v * (d-1) ≤ (endpoints G v).card := by
  rw [card_endpoints G h]
  calc
    G.degree v * (d-1) = ∑ _u ∈ G.neighborFinset v, (d-1) := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro u _
      exact Nat.sub_le_sub_right (minimum u) 1

theorem no_self (v : V) : v ∉ endpoints G v := by simp [mem_endpoints]

theorem improved_moore [Nonempty V] (h : ¬(cycleGraph 4).IsContained G) {d : ℕ}
    (large : 3 ≤ d) (minimum : ∀ v, d ≤ G.degree v) :
    d*(d-1)+2 ≤ Fintype.card V := by
  classical
  by_contra! contra
  have all (v w : V) (ne : v ≠ w) : ∃ u, G.Adj v u ∧ G.Adj w u := by
    by_contra none
    have exc : endpoints G v ⊆ ((univ.erase v).erase w) := by
      intro x hx
      have cond := (mem_endpoints G).mp hx
      refine mem_erase.mpr ⟨?_,mem_erase.mpr ⟨cond.1,mem_univ x⟩⟩
      rintro rfl
      exact none cond.2
    have ub := card_le_card exc
    rw [card_erase_of_mem (mem_erase.mpr ⟨ne.symm,mem_univ w⟩),
      card_erase_of_mem (mem_univ v),card_univ] at ub
    have lb := (Nat.mul_le_mul_right (d-1) (minimum v)).trans (local_bound G h d minimum v)
    have pos := Fintype.card_pos (α:=V)
    have nontriv : 2 ≤ Fintype.card V := by have := G.degree_lt_card_verts v; have := minimum v; omega
    omega
  have uniq {v w a b : V} (ne : v ≠ w) (va : G.Adj v a) (wa : G.Adj w a)
      (vb : G.Adj v b) (wb : G.Adj w b) : a=b := by
    by_contra ab
    exact h (cycle_isContained_of_two_common G ne ab va wa vb wb)
  have fr : Deldor14.FriendshipProof.Friendship G := by
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    intro v w ne
    rw [Fintype.card_eq_one_iff]
    obtain ⟨c,vc,wc⟩ := all v w ne
    exact ⟨⟨c,G.mem_commonNeighbors.mpr ⟨vc,wc⟩⟩,fun ⟨z,hz⟩ =>
      Subtype.ext (uniq ne (G.mem_commonNeighbors.mp hz).1 (G.mem_commonNeighbors.mp hz).2 vc wc)⟩
  obtain ⟨p,univP⟩ := Deldor14.FriendshipProof.friendship_theorem fr
  obtain ⟨u,pu⟩ := (G.degree_pos_iff_exists_adj p).mp (show 0<G.degree p by have := minimum p; omega)
  obtain ⟨c,cu,cp⟩ := all u p pu.ne.symm
  have subset : G.neighborFinset u ⊆ {p,c} := by
    intro t ht
    by_cases eq : t=p
    · simp [eq]
    · have tc := uniq pu.ne.symm ((mem_neighborFinset _ _ _).mp ht) (univP t (Ne.symm eq)) cu cp
      simp [tc]
  have ub := (card_le_card subset).trans Finset.card_le_two
  rw [card_neighborFinset_eq_degree] at ub
  have := minimum u
  omega

end Deldor14.Star.Packing


namespace Deldor14.Star
open SimpleGraph Finset

inductive Point (F : Type*) where
  | pole
  | inf (x : F)
  | aff (x y : F)
deriving DecidableEq, Fintype

namespace Point
variable {F : Type*} [Field F]

def inc : Point F → Point F → Prop
  | .aff a b, .aff c d => b+d=a*c
  | .aff a _, .inf c => a=c
  | .inf a, .aff c _ => a=c
  | .pole, .inf _ | .inf _, .pole => True
  | _,_ => False

theorem inc_symm {u v : Point F} (h : inc u v) : inc v u := by
  cases u <;> cases v <;> simpa [inc,eq_comm,add_comm,mul_comm] using h

def graph : SimpleGraph (Point F) where
  Adj u v := u ≠ v ∧ inc u v
  symm := ⟨fun u v h => ⟨h.1.symm,inc_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem affine_lines {a b c d x y z w : F}
    (dif : a=c → b=d → False)
    (h1 : b+y=a*x) (h2 : d+y=c*x) (h3 : b+w=a*z) (h4 : d+w=c*z) :
    x=z ∧ y=w := by
  have h : (a-c)*(x-z)=0 := by linear_combination -h1+h2+h3-h4
  rcases mul_eq_zero.mp h with e | e
  · have ac := sub_eq_zero.mp e
    subst c
    exact (dif rfl (by linear_combination h1-h2)).elim
  · have xz := sub_eq_zero.mp e
    subst z
    exact ⟨rfl,by linear_combination h1-h3⟩

theorem common_unique {a b x y : Point F} (ab : a ≠ b)
    (ax : inc a x) (bx : inc b x) (ay : inc a y) (by' : inc b y) : x=y := by
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp only [inc] at ax bx ay by' <;>
    first
    | contradiction
    | rfl
    | (obtain ⟨e,f⟩ := affine_lines (fun h k => ab (by rw [h,k])) ax bx ay by'
       rw [e,f])
    | grind

variable [Fintype F] [DecidableEq F]

theorem card_points : Fintype.card (Point F) = (Fintype.card F)^2 + Fintype.card F + 1 := by
  let e : Point F ≃ Option (F × Option F) := {
    toFun := fun | .pole => none | .inf a => some (a,none) | .aff a b => some (a,some b)
    invFun := fun | none => .pole | some (a,none) => .inf a | some (a,some b) => .aff a b
    left_inv := by rintro (_|_|_); all_goals rfl
    right_inv := by rintro (_|⟨a,_|b⟩); all_goals rfl }
  rw [Fintype.card_congr e,Fintype.card_option,Fintype.card_prod,Fintype.card_option]
  ring

private def neighbors (v : Point F) (x : F) : Point F :=
  match v with
  | .pole => .inf x
  | .inf a => .aff a x
  | .aff a b => if x=a then .inf a else .aff x (a*x-b)

private theorem neighbors_adj (v : Point F) (x : F) : graph.Adj v (neighbors v x) := by
  cases v with
  | pole => simp [graph,neighbors,inc]
  | inf a => simp [graph,neighbors,inc]
  | aff a b =>
    by_cases h : x=a
    · simp [graph,neighbors,inc,h]
    · simp [graph,neighbors,inc,h,Ne.symm h]

private theorem neighbors_inj (v : Point F) : Function.Injective (neighbors v) := by
  intro x y h
  cases v with
  | pole => simpa [neighbors] using h
  | inf a => simpa [neighbors] using h
  | aff a b =>
    by_cases hx : x=a <;> by_cases hy : y=a <;> simp_all [neighbors]

theorem le_degree [DecidableRel (graph (F:=F)).Adj] (v : Point F) :
    Fintype.card F ≤ graph.degree v := by
  let f (i : F) : ↥(graph.neighborFinset v) :=
    ⟨neighbors v i, (mem_neighborFinset _ _ _).mpr (neighbors_adj v i)⟩
  have inj : Function.Injective f := fun _ _ h => neighbors_inj v (congrArg Subtype.val h)
  rw [← card_neighborFinset_eq_degree]
  exact (Fintype.card_le_of_injective f inj).trans_eq (Fintype.card_coe _)

theorem no_square : ¬(cycleGraph 4).IsContained (graph (F:=F)) := by
  rintro ⟨f⟩
  have e01 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide)
  have e21 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 1 by decide)
  have e03 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 3 by decide)
  have e23 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide)
  have dif : f 0 ≠ f 2 := f.injective.ne (by decide)
  have eq := common_unique dif e01.2 e21.2 e03.2 e23.2
  exact (by decide : (1 : Fin 4) ≠ 3) (f.injective eq)

end Point
end Deldor14.Star


namespace Deldor14.Star.Slices
open SimpleGraph Finset

abbrev Vertex (F : Type*) (k t : ℕ) := (Fin k × Option F) ⊕ Fin t

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k t : ℕ}
variable (r : Fin k ↪ F) (z : F) (h : Fin t ↪ F)

def point : Vertex F k t → Point F
  | .inl (i,none) => .inf (r i)
  | .inl (i,some b) => .aff (r i) b
  | .inr x => .aff z (h x)

theorem point_injective (hz : ∀ i, ∀ _ : Fin t, r i ≠ z) :
    Function.Injective (point r z h) := by
  rintro (⟨i, _|b⟩ | x) (⟨j, _|c⟩ | y) e <;>
    simp only [point,Point.inf.injEq,Point.aff.injEq,reduceCtorEq] at e
  · rw [r.injective e]
  · rcases e with ⟨ij,bc⟩
    rw [r.injective ij,bc]
  · exact (hz i y e.1).elim
  · exact (hz j x e.1.symm).elim
  · rw [h.injective e.2]


def host : SimpleGraph (Vertex F k t) := Point.graph.comap (point r z h)

theorem no_square (hz : ∀ i, ∀ _ : Fin t, r i ≠ z) :
    ¬(cycleGraph 4).IsContained (host r z h) := by
  have emb : (host r z h).IsContained Point.graph :=
    ⟨⟨⟨point r z h, fun e => e⟩,point_injective r z h hz⟩⟩
  exact fun bad => Point.no_square (bad.trans emb)

def neighbor (v : Vertex F k t) (j : Fin k) : Vertex F k t :=
  match v with
  | .inl (i,none) => .inl (i,some (r j))
  | .inl (i,some b) =>
    if j=i then .inl (i,none) else .inl (j,some (r i*r j-b))
  | .inr x => .inl (j,some (z*r j-h x))

theorem neighbor_injective (v : Vertex F k t) : Function.Injective (neighbor r z h v) := by
  rintro a b e
  rcases v with ⟨i, _|y⟩ | x
  · exact r.injective (by simpa [neighbor] using e)
  · by_cases ai : a=i <;> by_cases bi : b=i <;> simp_all [neighbor]
  · exact (by simpa [neighbor] using e : a=b ∧ _) |>.1

theorem neighbor_adj (hz : ∀ i, ∀ _ : Fin t, r i ≠ z) (v : Vertex F k t) (j : Fin k) :
    (host r z h).Adj v (neighbor r z h v j) := by
  rcases v with ⟨i, _|y⟩ | x
  · simp [host,Point.graph,Point.inc,point,neighbor]
  · by_cases eq : j=i
    · simp [host,Point.graph,Point.inc,point,neighbor,eq]
    · have dif := r.injective.ne (Ne.symm eq)
      simp [host,Point.graph,Point.inc,point,neighbor,eq,dif]
  · have dif := (hz j x).symm
    simp [host,Point.graph,Point.inc,point,neighbor,dif]

theorem le_degree (hz : ∀ i, ∀ _ : Fin t, r i ≠ z) [DecidableRel (host r z h).Adj]
    (v : Vertex F k t) : k ≤ (host r z h).degree v := by
  let G := host r z h
  let f (i : Fin k) : ↥(G.neighborFinset v) :=
    ⟨neighbor r z h v i,(mem_neighborFinset _ _ _).mpr (neighbor_adj r z h hz v i)⟩
  have inj : Function.Injective f := fun _ _ e => neighbor_injective r z h v (congrArg Subtype.val e)
  have count := (Fintype.card_le_of_injective f inj).trans_eq (Fintype.card_coe _)
  simpa only [Fintype.card_fin,card_neighborFinset_eq_degree] using count

end Deldor14.Star.Slices


namespace Deldor14.Star
open SimpleGraph Finset OMA.ChenStar

/-- A single host graph obstructs every Ramsey assertion on fewer vertices. -/
theorem lower_from_host {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} (red : ¬ (cycleGraph 4).IsContained G)
    (blue : ∀ v, Gᶜ.degree v < n) :
    Fintype.card V <
      graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) := by
  classical
  let m := graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n))
  change Fintype.card V < m
  by_contra! small
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin m) ≤ Fintype.card V by simpa using small)
  let C : SimpleGraph (Fin m) := G.comap e
  have r : C.IsContained G := ⟨⟨⟨e,fun h => h⟩,e.injective⟩⟩
  have b : Cᶜ.IsContained Gᶜ := by
    refine ⟨⟨⟨e,?_⟩,e.injective⟩⟩
    intro i j h
    rw [compl_adj] at h ⊢
    exact ⟨e.injective.ne h.1,h.2⟩
  have mem : m ∈ ramseySet n := Nat.sInf_mem (ramseySet_nonempty n)
  rcases mem C with h | h
  · exact red (h.trans r)
  · obtain ⟨v,hv⟩ := exists_le_degree_of_star_isContained Gᶜ (h.trans b)
    exact (blue v).not_ge hv

end Deldor14.Star


namespace Deldor14.Star
open SimpleGraph Finset OMA.ChenStar

noncomputable abbrev number (n : ℕ) :=
  graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n))

/-- Field orders give a whole block of lower bounds, including the square order.
Each full row consists of all affine points of one slope and its point at infinity.
Additional affine points are taken from an extra row. -/
theorem lower_on_block (F : Type*) [Field F] [Fintype F] {k t : ℕ}
    (hk : k ≤ Fintype.card F) (ht : t < Fintype.card F)
    (room : 0<t → k<Fintype.card F) :
    k * Fintype.card F + t + k < number (k * Fintype.card F + t) := by
  classical
  let q := Fintype.card F
  have pos : 0<q := Fintype.card_pos
  let e : Fin q ≃ F := (Fintype.equivFin F).symm
  let r : Fin k ↪ F := (Fin.castLEEmb hk).trans e.toEmbedding
  let h : Fin t ↪ F := (Fin.castLEEmb ht.le).trans e.toEmbedding
  let z := e ⟨k%q,Nat.mod_lt k pos⟩
  have sep (i : Fin k) (j : Fin t) : r i ≠ z := by
    intro bad
    have lt := room (Nat.zero_lt_of_lt j.isLt)
    have eq : (i.val:ℕ)=k%q := congrArg Fin.val (e.injective bad)
    rw [Nat.mod_eq_of_lt lt] at eq
    have := i.isLt
    omega
  let G := Slices.host r z h
  have sz : Fintype.card (Slices.Vertex F k t) = k*q+t+k := by
    simp only [Slices.Vertex,Fintype.card_sum,Fintype.card_prod,Fintype.card_option,Fintype.card_fin,q]
    ring
  obtain hk0 | hkpos := Nat.eq_zero_or_pos k
  · subst k
    simp only [Nat.zero_mul,Nat.zero_add,Nat.add_zero]
    by_cases ht0 : t=0
    · subst t
      change 0 < number 0
      by_contra! bad
      have eq : number 0 = 0 := by omega
      have hm : number 0 ∈ ramseySet 0 := Nat.sInf_mem (ramseySet_nonempty 0)
      rw [eq] at hm
      rcases hm (⊥ : SimpleGraph (Fin 0)) with ⟨f⟩ | ⟨f⟩
      · obtain ⟨g⟩ := f
        exact Fin.elim0 (g 0)
      · obtain ⟨g⟩ := f
        exact Fin.elim0 (g (.inl 0))
    · exact lt_of_lt_of_le (by omega : t < t+2) (add_two_le_ramsey t (by omega))
  · have positive : 0 < k*q+t := by have := Nat.mul_pos hkpos pos; omega
    have d (v) := Slices.le_degree r z h sep v
    have bound : ∀ v, Gᶜ.degree v < k*q+t := by
      intro v
      rw [degree_compl,sz]
      have := d v
      change k ≤ G.degree v at this
      omega
    simpa only [sz] using lower_from_host G (Slices.no_square r z h sep) bound

theorem field_lower (F : Type*) [Field F] [Fintype F] {n : ℕ}
    (hn : n ≤ Fintype.card F ^ 2) : n + n/Fintype.card F < number n := by
  let q := Fintype.card F
  have pos : 0<q := Fintype.card_pos
  have eq := Nat.div_add_mod n q
  have hsplit : n/q*q + n%q = n := by simpa [Nat.mul_comm] using eq
  have hk : n/q ≤ q := by
    by_contra! bad
    have := Nat.mul_le_mul_right q bad
    change n ≤ q^2 at hn
    rw [Nat.succ_mul] at this
    rw [pow_two] at hn
    omega
  have room (rem : 0 < n%q) : n/q < q := by
    by_contra! no
    have same : n/q=q := by omega
    rw [same] at hsplit
    change n ≤ q^2 at hn
    nlinarith only [hsplit,hn,rem]
  have g := lower_on_block F hk (Nat.mod_lt n pos) room
  change n/q*q+n%q + n/q < number (n/q*q+n%q) at g
  rwa [hsplit] at g

theorem field_plus_one (F : Type*) [Field F] [Fintype F] :
    Fintype.card F ^ 2 + Fintype.card F + 1 < number (Fintype.card F^2+1) := by
  classical
  let G := Point.graph (F:=F)
  have low := lower_from_host (n:=Fintype.card F^2+1) G Point.no_square (by
    intro v
    rw [degree_compl,Point.card_points]
    have h := Point.le_degree v
    change Fintype.card F ≤ G.degree v at h
    omega)
  simpa only [Point.card_points] using low

end Deldor14.Star


namespace Deldor14.Star
open SimpleGraph OMA.ChenStar

/-- The friendship theorem rules out the one missing vertex in the elementary
two-step count. This is the sharp square-order side of Parsons' estimate. -/
theorem parsons_upper {n k : ℕ} (hk : 2 ≤ k) (hn : n ≤ k^2) :
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) ≤ n+k+1 := by
  classical
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra hs
  have minimum (v : Fin (n+k+1)) : k+1 ≤ G.degree v := by
    have small : Gᶜ.degree v < n := lt_of_not_ge (fun large => hs (star_isContained_of_le_degree Gᶜ large))
    rw [degree_compl,Fintype.card_fin] at small
    omega
  haveI : Nonempty (Fin (n+k+1)) := ⟨⟨0,by omega⟩⟩
  have bound := Packing.improved_moore G red (d:=k+1) (by omega) minimum
  simp only [Nat.add_sub_cancel,Fintype.card_fin] at bound
  nlinarith

end Deldor14.Star


namespace Deldor14.Star
open SimpleGraph

/-- Covers every finite field, including non-prime orders. -/
theorem field_square (F : Type*) [Field F] [Fintype F] :
    number (Fintype.card F ^ 2) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  let q := Fintype.card F
  have pos : 0<q := Fintype.card_pos
  have two : 2 ≤ q := Fintype.one_lt_card
  have lo := field_lower F (n:=q^2) (by rfl)
  have div : q^2/q=q := by rw [pow_two,Nat.mul_div_cancel _ pos]
  change q^2 + q^2/q < number (q^2) at lo
  rw [div] at lo
  exact Nat.le_antisymm (parsons_upper two le_rfl) lo

theorem prime_square {p : ℕ} (hp : p.Prime) : number (p^2)=p^2+p+1 := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [ZMod.card] using field_square (ZMod p)

/-- If a Ramsey value saves c below n+sqrt(n), the entire interval from
sqrt(n) through sqrt(n)+c is devoid of finite-field orders. -/
theorem field_gap (F : Type*) [Field F] [Fintype F] {n : ℕ} {c : ℝ}
    (hn : n ≤ Fintype.card F^2)
    (witness : (number n : ℝ) ≤ (n : ℝ) + Real.sqrt n - c) :
    Real.sqrt n + c < Fintype.card F := by
  let q := Fintype.card F
  have hq : 0<q := Fintype.card_pos
  have lo : n+n/q+1 ≤ number n := field_lower F hn
  have realLo : (n:ℝ)+(n/q:ℕ)+1 ≤ (number n:ℝ) := by exact_mod_cast lo
  have y : (n/q:ℕ)+1 ≤ Real.sqrt n - c := by linarith
  have divbound : n < (n/q+1)*q := by
    have eq := Nat.mod_add_div n q
    have rem := Nat.mod_lt n hq
    nlinarith only [eq,rem]
  have divbound' : (n:ℝ) < ((n/q:ℕ)+1 : ℝ)*q := by exact_mod_cast divbound
  have pos : (0:ℝ) ≤ q := by positivity
  have bound := lt_of_lt_of_le divbound' (mul_le_mul_of_nonneg_right y pos)
  have square := Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)
  change Real.sqrt n + c < (q:ℝ)
  by_contra! contra
  have product := mul_nonneg (show 0 ≤ Real.sqrt n + c - (q:ℝ) by linarith) pos
  nlinarith [sq_nonneg ((q:ℝ)-Real.sqrt n)]

theorem prime_gap {p n : ℕ} (hp : p.Prime) (hn : n ≤ p^2) {c : ℝ}
    (witness : (number n : ℝ) ≤ n + Real.sqrt n - c) : Real.sqrt n + c < p := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := field_gap (ZMod p) (n:=n) (c:=c) (by simpa only [ZMod.card] using hn) witness
  simpa only [ZMod.card] using h

end Deldor14.Star


namespace Deldor14.Star.EvenRows
open SimpleGraph Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
variable {s : ℕ} (r : Fin s ↪ F) (zeroRow : Fin s)

abbrev Vertex (F : Type*) (s : ℕ) := (F × F) ⊕ Fin s

def point : Vertex F s → Point F
  | .inl (a,b) => .aff a b
  | .inr i => .inf (r i)

theorem point_injective : Function.Injective (point r) := by
  rintro (⟨a,b⟩|i) (⟨x,y⟩|j) e <;> simp_all [point]

def host := Point.graph.comap (point r)

theorem no_square : ¬(cycleGraph 4).IsContained (host r) := by
  have e : (host r).IsContained Point.graph :=
    ⟨⟨⟨point r, fun h => h⟩, point_injective r⟩⟩
  exact fun h => Point.no_square (h.trans e)

/-- A row of slope zero needs its point at infinity to replace a missing loop.
All other rows have a genuine neighbour at each affine slope. -/
def neighbor (v : Vertex F s) (x : F) : Vertex F s :=
  match v with
  | .inl (a,b) => if a=0 ∧ x=0 then .inr zeroRow else .inl (x,a*x-b)
  | .inr i => .inl (r i,x)

theorem neighbor_injective (v : Vertex F s) : Function.Injective (neighbor r zeroRow v) := by
  intro x y e
  rcases v with ⟨a,b⟩ | i
  · by_cases hx : a=0 ∧ x=0 <;> by_cases hy : a=0 ∧ y=0 <;> simp_all [neighbor]
  · simpa [neighbor] using e

theorem neighbor_adj (zero : r zeroRow=0) (v : Vertex F s) (x : F) :
    (host r).Adj v (neighbor r zeroRow v x) := by
  rcases v with ⟨a,b⟩ | i
  · by_cases hx : a=0 ∧ x=0
    · simp [host,neighbor,point,Point.graph,Point.inc,hx,zero,hx.1]
    · have ne : ¬(a=x ∧ b=a*x-b) := by
        rintro ⟨rfl,eq⟩
        have h : b+b=a*a := by linear_combination eq
        rw [CharTwo.add_self_eq_zero] at h
        have a0 := mul_self_eq_zero.mp h.symm
        exact hx ⟨a0,a0⟩
      simp [host,neighbor,point,Point.graph,Point.inc,hx]
      tauto
  · simp [host,neighbor,point,Point.graph,Point.inc]

theorem min_degree (zero : r zeroRow=0) [DecidableRel (host r).Adj] (v : Vertex F s) :
    Fintype.card F ≤ (host r).degree v := by
  let f (i : F) : ↥((host r).neighborFinset v) :=
    ⟨neighbor r zeroRow v i, (mem_neighborFinset _ _ _).mpr (neighbor_adj r zeroRow zero v i)⟩
  have inj : Function.Injective f := fun _ _ e => neighbor_injective r zeroRow v (congrArg Subtype.val e)
  rw [← card_neighborFinset_eq_degree]
  exact (Fintype.card_le_of_injective f inj).trans_eq (Fintype.card_coe _)

end Deldor14.Star.EvenRows


namespace Deldor14.Star
open SimpleGraph Finset

/-- Parsons' interval at a power of two. Removing chosen points at infinity
preserves the minimum degree as long as the point for slope zero remains. -/
theorem even_field_interval (F : Type*) [Fintype F] [Field F] [CharP F 2]
    {n s : ℕ} (spos : 0<s) (sle : s ≤ Fintype.card F)
    (sz : n + Fintype.card F = Fintype.card F^2+s) :
    number n = n + Fintype.card F + 1 := by
  classical
  let q := Fintype.card F
  have two : 2 ≤ q := Fintype.one_lt_card
  let e := (Fintype.equivFin F).symm.toEmbedding
  let b := (Fin.castLEEmb sle).trans e
  let z : Fin s := ⟨0,spos⟩
  let r : Fin s ↪ F := ⟨fun x => b x - b z, fun _ _ h => b.injective (sub_left_inj.mp h)⟩
  have zero : r z=0 := sub_self _
  let G := EvenRows.host r
  have count : Fintype.card (EvenRows.Vertex F s) = n+q := by
    rw [sz]
    simp [EvenRows.Vertex,pow_two]
  have min (v) : q ≤ G.degree v := EvenRows.min_degree r z zero v
  have hs : n+q=q^2+s := sz
  have bound : ∀ v, Gᶜ.degree v < n := by
    intro v
    have := min v
    have positive : 0 < n := by
      have h : q ≤ q^2 := by exact Nat.le_self_pow (by decide : 2≠0) q
      omega
    rw [degree_compl,count]
    omega
  have lower := lower_from_host G (EvenRows.no_square r) bound
  rw [count] at lower
  have nq : n ≤ q^2 := by change s ≤ q at sle; omega
  exact Nat.le_antisymm (parsons_upper two nq) lower

theorem power_two_interval {m n s : ℕ} (hm : m≠0) (spos : 0<s) (sle : s ≤ 2^m)
    (sz : n + 2^m = (2^m)^2+s) : number n = n+2^m+1 := by
  letI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 m) = 2^m := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 m hm]
  simpa only [hq] using even_field_interval (GaloisField 2 m) spos
    (by simpa only [hq] using sle) (n:=n) (by simpa only [hq] using sz)

end Deldor14.Star


namespace Deldor14.Star.ExcessOne
open Finset SimpleGraph OMA.ChenStar Packing
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ}

def common (v w : V) : Finset V := G.neighborFinset v ∩ G.neighborFinset w

theorem mem_common {v w u : V} : u ∈ common G v w ↔ G.Adj v u ∧ G.Adj w u := by
  simp [common]

theorem codeg_le_one (red : ¬ (cycleGraph 4).IsContained G) {v w : V} (vw : v≠w) :
    (common G v w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra ab
  exact red (cycle_isContained_of_two_common G vw ab ((mem_common G).mp ha).1 ((mem_common G).mp ha).2
    ((mem_common G).mp hb).1 ((mem_common G).mp hb).2)

theorem regular_of_min (red : ¬ (cycleGraph 4).IsContained G) (large : 3≤d)
    (count : Fintype.card V=d*(d-1)+2) (minimum : ∀ v, d≤G.degree v) :
    ∀ v, G.degree v=d := by
  intro v
  have sub : endpoints G v ⊆ univ.erase v := fun x hx =>
    mem_erase.mpr ⟨((mem_endpoints G).mp hx).1, mem_univ x⟩
  have ub := card_le_card sub
  rw [card_erase_of_mem (mem_univ v),card_univ,count] at ub
  have low := local_bound G red d minimum v
  by_contra not_eq
  have high : d+1 ≤ G.degree v := by have := minimum v; omega
  have h := Nat.mul_le_mul_right (d-1) high
  rw [Nat.add_mul,one_mul] at h
  omega

def missing (v : V) := (univ.erase v) \ endpoints G v

theorem mem_missing {v w : V} : w ∈ missing G v ↔ w≠v ∧ common G v w = ∅ := by
  classical
  simp only [missing,mem_sdiff,mem_erase,mem_univ,and_true,mem_endpoints]
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [mem_common]
  constructor
  · rintro ⟨ne,none⟩
    exact ⟨ne,fun x hx => none ⟨ne,x,hx⟩⟩
  · rintro ⟨ne,none⟩
    exact ⟨ne,fun ⟨_,x,hx⟩ => none x hx⟩

theorem one_missing (red : ¬ (cycleGraph 4).IsContained G)
    (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d) (v : V) :
    (missing G v).card=1 := by
  have sub : endpoints G v ⊆ univ.erase v := fun x hx =>
    mem_erase.mpr ⟨((mem_endpoints G).mp hx).1, mem_univ x⟩
  have ep : (endpoints G v).card = d*(d-1) := by
    rw [card_endpoints G red]
    simp [reg]
  unfold missing
  rw [card_sdiff_of_subset sub, card_erase_of_mem (mem_univ v), card_univ, count, ep]
  omega

noncomputable def mate (red : ¬ (cycleGraph 4).IsContained G)
    (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d) (v : V) : V :=
  Classical.choose (Finset.card_eq_one.mp (one_missing G red count reg v))

theorem singleton_mate (red : ¬ (cycleGraph 4).IsContained G)
    (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d) (v : V) :
    missing G v = {mate G red count reg v} :=
  Classical.choose_spec (Finset.card_eq_one.mp (one_missing G red count reg v))

end Deldor14.Star.ExcessOne


namespace Deldor14.Star.ExcessOne
open Finset SimpleGraph OMA.ChenStar
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ} (red : ¬ (cycleGraph 4).IsContained G)
  (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d)

theorem mate_spec (v w : V) :
    w = mate G red count reg v ↔ w≠v ∧ common G v w=∅ := by
  rw [← mem_missing, singleton_mate G red count reg, mem_singleton]

theorem mate_ne (v : V) : mate G red count reg v ≠ v := ((mate_spec G red count reg v _).mp rfl).1

theorem mate_involutive : Function.Involutive (mate G red count reg) := by
  intro v
  have spec := (mate_spec G red count reg v _).mp rfl
  symm
  apply (mate_spec G red count reg _ _).mpr
  exact ⟨spec.1.symm, (inter_comm _ _).trans spec.2⟩

theorem codegree_formula (v w : V) :
    ((common G v w).card : ℤ) =
      1 + (if v=w then (d : ℤ)-1 else 0) - (if v=mate G red count reg w then 1 else 0) := by
  classical
  by_cases eq : v=w
  · subst v
    have ne := Ne.symm (mate_ne G red count reg w)
    simp [common, reg, ne]
  · by_cases opposite : v=mate G red count reg w
    · have emp := ((mate_spec G red count reg w v).mp opposite).2
      have emp' : common G v w=∅ := (inter_comm _ _).trans emp
      rw [emp',card_empty,if_neg eq,if_pos opposite]
      norm_num
    · have notemp : common G v w ≠ ∅ := by
        intro emp
        exact opposite ((mate_spec G red count reg w v).mpr ⟨eq,(inter_comm _ _).trans emp⟩)
      have lo := card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr notemp)
      have hi := codeg_le_one G red eq
      have one : (common G v w).card=1 := by omega
      simp [one,eq,opposite]

def walks (v w : V) : ℤ := ∑ a ∈ G.neighborFinset v, ((common G a w).card : ℤ)

theorem walks_expand (x y : V) : walks G x y = ∑ a ∈ G.neighborFinset x, ∑ b ∈ G.neighborFinset y,
    (if G.Adj a b then (1:ℤ) else 0)  := by
  classical
  apply sum_congr rfl
  intro a _
  rw [sum_boole]
  congr 1
  congr 1
  ext b
  simp [common,and_comm]

theorem walks_symm (v w : V) : walks G v w = walks G w v := by
  classical
  rw [walks_expand,walks_expand,Finset.sum_comm]
  simp_rw [G.adj_comm]

theorem walks_formula (v w : V) :
    walks G v w = (d:ℤ) + (if G.Adj v w then (d:ℤ)-1 else 0) -
      (if G.Adj v (mate G red count reg w) then 1 else 0) := by
  classical
  unfold walks
  simp_rw [codegree_formula G red count reg]
  rw [sum_sub_distrib,sum_add_distrib]
  simp [reg]

theorem mate_commutes (v w : V) :
    G.Adj v (mate G red count reg w) ↔ G.Adj w (mate G red count reg v) := by
  classical
  have h := walks_symm G v w
  rw [walks_formula G red count reg,walks_formula G red count reg] at h
  simp only [G.adj_comm w v] at h
  by_cases a : G.Adj v (mate G red count reg w) <;>
    by_cases b : G.Adj w (mate G red count reg v) <;> simp_all <;> omega

theorem mate_preserves (v w : V) :
    G.Adj (mate G red count reg v) (mate G red count reg w) ↔ G.Adj v w := by
  rw [mate_commutes G red count reg, mate_involutive G red count reg, G.adj_comm]

theorem even_edges (S : Finset V) :
    Even (∑ a ∈ S, ∑ b ∈ S, (if G.Adj a b then (1:ℤ) else 0)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    simp_rw [sum_insert ha]
    rw [sum_add_distrib]
    have flip : (∑ b ∈ S, (if G.Adj b a then (1:ℤ) else 0)) =
        ∑ b ∈ S, (if G.Adj a b then (1:ℤ) else 0) := by
      apply sum_congr rfl
      intro b _
      simp only [G.adj_comm b a]
    rw [flip]
    obtain ⟨k,hk⟩ := ih
    rw [hk]
    exact ⟨(∑ b ∈ S, (if G.Adj a b then (1:ℤ) else 0))+k,by rw [if_neg (G.irrefl (v:=a))]; ring⟩

theorem even_diagonal (v : V) : Even (walks G v v) := by
  rw [walks_expand]
  exact even_edges G _

end Deldor14.Star.ExcessOne


namespace Deldor14.Star.ExcessOne
open Finset SimpleGraph Matrix
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ} (red : ¬ (cycleGraph 4).IsContained G)
  (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d)

theorem mate_not_adj_of_even (even : Even d) (v : V) : ¬G.Adj v (mate G red count reg v) := by
  classical
  intro adj
  obtain ⟨z,h⟩ := even_diagonal G v
  rw [walks_formula G red count reg,if_neg (G.irrefl (v:=v)),if_pos adj] at h
  obtain ⟨k,hk⟩ := even
  omega

variable (R : Type*) [CommRing R]

def ones (V : Type*) (R : Type*) [One R] : Matrix V V R := Matrix.of fun _ _ => 1

noncomputable def permutation : Matrix V V R := Matrix.of (fun i j => if i=mate G red count reg j then 1 else 0)

theorem mul_permutation (B : Matrix V V R) (i j : V) :
    (B * permutation G red count reg R) i j = B i (mate G red count reg j) := by
  classical
  simp [Matrix.mul_apply,permutation,mul_ite]

theorem permutation_mul (B : Matrix V V R) (i j : V) :
    (permutation G red count reg R * B) i j = B (mate G red count reg i) j := by
  classical
  have eq (k : V) : i=mate G red count reg k ↔ k=mate G red count reg i := by
    constructor <;> intro h
    · rw [h,mate_involutive G red count reg]
    · rw [h,mate_involutive G red count reg]
  simp [Matrix.mul_apply, permutation, eq, ite_mul]

theorem adj_square_entries (i j : V) :
    ((G.adjMatrix R)^2) i j = ((common G i j).card : R) := by
  classical
  rw [sq,mul_adjMatrix_apply]
  simp only [adjMatrix_apply,sum_boole]
  congr 1
  congr 1
  ext x
  simp [common,and_comm]

theorem adj_square_decomp :
    G.adjMatrix R ^ 2 = ones V R + ((d:R)-1) • (1 : Matrix V V R) - permutation G red count reg R := by
  classical
  ext i j
  have c := codegree_formula G red count reg i j
  rw [adj_square_entries]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, ones, permutation, Matrix.of_apply,
    Matrix.one_apply,smul_eq_mul]
  have lift := congrArg (fun z : ℤ => (z:R)) c
  by_cases same : i=j <;> by_cases opp : i=mate G red count reg j <;>
    first
    | simpa only [if_pos same,if_pos opp,mul_one,Int.cast_natCast,Int.cast_add,Int.cast_sub,Int.cast_one] using lift
    | simpa only [if_pos same,if_neg opp,mul_one,Int.cast_natCast,Int.cast_add,Int.cast_sub,Int.cast_one,Int.cast_zero] using lift
    | simpa only [if_neg same,if_pos opp,mul_zero,Int.cast_natCast,Int.cast_add,Int.cast_sub,Int.cast_one,Int.cast_zero] using lift
    | simpa only [if_neg same,if_neg opp,mul_zero,Int.cast_natCast,Int.cast_add,Int.cast_sub,Int.cast_one,Int.cast_zero] using lift

theorem commute_adj : Commute (G.adjMatrix R) (permutation G red count reg R) := by
  classical
  ext i j
  rw [mul_permutation,permutation_mul]
  simp only [adjMatrix_apply]
  have eq := (mate_commutes G red count reg i j).trans (G.adj_comm j _)
  by_cases h : G.Adj i (mate G red count reg j) <;> simp [h,← eq]

theorem perm_sq : permutation G red count reg R ^ 2 = 1 := by
  classical
  ext i j
  rw [sq,mul_permutation]
  simp only [permutation,Matrix.of_apply,Matrix.one_apply]
  rw [mate_involutive G red count reg j]

theorem perm_ones : permutation G red count reg R * ones V R = ones V R := by
  ext i j
  rw [permutation_mul]
  rfl

theorem ones_perm : ones V R * permutation G red count reg R = ones V R := by
  ext i j
  rw [mul_permutation]
  rfl

include reg in
theorem adj_ones : G.adjMatrix R * ones V R = (d:R) • ones V R := by
  classical
  ext i j
  rw [adjMatrix_mul_apply]
  simp [ones,reg]

end Deldor14.Star.ExcessOne


namespace Deldor14.Star.ExcessOne
open Finset SimpleGraph OMA.ChenStar
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ} (red : ¬ (cycleGraph 4).IsContained G)
  (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d)

theorem mate_adj_of_odd (odd : Odd d) (v : V) : G.Adj v (mate G red count reg v) := by
  classical
  by_contra avoid
  have h := even_diagonal G v
  rw [walks_formula G red count reg,if_neg (G.irrefl (v:=v)),if_neg avoid,sub_zero,add_zero] at h
  obtain ⟨k,hk⟩ := odd
  obtain ⟨z,hz⟩ := h
  omega

include red count reg in
theorem no_odd_excess [Nonempty V] (large : 3≤d) (odd : Odd d) : False := by
  classical
  let v : V := Classical.arbitrary V
  let m := mate G red count reg
  have single : ∃ u, G.Adj v u ∧ u≠m v := by
    by_contra! no
    have sub : G.neighborFinset v ⊆ {m v} := by
      intro u hu
      exact mem_singleton.mpr (no u ((G.mem_neighborFinset _ _).mp hu))
    have h := card_le_card sub
    rw [card_neighborFinset_eq_degree,reg,card_singleton] at h
    omega
  obtain ⟨u,vu,ne⟩ := single
  have mu : v ≠ m u := by
    intro eq
    have h : m (m u)=u := mate_involutive G red count reg u
    exact ne (h.symm.trans (congrArg m eq.symm))
  have h := cycle_isContained_of_two_common G mu ne vu
    (mate_adj_of_odd G red count reg odd u).symm (mate_adj_of_odd G red count reg odd v)
    ((mate_preserves G red count reg u v).mpr vu.symm)
  exact red h

end Deldor14.Star.ExcessOne
namespace Deldor14.Star
open SimpleGraph OMA.ChenStar

theorem upper_square_plus_one {q : ℕ} (hq : 2≤q) (even : Even q) :
    number (q^2+1) ≤ q^2+q+2 := by
  classical
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra blue
  have minimum (v : Fin (q^2+q+2)) : q+1 ≤ G.degree v := by
    have small : Gᶜ.degree v < q^2+1 :=
      lt_of_not_ge (fun large => blue (star_isContained_of_le_degree Gᶜ large))
    rw [degree_compl,Fintype.card_fin] at small
    omega
  have count : Fintype.card (Fin (q^2+q+2)) = (q+1)*(q+1-1)+2 := by simp; ring
  have reg := ExcessOne.regular_of_min G red (d:=q+1) (by omega) count minimum
  haveI : Nonempty (Fin (q^2+q+2)) := ⟨⟨0,by omega⟩⟩
  have odd : Odd (q+1) := by obtain ⟨l,hl⟩ := even; exact ⟨l,by omega⟩
  exact ExcessOne.no_odd_excess G red count reg (by omega) odd

theorem field_even_square_plus_one (F : Type*) [Field F] [Fintype F] (even : Even (Fintype.card F)) :
    number (Fintype.card F^2+1) = Fintype.card F^2+Fintype.card F+2 :=
  Nat.le_antisymm (upper_square_plus_one Fintype.one_lt_card even) (field_plus_one F)

end Deldor14.Star


namespace Deldor14.Star.Cubic
open Matrix Finset

theorem identities {V : Type*} [Fintype V] [DecidableEq V] (A M J : Matrix V V ℝ)
    (d : ℝ) (aa : A^2=J+(d-1) • 1-M) (mm : M^2=1) (comm : Commute A M)
    (aj : A*J=d • J) (mj : M*J=J) (jm : J*M=J) :
    let S := A*(1+M)
    S^3-(4*(d-2)) • S = (8*d) • J ∧ S*J = (2*d) • J := by
  let S := A*(1+M)
  change S^3-(4*(d-2)) • S = (8*d) • J ∧ S*J=(2*d) • J
  have pair : (1+M : Matrix V V ℝ)^2=(2:ℝ) • (1+M) := by
    have ms : M*M=1 := by simpa [sq] using mm
    rw [sq]; simp only [add_mul,mul_add,one_mul,mul_one,ms]
    module
  have mx : (J+(d-1) • (1:Matrix V V ℝ)-M)*(1+M) = (2:ℝ) • J + (d-2) • (1+M) := by
    have mm' : M*M=1 := by simpa [sq] using mm
    simp only [sub_mul,add_mul,mul_add,one_mul,mul_one,smul_mul,jm,mm']
    module
  have commute : Commute A (1+M) := (Commute.one_right A).add_right comm
  have sqS : S^2 = (4:ℝ) • J + (2*(d-2)) • (1+M) := by
    change (A*(1+M))^2 = _
    rw [commute.mul_pow,aa,pair,Matrix.mul_smul,mx,smul_add,smul_smul,smul_smul]
    norm_num
  have sp : S*(1+M)=(2:ℝ) • S := by
    change (A*(1+M))*(1+M)=_
    rw [mul_assoc,←sq,pair,Matrix.mul_smul]
  have sj : S*J=(2*d) • J := by
    change (A*(1+M))*J=_
    rw [mul_assoc,add_mul,one_mul,mj,mul_add,aj]
    module
  refine ⟨?_,sj⟩
  rw [show S^3=S*S^2 by rw [←pow_succ'],sqS,mul_add,Matrix.mul_smul,Matrix.mul_smul,sj,sp,
    smul_smul,smul_smul]
  module
end Deldor14.Star.Cubic


namespace Deldor14.Star.SpectralCount
open Finset

/-- The trace and third moment force the degree of an even-regular
excess-one graph to be six. This argument counts the spectrum with
multiplicity, including the zero eigenvalues on the antipodal subspace. -/
theorem degree_six {V : Type*} [Fintype V] (f : V → ℝ) {d : ℕ} (large : 3≤d) (even : Even d)
    (roots : ∀ i, f i=2*d ∨ f i=0 ∨ (f i)^2=4*((d:ℝ)-2))
    (trace : ∑ i, f i=0)
    (moment : ∑ i, ((f i)^3-4*((d:ℝ)-2)*f i)=8*d*((d:ℝ)^2-d+2)) : d=6 := by
  classical
  let big := (univ.filter (fun i => f i=2*d)).card
  let s := Real.sqrt ((d:ℝ)-2)
  have dr : (3:ℝ)≤d := by exact_mod_cast large
  have s_pos : 0<s := Real.sqrt_pos.mpr (by linarith)
  have s_sq : s^2=(d:ℝ)-2 := Real.sq_sqrt (by linarith)
  have row (i) : (f i)^3-4*((d:ℝ)-2)*f i =
      (if f i=2*d then 8*d*((d:ℝ)^2-d+2) else 0) := by
    by_cases top : f i=2*d
    · rw [if_pos top,top]; ring
    · rw [if_neg top]
      rcases roots i with h|h|h
      · contradiction
      · simp [h]
      · linear_combination f i*h
  have tally : (big:ℝ)*(8*d*((d:ℝ)^2-d+2))=8*d*((d:ℝ)^2-d+2) := by
    conv_rhs => rw [← moment]
    simp_rw [row]
    simp [big,Finset.sum_ite]
  have nz : 0 < 8*d*((d:ℝ)^2-d+2) := by nlinarith [sq_nonneg ((d:ℝ)-1),mul_nonneg (by linarith : (0:ℝ)≤d) (sq_nonneg ((d:ℝ)-1))]
  have one : (big:ℝ)=1 := by
    apply (mul_right_cancel₀ nz.ne')
    simpa using tally
  let plus := (univ.filter (fun i => f i=2*s)).card
  let minus := (univ.filter (fun i => f i= -(2*s))).card
  have ds : s<(d:ℝ) := by nlinarith [sq_nonneg (s-1)]
  have sign (i) : f i = (if f i=2*d then 2*(d:ℝ) else 0) +
      (if f i=2*s then 2*s else 0) - (if f i= -(2*s) then 2*s else 0) := by
    rcases roots i with top|zero|other
    · have h1 : (2*(d:ℝ)) ≠ 2*s := by linarith
      have h2 : (2*(d:ℝ)) ≠ -(2*s) := by linarith
      simp [top,h1,h2]
    · rw [zero,if_neg (by linarith),if_neg (by linarith),if_neg (by linarith)]; ring
    · have options : f i=2*s ∨ f i= -(2*s) := by
        have product : (f i-2*s)*(f i+2*s)=0 := by nlinarith
        rcases mul_eq_zero.mp product with h|h
        · left; linarith
        · right; linarith
      rcases options with h|h
      · rw [h,if_neg (by linarith),if_pos rfl,if_neg (by linarith)]; ring
      · rw [h,if_neg (by linarith),if_neg (by linarith),if_pos rfl]; ring
  have trace' : (big:ℝ)*(2*d)+(plus:ℝ)*(2*s)-(minus:ℝ)*(2*s)=0 := by
    calc
      _ = ∑ i : V, ((if f i=2*d then 2*(d:ℝ) else 0) +
        (if f i=2*s then 2*s else 0) - (if f i= -(2*s) then 2*s else 0)) := by
          simp [big,plus,minus,Finset.sum_ite,sum_add_distrib,sum_sub_distrib]
      _ = _ := by simpa only [← sign] using trace
  rw [one] at trace'
  let z : ℤ := (minus:ℤ)-plus
  have val : (d:ℝ)=(z:ℝ)*s := by dsimp [z]; push_cast; linarith
  have sqReal : (d:ℝ)^2=((z:ℝ)^2)*((d:ℝ)-2) := by
    calc
      (d:ℝ)^2 = ((z:ℝ)*s)^2 := congrArg (fun x : ℝ => x^2) val
      _ = _ := by rw [mul_pow,s_sq]
  have eq : (d:ℤ)^2=z^2*((d:ℤ)-2) := by exact_mod_cast sqReal
  have divide : ((d:ℤ)-2)*(z^2-((d:ℤ)+2))=4 := by linear_combination -eq
  have pos : 0<z^2-((d:ℤ)+2) := by
    by_contra! no
    have := mul_nonpos_of_nonneg_of_nonpos (by omega : (0:ℤ)≤(d:ℤ)-2) no
    omega
  have ub : d≤6 := by
    have h := mul_le_mul_of_nonneg_left (show (1:ℤ)≤z^2-((d:ℤ)+2) by omega)
      (show (0:ℤ)≤(d:ℤ)-2 by omega)
    omega
  obtain ⟨k,hk⟩ := even
  have cases : d=4 ∨ d=6 := by omega
  rcases cases with rfl|h
  · norm_num at eq
    by_cases small : -2≤z ∧ z≤2
    · have x := mul_nonneg (show 0≤z+2 by omega) (show 0≤2-z by omega)
      nlinarith
    · have x := mul_nonneg (show 0≤(z-3)*(z+3) by
          rcases le_total z 0 with neg|pos
          · apply mul_nonneg_of_nonpos_of_nonpos <;> omega
          · apply mul_nonneg <;> omega) (by decide : (0:ℤ)≤1)
      nlinarith
  · exact h
end Deldor14.Star.SpectralCount


namespace Deldor14.Star.SpectralMatrix
open Matrix Finset Unitary

/-- Read a cubic trace and a fourth-order annihilating relation on a real
symmetric matrix in an orthonormal eigenbasis. -/
theorem multiplicities {V : Type*} [Fintype V] [DecidableEq V] (S : Matrix V V ℝ)
    (herm : S.IsHermitian) {d : ℕ} (large : 3≤d) (even : Even d)
    (tr : S.trace=0)
    (action : S*(S^3 - (4*((d:ℝ)-2)) • S) = (2*(d:ℝ)) • (S^3-(4*((d:ℝ)-2)) • S))
    (moment : (S^3 - (4*((d:ℝ)-2)) • S).trace=8*d*((d:ℝ)^2-d+2)) : d=6 := by
  classical
  let f := herm.eigenvalues
  let c := 4*((d:ℝ)-2)
  let e := conjStarAlgAut ℝ _ (star herm.eigenvectorUnitary)
  let T := S^3-c • S
  have diagS : e S=diagonal f := by simpa [e,f,Function.comp_def] using herm.conjStarAlgAut_star_eigenvectorUnitary
  have diagT : e T=diagonal (fun i => f i ^ 3-c*f i) := by
    dsimp only [T]
    rw [map_sub,map_pow,map_smul,diagS,diagonal_pow,← diagonal_smul,diagonal_sub]
    rfl
  have h := congrArg e action
  change e (S*T)=e ((2*(d:ℝ)) • T) at h
  rw [map_mul,map_smul,diagS,diagT,diagonal_mul_diagonal] at h
  have root (i : V) : f i=2*d ∨ f i=0 ∨ (f i)^2=4*((d:ℝ)-2) := by
    have ev := congrArg (fun B : Matrix V V ℝ => B i i) h
    simp only [diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul] at ev
    have zero : (f i-2*d)* (f i*(f i^2-c))=0 := by linear_combination ev
    rcases mul_eq_zero.mp zero with top | mid
    · exact Or.inl (sub_eq_zero.mp top)
    · exact Or.inr ((mul_eq_zero.mp mid).imp_right sub_eq_zero.mp)
  have traceConj (B : Matrix V V ℝ) : (e B).trace=B.trace := by
    dsimp only [e]
    rw [conjStarAlgAut_apply,trace_mul_cycle,coe_star_mul_self,one_mul]
  have fm : ∑ i, (f i^3-c*f i)=8*d*((d:ℝ)^2-d+2) := by
    rw [← trace_diagonal,← diagT,traceConj]
    exact moment
  apply SpectralCount.degree_six f large even root _ fm
  simpa [f] using herm.trace_eq_sum_eigenvalues.symm.trans tr
end Deldor14.Star.SpectralMatrix


namespace Deldor14.Star.ExcessOne
open Matrix SimpleGraph Finset

theorem degree_eq_six {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (red : ¬(cycleGraph 4).IsContained G)
    (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d)
    (large : 3≤d) (even : Even d) : d=6 := by
  classical
  let A := G.adjMatrix ℝ
  let M := permutation G red count reg ℝ
  let J := ones V ℝ
  let S := A*(1+M)
  have s_entry (i j : V) : S i j = A i j + A i (mate G red count reg j) := by
    change (A*(1+M)) i j = _
    rw [mul_add,mul_one,Matrix.add_apply,mul_permutation]
  have symm : S.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial,s_entry]
    have j1 := G.adj_comm j i
    have j2 := mate_commutes G red count reg j i
    simp only [A,adjMatrix_apply,j1,j2]
  have zero : S.trace=0 := by
    apply sum_eq_zero
    intro i _
    change S i i=0
    rw [s_entry]
    simp [A,adjMatrix_apply,G.irrefl (v:=i),mate_not_adj_of_even G red count reg even i]
  have aa := adj_square_decomp G red count reg ℝ
  obtain ⟨cubic,sj⟩ := Cubic.identities A M J (d:ℝ) aa (perm_sq G red count reg _)
    (commute_adj G red count reg _) (adj_ones G reg _) (perm_ones G red count reg _) (ones_perm G red count reg _)
  change S^3 - (4*((d:ℝ)-2)) • S = (8*(d:ℝ)) • J at cubic
  change S*J=(2*(d:ℝ)) • J at sj
  apply SpectralMatrix.multiplicities S symm large even zero
  · rw [cubic,Matrix.mul_smul,sj,smul_smul,smul_smul]
    congr 1
    ring
  · rw [cubic,Matrix.trace_smul]
    have jr : J.trace = (Fintype.card V : ℝ) := by simp [J,ones,Matrix.trace,Matrix.diag]
    rw [jr,count,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1≤d)]
    push_cast
    change (8*(d:ℝ)) * _ = _
    ring
end Deldor14.Star.ExcessOne


/-
# A signed obstruction in the degree-six case of the quadrilateral–star bound

The Ramsey bound is due to T. D. Parsons, *Ramsey Graphs and Block Designs, I*
(1975), https://doi.org/10.2307/1997368. Here we isolate a local parity
argument for the signed quotient on sixteen vertices.

In the link of any vertex every point has two neighbors. A triangle in the
link would give a tetrahedron, whose three quadrilaterals cannot all have odd
sign. Thus the link is a hexagon. Write its vertices in cyclic order as
0, 1, 2, 3, 4, 5. Each of the four pairs (0,1), (3,4), (0,3), (1,4) has
another common neighbor besides the center. For either opposite pair, degree
six forces the two indicated common neighbors of consecutive pairs to lie
next to its own common neighbor. The resulting nine vertices carry nine
quadrilaterals in which each edge occurs exactly twice. Summing their odd
sign equations modulo two gives the contradiction.
-/

namespace Deldor14.Star.SignedSix
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
abbrev Common (p q : V) := G.neighborFinset p ∩ G.neighborFinset q

structure SignedSquares where
  sign : V → V → Bool
  sym : ∀ x y, sign x y = sign y x
  square : ∀ x a y b, x ≠ y → a ≠ b → G.Adj x a → G.Adj a y → G.Adj y b → G.Adj b x →
    Bool.xor (sign x a) (sign a y) ≠ Bool.xor (sign x b) (sign b y)

private theorem xor_odd (a b c d : Bool) (h : a.xor b ≠ c.xor d) :
    (a.toNat + b.toNat + c.toNat + d.toNat)%2 = 1 := by
  revert h
  decide +revert

private theorem circuit (S : SignedSquares G) (p : Fin 9 → V) (inj : Function.Injective p)
    (edge : ∀ i j : Fin 9, (i.val,j.val) ∈ ([(0,1),(0,2),(0,3),(0,4),
      (1,2),(3,4),(1,5),(2,5),(3,6),(4,6),(1,7),(3,7),(2,8),(4,8),
      (5,7),(5,8),(6,7),(6,8)] : List (ℕ × ℕ)) → G.Adj (p i) (p j)) : False := by
  let w (i j : Fin 9) := (S.sign (p i) (p j)).toNat
  have sym (i j) : w i j = w j i := congrArg Bool.toNat (S.sym _ _)
  have quad (i j k l : Fin 9) (hik : i ≠ k) (hjl : j ≠ l)
      (a : G.Adj (p i) (p j)) (b : G.Adj (p j) (p k))
      (c : G.Adj (p k) (p l)) (d : G.Adj (p l) (p i)) :
      (w i j + w j k + w i l + w l k)%2 = 1 :=
    xor_odd _ _ _ _ (S.square _ _ _ _ (inj.ne hik) (inj.ne hjl) a b c d)
-- The nine quadrilaterals use each of their edges twice.
  have h0 := quad 0 1 5 2 (by decide) (by decide) (edge 0 1 (by decide)) (edge 1 5 (by decide)) (edge 2 5 (by decide)).symm (edge 0 2 (by decide)).symm
  have h1 := quad 0 3 6 4 (by decide) (by decide) (edge 0 3 (by decide)) (edge 3 6 (by decide)) (edge 4 6 (by decide)).symm (edge 0 4 (by decide)).symm
  have h2 := quad 0 1 7 3 (by decide) (by decide) (edge 0 1 (by decide)) (edge 1 7 (by decide)) (edge 3 7 (by decide)).symm (edge 0 3 (by decide)).symm
  have h3 := quad 0 2 8 4 (by decide) (by decide) (edge 0 2 (by decide)) (edge 2 8 (by decide)) (edge 4 8 (by decide)).symm (edge 0 4 (by decide)).symm
  have h4 := quad 5 7 6 8 (by decide) (by decide) (edge 5 7 (by decide)) (edge 6 7 (by decide)).symm (edge 6 8 (by decide)) (edge 5 8 (by decide)).symm
  have h5 := quad 5 2 1 7 (by decide) (by decide) (edge 2 5 (by decide)).symm (edge 1 2 (by decide)).symm (edge 1 7 (by decide)) (edge 5 7 (by decide)).symm
  have h6 := quad 5 1 2 8 (by decide) (by decide) (edge 1 5 (by decide)).symm (edge 1 2 (by decide)) (edge 2 8 (by decide)) (edge 5 8 (by decide)).symm
  have h7 := quad 6 4 3 7 (by decide) (by decide) (edge 4 6 (by decide)).symm (edge 3 4 (by decide)).symm (edge 3 7 (by decide)) (edge 6 7 (by decide)).symm
  have h8 := quad 6 3 4 8 (by decide) (by decide) (edge 3 6 (by decide)).symm (edge 3 4 (by decide)) (edge 4 8 (by decide)) (edge 6 8 (by decide)).symm
  simp only [sym 2 1, sym 4 3, sym 5 1, sym 5 2, sym 6 3, sym 6 4, sym 7 1, sym 7 3, sym 7 6, sym 8 2, sym 8 4, sym 8 6] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega

section
open Finset

variable {W : Type*} [Fintype W] [DecidableEq W] (A : W → W → Prop) [DecidableRel A]
private abbrev N (a : W) := univ.filter (A a)

private theorem pair_neighbors (deg : ∀ v, (N A v).card=2) {v a b : W} (ne : a≠b)
    (ha : A v a) (hb : A v b) : ∀ t, A v t ↔ t=a ∨ t=b := by
  have sub : ({a,b} : Finset W) ⊆ N A v := by simp only [insert_subset_iff, singleton_subset_iff, N, mem_filter, mem_univ, true_and]; exact ⟨ha,hb⟩
  have eq := Finset.eq_of_subset_of_card_le sub (by simp [deg,ne])
  intro t
  simpa [N] using (Finset.ext_iff.mp eq.symm t)

private theorem another (deg : ∀ v, (N A v).card=2) (v a : W) :
    ∃ b, A v b ∧ b ≠ a := by
  by_contra! bad
  have sub : N A v ⊆ {a} := by
    intro x hx
    exact mem_singleton.mpr (bad x (by simpa [N] using hx))
  have := card_le_card sub
  simp [deg] at this

private theorem closed_full (sz : Fintype.card W=6) (sym : ∀{a b}, A a b → A b a)
    (irr : ∀a, ¬A a a) (deg : ∀v, (N A v).card=2)
    (S : Finset W) (large : 4≤S.card) (closed : ∀u∈S, ∀v, A u v → v∈S) :
    S = univ := by
  by_contra ne
  rw [Finset.eq_univ_iff_forall] at ne
  push Not at ne
  obtain ⟨v,hv⟩ := ne
  let B := insert v (N A v)
  have hB : B.card=3 := by simp [B,N,irr, show (univ.filter (A v)).card=2 from deg v]
  have dis : Disjoint S B := by
    rw [Finset.disjoint_left]
    intro x hx h
    rcases Finset.mem_insert.mp h with rfl|edge
    · exact hv hx
    · exact hv (closed x hx v (sym (by simpa [N] using edge)))
  have bound := Finset.card_le_card (Finset.subset_univ (S ∪ B))
  rw [Finset.card_union_of_disjoint dis,Finset.card_univ,sz,hB] at bound
  omega

private theorem cannot_four (sz : Fintype.card W=6) (sym : ∀{a b}, A a b → A b a)
    (irr : ∀a, ¬A a a) (deg : ∀v, (N A v).card=2) {a b c d : W}
    (ac : a≠c) (bd : b≠d) (ab : A a b) (bc : A b c) (cd : A c d) (da : A d a) : False := by
  have nab : a ≠ b := by rintro rfl; exact irr a ab
  have nbc : b ≠ c := by rintro rfl; exact irr b bc
  have ncd : c ≠ d := by rintro rfl; exact irr c cd
  have nda : d ≠ a := by rintro rfl; exact irr d da
  let S : Finset W := {a,b,c,d}
  have hc : S.card=4 := by simp [S,ac,bd,nab,nbc,ncd,nda.symm]
  have h := closed_full A sz sym irr deg S hc.ge (by
    intro u hu v uv
    simp only [S,mem_insert,mem_singleton] at hu ⊢
    rcases hu with rfl|rfl|rfl|rfl
    · grind [pair_neighbors A deg bd ab (sym da) v]
    · grind [pair_neighbors A deg ac (sym ab) bc v]
    · grind [pair_neighbors A deg bd (sym bc) cd v]
    · grind [pair_neighbors A deg ac da (sym cd) v])
  have hh := congrArg Finset.card h
  rw [hc,card_univ,sz] at hh
  contradiction

private theorem cannot_five (sz : Fintype.card W=6) (sym : ∀{a b}, A a b → A b a)
    (irr : ∀a, ¬A a a) (deg : ∀v, (N A v).card=2)
    (tri : ∀{a b c}, A a b → A b c → A c a → False)
    {a b c d e : W} (ab : A a b) (bc : A b c) (cd : A c d) (de : A d e) (ea : A e a) : False := by
  have distinct : a≠b ∧ a≠c ∧ a≠d ∧ a≠e ∧ b≠c ∧ b≠d ∧ b≠e ∧ c≠d ∧ c≠e ∧ d≠e := by
    grind
  obtain ⟨nab,ac,ad,ae,bc',bd,be,cd',ce,de'⟩ := distinct
  let S : Finset W := {a,b,c,d,e}
  have hc : S.card=5 := by simp [S, *]
  have h := closed_full A sz sym irr deg S (by omega) (by
    intro u hu v uv
    simp only [S,mem_insert,mem_singleton] at hu ⊢
    rcases hu with rfl|rfl|rfl|rfl|rfl
    · grind [pair_neighbors A deg be ab (sym ea) v]
    · grind [pair_neighbors A deg ac (sym ab) bc v]
    · grind [pair_neighbors A deg bd (sym bc) cd v]
    · grind [pair_neighbors A deg ce (sym cd) de v]
    · grind [pair_neighbors A deg ad ea (sym de) v])
  have hh := congrArg Finset.card h
  rw [hc,card_univ,sz] at hh
  contradiction

/-- A triangle-free regular graph of degree two on six points is a hexagon. -/
theorem order_link (sz : Fintype.card W=6) (sym : ∀{a b}, A a b → A b a)
    (irr : ∀a, ¬ A a a) (deg : ∀v, (N A v).card=2)
    (tri : ∀{a b c}, A a b → A b c → A c a → False) :
    ∃ f : Fin 6 ≃ W, ∀ i j, A (f i) (f j) ↔ j=i+1 ∨ i=j+1 := by
  have non : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a⟩ := non
  obtain ⟨b,ab,_⟩ := another A deg a a
  obtain ⟨c,bc,ca⟩ := another A deg b a
  obtain ⟨d,cd,db⟩ := another A deg c b
  obtain ⟨e,de,ec⟩ := another A deg d c
  obtain ⟨f,ef,fd⟩ := another A deg e d
  have no4 := @cannot_four W _ _ A _ sz sym irr deg
  have no5 := @cannot_five W _ _ A _ sz sym irr deg tri
  have distinct : a≠b ∧ a≠c ∧ a≠d ∧ a≠e ∧ a≠f ∧ b≠c ∧ b≠d ∧ b≠e ∧ b≠f ∧
      c≠d ∧ c≠e ∧ c≠f ∧ d≠e ∧ d≠f ∧ e≠f := by
    have ad : a ≠ d := by rintro rfl; exact tri ab bc cd
    have be : b ≠ e := by rintro rfl; exact tri bc cd de
    have cf : c ≠ f := by rintro rfl; exact tri cd de ef
    have ae : a ≠ e := by rintro rfl; exact no4 ca.symm db.symm ab bc cd de
    have bf : b ≠ f := by rintro rfl; exact no4 db.symm ec.symm bc cd de ef
    have af : a ≠ f := by rintro rfl; exact no5 ab bc cd de ef
    grind
  let t : Fin 6 → W := ![a,b,c,d,e,f]
  have inj : Function.Injective t := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [t] at h; grind only)
  let E := Equiv.ofBijective t ((Fintype.bijective_iff_injective_and_card t).mpr ⟨inj,by simpa [sz]⟩)
  have fa : A f a := by
    obtain ⟨g,fg,ge⟩ := another A deg f e
    obtain ⟨i,hi⟩ := E.surjective g
    change t i = g at hi
    fin_cases i <;> simp [t] at hi <;> subst g
    · exact fg
    · exact (no5 bc cd de ef fg).elim
    · exact (no4 ec.symm fd.symm cd de ef fg).elim
    · exact (tri de ef fg).elim
    · contradiction
    · exact (irr _ fg).elim
  have cycle (i : Fin 6) : A (E i) (E (i+1)) := by
    fin_cases i <;> first | exact ab | exact bc | exact cd | exact de | exact ef | exact fa
  refine ⟨E,fun i j => ?_⟩
  have prev (i : Fin 6) : (i-1)+1 = i := by omega
  have diff (i : Fin 6) : i+1 ≠ i-1 := by decide +revert
  have back : A (E i) (E (i-1)) := by simpa only [prev] using sym (cycle (i-1))
  rw [pair_neighbors A deg (E.injective.ne (diff i)) (cycle i) back (E j)]
  simp only [Equiv.apply_eq_iff_eq]
  omega


end

section
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem small_common {p q a b : V} (hab : a ≠ b) (c : (G.neighborFinset p ∩ G.neighborFinset q).card = 2)
    (pa : G.Adj p a) (qa : G.Adj q a) (pb : G.Adj p b) (qb : G.Adj q b) :
    ∀ t, G.Adj p t ∧ G.Adj q t ↔ t=a ∨ t=b := by
  have sub : ({a,b} : Finset V) ⊆ G.neighborFinset p ∩ G.neighborFinset q := by
    simp only [insert_subset_iff, singleton_subset_iff, mem_inter, mem_neighborFinset]; exact ⟨⟨pa,qa⟩,⟨pb,qb⟩⟩
  have eq := Finset.eq_of_subset_of_card_le sub (by simp [c,hab])
  intro t
  simpa using (Finset.ext_iff.mp eq.symm t)

private theorem second_common (com : ∀ p q : V, p≠q → (G.neighborFinset p ∩ G.neighborFinset q).card=2)
    (p q o : V) (ne : p ≠ q) : ∃ x, x≠o ∧ G.Adj p x ∧ G.Adj q x := by
  by_contra! no
  have sub : G.neighborFinset p ∩ G.neighborFinset q ⊆ {o} := by
    intro t ht
    obtain ⟨pt,qt⟩ : G.Adj p t ∧ G.Adj q t := by simpa using ht
    by_contra! h
    exact no t (by simpa using h) pt qt
  have c := card_le_card sub
  simp [com p q ne] at c

/-- Four neighbors that cannot occur in the intersection force either of the
two remaining neighbors into it. -/
private theorem force_edge {p x e o l r : V} (degree : G.degree p=6)
    (co : (G.neighborFinset p ∩ G.neighborFinset x).card=2)
    (pO : G.Adj p o) (pL : G.Adj p l) (pR : G.Adj p r) (pX : G.Adj p x)
    (nO : ¬G.Adj x o) (nL : ¬G.Adj x l) (nR : ¬G.Adj x r)
    (ol : o≠l) (orr : o≠r) (ox : o≠x) (lr : l≠r) (lx : l≠x) (rx : r≠x)
    (pe : G.Adj p e) (eo : e≠o) (el : e≠l) (er : e≠r) (ex : e≠x) : G.Adj x e := by
  let C := G.neighborFinset p ∩ G.neighborFinset x
  let F : Finset V := {o,l,r,x}
  have cf : F.card=4 := by simp [F,ol,orr,ox,lr,lx,rx]
  have dis : Disjoint F C := by
    simp [F,C,nO,nL,nR]
  have inc : F ∪ C ⊆ G.neighborFinset p := by
    apply union_subset
    · simp only [F,insert_subset_iff,singleton_subset_iff,mem_neighborFinset]
      exact ⟨pO,pL,pR,pX⟩
    · exact inter_subset_left
  have eq := Finset.eq_of_subset_of_card_le inc (by
    rw [card_union_of_disjoint dis,cf,show C.card=2 from co,card_neighborFinset_eq_degree,degree])
  have he : e∈F ∪ C := eq.symm ▸ ((G.mem_neighborFinset p e).mpr pe)
  simpa [F,C,pe,eo,el,er,ex] using he


end

private theorem from_hexagon {o : V} (S : SignedSquares G)
    (reg : ∀ p, G.degree p=6) (com : ∀ p q : V, p≠q → (G.neighborFinset p ∩ G.neighborFinset q).card=2)
    (f : Fin 6 → V) (inj : Function.Injective f)
    (link : ∀ w, G.Adj o w ↔ ∃ i, f i=w)
    (cycle : ∀ i j, G.Adj (f i) (f j) ↔ j=i+1 ∨ i=j+1) : False := by
  let L : Fin 4 → Fin 6 := ![0,3,0,1]
  let R : Fin 4 → Fin 6 := ![1,4,3,4]
  have lr : ∀ k, L k ≠ R k := by decide
  choose X xo xl xr using fun k => second_common G com (f (L k)) (f (R k)) o (inj.ne (lr k))
  have localAdj (i) := (link (f i)).mpr ⟨i,rfl⟩
  have fno (i) : f i≠o := (localAdj i).ne.symm
  have noLocal : ∀ k i, ¬((i=L k+1 ∨ L k=i+1) ∧ (i=R k+1 ∨ R k=i+1)) := by decide
  have xf (k i) : X k ≠ f i := by
    intro h
    have a := xl k; have b := xr k
    rw [h,cycle] at a b
    exact noLocal k i ⟨a,b⟩
  have xOutside (k) : ¬G.Adj o (X k) := by
    intro h
    obtain ⟨i,hi⟩ := (link _).mp h
    exact xf k i hi.symm
  have adjX (k i) : G.Adj (X k) (f i) ↔ i=L k ∨ i=R k := by
    have h := small_common G (inj.ne (lr k)) (com o (X k) (xo k).symm)
      (localAdj _) (xl k).symm (localAdj _) (xr k).symm (f i)
    simpa only [localAdj,true_and,inj.eq_iff] using h
  have unique : ∀ k j, (∀ i, (i=L k ∨ i=R k) ↔ (i=L j ∨ i=R j)) → k=j := by decide
  have xi : Function.Injective X := by
    intro k j kj
    exact unique k j fun i => (adjX k i).symm.trans (kj ▸ adjX j i)
  have force (k j : Fin 4) (t l r : Fin 6) (kj : k≠j)
      (hx : t=L k ∨ t=R k) (he : t=L j ∨ t=R j) (tl : l=t+1 ∨ t=l+1)
      (tr : r=t+1 ∨ t=r+1) (lr' : l≠r) (noL : ¬(l=L k ∨ l=R k)) (noR : ¬(r=L k ∨ r=R k)) :
      G.Adj (X k) (X j) :=
    force_edge G (reg _) (com _ _ (xf k t).symm)
      (localAdj t).symm ((cycle t l).mpr tl) ((cycle t r).mpr tr) ((adjX k t).mpr hx).symm
      (fun a => xOutside k a.symm) (fun a => noL ((adjX k l).mp a))
      (fun a => noR ((adjX k r).mp a)) (fno l).symm (fno r).symm (xo k).symm (inj.ne lr')
      (xf k l).symm (xf k r).symm ((adjX j t).mpr he).symm (xo j) (xf j l) (xf j r) (xi.ne kj.symm)
  have fe1 : G.Adj (X 0) (X 2) := (force 2 0 0 1 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).symm
  have fe2 : G.Adj (X 0) (X 3) := (force 3 0 1 2 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).symm
  have fe3 : G.Adj (X 1) (X 2) := (force 2 1 3 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).symm
  have fe4 : G.Adj (X 1) (X 3) := (force 3 1 4 5 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).symm
  let emb : Unit ⊕ (Fin 6 ⊕ Fin 4) → V := Sum.elim (fun _ => o) (Sum.elim f X)
  have ei : Function.Injective emb := by
    intro i j h
    rcases i with _ | i | i <;> rcases j with _ | j | j <;> simp [emb] at h ⊢
    all_goals first | exact (fno _ h).elim | exact (fno _ h.symm).elim | exact (xo _ h).elim
                         | exact (xo _ h.symm).elim | exact (xf _ _ h).elim | exact (xf _ _ h.symm).elim
                         | exact inj h | exact xi h
  let lab : Fin 9 → Unit ⊕ (Fin 6 ⊕ Fin 4) := ![.inl (),.inr (.inl 0), .inr (.inl 1),
    .inr (.inl 3),.inr (.inl 4),.inr (.inr 0),.inr (.inr 1),.inr (.inr 2),.inr (.inr 3)]
  have li : Function.Injective lab := by decide
  apply circuit G S (emb ∘ lab) (ei.comp li)
  intro i j h
  fin_cases i <;> fin_cases j <;> first | exact False.elim (by revert h; decide)
                                        | exact localAdj _
                                        | exact ((cycle _ _).mpr (by decide))
                                        | exact ((adjX _ _).mpr (by decide)).symm
                                        | exact fe1 | exact fe2 | exact fe3 | exact fe4

private theorem no_tetra (S : SignedSquares G) {o a b c : V}
    (oa : G.Adj o a) (ob : G.Adj o b) (oc : G.Adj o c)
    (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False := by
  have h0 := xor_odd _ _ _ _ (S.square o b a c oa.ne bc.ne ob ab.symm ca.symm oc.symm)
  have h1 := xor_odd _ _ _ _ (S.square o a b c ob.ne ca.ne.symm oa ab bc oc.symm)
  have h2 := xor_odd _ _ _ _ (S.square o a c b oc.ne ab.ne oa ca.symm bc.symm ob.symm)
  rw [S.sym b a] at h0
  rw [S.sym c b] at h1
  rw [S.sym c a] at h0
  omega

/-- The signed quotient required by the putative 6-regular graph is impossible. -/
theorem quotient_six_impossible (card : Fintype.card V = 16) (reg : ∀ v, G.degree v = 6)
    (com : ∀ x y, x ≠ y → (G.neighborFinset x ∩ G.neighborFinset y).card = 2)
    (sign : V → V → Bool) (sym : ∀ x y, sign x y = sign y x)
    (square : ∀ x a y b, x ≠ y → a ≠ b → G.Adj x a → G.Adj a y → G.Adj y b → G.Adj b x →
      Bool.xor (sign x a) (sign a y) ≠ Bool.xor (sign x b) (sign b y)) : False := by
  let S : SignedSquares G := ⟨sign,sym,square⟩
  obtain ⟨o⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  let W : Type _ := ↑(G.neighborFinset o)
  let A (a b : W) : Prop := G.Adj a.val b.val
  letI : DecidableRel A := fun x y => inferInstanceAs (Decidable (G.Adj x.val y.val))
  have local_sz : Fintype.card W=6 := by
    change Fintype.card (↑(G.neighborFinset o) : Type _) = 6
    rw [Fintype.card_coe]; exact reg o
  have spoke (x : W) : G.Adj o x.val := (G.mem_neighborFinset o x.val).mp x.property
  have deg (v : W) : (univ.filter (A v)).card=2 := by
    calc (univ.filter (A v)).card = (G.neighborFinset o ∩ G.neighborFinset v.val).card := by
           apply Finset.card_bij (fun x _ => x.val)
           · intro x hx
             exact mem_inter.mpr ⟨x.property, (mem_neighborFinset G _ _).mpr (mem_filter.mp hx).2⟩
           · intro a _ b _ eq
             exact Subtype.ext eq
           · intro x hx
             obtain ⟨ox,vx⟩ := mem_inter.mp hx
             exact ⟨⟨x,ox⟩,mem_filter.mpr ⟨mem_univ _, (mem_neighborFinset G _ _).mp vx⟩,rfl⟩
         _ = 2 := com o v.val (spoke v).ne
  have tri {a b c : W} (ab : A a b) (bc : A b c) (ca : A c a) : False :=
    no_tetra G S (spoke a) (spoke b) (spoke c) ab bc ca
  obtain ⟨f,hf⟩ := order_link A local_sz (fun h => h.symm) (fun x => G.irrefl) deg tri
  refine from_hexagon (o := o) G S reg com (fun i => (f i).val) (Subtype.val_injective.comp f.injective) ?_ hf
  intro w
  constructor
  · intro hw
    let v : W := ⟨w,(mem_neighborFinset G _ _).mpr hw⟩
    obtain ⟨i,hi⟩ := f.surjective v
    exact ⟨i,congrArg Subtype.val hi⟩
  · rintro ⟨i,rfl⟩
    exact spoke (f i)

end Deldor14.Star.SignedSix


/- The antipodal quotient of a six-regular graph of order 32. -/
namespace Deldor14.Star.SignedQuotient
open SimpleGraph Finset Deldor14.Star.ExcessOne

private structure Cover {X Q : Type*} (G : SimpleGraph X) where
  lift : Q × Bool ≃ X
  flip : ∀ x y : Q, G.Adj (lift (x,true)) (lift (y,true)) ↔ G.Adj (lift (x,false)) (lift (y,false))
  cross : ∀ x y : Q, G.Adj (lift (x,false)) (lift (y,true)) ↔ G.Adj (lift (y,false)) (lift (x,true))
  separate : ∀ x : Q, ¬G.Adj (lift (x,false)) (lift (x,true))
  exclusive : ∀ (y : Q) (u : X), ¬(G.Adj u (lift (y,false)) ∧ G.Adj u (lift (y,true)))

variable {X Q : Type*} {G : SimpleGraph X}

private def project (s : Cover (Q:=Q) G) : SimpleGraph Q where
  Adj x y := G.Adj (s.lift (x,false)) (s.lift (y,false)) ∨ G.Adj (s.lift (x,false)) (s.lift (y,true))
  symm := ⟨fun {_ _} h => h.elim (fun e=>Or.inl e.symm) (fun e=>Or.inr ((s.cross ..).mp e))⟩
  loopless := ⟨fun x h=>h.elim (G.irrefl) (s.separate x)⟩

private def sign [DecidableRel G.Adj] (s : Cover (Q:=Q) G) (x y : Q) :=
  decide (G.Adj (s.lift (x,false)) (s.lift (y,true)))

private theorem sign_symm [DecidableRel G.Adj] (s : Cover (Q:=Q) G) (x y : Q) :
    sign s x y=sign s y x := by simp [sign,s.cross x y]

private theorem lift_adj [DecidableRel G.Adj] (s : Cover (Q:=Q) G) (x y : Q) (i j : Bool) :
    G.Adj (s.lift (x,i)) (s.lift (y,j)) ↔
      (project s).Adj x y ∧ (Bool.xor i j)=sign s x y := by
  have excl := s.exclusive y (s.lift (x,false))
  have cross : G.Adj (s.lift (x,true)) (s.lift (y,false)) ↔ G.Adj (s.lift (x,false)) (s.lift (y,true)) :=
    (G.adj_comm _ _).trans (s.cross y x)
  cases i <;> cases j <;> simp only [Bool.false_xor,Bool.true_xor,Bool.not_true,Bool.not_false,
    sign,project,s.flip,cross]
  all_goals by_cases h : G.Adj (s.lift (x,false)) (s.lift (y,true)) <;> simp_all

private def side (s : Cover (Q:=Q) G) [DecidableRel G.Adj] (x y : Q) := s.lift (y,sign s x y)

private theorem side_bij (s : Cover (Q:=Q) G) [Fintype X] [DecidableRel G.Adj] [Fintype Q]
    [DecidableRel (project s).Adj] (x : Q) :
    Set.BijOn (side s x) ((project s).neighborFinset x : Set Q) (G.neighborFinset (s.lift (x,false)) : Set X) := by
  refine ⟨?_,?_,?_⟩
  · intro y hy
    exact (G.mem_neighborFinset ..).mpr ((lift_adj s x y false _).mpr ⟨((project s).mem_neighborFinset ..).mp hy,by simp⟩)
  · intro a _ b _ hh
    exact congrArg Prod.fst (s.lift.injective hh)
  · intro z hz
    obtain ⟨⟨y,j⟩,rfl⟩ := s.lift.surjective z
    obtain ⟨adj,eq⟩ := (lift_adj s x y false j).mp ((G.mem_neighborFinset ..).mp hz)
    refine ⟨y,((project s).mem_neighborFinset ..).mpr adj,?_⟩
    rw [Bool.false_xor] at eq
    exact congrArg (fun b=>s.lift (y,b)) eq.symm

private theorem degree_proj (s : Cover (Q:=Q) G) [Fintype X] [DecidableRel G.Adj] [Fintype Q]
    [DecidableRel (project s).Adj] (x : Q) :
    (project s).degree x=G.degree (s.lift (x,false)) := by
  have h := side_bij s x
  simpa using card_nbij (side s x) h.mapsTo h.injOn h.surjOn

private theorem either_lift [DecidableRel G.Adj] (s : Cover (Q:=Q) G) (y z : Q) (j : Bool) :
    (project s).Adj y z ↔ G.Adj (s.lift (y,false)) (s.lift (z,j)) ∨
      G.Adj (s.lift (y,true)) (s.lift (z,j)) := by
  rw [lift_adj,lift_adj]
  cases j <;> cases h : sign s y z <;> simp

private theorem codegree_proj (s : Cover (Q:=Q) G) [Fintype X] [DecidableEq X] [DecidableRel G.Adj]
    [Fintype Q] [DecidableEq Q] [DecidableRel (project s).Adj] (x y : Q)
    (one : ∀ j,(common G (s.lift (x,false)) (s.lift (y,j))).card=1) :
    (common (project s) x y).card=2 := by
  let C (j : Bool) := common G (s.lift (x,false)) (s.lift (y,j))
  have dis : Disjoint (C false) (C true) := by
    apply Finset.disjoint_left.mpr
    intro z hz hw
    exact s.exclusive y z ⟨((mem_common G).mp hz).2.symm,((mem_common G).mp hw).2.symm⟩
  have e : (common (project s) x y).card=(C false ∪ C true).card := by
    apply Finset.card_bij' (fun z _=>side s x z) (fun u _=>(s.lift.symm u).1)
    · intro z hz
      have adj := (mem_common _).mp hz
      have a := (lift_adj s x z false (sign s x z)).mpr ⟨adj.1,by simp⟩
      exact mem_union.mpr (((either_lift s y z _).mp adj.2).imp (fun h=>(mem_common G).mpr ⟨a,h⟩) (fun h=>(mem_common G).mpr ⟨a,h⟩))
    · intro u hu
      obtain ⟨⟨z,j⟩,rfl⟩ := s.lift.surjective u
      simp only [Equiv.symm_apply_apply]
      rcases mem_union.mp hu with h|h <;> obtain ⟨a,b⟩ := (mem_common G).mp h
      · exact (mem_common _).mpr ⟨((lift_adj s x z false j).mp a).1,((lift_adj s y z false j).mp b).1⟩
      · exact (mem_common _).mpr ⟨((lift_adj s x z false j).mp a).1,((lift_adj s y z true j).mp b).1⟩
    · intro z _; simp [side]
    · intro u hu
      obtain ⟨⟨z,j⟩,rfl⟩ := s.lift.surjective u
      have a : G.Adj (s.lift (x,false)) (s.lift (z,j)) := (mem_union.mp hu).elim (fun h=>((mem_common G).mp h).1) (fun h=>((mem_common G).mp h).1)
      have eq := ((lift_adj s x z false j).mp a).2
      simpa [side] using congrArg (fun i=>s.lift (z,i)) eq.symm
  rw [e,card_union_of_disjoint dis,show (C false).card=1 from one false,show (C true).card=1 from one true]

private theorem signed_square (s : Cover (Q:=Q) G) [Fintype X] [DecidableEq X] [DecidableRel G.Adj]
    (red : ¬ (cycleGraph 4).IsContained G) (x a y b : Q) (xy : x≠y) (ab : a≠b)
    (xa : (project s).Adj x a) (ay : (project s).Adj a y) (yb : (project s).Adj y b) (bx : (project s).Adj b x) :
    (Bool.xor (sign s x a) (sign s a y)) ≠ (Bool.xor (sign s x b) (sign s b y)) := by
  intro eq
  let v := Bool.xor (sign s x a) (sign s a y)
  have f (c : Q) (xc : (project s).Adj x c) (cy : (project s).Adj c y)
      (hh : v=Bool.xor (sign s x c) (sign s c y)) : side s x c∈common G (s.lift (x,false)) (s.lift (y,v)) := by
    apply (mem_common G).mpr
    refine ⟨(lift_adj s x c false _).mpr ⟨xc,by simp⟩,((lift_adj s c y _ v).mpr ⟨cy,?_⟩).symm⟩
    rw [hh]; cases sign s x c <;> cases sign s c y <;> rfl
  have under : s.lift (x,false)≠s.lift (y,v) := fun h=>xy (congrArg Prod.fst (s.lift.injective h))
  have eq' := Finset.card_le_one.mp (codeg_le_one G red under) (side s x a) (f a xa ay rfl) (side s x b) (f b bx.symm yb.symm eq)
  exact ab (congrArg Prod.fst (s.lift.injective eq'))

private def splitSides {A : Type*} (P : A→Prop) [DecidablePred P]
    (m : A→A) (mm : Function.Involutive m) (switch : ∀ x,P (m x) ↔ ¬P x) :
    A ≃ Subtype P × Bool where
  toFun x := if h : P x then (⟨x,h⟩,false) else (⟨m x,(switch x).mpr h⟩,true)
  invFun x := if x.2 then m x.1.val else x.1.val
  left_inv x := by by_cases h : P x <;> simp [h,mm x]
  right_inv := by
    rintro ⟨⟨x,hx⟩,b⟩
    cases b
    · simp [hx]
    · simp [show ¬P (m x) from fun z=>(switch x).mp z hx,mm x]

theorem regular_six_from_quotient
    (obstruction : ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W=16 → (∀ x,H.degree x=6) →
      (∀ x y,x≠y → (H.neighborFinset x ∩ H.neighborFinset y).card=2) →
      ∀ (sig : W→W→Bool), (∀ x y,sig x y=sig y x) →
      (∀ x a y b,x≠y → a≠b → H.Adj x a → H.Adj a y → H.Adj y b → H.Adj b x →
        (Bool.xor (sig x a) (sig a y)) ≠ (Bool.xor (sig x b) (sig b y))) → False)
    (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj] (red : ¬(cycleGraph 4).IsContained G)
    (reg : ∀ v,G.degree v=6) : False := by
  classical
  have count : Fintype.card (Fin 32)=6*(6-1)+2 := by decide
  let m := mate G red count reg
  have mm : Function.Involutive m := mate_involutive G red count reg
  have fixed := mate_ne G red count reg
  let P (x : Fin 32) := x < m x
  have switch (x : Fin 32) : P (m x) ↔ ¬P x := by
    change m x < m (m x) ↔ ¬x < m x
    rw [mm]
    exact ⟨not_lt_of_gt,fun h=>lt_of_le_of_ne (le_of_not_gt h) (fixed x)⟩
  let W := Subtype P
  let L : W × Bool ≃ Fin 32 := (splitSides P m mm switch).symm
  have neg (x : W) : L (x,false)=x.val := rfl
  have pos (x : W) : L (x,true)=m x.val := rfl
  have toggle (x : W) (j : Bool) : m (L (x,j))=L (x,!j) := by
    cases j with
    | false => rfl
    | true => exact mm x.val
  let s : Cover (Q:=W) G := {
    lift := L
    flip := fun x y => mate_preserves G red count reg x.val y.val
    cross := fun x y => mate_commutes G red count reg x.val y.val
    separate := fun x=>mate_not_adj_of_even G red count reg (by decide) x.val
    exclusive := by
      intro y u hh
      have z : u∈common G y.val (m y.val) := (mem_common G).mpr ⟨hh.1.symm,hh.2.symm⟩
      have emp := ((mate_spec G red count reg y.val (m y.val)).mp rfl).2
      rw [emp] at z
      exact notMem_empty u z }
  let : Fintype W := Fintype.ofFinite W
  let : DecidableRel (project s).Adj := Classical.decRel _
  have cw : Fintype.card W=16 := by
    have c := Fintype.card_congr L
    simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at c
    omega
  have com (x y : W) (ne : x≠y) (j : Bool) : (common G (L (x,false)) (L (y,j))).card=1 := by
    have distinct (k : Bool) : L (x,false)≠L (y,k) := fun e=>ne (congrArg Prod.fst (L.injective e))
    have other : L (x,false)≠mate G red count reg (L (y,j)) := by
      change L (x,false)≠m (L (y,j))
      rw [toggle]
      exact distinct _
    have c := codegree_formula G red count reg (L (x,false)) (L (y,j))
    rw [if_neg (distinct j),if_neg other] at c
    omega
  exact obstruction (project s) cw (fun x=>(degree_proj s x).trans (reg _))
    (fun x y ne=>codegree_proj s x y (com x y ne)) (sign s) (sign_symm s) (signed_square s red)

end Deldor14.Star.SignedQuotient


namespace Deldor14.Star.SignedQuotient
open SimpleGraph

theorem six_regular_impossible (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj]
    (red : ¬(cycleGraph 4).IsContained G) (reg : ∀ x,G.degree x=6) : False :=
  regular_six_from_quotient (@Deldor14.Star.SignedSix.quotient_six_impossible) G red reg

end Deldor14.Star.SignedQuotient


namespace Deldor14.Star
open SimpleGraph OMA.ChenStar

/-- The upper bound at one more than a square, including the last exceptional order. -/
theorem parsons_upper_plus_one {q : ℕ} (hq : 2≤q) :
    number (q^2+1)≤q^2+q+2 := by
  classical
  rcases Nat.even_or_odd q with h|h
  · exact upper_square_plus_one hq h
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra bad
  have min (v) : q+1 ≤ G.degree v := by
    have lt : Gᶜ.degree v<q^2+1 :=
      lt_of_not_ge (fun ge => bad (star_isContained_of_le_degree Gᶜ ge))
    rw [degree_compl,Fintype.card_fin] at lt
    omega
  have count : Fintype.card (Fin (q^2+q+2)) = (q+1)*(q+1-1)+2 := by simp; ring
  have reg := ExcessOne.regular_of_min G red (d:=q+1) (by omega) count min
  have he : Even (q+1) := by obtain ⟨k,hk⟩ := h; exact ⟨k+1,by omega⟩
  have := ExcessOne.degree_eq_six G red count reg (by omega) he
  have five : q=5 := by omega
  subst q
  exact SignedQuotient.six_regular_impossible G red reg

/-- Parsons' square-plus-one value of the quadrilateral-star Ramsey number. -/
theorem field_plus_one_exact (F : Type*) [Fintype F] [Field F] :
    number (Fintype.card F^2+1) = Fintype.card F^2+Fintype.card F+2 :=
  Nat.le_antisymm (parsons_upper_plus_one Fintype.one_lt_card) (field_plus_one F)

end Deldor14.Star


/- X. Zhang, Y. Chen and T. C. E. Cheng, Polarity graphs and Ramsey numbers for C₄ versus stars (2017), https://doi.org/10.1016/j.disc.2016.12.005. -/
namespace Deldor14.Star.OddWindow
open Finset
theorem choose_pairs {α : Type*} [DecidableEq α] (f : α → α) (sq : Function.Involutive f)
    (U : Finset α) (stable : ∀ x∈U,f x∈U) (free : ∀ x∈U,f x≠x) :
    ∃ k, U.card=2*k ∧ ∀ i≤k,∃ T : Finset α, T⊆U ∧ T.card=2*i ∧ ∀ x∈T,f x∈T := by
  induction U using Finset.strongInduction with
  | H U ih =>
    rcases U.eq_empty_or_nonempty with eq|⟨x,hx⟩
    · subst U
      exact ⟨0,rfl,by intro i hi; have := Nat.eq_zero_of_le_zero hi; subst i; exact ⟨∅,by simp⟩⟩
    let y := f x
    have hy : y∈U := stable x hx
    have dif : y≠x := free x hx
    let V := (U.erase x).erase y
    have inside : V⊆U := (erase_subset ..).trans (erase_subset ..)
    have smaller : V ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨inside,fun he => by
      have : x∈V := he ▸ hx
      simp [V] at this⟩
    have vc : V.card + 2 = U.card := by
      have first := card_erase_add_one hx
      have second := card_erase_add_one (mem_erase.mpr ⟨dif,hy⟩ : y∈U.erase x)
      dsimp [V]
      omega
    have sv (a) (ha : a∈V) : f a∈V := by
      obtain ⟨ay,ax,au⟩ := show a≠y ∧ a≠x ∧ a∈U by simpa [V] using ha
      have ex : f a≠x := fun e => ay (by simpa [y,sq a] using congrArg f e)
      have ey : f a≠y := fun e => ax (sq.injective e)
      simp [V,ex,ey,stable a au]
    obtain ⟨k,hk,sub⟩ := ih V smaller sv (fun a ha=>free a (inside ha))
    refine ⟨k+1,by omega,?_⟩
    intro i hi
    cases i with
    | zero => exact ⟨∅,by simp⟩
    | succ i =>
      obtain ⟨T,hT,cT,sT⟩ := sub i (by omega)
      have xn : x∉T := by intro h; have := hT h; simp [V] at this
      have yn : y∉T := by intro h; have := hT h; simp [V] at this
      refine ⟨insert x (insert y T),?_,?_,?_⟩
      · exact insert_subset hx (insert_subset hy (hT.trans inside))
      · rw [card_insert_of_notMem (by simp [dif.symm,xn]),card_insert_of_notMem yn,cT]
        omega
      · intro a ha
        rcases mem_insert.mp ha with rfl|h
        · exact mem_insert_of_mem (mem_insert_self ..)
        rcases mem_insert.mp h with e|h
        · rw [e,show f y=x from sq x]; simp
        · exact mem_insert_of_mem (mem_insert_of_mem (sT _ h))
end Deldor14.Star.OddWindow

/- Count the points of the hyperbola by factoring its equation. -/
namespace Deldor14.Star.OddWindow
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private abbrev Conic (F : Type*) [Field F] := {p : F × F // p.2^2=p.1^2+1}

private def toUnit (p : Conic F) : Fˣ where
  val := p.val.2 + p.val.1
  inv := p.val.2 - p.val.1
  val_inv := by linear_combination p.property
  inv_val := by linear_combination p.property

private def ofUnit (two : (2:F)≠0) (u : Fˣ) : Conic F :=
  ⟨⟨((u:F)-(↑u⁻¹:F))/2,((u:F)+(↑u⁻¹:F))/2⟩,by
    dsimp
    field_simp
    linear_combination 4 * (Units.val_inv u)⟩

private def hyperbola (two : (2:F)≠0) : Conic F ≃ Fˣ where
  toFun := toUnit
  invFun := ofUnit two
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change ((p.val.2+p.val.1)-(p.val.2-p.val.1))/2 = p.val.1
      field_simp; ring
    · change ((p.val.2+p.val.1)+(p.val.2-p.val.1))/2 = p.val.2
      field_simp; ring
  right_inv u := by
    apply Units.ext
    change ((u:F)+↑u⁻¹)/2+((u:F)-↑u⁻¹)/2=(u:F)
    field_simp; ring

private def fibers : (Σ a : F,{y : F // y^2=a^2+1}) ≃ Conic F where
  toFun := fun ⟨a,y⟩ => ⟨(a,y.val),y.property⟩
  invFun := fun p => ⟨p.val.1,p.val.2,p.property⟩
  left_inv := by rintro ⟨a,⟨y,h⟩⟩; rfl
  right_inv := by rintro ⟨⟨a,y⟩,h⟩; rfl

private def solutions (x : F) := univ.filter fun y : F => y^2=x
private theorem sum_solutions (two : (2:F)≠0) :
    ∑ a : F,(solutions (a^2+1)).card = Fintype.card F-1 := by
  have e := Fintype.card_congr (fibers.trans (hyperbola two))
  simpa [Fintype.card_sigma,Fintype.card_subtype,solutions,Fintype.card_units] using e

def zeroSet (F : Type*) [Field F] [Fintype F] [DecidableEq F] := univ.filter (fun a : F=>a^2+1=0)
noncomputable def dark (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F := by
  classical exact univ.filter (fun a : F=>¬∃y : F,y^2=a^2+1)

private theorem sols_nonzero (two : (2:F)≠0) {x : F} (hx : x≠0) (y : F) (hy : y^2=x) :
    (solutions x).card=2 := by
  have nz : y≠0 := by intro e; simp [e] at hy; exact hx hy.symm
  have dif : y≠-y := by
    intro e
    exact (mul_ne_zero two nz) (by linear_combination e)
  have set : solutions x = {y,-y} := by
    ext z
    simp only [solutions,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
    rw [←hy]
    exact sq_eq_sq_iff_eq_or_eq_neg
  simp [set,dif]

theorem zero_count (two : (2:F)≠0) : (zeroSet F).card=0 ∨ (zeroSet F).card=2 := by
  classical
  have eq : zeroSet F=solutions (-1:F) := by
    ext a
    simp [zeroSet,solutions,eq_neg_iff_add_eq_zero]
  rw [eq]
  by_cases h : ∃y : F, y^2= -1
  · obtain ⟨y,hy⟩ := h
    exact Or.inr (sols_nonzero two (neg_ne_zero.mpr one_ne_zero) y hy)
  · left
    apply Finset.card_eq_zero.mpr
    simpa [solutions,Finset.filter_eq_empty_iff] using h

theorem dark_count (two : (2:F)≠0) :
    2*(dark F).card+(zeroSet F).card=Fintype.card F+1 := by
  classical
  have fiber (a : F) : (solutions (a^2+1)).card +
      2*(if a∈dark F then 1 else 0) + (if a∈zeroSet F then 1 else 0) = 2 := by
    by_cases z : a^2+1=0
    · have notdark : a∉dark F := by simp only [dark,mem_filter,mem_univ,true_and,not_not]; exact ⟨0,by simp [z]⟩
      have sing : (univ.filter (fun x : F=>x=0)) = {0} := by ext x; simp
      simp [solutions,z,notdark,zeroSet,sing]
    by_cases sq : ∃y:F,y^2=a^2+1
    · obtain ⟨y,hy⟩ := sq
      have n : a∉dark F := by simp only [dark,mem_filter,mem_univ,true_and,not_not]; exact ⟨y,hy⟩
      simp [sols_nonzero two z y hy,n,zeroSet,z]
    · have card : (solutions (a^2+1)).card=0 := by
        apply card_eq_zero.mpr
        simpa [solutions,Finset.filter_eq_empty_iff] using sq
      simp [card,dark,sq,zeroSet,z]
  have h := Finset.sum_congr (s₁:=univ) rfl (fun a _=> fiber a)
  simp only [sum_add_distrib,← Finset.mul_sum,Finset.sum_boole,filter_mem_eq_inter,univ_inter,
    sum_const,card_univ,smul_eq_mul,sum_solutions two,Nat.cast_id] at h
  have pos : 0<Fintype.card F := Fintype.card_pos
  omega
end Deldor14.Star.OddWindow

namespace Deldor14.Star.OddWindow
open SimpleGraph Finset
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

def center : Point F := .aff 0 (2⁻¹)
def row (a : F) : Point F := .aff a (-(2⁻¹))

def removed (S : Finset F) : Finset (Point F) := insert center (S.image row)

theorem row_inj : Function.Injective (row (F:=F)) := by
  intro a b e
  exact (Point.aff.inj e).1

theorem center_ne (two : (2:F) ≠ 0) (a : F) : center ≠ row a := by
  intro e
  have h := (Point.aff.inj e).2
  change (2:F)⁻¹ = -2⁻¹ at h
  field_simp at h
  exact two (by linear_combination h)

theorem card_removed (two : (2:F) ≠ 0) (S : Finset F) : (removed S).card = S.card+1 := by
  have ex : center ∉ S.image row := by
    rintro h
    obtain ⟨a,_,eq⟩ := mem_image.mp h
    exact center_ne two a eq.symm
  simp [removed,ex,card_image_of_injective _ row_inj]

def through (v : Point F) : Option F → Point F :=
  match v with
  | .pole => fun | none => .pole | some a => .inf a
  | .inf a => fun | none => .pole | some b => .aff a b
  | .aff a b => fun | none => .inf a | some x => .aff x (a*x-b)

theorem through_inj (v : Point F) : Function.Injective (through v) := by
  cases v <;> rintro (_|a) (_|b) h <;> simp_all [through]

theorem through_inc (v : Point F) (i : Option F) :
    Point.inc v (through v i) ∨ (v=.pole ∧ through v i=.pole) := by
  cases v <;> cases i <;> simp [through,Point.inc]

theorem inc_center_row (a : F) : Point.inc center (row a) := by simp [center,row,Point.inc]

theorem inc_pair (two : (2:F)≠0) {a : F} (ha : a≠0) :
    Point.inc (row a) (row (-a⁻¹)) := by
  simp [row,Point.inc,ha]
  field_simp
  ring

theorem blocked_neighbor (two : (2:F)≠0) (S : Finset F)
    (nozero : 0∉S) (pairs : ∀ a∈S,-a⁻¹∈S) (v : Point F) (hv : v∉removed S)
    {u w : Point F} (hu : u∈removed S) (hw : w∈removed S)
    (iu : Point.inc v u) (iw : Point.inc v w) : u=w := by
  have nc (a : F) := center_ne two a
  have diff (a : F) (ha : a∈S) : a≠0 := fun h => nozero (h ▸ ha)
  have cx (a : F) (ha : a∈S) (hx : Point.inc v center) (hy : Point.inc v (row a)) : False := by
    have e := Point.common_unique (nc a) (Point.inc_symm hx) (Point.inc_symm hy)
      (inc_center_row (-a⁻¹)) (inc_pair two (diff a ha))
    exact hv (e ▸ mem_insert_of_mem (mem_image_of_mem row (pairs a ha)))
  rcases mem_insert.mp hu with h|h <;> rcases mem_insert.mp hw with k|k
  · exact h.trans k.symm
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp k
    exact (cx a ha (h ▸ iu) iw).elim
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    exact (cx a ha (k ▸ iw) iu).elim
  · obtain ⟨a,_,rfl⟩ := mem_image.mp h
    obtain ⟨b,_,rfl⟩ := mem_image.mp k
    by_contra neq
    have e := Point.common_unique neq (Point.inc_symm iu) (Point.inc_symm iw)
      (Point.inc_symm (inc_center_row a)) (Point.inc_symm (inc_center_row b))
    exact hv (e ▸ mem_insert_self ..)

theorem absolute_safe (two : (2:F)≠0) (S : Finset F)
    (roots : ∀ a : F, a^2+1=0 → a∈S)
    (safe : ∀ a∈S, (∃ x : F, x^2=a^2+1) → a^2+1=0)
    (v : Point F) (hv : v∉removed S) (self : Point.inc v v ∨ v=.pole)
    {u : Point F} (hu : u∈removed S) (h : Point.inc v u) : False := by
  cases v with
  | pole =>
    rcases mem_insert.mp hu with e|e
    · subst u; exact h
    · obtain ⟨a,_,rfl⟩ := mem_image.mp e; exact h
  | inf x => simp [Point.inc] at self
  | aff x y =>
    have abs : y+y=x*x := by simpa [Point.inc] using self
    rcases mem_insert.mp hu with e|e
    · subst u
      change y+2⁻¹=x*0 at h
      have h2 : (2:F)*2⁻¹=1 := mul_inv_cancel₀ two
      have z : x^2+1=0 := by linear_combination -abs+2*h-h2
      apply hv
      have yy : y= -(2:F)⁻¹ := by linear_combination h
      rw [yy]
      exact mem_insert_of_mem (mem_image_of_mem row (roots x z))
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp e
      change y+ -(2:F)⁻¹=x*a at h
      have h2 : (2:F)*2⁻¹=1 := mul_inv_cancel₀ two
      have e : (x-a)^2=a^2+1 := by linear_combination -abs+2*h+h2
      have z := safe a ha ⟨_,e⟩
      have eq : x=a := sub_eq_zero.mp (sq_eq_zero_iff.mp (e.trans z))
      subst x
      have yy : y= -(2:F)⁻¹ := by linear_combination h+z+h2
      apply hv; rw [yy]
      exact mem_insert_of_mem (mem_image_of_mem row ha)

abbrev Vertex (S : Finset F) := {v : Point F // v∉removed S}

def host (S : Finset F) : SimpleGraph (Vertex S) := Point.graph.comap Subtype.val

theorem no_square (S : Finset F) : ¬(cycleGraph 4).IsContained (host S) := by
  have sub : (host S).IsContained Point.graph :=
    ⟨⟨⟨Subtype.val,fun h=>h⟩,Subtype.val_injective⟩⟩
  exact fun bad=>Point.no_square (bad.trans sub)

theorem minimum (two : (2:F)≠0) (S : Finset F)
    (nozero : 0∉S) (pairs : ∀ a∈S,-a⁻¹∈S)
    (roots : ∀ a : F, a^2+1=0 → a∈S)
    (safe : ∀ a∈S, (∃ x : F, x^2=a^2+1) → a^2+1=0)
    [DecidableRel (host S).Adj] (v : Vertex S) : Fintype.card F ≤ (host S).degree v := by
  classical
  have pole_ok : Point.pole ∉ removed S := by
    simp [removed,center,row]
  let bad (i : Option F) := through v.val i=v.val ∨ through v.val i ∈ removed S
  have abs (i) (e : through v.val i=v.val) : Point.inc v.val v.val ∨ v.val=.pole := by
    rcases through_inc v.val i with h|⟨h,_⟩
    · exact Or.inl (by simpa only [e] using h)
    · exact Or.inr h
  have hits (i) (h : through v.val i ∈ removed S) : Point.inc v.val (through v.val i) := by
    rcases through_inc v.val i with out|⟨_,e⟩
    · exact out
    · exact (pole_ok (e ▸ h)).elim
  have small : (univ.filter bad).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    apply through_inj v.val
    rcases (mem_filter.mp hi).2 with a|a <;> rcases (mem_filter.mp hj).2 with b|b
    · exact a.trans b.symm
    · exact (absolute_safe two S roots safe v.val v.property (abs i a) b (hits j b)).elim
    · exact (absolute_safe two S roots safe v.val v.property (abs j b) a (hits i a)).elim
    · exact blocked_neighbor two S nozero pairs v.val v.property a b (hits i a) (hits j b)
  let A := univ.filter (fun i => ¬bad i)
  have many : Fintype.card F ≤ A.card := by
    have h := card_filter_add_card_filter_not (s:=univ) bad
    rw [card_univ,Fintype.card_option] at h
    change _ ≤ (univ.filter (fun i=>¬bad i)).card
    omega
  have clean (i : A) : through v.val i.val ≠ v.val ∧ through v.val i.val ∉ removed S :=
    not_or.mp (mem_filter.mp i.property).2
  let target (i : A) : Vertex S := ⟨through v.val i.val,(clean i).2⟩
  have adj (i : A) : (host S).Adj v (target i) := by
    refine ⟨(clean i).1.symm,?_⟩
    rcases through_inc v.val i.val with h|⟨e,f⟩
    · exact h
    · exact ((clean i).1 (f.trans e.symm)).elim
  let f (i : A) : ↥((host S).neighborFinset v) := ⟨target i,(mem_neighborFinset ..).mpr (adj i)⟩
  have inj : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    exact through_inj v.val (congrArg (fun x : ↥((host S).neighborFinset v) => x.val.val) h)
  simpa only [Fintype.card_coe,card_neighborFinset_eq_degree] using
    (many.trans (by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inj) :
        Fintype.card F ≤ ((host S).neighborFinset v).card)

theorem cardinality (two : (2:F)≠0) (S : Finset F) :
    Fintype.card (Vertex S) + S.card = (Fintype.card F)^2 + Fintype.card F := by
  classical
  have h := Finset.card_le_univ (removed S)
  rw [card_removed two,Point.card_points] at h
  change Fintype.card {v : Point F // v∉removed S} + _ = _
  rw [Fintype.card_subtype_compl, Fintype.card_coe, card_removed two, Point.card_points]
  omega

end Deldor14.Star.OddWindow

/- Even steps of the quadratic-star Ramsey interval in odd characteristic.
Parsons (1976); Zhang, Chen and Cheng (2017), DOI 10.1016/j.disc.2016.12.005. -/
namespace Deldor14.Star.OddWindow
open Finset SimpleGraph
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem dark_iff (a : F) : a∈dark F ↔ ¬∃x : F,x^2=a^2+1 := by
  classical
  simp [dark]
theorem zero_iff (a : F) : a∈zeroSet F ↔ a^2+1=0 := by simp [zeroSet]
theorem nz_dark {a : F} (ha : a∈dark F) : a≠0 := by
  rintro rfl
  exact (dark_iff _).mp ha ⟨1,by simp⟩
theorem flip_eq {a : F} (h : a^2+1=0) : -a⁻¹=a := by
  have nz : a≠0 := by rintro rfl; simp at h
  field_simp
  linear_combination -h
private theorem flip_dark (a : F) (ha : a∈dark F) : -a⁻¹∈dark F := by
  apply (dark_iff _).mpr
  rintro ⟨x,hx⟩
  apply (dark_iff _).mp ha
  refine ⟨x*a,?_⟩
  have nz := nz_dark ha
  field_simp at hx
  linear_combination hx

theorem choose_rows (two : (2:F)≠0) {t : ℕ} (ht : Even t) (pos : 2 ≤ t)
    (le : t≤2*((Fintype.card F+3)/4)) :
    ∃ S : Finset F, S.card=t ∧ 0∉S ∧ (∀ a∈S,-a⁻¹∈S) ∧
      (∀ a : F,a^2+1=0 → a∈S) ∧ (∀ a∈S,(∃ x : F,x^2=a^2+1) → a^2+1=0) := by
  classical
  let f (a : F) := -a⁻¹
  have sq : Function.Involutive f := by intro a; simp [f]
  have free (a : F) (ha : a∈dark F) : f a≠a := by
    intro e
    have nz := nz_dark ha
    change -a⁻¹=a at e
    field_simp at e
    exact (dark_iff _).mp ha ⟨0,by linear_combination e⟩
  obtain ⟨k,hk,sub⟩ := choose_pairs f sq (dark F) flip_dark free
  obtain ⟨u,hu⟩ := ht
  have ze := zero_count two
  have dc := dark_count two
  have size : (zeroSet F).card ≤ t ∧ t≤2*k+(zeroSet F).card := by omega
  obtain ⟨T,hT,cT,sT⟩ := sub ((t-(zeroSet F).card)/2) (by omega)
  have dis : Disjoint (zeroSet F) T := by
    apply Finset.disjoint_left.mpr
    intro a hz h
    exact (dark_iff _).mp (hT h) ⟨0,by simp [(zero_iff _).mp hz]⟩
  refine ⟨zeroSet F ∪ T,?_,?_,?_,?_,?_⟩
  · rw [card_union_of_disjoint dis,cT]; omega
  · intro h
    rcases mem_union.mp h with z|h
    · simpa using (zero_iff _).mp z
    · exact nz_dark (hT h) rfl
  · intro a ha
    rcases mem_union.mp ha with z|t'
    · rw [flip_eq ((zero_iff _).mp z)]
      exact mem_union_left _ z
    · exact mem_union_right _ (sT a t')
  · intro a z; exact mem_union_left _ ((zero_iff _).mpr z)
  · intro a ha ex
    rcases mem_union.mp ha with z|t'
    · exact (zero_iff _).mp z
    · exact ((dark_iff _).mp (hT t') ex).elim

theorem field_even_step (two : (2:F)≠0) {t n : ℕ} (ht : Even t) (pos : 2 ≤ t)
    (le : t≤2*((Fintype.card F+3)/4)) (hn : n+t=Fintype.card F^2) :
    number n = n + Fintype.card F + 1 := by
  classical
  obtain ⟨S,sc,nz,fl,roots,safe⟩ := choose_rows two ht pos le
  let q := Fintype.card F
  have qtwo : 2≤q := Fintype.one_lt_card
  have count := cardinality two S
  rw [sc] at count
  have card : Fintype.card (Vertex S)=n+q := by dsimp [q]; omega
  let G := host S
  have red := no_square S
  have npos : 0<n := by
    have p2 : q≤q^2 := Nat.le_self_pow (by decide : 2≠0) q
    change t≤2*((q+3)/4) at le
    change n+t=q^2 at hn
    by_contra! e
    have qsq : q+1 ≤ q^2 := by nlinarith [show 0≤(q-2)^2 by positivity]
    omega
  have blue : ∀ v,Gᶜ.degree v < n := by
    intro v
    have low := minimum two S nz fl roots safe v
    rw [degree_compl,card]
    change q≤G.degree v at low
    omega
  have lower := lower_from_host G red blue
  rw [card] at lower
  exact Nat.le_antisymm (parsons_upper qtwo (by omega)) lower

theorem prime_power_even_step {p m t n : ℕ} (hp : p.Prime) (odd : p≠2) (hm : m≠0)
    (ht : Even t) (pos : 2≤t) (le : t≤2*((p^m+3)/4)) (hn : n+t=(p^m)^2) :
    number n=n+p^m+1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p m
  letI : Fintype F := Fintype.ofFinite _
  classical
  have two : (2:F)≠0 := by
    intro h
    have d : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp (by simpa using h)
    exact odd (Nat.le_antisymm (Nat.le_of_dvd (by decide) d) hp.two_le)
  have hq : Fintype.card F=p^m := by rw [← Nat.card_eq_fintype_card,GaloisField.card p m hm]
  simpa only [hq] using field_even_step two ht pos (by simpa only [hq] using le)
    (n:=n) (by simpa only [hq] using hn)
end Deldor14.Star.OddWindow

/- Add one edge and delete the matching between its two old neighbourhoods. -/
namespace Deldor14.Star.OddWindow
open SimpleGraph Finset
variable {V : Type*}

def special (a b v w : V) := v=a ∧ w=b ∨ v=b ∧ w=a
def cross (G : SimpleGraph V) (a b v w : V) := G.Adj a v ∧ G.Adj b w ∨ G.Adj b v ∧ G.Adj a w

def switch (G : SimpleGraph V) (a b : V) (ab : a≠b) : SimpleGraph V where
  Adj v w := special a b v w ∨ G.Adj v w ∧ ¬cross G a b v w
  symm := ⟨by intro x y; simp only [special,cross]; grind [SimpleGraph.adj_symm]⟩
  loopless := ⟨by intro v; simp [special]; grind⟩

theorem switch_nosquare (G : SimpleGraph V) (a b : V) (ab : a≠b)
    (uniq : ∀ {x y u w},x≠y → G.Adj x u → G.Adj y u → G.Adj x w → G.Adj y w → u=w) :
    ¬(cycleGraph 4).IsContained (switch G a b ab) := by
  rintro ⟨f⟩
  let H := switch G a b ab
  have impossible {v w x y : V} (vx : v≠x) (wy : w≠y) (vw : v≠w) (xy : x≠y)
      (wx : w≠x) (yv : y≠v) (s : special a b v w)
      (h1 : H.Adj w x) (h2 : H.Adj x y) (h3 : H.Adj y v) : False := by
    change special a b _ _ ∨ _ ∧ ¬cross G a b _ _ at h1 h2 h3
    have pw := h1.resolve_left (by unfold special at *; grind)
    have px := h2.resolve_left (by unfold special at *; grind)
    have py := h3.resolve_left (by unfold special at *; grind)
    rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact px.2 (Or.inr ⟨pw.1,py.1.symm⟩)
    · exact px.2 (Or.inl ⟨pw.1,py.1.symm⟩)
  have go {v w x y : V} (distinct : [v,w,x,y].Nodup)
      (h0 : H.Adj v w) (h1 : H.Adj w x) (h2 : H.Adj x y) (h3 : H.Adj y v) : False := by
    simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true,not_or] at distinct
    by_cases s0 : special a b v w
    · exact impossible (by grind) (by grind) (by grind) (by grind) (by grind) (by grind) s0 h1 h2 h3
    by_cases s1 : special a b w x
    · exact impossible (by grind) (by grind) (by grind) (by grind) (by grind) (by grind) s1 h2 h3 h0
    by_cases s2 : special a b x y
    · exact impossible (by grind) (by grind) (by grind) (by grind) (by grind) (by grind) s2 h3 h0 h1
    by_cases s3 : special a b y v
    · exact impossible (by grind) (by grind) (by grind) (by grind) (by grind) (by grind) s3 h0 h1 h2
    change special a b _ _ ∨ _ ∧ _ at h0 h1 h2 h3
    exact (by grind : w≠y) (uniq (by grind : v≠x) (h0.resolve_left s0).1
      (h1.resolve_left s1).1.symm (h3.resolve_left s3).1.symm (h2.resolve_left s2).1)
  apply go (v:=f 0) (w:=f 1) (x:=f 2) (y:=f 3)
  · exact List.Nodup.map f.injective (by decide : ([0,1,2,3] : List (Fin 4)).Nodup)
  all_goals apply f.toHom.map_adj; decide

theorem switch_old [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (ab : a≠b) [DecidableRel (switch G a b ab).Adj] (v : V)
    (uncut : ∀ w,G.Adj v w → ¬cross G a b v w) :
    G.degree v≤(switch G a b ab).degree v := by
  apply card_le_card
  intro w hw
  have e := (mem_neighborFinset ..).mp hw
  exact (mem_neighborFinset ..).mpr (Or.inr ⟨e,uncut w e⟩)

theorem switch_loss [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (ab : a≠b) [DecidableRel (switch G a b ab).Adj]
    (separate : ∀ v,G.Adj a v → ¬G.Adj b v)
    (uniq : ∀ {x y u w},x≠y → G.Adj x u → G.Adj y u → G.Adj x w → G.Adj y w → u=w)
    (nedge : ¬G.Adj a b) (v : V) : G.degree v≤(switch G a b ab).degree v+1 := by
  classical
  let A := G.neighborFinset v
  let B := (switch G a b ab).neighborFinset v
  have lost (w : V) (hw : w∈A \ B) : G.Adj v w ∧ cross G a b v w := by
    obtain ⟨e,ne⟩ := mem_sdiff.mp hw
    have ed := (mem_neighborFinset ..).mp e
    exact ⟨ed,by by_contra h; exact ne ((mem_neighborFinset ..).mpr (Or.inr ⟨ed,h⟩))⟩
  have small : (A \ B).card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨vx,dx⟩ := lost x hx
    obtain ⟨vy,dy⟩ := lost y hy
    rcases dx with ⟨av,bx⟩|⟨bv,ax⟩ <;> rcases dy with ⟨_,by'⟩|⟨_,ay⟩
    · exact uniq (x:=v) (y:=b) (fun e=>nedge (by simpa only [e] using av)) vx bx vy by'
    · exact (separate _ av ‹G.Adj b v›).elim
    · exact (separate _ ‹G.Adj a v› bv).elim
    · exact uniq (x:=v) (y:=a) (fun e=>nedge (by simpa only [e] using bv.symm)) vx ax vy ay
  have bound := card_le_card_sdiff_add_card (s:=A) (t:=B)
  change A.card≤B.card+1
  omega
theorem switch_gain [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (ab : a≠b) [DecidableRel (switch G a b ab).Adj] (noab : ¬G.Adj a b) :
    G.degree a+1≤(switch G a b ab).degree a := by
  have lower : insert b (G.neighborFinset a) ⊆ (switch G a b ab).neighborFinset a := by
    intro w hw
    apply (mem_neighborFinset ..).mpr
    rcases mem_insert.mp hw with rfl|h
    · exact Or.inl (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inr ⟨(mem_neighborFinset ..).mp h, by
        unfold cross; simp [show ¬G.Adj b a from fun e=>noab e.symm]⟩
  simpa [card_insert_of_notMem,mem_neighborFinset,noab] using card_le_card lower

end Deldor14.Star.OddWindow

/- Neighbours near the polar line retained in the odd-step construction. -/
namespace Deldor14.Star.OddWindow
open SimpleGraph Finset
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

theorem row_neighbor (two : (2:F)≠0) {a b : F} (az : a≠0)
    (h : Point.inc (row a) (row b)) : b= -a⁻¹ := by
  change -2⁻¹+ -2⁻¹=a*b at h
  field_simp
  have h2 : (2:F)*2⁻¹=1 := mul_inv_cancel₀ two
  linear_combination -h-h2

theorem absolute_row (two : (2:F)≠0) {a : F}
    (safe : (∃x:F,x^2=a^2+1) → a^2+1=0) (v : Point F)
    (absv : Point.inc v v ∨ v=.pole) (near : Point.inc v (row a)) : v=row a := by
  cases v with
  | pole => exact False.elim near
  | inf t => simp [Point.inc] at absv
  | aff x y =>
    have abs : y+y=x*x := by simpa [Point.inc] using absv
    change y+ -(2:F)⁻¹=x*a at near
    have h2 : (2:F)*2⁻¹=1 := mul_inv_cancel₀ two
    have e : (x-a)^2=a^2+1 := by linear_combination -abs+2*near+h2
    have z := safe ⟨_,e⟩
    have eq : x=a := sub_eq_zero.mp (sq_eq_zero_iff.mp (e.trans z))
    subst x
    have yy : y= -(2:F)⁻¹ := by linear_combination near+z+h2
    rw [yy]; rfl

theorem retained_row (two : (2:F)≠0) {S : Finset F} {a : F} (ha : a∉S) :
    row a∉removed S := by
  intro h
  rcases mem_insert.mp h with e|e
  · exact center_ne two a e.symm
  · obtain ⟨b,hb,eq⟩ := mem_image.mp e
    exact ha (row_inj eq ▸ hb)

theorem through_degree (S : Finset F) [DecidableRel (host S).Adj] (v : Vertex S)
    (A : Finset (Option F)) (good : ∀ i∈A, through v.val i≠v.val ∧ through v.val i∉removed S) :
    A.card≤(host S).degree v := by
  let vertex (i : A) : Vertex S := ⟨through v.val i.val,(good i i.property).2⟩
  have adj (i : A) : (host S).Adj v (vertex i) := by
    refine ⟨(good i i.property).1.symm,?_⟩
    rcases through_inc v.val i.val with h|⟨e,f⟩
    · exact h
    · exact ((good i i.property).1 (f.trans e.symm)).elim
  let f (i : A) : ↥((host S).neighborFinset v) := ⟨vertex i,(mem_neighborFinset ..).mpr (adj i)⟩
  have inj : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    exact through_inj v.val (congrArg (fun x : ↥((host S).neighborFinset v) => x.val.val) h)
  simpa only [Fintype.card_coe,card_neighborFinset_eq_degree] using Fintype.card_le_of_injective f inj

theorem new_degree (two : (2:F)≠0) (S : Finset F) [DecidableRel (host S).Adj]
    (a : F) (az : a≠0) (ha : row a∉removed S) :
    Fintype.card F ≤ (host S).degree ⟨row a,ha⟩+1 := by
  classical
  let A : Finset (Option F) := (univ.erase (some 0)).erase (some (-a⁻¹))
  have good (i) (hi : i∈A) : through (row a) i≠row a ∧ through (row a) i∉removed S := by
    have no := mem_erase.mp hi
    have ne0 := (mem_erase.mp no.2).1
    cases i with
    | none => simp [through,row,removed,center]
    | some x =>
      have dif : x≠ -a⁻¹ := by simpa using no.1
      have nz : x≠0 := by simpa using ne0
      have eq : ∀ b:F, through (row a) (some x) ≠ row b := by
        intro b e
        have i := through_inc (row a) (some x)
        have ii : Point.inc (row a) (row b) := by
          rw [e] at i
          exact i.resolve_right (by simp [row])
        have xeq : x=b := (Point.aff.inj e).1
        exact dif (xeq.trans (row_neighbor two az ii))
      refine ⟨eq _,?_⟩
      intro e
      rcases mem_insert.mp e with cen|im
      · exact nz (Point.aff.inj cen).1
      · obtain ⟨b,_,ex⟩ := mem_image.mp im
        exact eq b ex.symm
  have deg := through_degree S (⟨row a,ha⟩) A good
  have card : A.card+2=Fintype.card F+1 := by
    have eq1 := card_erase_add_one (mem_univ (some (0:F)))
    have e : some (-a⁻¹)∈(univ.erase (some (0:F))) := by simp [az]
    have eq2 := card_erase_add_one e
    rw [card_univ,Fintype.card_option] at eq1
    dsimp [A]
    omega
  omega

theorem surplus (two : (2:F)≠0) (S : Finset F) [DecidableRel (host S).Adj]
    {a b : F} (safe : (∃x:F,x^2=a^2+1) → a^2+1=0) (ha : row a∉removed S)
    (nedge : ¬Point.graph.Adj (row a) (row b)) (v w : Vertex S)
    (va : Point.graph.Adj (row a) v.val) (wb : Point.graph.Adj (row b) w.val)
    (vw : Point.graph.Adj v.val w.val) : Fintype.card F+1≤(host S).degree v := by
  classical
  have vnc : v.val ≠center := fun e => v.property (e ▸ mem_insert_self ..)
  have wnc : w.val ≠center := fun e => w.property (e ▸ mem_insert_self ..)
  have vnb : v.val≠row b := fun e => nedge (by simpa only [e] using va)
  have noC : ¬Point.inc v.val center := by
    intro e
    exact wnc (Point.common_unique vnb vw.2 wb.2 e (Point.inc_symm (inc_center_row b)))
  have clean (p : Point F) (h : Point.inc v.val p) : p∉removed S := by
    intro hp
    rcases mem_insert.mp hp with rfl|im
    · exact noC h
    · obtain ⟨c,hc,rfl⟩ := mem_image.mp im
      have d : row a≠row c := by intro z; exact ha (z ▸ mem_insert_of_mem (mem_image_of_mem row hc))
      exact vnc (Point.common_unique d va.2 (Point.inc_symm h)
        (Point.inc_symm (inc_center_row a)) (Point.inc_symm (inc_center_row c)))
  have good (i : Option F) (hi : i∈univ) :
      through v.val i≠v.val ∧ through v.val i∉removed S := by
    rcases through_inc v.val i with h|⟨vp,_⟩
    · refine ⟨fun e=>?_,clean _ h⟩
      have abs : Point.inc v.val v.val := by simpa only [e] using h
      exact va.1 (absolute_row two safe _ (Or.inl abs) (Point.inc_symm va.2)).symm
    · exact (va.1 (absolute_row two safe _ (Or.inr vp) (Point.inc_symm va.2)).symm).elim
  simpa only [card_univ,Fintype.card_option] using through_degree S v univ good

theorem min_old (S T : Finset F) (sub : S⊆T)
    [DecidableRel (host S).Adj] [DecidableRel (host T).Adj]
    {v : Vertex S} (old : v.val∉removed T) :
    (host T).degree ⟨v.val,old⟩ ≤ (host S).degree v := by
  let v' : Vertex T := ⟨v.val,old⟩
  have incl : removed S⊆removed T := insert_subset_insert _ (image_subset_image sub)
  let inc (x : Vertex T) : Vertex S := ⟨x.val,fun e=>x.property (incl e)⟩
  let f (x : (host T).neighborSet v') : (host S).neighborSet v := ⟨inc x.val,x.property⟩
  have inj : Function.Injective f := fun _ _ e=>Subtype.ext (Subtype.ext (congrArg (fun x : (host S).neighborSet v=>x.val.val) e))
  simpa only [card_neighborSet_eq_degree] using Fintype.card_le_of_injective f inj
end Deldor14.Star.OddWindow

/- Complete odd-order interval of Zhang, Chen, and Cheng (2017). The odd steps
use a single edge switch between two surviving points of the polar line. -/
namespace Deldor14.Star.OddWindow
open Finset SimpleGraph
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem extra_dark (two : (2:F)≠0) (T : Finset F) (roots : ∀a:F,a^2+1=0 → a∈T)
    (small : T.card < 2*((Fintype.card F+3)/4)) :
    ∃ b∈dark F,b∉T := by
  classical
  by_contra! h
  have sub : dark F ∪ zeroSet F ⊆ T := by
    intro v hv
    exact (mem_union.mp hv).elim (h v) (fun e =>roots v ((zero_iff v).mp e))
  have d : Disjoint (dark F) (zeroSet F) := by
    apply Finset.disjoint_left.mpr
    intro a ha hz
    exact (dark_iff _).mp ha ⟨0,by simp [(zero_iff _).mp hz]⟩
  have bound := card_le_card sub
  rw [card_union_of_disjoint d] at bound
  have z := zero_count two
  have count := dark_count two
  have flip_stable (a : F) (ha : a∈dark F) : -a⁻¹∈dark F := by
    apply (dark_iff _).mpr
    rintro ⟨x,hx⟩
    apply (dark_iff _).mp ha
    have nz := nz_dark ha
    field_simp at hx
    exact ⟨x*a,by linear_combination hx⟩
  have flip_free (a : F) (ha : a∈dark F) : -a⁻¹≠a := by
    intro e
    have nz := nz_dark ha
    field_simp at e
    exact (dark_iff _).mp ha ⟨0,by linear_combination e⟩
  obtain ⟨k,dup,_⟩ := choose_pairs (fun a:F=> -a⁻¹) (by intro a; simp) (dark F) flip_stable flip_free
  omega

private theorem odd_host (two : (2:F)≠0) {t : ℕ} (ht : Odd t)
    (room : t+1 < 2*((Fintype.card F+3)/4)) :
    ∃ (S : Finset F) (H : SimpleGraph (Vertex S)) (_ : DecidableRel H.Adj),
      S.card=t ∧ ¬(cycleGraph 4).IsContained H ∧ ∀v,Fintype.card F≤H.degree v := by
  classical
  obtain ⟨k,hk⟩ := ht
  have pe : Even (t+1) := ⟨k+1,by omega⟩
  obtain ⟨T,tc,nz,pairs,roots,safe⟩ := choose_rows two pe (by omega) room.le
  obtain ⟨b,bd,bT⟩ := extra_dark two T roots (by omega)
  obtain ⟨a,aT⟩ := card_pos.mp (show 0<T.card by omega)
  let S := T.erase a
  have sc : S.card=t := by have h := card_erase_add_one aT; dsimp [S]; omega
  have a0 : a≠0 := fun e=>nz (e ▸ aT)
  have aS : a∉S := by simp [S]
  have bS : b∉S := fun e=>bT (mem_of_mem_erase e)
  let A : Vertex S := ⟨row a,retained_row two aS⟩
  let B : Vertex S := ⟨row b,retained_row two bS⟩
  have diff : A≠B := fun e => bT (row_inj (congrArg Subtype.val e) ▸ aT)
  have nepoint : ¬Point.graph.Adj (row a) (row b) := by
    intro e
    exact bT ((row_neighbor two a0 e.2) ▸ pairs a aT)
  let G := host S
  have nedge : ¬G.Adj A B := nepoint
  have uniq {v w x y : Vertex S} (vw : v≠w) (vx : G.Adj v x) (wx : G.Adj w x)
      (vy : G.Adj v y) (wy : G.Adj w y) : x=y := by
    apply Subtype.ext
    exact Point.common_unique (fun e=>vw (Subtype.ext e)) vx.2 wx.2 vy.2 wy.2
  have sep (v : Vertex S) (av : G.Adj A v) (bv : G.Adj B v) : False := by
    have e := Point.common_unique (show row a≠row b from fun e=>diff (Subtype.ext e))
      av.2 bv.2 (Point.inc_symm (inc_center_row a)) (Point.inc_symm (inc_center_row b))
    exact v.property (e ▸ mem_insert_self ..)
  let H := switch G A B diff
  refine ⟨S,H,inferInstance,sc,switch_nosquare G A B diff (fun e=>uniq e),?_⟩
  intro v
  by_cases va : v=A
  · subst v
    have d := new_degree two S a a0 A.property
    have g := switch_gain G A B diff nedge
    exact d.trans g
  have old : v.val∉removed T := by
    intro h
    rcases mem_insert.mp h with e|im
    · exact v.property (e ▸ mem_insert_self ..)
    · obtain ⟨c,hc,e⟩ := mem_image.mp im
      by_cases eq : c=a
      · exact va (Subtype.ext (by simpa only [eq] using e.symm))
      · exact v.property (e ▸ mem_insert_of_mem (mem_image_of_mem row (mem_erase.mpr ⟨eq,hc⟩)))
  by_cases unc : ∀ w,G.Adj v w → ¬cross G A B v w
  · have d0 := minimum two T nz pairs roots safe (⟨v.val,old⟩)
    exact (d0.trans (min_old S T (erase_subset ..) old)).trans (switch_old G A B diff v unc)
  push Not at unc
  obtain ⟨w,vw,cut⟩ := unc
  have plus : Fintype.card F+1 ≤ G.degree v := by
    rcases cut with ⟨av,bw⟩|⟨bv,aw⟩
    · exact surplus two S (safe a aT) A.property nepoint v w av bw vw
    · exact surplus two S (fun ex=>((dark_iff _).mp bd ex).elim) B.property
        (fun h=>nepoint h.symm) v w bv aw vw
  have enough := switch_loss G A B diff sep (fun e=>uniq e) nedge v
  change Fintype.card F≤(switch G A B diff).degree v
  omega

theorem field_odd_step (two : (2:F)≠0) {t n : ℕ} (ht : Odd t)
    (room : t+1<2*((Fintype.card F+3)/4)) (hn : n+t=Fintype.card F^2) :
    number n=n+Fintype.card F+1 := by
  classical
  obtain ⟨S,H,inst,sc,red,min⟩ := odd_host two ht room
  have count := cardinality two S
  rw [sc] at count
  have qtwo := Fintype.one_lt_card (α:=F)
  have card : Fintype.card (Vertex S)=n+Fintype.card F := by omega
  have npos : 0<n := by
    have qsq : Fintype.card F+1 ≤ Fintype.card F^2 := by nlinarith only [qtwo]
    omega
  have blue : ∀ v,Hᶜ.degree v<n := by
    intro v
    have d := min v
    rw [degree_compl,card]; omega
  have low := lower_from_host H red blue
  rw [card] at low
  exact Nat.le_antisymm (parsons_upper qtwo (by omega)) low

theorem prime_power_interval {p m t n : ℕ} (hp : p.Prime) (op : p≠2) (hm : m≠0)
    (pos : 1≤t) (le : t≤2*((p^m+3)/4)) (except : t+1≠2*((p^m+3)/4)) (hn : n+t=(p^m)^2) :
    number n=n+p^m+1 := by
  rcases Nat.even_or_odd t with he|ho
  · have ⟨v,hv⟩ := he
    exact prime_power_even_step hp op hm he (by omega) le hn
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p m
  letI : Fintype F := Fintype.ofFinite _
  classical
  have two : (2:F)≠0 := by
    intro e
    have div := (CharP.cast_eq_zero_iff F p 2).mp (by simpa using e)
    exact op (Nat.le_antisymm (Nat.le_of_dvd (by decide) div) hp.two_le)
  have hq : Fintype.card F=p^m := by rw [← Nat.card_eq_fintype_card,GaloisField.card p m hm]
  have room : t+1<2*((p^m+3)/4) := by obtain ⟨k,hk⟩ := ho; omega
  simpa only [hq] using field_odd_step two ho (by simpa only [hq] using room)
    (n:=n) (by simpa only [hq] using hn)
end Deldor14.Star.OddWindow

/- The following formalizes Zach Waddle’s 2026 preprint calculation for 39 leaves. Original mathematical argument and graph data: https://github.com/zach7036/c4-star-ramsey/tree/86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33 . The original written proof is available under CC BY 4.0; the witness data and code under the MIT license, Copyright 2026 Zach Waddle. The verification and Bernstein certificates in Lean were written for Left to Solve. -/
/- The adjacent even steps at q(q−1), from Zhang, Chen, and Cheng,
Some values of Ramsey numbers for C₄ versus stars, Finite Fields Appl. 45 (2017).
Deleting the line at infinity leaves at most one fewer neighbour per point. -/
namespace Deldor14.Star.OddWindow
open Finset SimpleGraph OMA.ChenStar
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Affine (S : Finset F) := {p:F×F // Point.aff p.1 p.2∉removed S}
def embed (S : Finset F) (v : Affine S) : Vertex S := ⟨Point.aff v.val.1 v.val.2,v.property⟩
def affineGraph (S : Finset F) := (host S).comap (embed S)
private theorem injective_embed (S : Finset F) : Function.Injective (embed S) := by
  rintro ⟨⟨a,b⟩,h⟩ ⟨⟨c,d⟩,k⟩ e
  obtain ⟨rfl,rfl⟩ := Point.aff.inj (congrArg Subtype.val e)
  rfl
private theorem erase_line (S : Finset F) : Fintype.card (Vertex S)=Fintype.card (Affine S)+Fintype.card F+1 := by
  classical
  have ip (a : F) : Point.inf a∉removed S := by simp [removed,center,row]
  have pp : Point.pole∉removed S := by simp [removed,center,row]
  let e : Vertex S ≃ (Affine S ⊕ Option F) := {
    toFun := fun | ⟨.aff x y,h⟩ => .inl ⟨(x,y),h⟩ | ⟨.inf a,_⟩ => .inr (some a) | ⟨.pole,_⟩ => .inr none
    invFun := fun | .inl v => embed S v | .inr (some a) => ⟨.inf a,ip a⟩ | .inr none=>⟨.pole,pp⟩
    left_inv := by rintro ⟨v,h⟩; cases v <;> rfl
    right_inv := by rintro (⟨⟨x,y⟩,h⟩|_|a) <;> rfl }
  simpa [Nat.add_assoc] using Fintype.card_congr e

private theorem loses_one (S : Finset F) [DecidableRel (host S).Adj] [DecidableRel (affineGraph S).Adj]
    (v : Affine S) : (host S).degree (embed S v) ≤ (affineGraph S).degree v+1 := by
  let f : (host S).neighborSet (embed S v) → Option ((affineGraph S).neighborSet v) :=
    fun | ⟨⟨.aff x y,h⟩,e⟩ => some ⟨⟨(x,y),h⟩,e⟩ | _ => none
  have inj : Function.Injective f := by
    rintro ⟨⟨z,hz⟩,e⟩ ⟨⟨w,hw⟩,k⟩ h
    have ze := e.2
    have wk := k.2
    change Point.inc (Point.aff v.val.1 v.val.2) z at ze
    change Point.inc (Point.aff v.val.1 v.val.2) w at wk
    cases z <;> cases w <;> simp_all [f,Point.inc,Subtype.ext_iff]
  simpa only [Fintype.card_option,card_neighborSet_eq_degree] using Fintype.card_le_of_injective f inj

private theorem odd_regular_upper {q t n : ℕ} (qtwo : 2≤q) (qo : Odd q) (te : Even t)
    (pos : 0<t) (hn : n+q+t=q^2) : number n ≤ n+q := by
  classical
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra hs
  have min (v : Fin (n+q)) : q ≤ G.degree v := by
    have small : Gᶜ.degree v<n := lt_of_not_ge (fun large=>hs (star_isContained_of_le_degree Gᶜ large))
    rw [degree_compl,Fintype.card_fin] at small
    omega
  have product : (q+1)*(q-1)+1=q^2 := by
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
    simp only [Nat.succ_sub_one,Nat.succ_eq_add_one]
    ring
  have reg (v) : G.degree v=q := by
    apply le_antisymm _ (min v)
    by_contra! h
    have lb := Packing.local_bound G red q min v
    have ub := Finset.card_lt_univ_of_notMem (Packing.no_self G v)
    have x : (q+1)*(q-1) ≤ G.degree v*(q-1) := Nat.mul_le_mul_right _ h
    rw [Fintype.card_fin] at ub
    have endlt : (q+1)*(q-1)<n+q := (x.trans lb).trans_lt ub
    omega
  have ev := G.even_card_odd_degree_vertices
  simp only [reg,qo,filter_true,card_univ,Fintype.card_fin] at ev
  have oo := qo.pow (n:=2)
  obtain ⟨i,hi⟩ := ev
  obtain ⟨j,hj⟩ := te
  obtain ⟨k,hk⟩ := oo
  omega

theorem affine_field_even (two : (2:F)≠0) (odd : Odd (Fintype.card F))
    (five : 5≤Fintype.card F) {t n : ℕ} (et : Even t) (pos : 2≤t)
    (le : t≤2*((Fintype.card F+3)/4)) (hn : n+Fintype.card F+t=Fintype.card F^2) :
    number n=n+Fintype.card F := by
  classical
  obtain ⟨S,sc,nz,pairs,roots,safe⟩ := choose_rows two et pos le
  let q := Fintype.card F
  let G := affineGraph S
  have count := cardinality two S
  have ec := erase_line S
  rw [sc,ec] at count
  have cardinal : Fintype.card (Affine S)+1=n+q := by dsimp [q]; omega
  have red : ¬(cycleGraph 4).IsContained G := by
    have sub : G.IsContained (host S) := ⟨⟨⟨embed S,fun h=>h⟩,injective_embed S⟩⟩
    exact fun h => no_square S (h.trans sub)
  have npos : 0<n := by
    change n+q+t=q^2 at hn
    change 5≤q at five
    change t≤2*((q+3)/4) at le
    have qsq : 2*q+1≤q^2 := by nlinarith only [five]
    omega
  have blue : ∀v,Gᶜ.degree v<n := by
    intro v
    have lb := minimum two S nz pairs roots safe (embed S v)
    have l := loses_one S v
    change q≤(host S).degree (embed S v) at lb
    change (host S).degree (embed S v) ≤ G.degree v+1 at l
    rw [degree_compl]
    omega
  have low : Fintype.card (Affine S)<number n := lower_from_host G red blue
  change Fintype.card (Affine S)+1=n+Fintype.card F at cardinal
  apply le_antisymm (odd_regular_upper (by omega) odd et (by omega) hn)
  omega

theorem prime_power_affine {p m t n : ℕ} (hp : p.Prime) (op : p≠2) (hm : m≠0) (five : 5≤p^m)
    (et : Even t) (pos : 2≤t) (le : t≤2*((p^m+3)/4)) (hn : n+p^m+t=(p^m)^2) :
    number n=n+p^m := by
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p m
  letI : Fintype F := Fintype.ofFinite _
  classical
  have two : (2:F)≠0 := by
    intro e
    have d := (CharP.cast_eq_zero_iff F p 2).mp (by simpa using e)
    exact op (Nat.le_antisymm (Nat.le_of_dvd (by decide) d) hp.two_le)
  have card : Fintype.card F=p^m := by rw [← Nat.card_eq_fintype_card,GaloisField.card p m hm]
  have odd : Odd (p^m) := (hp.odd_of_ne_two op).pow
  simpa only [card] using affine_field_even two (by simpa only [card] using odd)
    (by simpa only [card] using five) et pos (by simpa only [card] using le)
    (n:=n) (by simpa only [card] using hn)
end Deldor14.Star.OddWindow

/- Deficiency matrices for near-extremal quadrilateral-free graphs.
These identities generalize the antipodal decomposition to regular deficiency >1. -/
namespace Deldor14.Star.Deficiency
open SimpleGraph Finset Matrix OMA.ChenStar Packing ExcessOne

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def graph : SimpleGraph V where
  Adj i j := j∈missing G i
  symm := ⟨fun i j h => (mem_missing G).mpr ⟨((mem_missing G).mp h).1.symm,
    by simpa [common,inter_comm] using ((mem_missing G).mp h).2⟩⟩
  loopless := ⟨fun i h => ((mem_missing G).mp h).1 rfl⟩
instance : DecidableRel (graph G).Adj := fun i j => inferInstanceAs (Decidable (j∈missing G i))

theorem neighbors (i : V) : (graph G).neighborFinset i=missing G i := by
  ext
  exact mem_neighborFinset _ _ _

theorem regular_of_bounds {d : ℕ} (red : ¬(cycleGraph 4).IsContained G)
    (min : ∀ v, d≤G.degree v) (small : Fintype.card V ≤ (d+1)*(d-1)) : ∀ v,G.degree v=d := by
  intro v
  have sub : endpoints G v ⊆ univ.erase v := fun x hx =>
    mem_erase.mpr ⟨((mem_endpoints G).mp hx).1,mem_univ x⟩
  have ub := card_le_card sub
  rw [card_erase_of_mem (mem_univ v),card_univ] at ub
  have low := local_bound G red d min v
  have vz : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  by_contra bad
  have high : d+1≤G.degree v := by have := min v; omega
  have big := Nat.mul_le_mul_right (d-1) high
  omega

theorem degree {d e : ℕ} (red : ¬(cycleGraph 4).IsContained G)
    (size : Fintype.card V = d*(d-1)+1+e) (reg : ∀ v,G.degree v=d) (v : V) :
    (graph G).degree v=e := by
  rw [←card_neighborFinset_eq_degree,neighbors,missing,card_sdiff_of_subset (by
    intro x hx
    exact mem_erase.mpr ⟨((mem_endpoints G).mp hx).1,mem_univ _⟩)]
  rw [card_erase_of_mem (mem_univ v),card_univ,card_endpoints G red]
  simp [reg,size]

theorem adj_square {d : ℕ} (red : ¬(cycleGraph 4).IsContained G)
    (reg : ∀ v,G.degree v=d) :
    (G.adjMatrix ℝ)^2 = ((d:ℝ)-1) • (1:Matrix V V ℝ) + ones V ℝ - (graph G).adjMatrix ℝ := by
  classical
  ext i j
  rw [adj_square_entries G]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, ones, Matrix.of_apply, adjMatrix_apply]
  by_cases ij : i=j
  · subst j
    have nope := (graph G).irrefl (v:=i)
    simp [common,reg,nope]
  · rw [if_neg ij,mul_zero,zero_add]
    have few := codeg_le_one G red ij
    by_cases h : (graph G).Adj i j
    · rw [if_pos h,sub_self]
      have emp := ((mem_missing G).mp h).2
      simp [emp]
    · rw [if_neg h,sub_zero]
      have ne : common G i j ≠ ∅ := fun e => h ((mem_missing G).mpr ⟨Ne.symm ij,e⟩)
      have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ne)
      exact_mod_cast (show (common G i j).card=1 by omega)

theorem adj_trace : (G.adjMatrix ℝ).trace=0 := by simp [Matrix.trace,Matrix.diag,adjMatrix_apply]
end Deldor14.Star.Deficiency

/- Lower-bound examples of Zach Waddle. The edge lists were taken from
https://github.com/zach7036/c4-star-ramsey/tree/86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33 .
The code below independently checks the symmetry, all codegrees, and each minimum degree.
The original edge lists are distributed under the MIT license (Copyright 2026 Zach Waddle). -/
namespace Deldor14.Star.Waddle39
open SimpleGraph Finset

namespace Host45
private def rows : List ℕ := [279206957088, 4398591836676, 2233655656706, 17731772745744, 8865903150088, 1116827828353, 34634616274944, 567212640288, 618609545220, 687734260738, 585222865424, 554055237768, 826798047489, 66060288, 1101660193824, 8937828008196, 17610440708098, 2474439082128, 4432542042120, 68989223425, 1040384, 2336613212704, 1375463286788, 4468947034242, 8796363567120, 17630849147905, 541165879296, 4407712547104, 17600793280644, 1112396661250, 8728413200, 2207621599240, 8805253416961, 8522825728, 8830519935136, 2216304051204, 1099587649808, 17867133190664, 4535556902913, 8128, 17661446602848, 36509450308, 9071113797698, 4419538157648, 1237252636744]
private def edge (i j : Fin 45) : Bool := (rows.getD i.val 0).testBit j.val
private theorem symm : ∀ i j, edge i j=edge j i := by decide +kernel
private theorem irrefl : ∀ i, edge i i=false := by decide +kernel
private def G : SimpleGraph (Fin 45) where
  Adj i j := edge i j=true
  symm := ⟨fun i j h => (symm i j).symm ▸ h⟩
  loopless := ⟨fun i h => Bool.noConfusion ((irrefl i).symm.trans h)⟩
private instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (edge i j=true))
private theorem codegree : ∀ i j : Fin 45, i≠j → (univ.filter (fun x => edge i x && edge j x)).card≤1 := by decide +kernel
private theorem no_square : ¬(cycleGraph 4).IsContained G := by
  rintro ⟨f⟩
  have e01 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide)
  have e21 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 1 by decide)
  have e03 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 3 by decide)
  have e23 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide)
  have few := Finset.card_le_one.mp (codegree (f 0) (f 2) (f.injective.ne (by decide)))
  have eq := few (a:=f 1) (b:=f 3)
     (mem_filter.mpr ⟨mem_univ _,(by simp only [Bool.and_eq_true]; exact ⟨e01,e21⟩)⟩)
     (mem_filter.mpr ⟨mem_univ _,(by simp only [Bool.and_eq_true]; exact ⟨e03,e23⟩)⟩)
  exact (by decide : (1:Fin 4)≠3) (f.injective eq)
private theorem minimum : ∀ i : Fin 45, 6 ≤ (univ.filter (fun j => edge i j)).card := by decide +kernel
theorem lower : 46 ≤ Deldor14.Star.number 39 := by
  classical
  apply (show 45<Deldor14.Star.number 39 from ?_)
  have h := lower_from_host G no_square (n:=39) (by
    intro v
    have mn : 6 ≤ G.degree v := by
      rw [←card_neighborFinset_eq_degree]
      have seteq : G.neighborFinset v = univ.filter (fun j => edge v j) := by
        ext j
        simp only [mem_neighborFinset,mem_filter,mem_univ,true_and]
        rfl
      rw [seteq]
      exact minimum v
    rw [degree_compl,Fintype.card_fin]
    omega)
  simpa using h
end Host45

namespace Host58
private def rows : List ℕ := [4538922520609024, 72622751672176656, 144119603437510688, 1134730630152256, 9077845041086978, 18155690048750596, 36311371541121032, 32512, 145242196101169281, 18014707755778192, 9290877818175648, 36169689193251008, 563500817580162, 4582764599312516, 72097178606108808, 17523466567680, 36028868154885121, 72128065894875424, 4785151914541632, 19140367202983938, 35270288478212, 144678211052126216, 2234207627640832, 18034206934303233, 36055189594046736, 9029189495820352, 144132952061118466, 72076287077785604, 17875788170248, 285978576338026496, 2533859040169985, 2323285249441808, 2814887224935456, 2396935617249538, 3379900900706308, 2260597047689736, 4161536, 74771152799745, 144150922472227344, 37154972877492256, 18577350744637760, 72347882295952386, 9007345317232644, 4646570515537928, 532676608, 72198606409449473, 281614567481360, 18058387568724000, 144187756921488448, 4504703440261122, 9007766195142920, 68182605824, 9578945838325761, 5633898151150608, 141837545767456, 72058144347457600, 36066181085544450, 281750460694788]
private def edge (i j : Fin 58) : Bool := (rows.getD i.val 0).testBit j.val
private theorem symm : ∀ i j, edge i j=edge j i := by decide +kernel
private theorem irrefl : ∀ i, edge i i=false := by decide +kernel
private def G : SimpleGraph (Fin 58) where
  Adj i j := edge i j=true
  symm := ⟨fun i j h => (symm i j).symm ▸ h⟩
  loopless := ⟨fun i h => Bool.noConfusion ((irrefl i).symm.trans h)⟩
private instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (edge i j=true))
private theorem codegree : ∀ i j : Fin 58, i≠j → (univ.filter (fun x => edge i x && edge j x)).card≤1 := by decide +kernel
private theorem no_square : ¬(cycleGraph 4).IsContained G := by
  rintro ⟨f⟩
  have e01 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide)
  have e21 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 1 by decide)
  have e03 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 3 by decide)
  have e23 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide)
  have few := Finset.card_le_one.mp (codegree (f 0) (f 2) (f.injective.ne (by decide)))
  have eq := few (a:=f 1) (b:=f 3)
     (mem_filter.mpr ⟨mem_univ _,(by simp only [Bool.and_eq_true]; exact ⟨e01,e21⟩)⟩)
     (mem_filter.mpr ⟨mem_univ _,(by simp only [Bool.and_eq_true]; exact ⟨e03,e23⟩)⟩)
  exact (by decide : (1:Fin 4)≠3) (f.injective eq)
private theorem minimum : ∀ i : Fin 58, 7 ≤ (univ.filter (fun j => edge i j)).card := by decide +kernel
theorem lower : 59 ≤ Deldor14.Star.number 51 := by
  classical
  apply (show 58<Deldor14.Star.number 51 from ?_)
  have h := lower_from_host G no_square (n:=51) (by
    intro v
    have mn : 7 ≤ G.degree v := by
      rw [←card_neighborFinset_eq_degree]
      have seteq : G.neighborFinset v = univ.filter (fun j => edge v j) := by
        ext j
        simp only [mem_neighborFinset,mem_filter,mem_univ,true_and]
        rfl
      rw [seteq]
      exact minimum v
    rw [degree_compl,Fintype.card_fin]
    omega)
  simpa using h
end Host58
end Deldor14.Star.Waddle39

/-
The no-triangle lemma follows §5 of Zach Waddle, *The Ramsey number
R(C₄,K₁,₃₉)* (2026), © Zach Waddle, CC BY 4.0.
https://github.com/zach7036/c4-star-ramsey/blob/86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33/R_C4_K1_39.md
https://creativecommons.org/licenses/by/4.0/
Lean formalization by Deldor14.
-/

namespace Deldor14.Star.Waddle39
open Finset SimpleGraph ExcessOne
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem common_unique (red : ¬ (cycleGraph 4).IsContained G)
    {v x a b : V} (vx : v ≠ x) (va : G.Adj v a) (xa : G.Adj x a)
    (vb : G.Adj v b) (xb : G.Adj x b) : a = b :=
  Finset.card_le_one.mp (codeg_le_one G red vx) a ((mem_common G).mpr ⟨va,xa⟩)
    b ((mem_common G).mpr ⟨vb,xb⟩)

theorem no_triangle {d : ℕ} (red : ¬ (cycleGraph 4).IsContained G)
    (reg : ∀ v, G.degree v = d) (odd : Odd d) (v : V)
    (close : missing G v ⊆ G.neighborFinset v) {u w : V}
    (vu : G.Adj v u) (vw : G.Adj v w) (uw : G.Adj u w) : False := by
  classical
  let S := ((G.neighborFinset u).erase v).erase w
  have Smem {x : V} : x ∈ S ↔ x ≠ w ∧ x ≠ v ∧ G.Adj u x := by simp [S]
  have wm : w ∈ (G.neighborFinset u).erase v := by simp [vw.ne.symm,uw]
  have vm : v ∈ G.neighborFinset u := by simp [vu.symm]
  have Ssize : S.card = d - 1 - 1 := by
    simp only [S,card_erase_of_mem wm,card_erase_of_mem vm,card_neighborFinset_eq_degree,reg]
  have deg : 0 < d-1 := by
    have pos := Finset.card_pos.mpr ⟨w,wm⟩
    rwa [card_erase_of_mem vm,card_neighborFinset_eq_degree,reg] at pos
  have inside (x : V) (hx : x ∈ S) : (S.filter (G.Adj x)).card = 1 := by
    obtain ⟨xw,xv,ux⟩ := Smem.mp hx
    have vx : ¬ G.Adj v x := fun h => xw (common_unique G red vu.ne h ux vw uw)
    let X := (G.neighborFinset x).erase u
    let A := (G.neighborFinset v).erase w
    have xm {y : V} : y ∈ X ↔ y ≠ u ∧ G.Adj x y := by simp [X]
    have am {a : V} : a ∈ A ↔ a ≠ w ∧ G.Adj v a := by simp [A]
    have outside {y : V} (hy : y ∈ X) : y ≠ v ∧ ¬G.Adj v y := by
      obtain ⟨yu,xy⟩ := xm.mp hy
      refine ⟨fun h => vx (h ▸ xy.symm), ?_⟩
      intro vy
      exact yu (common_unique G red xv xy vy ux.symm vu)
    have witness (y : X) : ∃ a : A, G.Adj y.val a.val := by
      have yv := outside y.property
      have notEmpty : common G v y.val ≠ ∅ := by
        intro h
        have mem := close ((mem_missing G).mpr ⟨yv.1,h⟩)
        exact yv.2 ((G.mem_neighborFinset _ _).mp mem)
      obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr notEmpty
      obtain ⟨va,ya⟩ := (mem_common G).mp ha
      have aw : a ≠ w := by
        intro e
        subst a
        exact xw (common_unique G red (xm.mp y.property).1 (xm.mp y.property).2.symm ux ya uw)
      exact ⟨⟨a,am.mpr ⟨aw,va⟩⟩,ya⟩
    choose f hf using witness
    have inj : Function.Injective f := by
      intro y z e
      have az := hf z
      rw [←e] at az
      apply Subtype.ext
      have xa : x ≠ (f y).val := fun h => vx (h ▸ (am.mp (f y).property).2)
      exact common_unique G red xa (xm.mp y.property).2 (hf y).symm
        (xm.mp z.property).2 az.symm
    have sz : Fintype.card X = Fintype.card A := by
      rw [Fintype.card_coe,Fintype.card_coe]
      change ((G.neighborFinset x).erase u).card = ((G.neighborFinset v).erase w).card
      rw [card_erase_of_mem ((G.mem_neighborFinset _ _).mpr ux.symm),
        card_erase_of_mem ((G.mem_neighborFinset _ _).mpr vw),card_neighborFinset_eq_degree,
        card_neighborFinset_eq_degree,reg,reg]
    have onto := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,sz⟩).2
    obtain ⟨y,hy⟩ := onto ⟨u,am.mpr ⟨uw.ne,vu⟩⟩
    have yu := hf y
    rw [hy] at yu
    have yo := outside y.property
    have ys : y.val ∈ S := Smem.mpr ⟨fun e => yo.2 (e ▸ vw),yo.1,yu.symm⟩
    apply Finset.card_eq_one.mpr
    refine ⟨y.val, ?_⟩
    ext z
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨hz,xz⟩
      exact common_unique G red ux.ne (Smem.mp hz).2.2 xz yu.symm (xm.mp y.property).2
    · rintro rfl
      exact ⟨ys,(xm.mp y.property).2⟩
  have ev := even_edges G S
  have eq : (∑ a ∈ S, ∑ b ∈ S, (if G.Adj a b then (1:ℤ) else 0)) = (S.card : ℤ) := by
    trans ∑ _a ∈ S, (1:ℤ)
    swap
    · simp
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_boole,inside a ha]
    norm_num
  rw [eq,Ssize] at ev
  obtain ⟨k,hk⟩ := ev
  obtain ⟨j,hj⟩ := odd
  omega

theorem one_missing_neighbor (red : ¬ (cycleGraph 4).IsContained G)
    (reg : ∀ v, G.degree v = 7) (v : V) (three : (missing G v).card = 3) :
    (G.neighborFinset v ∩ missing G v).card = 1 := by
  classical
  let T := G.neighborFinset v
  let D := missing G v
  have Tsize : T.card = 7 := (G.card_neighborFinset_eq_degree v).trans (reg v)
  have Dsize : D.card = 3 := three
  have val (a : V) (ha : a ∈ T) : (common G v a).card = if a ∈ D then 0 else 1 := by
    have va := (G.mem_neighborFinset _ _).mp ha
    split
    · rename_i h
      rw [((mem_missing G).mp h).2,Finset.card_empty]
    · rename_i h
      have emp : common G v a ≠ ∅ := fun e => h ((mem_missing G).mpr ⟨va.ne.symm,e⟩)
      have low := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr emp)
      have high := codeg_le_one G red va.ne
      omega
  have even := even_edges G T
  have count : (∑ a ∈ T, ∑ b ∈ T, if G.Adj a b then (1:ℤ) else 0) =
      ((T.filter (fun a => a ∉ D)).card : ℤ) := by
    trans ∑ a ∈ T, if a ∉ D then (1:ℤ) else 0
    · apply sum_congr rfl
      intro a ha
      rw [sum_boole]
      have e : T.filter (G.Adj a) = common G v a := by
        ext b
        simp [T,common]
      rw [e,val a ha]
      by_cases h : a ∈ D <;> simp [h]
    · rw [sum_boole]
  rw [count] at even
  obtain ⟨k,hk⟩ := even
  have partition := Finset.card_filter_add_card_filter_not (s:=T) (fun a => a ∈ D)
  have meet : T.filter (fun a => a ∈ D) = T ∩ D := by ext; simp
  rw [meet,Tsize] at partition
  have upper := Finset.card_le_card (Finset.inter_subset_right (s₁:=T) (s₂:=D))
  change (T ∩ D).card = 1
  by_contra ne
  have full : (T ∩ D).card = 3 := by omega
  have eq : T ∩ D = D := eq_of_subset_of_card_le inter_subset_right (by omega)
  have close : D ⊆ T := fun a ha => Finset.mem_inter.mp (eq ▸ ha) |>.1
  have sub : T ⊆ D := by
    intro a ha
    have va := (G.mem_neighborFinset _ _).mp ha
    apply (mem_missing G).mpr
    refine ⟨va.ne.symm, Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro b hb
    obtain ⟨vb,ab⟩ := (mem_common G).mp hb
    exact no_triangle G red reg (by decide : Odd 7) v close va vb ab
  have low := Finset.card_le_card sub
  omega

end Deldor14.Star.Waddle39

/- Triangle and edge counts in rows of the deficiency graph. -/

namespace Deldor14.Star.Waddle39
open Finset SimpleGraph Matrix ExcessOne
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem deficiency_row_bound (v : V) (three : (missing G v).card = 3)
    (one : (G.neighborFinset v ∩ missing G v).card = 1) :
    let e := ∑ x ∈ missing G v, ∑ y ∈ missing G v, G.adjMatrix ℝ y x
    0 ≤ e ∧ e ≤ 2 := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp one
  have ain : a ∈ G.neighborFinset v ∩ missing G v := by rw [ha]; simp
  obtain ⟨va,ma⟩ := mem_inter.mp ain
  have va' := (G.mem_neighborFinset _ _).mp va
  have isolated (b : V) (hb : b ∈ missing G v) : ¬G.Adj a b := by
    intro ab
    have mem := (mem_common G).mpr ⟨va',ab.symm⟩
    rw [((mem_missing G).mp hb).2] at mem
    exact Finset.notMem_empty _ mem
  have two : ((missing G v).erase a).card = 2 := by rw [card_erase_of_mem ma,three]
  obtain ⟨b,c,bc,pair⟩ := Finset.card_eq_two.mp two
  have triple := Finset.insert_erase ma
  rw [pair] at triple
  have bm : b ∈ (missing G v).erase a := by rw [pair]; simp
  have cm : c ∈ (missing G v).erase a := by rw [pair]; simp
  obtain ⟨ba,bm⟩ := Finset.mem_erase.mp bm
  obtain ⟨ca,cm⟩ := Finset.mem_erase.mp cm
  have ab := isolated b bm
  have ac := isolated c cm
  change 0 ≤ ∑ x ∈ missing G v, ∑ y ∈ missing G v, G.adjMatrix ℝ y x ∧
    (∑ x ∈ missing G v, ∑ y ∈ missing G v, G.adjMatrix ℝ y x) ≤ 2
  rw [←triple]
  have hn : a ∉ ({b,c} : Finset V) := by simp [ba.symm,ca.symm]
  have hb : b ∉ ({c} : Finset V) := by simp [bc]
  simp only [Finset.sum_insert hn,Finset.sum_insert hb,Finset.sum_singleton]
  by_cases ed : G.Adj b c <;>
    simp [adjMatrix_apply,ab,ac,
      G.adj_comm b a,G.adj_comm c a,G.adj_comm c b,ed] <;> norm_num

theorem trace_counts (B : SimpleGraph V) [DecidableRel B.Adj]
    (rows : ∀ v, B.neighborFinset v = missing G v)
    (three : ∀ v, (missing G v).card = 3)
    (one : ∀ v, (G.neighborFinset v ∩ missing G v).card = 1) :
    (G.adjMatrix ℝ * B.adjMatrix ℝ).trace = Fintype.card V ∧
    0 ≤ (G.adjMatrix ℝ * B.adjMatrix ℝ ^ 2).trace ∧
    (G.adjMatrix ℝ * B.adjMatrix ℝ ^ 2).trace ≤ 2 * (Fintype.card V : ℝ) := by
  classical
  have diag1 (v : V) : (G.adjMatrix ℝ * B.adjMatrix ℝ) v v = 1 := by
    rw [B.mul_adjMatrix_apply,rows]
    simp only [adjMatrix_apply,sum_boole]
    have eq : (missing G v).filter (G.Adj v) = G.neighborFinset v ∩ missing G v := by
      ext x
      simp [and_comm]
    rw [eq,one]
    norm_num
  have diag2 (v : V) :
      0 ≤ (B.adjMatrix ℝ * G.adjMatrix ℝ * B.adjMatrix ℝ) v v ∧
      (B.adjMatrix ℝ * G.adjMatrix ℝ * B.adjMatrix ℝ) v v ≤ 2 := by
    simp only [B.mul_adjMatrix_apply,B.adjMatrix_mul_apply,rows]
    exact deficiency_row_bound G v (three v) (one v)
  constructor
  · simp [Matrix.trace,Matrix.diag,diag1]
  rw [sq,←Matrix.mul_assoc,Matrix.trace_mul_cycle]
  change 0 ≤ ∑ v, (B.adjMatrix ℝ * G.adjMatrix ℝ * B.adjMatrix ℝ) v v ∧
    (∑ v, (B.adjMatrix ℝ * G.adjMatrix ℝ * B.adjMatrix ℝ) v v) ≤ _
  refine ⟨Finset.sum_nonneg (fun v _ => (diag2 v).1),?_⟩
  calc
    _ ≤ ∑ _v : V, (2:ℝ) := Finset.sum_le_sum fun v _ => (diag2 v).2
    _ = _ := by simp [mul_comm]

end Deldor14.Star.Waddle39

/- The two mixed traces for the putative regular graph on 46 vertices. -/
namespace Deldor14.Star.Waddle39
open Finset SimpleGraph ExcessOne Deficiency

theorem traces_46 (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj]
    (red : ¬ (cycleGraph 4).IsContained G) (reg : ∀ v, G.degree v = 7) :
    let A := G.adjMatrix ℝ
    let D := (graph G).adjMatrix ℝ
    (A*D).trace = 46 ∧ 0 ≤ (A*D^2).trace ∧ (A*D^2).trace ≤ 92 := by
  have three (v : Fin 46) : (missing G v).card = 3 := by
    rw [←neighbors,card_neighborFinset_eq_degree]
    exact degree G red (d:=7) (e:=3) (by decide) reg v
  have result := trace_counts G (graph G) (neighbors G) three
    (fun v => one_missing_neighbor G red reg v (three v))
  norm_num at result
  exact result

end Deldor14.Star.Waddle39

/- Positive semidefiniteness of the signless Laplacian and the two-sided degree bound. -/
namespace Deldor14.Star.Waddle39
open Matrix SimpleGraph Finset Unitary
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem sum_endpoint (f : V → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then f i else 0) = ∑ i, G.degree i * f i := by
  apply sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp [← G.neighborFinset_eq_filter]

theorem signless_pos : (G.degMatrix ℝ + G.adjMatrix ℝ).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change _ᴴ=_
    rw [conjTranspose_eq_transpose_of_trivial,transpose_add]
    rw [show (G.adjMatrix ℝ)ᵀ = G.adjMatrix ℝ from G.isSymm_adjMatrix]
    simp [degMatrix]
  · intro x
    simp only [star_trivial,Matrix.add_mulVec,dotProduct_add,G.dotProduct_mulVec_degMatrix,
      G.dotProduct_mulVec_adjMatrix]
    have e1 := sum_endpoint G (fun i => x i*x i)
    have e2 : (∑ i,∑ j,if G.Adj i j then x j*x j else 0) = ∑ i,(G.degree i:ℝ)*(x i*x i) := by
      rw [Finset.sum_comm]
      simpa only [G.adj_comm] using e1
    have pos : 0 ≤ ∑ i,∑ j, if G.Adj i j then x i*x i+2*(x i*x j)+x j*x j else 0 := by
      apply sum_nonneg
      intro i _
      apply sum_nonneg
      intro j _
      split_ifs
      · nlinarith [sq_nonneg (x i+x j)]
      · exact le_rfl
    have dist (i j : V) : (if G.Adj i j then x i*x i+2*(x i*x j)+x j*x j else 0) =
        (if G.Adj i j then x i*x i else 0) + 2*(if G.Adj i j then x i*x j else 0) +
        (if G.Adj i j then x j*x j else 0) := by split_ifs <;> ring
    simp_rw [dist] at pos
    simp only [sum_add_distrib,←mul_sum,e1,e2] at pos
    simp only [mul_assoc] at *
    linarith

theorem signed_diag_bound (reg : ∀ x,G.degree x=3) (U : Matrix.unitaryGroup V ℝ) (i : V) :
    -3 ≤ ((conjStarAlgAut ℝ _ (star U)) (G.adjMatrix ℝ)) i i ∧
      ((conjStarAlgAut ℝ _ (star U)) (G.adjMatrix ℝ)) i i ≤ 3 := by
  let e := conjStarAlgAut ℝ _ (star U)
  have deg : G.degMatrix ℝ = (3:ℝ) • (1:Matrix V V ℝ) := by
    ext i j
    simp [degMatrix,Matrix.smul_apply,Matrix.one_apply,diagonal_apply,reg]
  have diagPos {B : Matrix V V ℝ} (h : B.PosSemidef) : 0≤(e B) i i := by
    have p := h.mul_mul_conjTranspose_same ((star U : Matrix.unitaryGroup V ℝ) : Matrix V V ℝ)
    exact p.diag_nonneg
  have plus := diagPos (signless_pos G)
  have minus := diagPos (G.posSemidef_lapMatrix ℝ)
  rw [lapMatrix,deg,map_sub,map_smul,map_one,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one] at minus
  rw [deg,map_add,map_smul,map_one,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one] at plus
  change -3 ≤ (e _) i i ∧ (e _) i i ≤ 3
  constructor <;> linarith
end Deldor14.Star.Waddle39

/- Integer-scaled dual polynomials from Zach Waddle's certificate for the star with 39 leaves.
Source https://github.com/zach7036/c4-star-ramsey, commit 86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33.
The interval bounds are independently checked in a rational Bernstein basis. -/
namespace Deldor14.Star.Waddle39
open Finset
def upperPoly (x : ℝ) := (555946:ℝ)*(x)^0 + (390143:ℝ)*(x)^1 + (-16348:ℝ)*(x)^2 + (-43595:ℝ)*(x)^3 + (1216:ℝ)*(x)^4 + (2115:ℝ)*(x)^5
def lowerPoly (x : ℝ) := (459756:ℝ)*(x)^0 + (395916:ℝ)*(x)^1 + (11122:ℝ)*(x)^2 + (-45053:ℝ)*(x)^3 + (-812:ℝ)*(x)^4 + (2200:ℝ)*(x)^5
private theorem upPosPart1 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  have posA : 0≤x-(108253175473/62500000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(295753175473/125000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (x) + (-1000000) = (1123671614636531795861820261283532351891813399904303174240/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^0*((295753175473/125000000000:ℝ)-x)^5 + (1197531464085065941450187494881695368303835725480760757935600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^1*((295753175473/125000000000:ℝ)-x)^4 + (3416316947996018576902430246843087421321691917461760757935600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^2*((295753175473/125000000000:ℝ)-x)^3 + (3294906434713644886308663101510879994966649054721380378967800/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^3*((295753175473/125000000000:ℝ)-x)^2 + (1221662348416924877555492969987761009267331787677970094741950/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^4*((295753175473/125000000000:ℝ)-x)^1 + (153275347093737278341368453924605583424222006167559509474195/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^5*((295753175473/125000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upPosPart2 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(1262259526419/500000000000:ℝ)) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  have posA : 0≤x-(295753175473/125000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(1262259526419/500000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (x) + (-1000000) = (156953955423986973021561296818796117426403334315580937701575680/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^0*((1262259526419/500000000000:ℝ)-x)^5 + (668216660205185812730551904800608915542583901826820516380908800/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^1*((1262259526419/500000000000:ℝ)-x)^4 + (1099551759347805882914618699706051562603232949955318774571363200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^2*((1262259526419/500000000000:ℝ)-x)^3 + (869633778837464336177826210934607046293692535377805080928522400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^3*((1262259526419/500000000000:ℝ)-x)^2 + (329226520188459210738422204641115057378453884358420405348195900/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^4*((1262259526419/500000000000:ℝ)-x)^1 + (47888406195466785886070519443971824555567522692524585802229385/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^5*((1262259526419/500000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upPosPart3 (x : ℝ) (ha : (1262259526419/500000000000:ℝ)≤x) (hb : x≤(670753175473/250000000000:ℝ)) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  have posA : 0≤x-(1262259526419/500000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(670753175473/250000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (x) + (-1000000) = (47888406195466785886070519443971824555567522692524585802229385/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^0*((670753175473/250000000000:ℝ)-x)^5 + (149657541766208648122282989798603188177221342566825452674097950/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^1*((670753175473/250000000000:ℝ)-x)^4 + (151357865148462085713269351564559569488762368211425270232130600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^2*((670753175473/250000000000:ℝ)-x)^3 + (47886924791301947315847210032575302521430853111388846821420400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^3*((670753175473/250000000000:ℝ)-x)^2 + (1438818470182442462122644193751348988840042471720282273806800/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^4*((670753175473/250000000000:ℝ)-x)^1 + (3147233534465586743178749384329301318271528965285904303174240/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^5*((670753175473/250000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upPosPart4 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(670753175473/250000000000:ℝ)) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  rcases le_total x (1262259526419/500000000000:ℝ) with h|h
  · exact upPosPart2 x ha h
  · exact upPosPart3 x h hb
private theorem upPosPart5 (x : ℝ) (ha : (670753175473/250000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  have posA : 0≤x-(670753175473/250000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤3-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (x) + (-1000000) = (98351047952049585724335918260290666195985280165184509474195/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^0*(3-x)^5 + (1385339564894341131982373511794900681137276547995250000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^1*(3-x)^4 + (13758346061960374283079150752184561031187500000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^2*(3-x)^3 + (37732094713286814137917547171875000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^3*(3-x)^2 + (39530494077903863281250000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^4*(3-x)^1 + (14276367187500000000000000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^5*(3-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upPosPart6 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  rcases le_total x (670753175473/250000000000:ℝ) with h|h
  · exact upPosPart4 x ha h
  · exact upPosPart5 x h hb
private theorem upPosPart7 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  rcases le_total x (295753175473/125000000000:ℝ) with h|h
  · exact upPosPart1 x ha h
  · exact upPosPart6 x h hb
private theorem upPos (x : ℝ) (hp : 0≤x) (lo : 3≤x^2) (hi : x^2≤9) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  have rpos : 0≤(108253175473/62500000000:ℝ) := by norm_num
  have rsq : (108253175473/62500000000:ℝ)^2<3 := by norm_num
  apply upPosPart7 x
  · by_contra! gap
    nlinarith [mul_pos (sub_pos.mpr gap) (show 0<(108253175473/62500000000:ℝ)+x by linarith)]
  · nlinarith [sq_nonneg (x-3)]
private theorem upNegPart8 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have posA : 0≤x-(108253175473/62500000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(295753175473/125000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (-x) + (0) = (1088109726824542504769843427702844561940778491624095696825760/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^0*((295753175473/125000000000:ℝ)-x)^5 + (3035282761365202474713882898687731122574175189591239242064400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^1*((295753175473/125000000000:ℝ)-x)^4 + (2758510375486067405546562885848966428702654150122239242064400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^2*((295753175473/125000000000:ℝ)-x)^3 + (856047856027819045164171637440721161618691555326619621032200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^3*((295753175473/125000000000:ℝ)-x)^2 + (52843671856683197329599226240722975772295258898029905258050/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^4*((295753175473/125000000000:ℝ)-x)^1 + (1522878909403467921516990439032698469069887896440490525805/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^5*((295753175473/125000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upNegPart9 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(2445272228311/1000000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have posA : 0≤x-(295753175473/125000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(2445272228311/1000000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (-x) + (0) = (49901696103332836852268742706223463434482086590561993549578240/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^0*((2445272228311/1000000000000:ℝ)-x)^5 + (64249360656272831031973247040505673055640356625580721779404800/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^1*((2445272228311/1000000000000:ℝ)-x)^4 + (95850283931664874356409215176284054406487772730542263113958400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^2*((2445272228311/1000000000000:ℝ)-x)^3 + (369570845725970819811821291046880675147904306195528480224713600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^3*((2445272228311/1000000000000:ℝ)-x)^2 + (458140964050148631216183891888168428840745167422676710098312200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^4*((2445272228311/1000000000000:ℝ)-x)^1 + (170066127425037823461220877670064549494416572654841699267204635/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^5*((2445272228311/1000000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upNegPart10 (x : ℝ) (ha : (2445272228311/1000000000000:ℝ)≤x) (hb : x≤(1262259526419/500000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have posA : 0≤x-(2445272228311/1000000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(1262259526419/500000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (-x) + (0) = (170066127425037823461220877670064549494416572654841699267204635/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^0*((1262259526419/500000000000:ℝ)-x)^5 + (1242520310200229603396024884812477066103420559125740282573734150/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^1*((1262259526419/500000000000:ℝ)-x)^4 + (3507088230326294708531185262744115224198605873007782770126401400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^2*((1262259526419/500000000000:ℝ)-x)^3 + (4731481847223618772223775339394121663856379858685723517251201200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^3*((1262259526419/500000000000:ℝ)-x)^2 + (3060477718039532849327977552081711793854021394911434650250514800/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^4*((1262259526419/500000000000:ℝ)-x)^1 + (763623308089152137580737034276067788603489631494765254328659680/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^5*((1262259526419/500000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upNegPart11 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(1262259526419/500000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  rcases le_total x (2445272228311/1000000000000:ℝ) with h|h
  · exact upNegPart9 x ha h
  · exact upNegPart10 x h hb
private theorem upNegPart12 (x : ℝ) (ha : (1262259526419/500000000000:ℝ)≤x) (hb : x≤(670753175473/250000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have posA : 0≤x-(1262259526419/500000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(670753175473/250000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (-x) + (0) = (23863228377786004299398032321127118393859050984211414197770615/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^0*((670753175473/250000000000:ℝ)-x)^5 + (166668568289319261407971887811799788792009427581206547325902050/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^1*((670753175473/250000000000:ℝ)-x)^4 + (443767496374043096477811662264422018038846024731166729767869400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^2*((670753175473/250000000000:ℝ)-x)^3 + (560104384163795235974495429560902727873397430680483153178579600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^3*((670753175473/250000000000:ℝ)-x)^2 + (335761940226871103448830932250154653267354726068951717726193200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^4*((670753175473/250000000000:ℝ)-x)^1 + (76613102247720838723726875449776224050899152254810095696825760/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^5*((670753175473/250000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upNegPart13 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(670753175473/250000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  rcases le_total x (1262259526419/500000000000:ℝ) with h|h
  · exact upNegPart11 x ha h
  · exact upNegPart12 x h hb
private theorem upNegPart14 (x : ℝ) (ha : (670753175473/250000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have posA : 0≤x-(670753175473/250000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤3-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (-x) + (0) = (2394159445241276210116464857805507001590598507962815490525805/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^0*(3-x)^5 + (14927270414439699186195039601447939194649307240132750000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^1*(3-x)^4 + (33665942922035935820670566709992481176812500000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^2*(3-x)^3 + (32402060040213468943495557953125000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^3*(3-x)^2 + (11276814927740824218750000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^4*(3-x)^1 + (976562500000000000000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^5*(3-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upNegPart15 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (-x) + (0) := by
  rcases le_total x (670753175473/250000000000:ℝ) with h|h
  · exact upNegPart13 x ha h
  · exact upNegPart14 x h hb
private theorem upNegPart16 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (-x) + (0) := by
  rcases le_total x (295753175473/125000000000:ℝ) with h|h
  · exact upNegPart8 x ha h
  · exact upNegPart15 x h hb
private theorem upNeg (x : ℝ) (hp : 0≤x) (lo : 3≤x^2) (hi : x^2≤9) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have rpos : 0≤(108253175473/62500000000:ℝ) := by norm_num
  have rsq : (108253175473/62500000000:ℝ)^2<3 := by norm_num
  apply upNegPart16 x
  · by_contra! gap
    nlinarith [mul_pos (sub_pos.mpr gap) (show 0<(108253175473/62500000000:ℝ)+x by linarith)]
  · nlinarith [sq_nonneg (x-3)]
private theorem loPosPart17 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤(512259526419/250000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have posA : 0≤x-(108253175473/62500000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(512259526419/250000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (x) + (1000000) = (27584982012691358767241415817142022109440685392730334305689600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^0*((512259526419/250000000000:ℝ)-x)^5 + (103536234988737114429558001266207765955493123584210753646336000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^1*((512259526419/250000000000:ℝ)-x)^4 + (150392172347464616636426126376539613288125515418524130469504000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^2*((512259526419/250000000000:ℝ)-x)^3 + (105332363260223745744153936595299575572696009095549097852128000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^3*((512259526419/250000000000:ℝ)-x)^2 + (35528391364599752328243391402301406319900768110201911694548000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^4*((512259526419/250000000000:ℝ)-x)^1 + (4630071536644650128571499361381086589155689296435936754182200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^5*((512259526419/250000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loPosPart18 (x : ℝ) (ha : (512259526419/250000000000:ℝ)≤x) (hb : x≤(220753175473/100000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have posA : 0≤x-(512259526419/250000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(220753175473/100000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (x) + (1000000) = (148162289172628804114287979564194770852982057485949976133830400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^0*((220753175473/100000000000:ℝ)-x)^5 + (542762906961119993605265584294638280278953141381394233890960000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^1*((220753175473/100000000000:ℝ)-x)^4 + (765584841464361835013345458335843942063190627618883723151600000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^2*((220753175473/100000000000:ℝ)-x)^3 + (516741112800872016200483979319096018654132794112869769293000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^3*((220753175473/100000000000:ℝ)-x)^2 + (166539427788601200648657001981693625496606971615279070538750000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^4*((220753175473/100000000000:ℝ)-x)^1 + (20775662724449612540913379894903425879571574280588178423125000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^5*((220753175473/100000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loPosPart19 (x : ℝ) (ha : (220753175473/100000000000:ℝ)≤x) (hb : x≤(2286778579257/1000000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have posA : 0≤x-(220753175473/100000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(2286778579257/1000000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (x) + (1000000) = (664821207182387601309228156636909628146290376978821709540000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^0*((2286778579257/1000000000000:ℝ)-x)^5 + (2321528209250287799440699143069724203151466281496697692930000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^1*((2286778579257/1000000000000:ℝ)-x)^4 + (3104620996304981896790433168640646734850326559859655847274000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^2*((2286778579257/1000000000000:ℝ)-x)^3 + (2005540035041667447240579280593957745966212431722730262546600000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^3*((2286778579257/1000000000000:ℝ)-x)^2 + (658298212063313659906445838616286118308658931807296618145970000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^4*((2286778579257/1000000000000:ℝ)-x)^1 + (100665295319577693895201243857065918587475008481085631266274600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^5*((2286778579257/1000000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loPosPart20 (x : ℝ) (ha : (2286778579257/1000000000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have posA : 0≤x-(2286778579257/1000000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(295753175473/125000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (x) + (1000000) = (100665295319577693895201243857065918587475008481085631266274600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^0*((295753175473/125000000000:ℝ)-x)^5 + (348354741132463279045566599954373067566091153003559694516776000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^1*((295753175473/125000000000:ℝ)-x)^4 + (765766151318265923797062325946305542995941316507782568029824000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^2*((295753175473/125000000000:ℝ)-x)^3 + (1182685749991710460514441896697506388537134345588457393804288000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^3*((295753175473/125000000000:ℝ)-x)^2 + (957205484070547973775750508478747916465624083384196175024128000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^4*((295753175473/125000000000:ℝ)-x)^1 + (292589563645067634478378085257145308345692762835786697782067200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^5*((295753175473/125000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loPosPart21 (x : ℝ) (ha : (220753175473/100000000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  rcases le_total x (2286778579257/1000000000000:ℝ) with h|h
  · exact loPosPart19 x ha h
  · exact loPosPart20 x h hb
private theorem loPosPart22 (x : ℝ) (ha : (512259526419/250000000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  rcases le_total x (220753175473/100000000000:ℝ) with h|h
  · exact loPosPart18 x ha h
  · exact loPosPart21 x h hb
private theorem loPosPart23 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  rcases le_total x (512259526419/250000000000:ℝ) with h|h
  · exact loPosPart17 x ha h
  · exact loPosPart22 x h hb
private theorem loPosPart24 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have posA : 0≤x-(295753175473/125000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤3-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (x) + (1000000) = (8929124867098011306102846840122842661916893397088217095400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^0*(3-x)^5 + (168117873884999382364532768821458604242894948136500000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^1*(3-x)^4 + (1129585422963148100372143066560324361703125000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^2*(3-x)^3 + (1921743878691896243045591771484375000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^3*(3-x)^2 + (958253661474991943359375000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^4*(3-x)^1 + (30517578125000000000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^5*(3-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loPosPart25 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  rcases le_total x (295753175473/125000000000:ℝ) with h|h
  · exact loPosPart23 x ha h
  · exact loPosPart24 x h hb
private theorem loPos (x : ℝ) (hp : 0≤x) (lo : 3≤x^2) (hi : x^2≤9) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have rpos : 0≤(108253175473/62500000000:ℝ) := by norm_num
  have rsq : (108253175473/62500000000:ℝ)^2<3 := by norm_num
  apply loPosPart25 x
  · by_contra! gap
    nlinarith [mul_pos (sub_pos.mpr gap) (show 0<(108253175473/62500000000:ℝ)+x by linarith)]
  · nlinarith [sq_nonneg (x-3)]
private theorem loNegPart26 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  have posA : 0≤x-(108253175473/62500000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(295753175473/125000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (-x) + (0) = (3814038667054337964233557192002608887255133845177052947200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^0*((295753175473/125000000000:ℝ)-x)^5 + (1330596721324964004229442968423987087803616525704942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^1*((295753175473/125000000000:ℝ)-x)^4 + (3857827929155154033334920021988173482982845216796942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^2*((295753175473/125000000000:ℝ)-x)^3 + (3834677632413381655624022684062845353877911953944471316184000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^3*((295753175473/125000000000:ℝ)-x)^2 + (1497118317934343731469434290161207970265319074872617829046000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^4*((295753175473/125000000000:ℝ)-x)^1 + (200361871168423872542618589949165220576037891125911782904600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^5*((295753175473/125000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loNegPart27 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(670753175473/250000000000:ℝ)) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  have posA : 0≤x-(295753175473/125000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(670753175473/250000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (-x) + (0) = (6411579877389563921363794878373287058433212516029177052947200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^0*((670753175473/250000000000:ℝ)-x)^5 + (24132955993472229706717512945220325414003988672256942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^1*((670753175473/250000000000:ℝ)-x)^4 + (31214609778875243254611874380425756500299946054440942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^2*((670753175473/250000000000:ℝ)-x)^3 + (15630347238340659817755407008587255452485451718312471316184000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^3*((670753175473/250000000000:ℝ)-x)^2 + (2355409415715779774260321796386448578502107602351117829046000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^4*((670753175473/250000000000:ℝ)-x)^1 + (225171779317914855390567474472524870867972727512411782904600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^5*((670753175473/250000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loNegPart28 (x : ℝ) (ha : (670753175473/250000000000:ℝ)≤x) (hb : x≤(1420753175473/500000000000:ℝ)) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  have posA : 0≤x-(670753175473/250000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(1420753175473/500000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (-x) + (0) = (7205496938173275372498159183120795867775127280397177052947200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^0*((1420753175473/500000000000:ℝ)-x)^5 + (16354676384847088905571045131222791752279732965360942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^1*((1420753175473/500000000000:ℝ)-x)^4 + (61047155106909116094260945235816887108621647729728942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^2*((1420753175473/500000000000:ℝ)-x)^3 + (172251149333502393002330519198292137869231781247048471316184000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^3*((1420753175473/500000000000:ℝ)-x)^2 + (191350052963739772143014658092315619705225684657308117829046000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^4*((1420753175473/500000000000:ℝ)-x)^1 + (71003755229622899131499694554832986660233092400285411782904600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^5*((1420753175473/500000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loNegPart29 (x : ℝ) (ha : (1420753175473/500000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  have posA : 0≤x-(1420753175473/500000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤3-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (-x) + (0) = (71003755229622899131499694554832986660233092400285411782904600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^0*(3-x)^5 + (518687499332489219171982287456014246897105239345546000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^1*(3-x)^4 + (1481600934808500181118201036653086646636750000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^2*(3-x)^3 + (2060358888134182641007345940125000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^3*(3-x)^2 + (1396278571489398562500000000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^4*(3-x)^1 + (369843750000000000000000000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^5*(3-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loNegPart30 (x : ℝ) (ha : (670753175473/250000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  rcases le_total x (1420753175473/500000000000:ℝ) with h|h
  · exact loNegPart28 x ha h
  · exact loNegPart29 x h hb
private theorem loNegPart31 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  rcases le_total x (670753175473/250000000000:ℝ) with h|h
  · exact loNegPart27 x ha h
  · exact loNegPart30 x h hb
private theorem loNegPart32 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  rcases le_total x (295753175473/125000000000:ℝ) with h|h
  · exact loNegPart26 x ha h
  · exact loNegPart31 x h hb
private theorem loNeg (x : ℝ) (hp : 0≤x) (lo : 3≤x^2) (hi : x^2≤9) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  have rpos : 0≤(108253175473/62500000000:ℝ) := by norm_num
  have rsq : (108253175473/62500000000:ℝ)^2<3 := by norm_num
  apply loNegPart32 x
  · by_contra! gap
    nlinarith [mul_pos (sub_pos.mpr gap) (show 0<(108253175473/62500000000:ℝ)+x by linarith)]
  · nlinarith [sq_nonneg (x-3)]
theorem dual (x : ℝ) (lo : 3≤x^2) (hi : x^2≤9) :
    lowerPoly x ≤ (if 0<x then 1000000 else 0) ∧ (if 0<x then 1000000 else 0) ≤ upperPoly x := by
  by_cases h : 0<x
  · rw [if_pos h]
    constructor <;> linarith only [upPos x h.le lo hi,loPos x h.le lo hi]
  · rw [if_neg h]
    have xp : 0≤ -x := by linarith
    have l : 3≤(-x)^2 := by nlinarith
    have u : (-x)^2≤9 := by nlinarith
    have a := upNeg (-x) xp l u
    have b := loNeg (-x) xp l u
    rw [neg_neg] at a b
    constructor <;> linarith
end Deldor14.Star.Waddle39

/- Integer obstruction for the nonprincipal eigenvalues, using Waddle's dual polynomials. -/
namespace Deldor14.Star.Waddle39
open Finset

theorem eigenvalue_count_impossible (f j : Fin 46 → ℝ)
    (jSum : ∑ i, j i = 46)
    (principal : ∀ i, f i = 7 → 40 ≤ j i)
    (other : ∀ i, f i ≠ 7 → j i = 0 ∧ 3 ≤ (f i)^2 ∧ (f i)^2 ≤ 9)
    (p1 : ∑ i, (f i)^1 = 0) (p2 : ∑ i, (f i)^2 = 322)
    (p3 : ∑ i, (f i)^3 = 276) (p4 : ∑ i, (f i)^4 = 4186)
    (p5 : 16192 ≤ ∑ i, (f i)^5) (p5' : ∑ i, (f i)^5 ≤ 16284) : False := by
  classical
  let top := univ.filter (fun i => f i = 7)
  have row (i : Fin 46) : (if f i = 7 then (40:ℝ) else 0) ≤ j i := by
    split
    · exact principal i ‹_›
    · rw [(other i ‹_›).1]
  have upper := Finset.sum_le_sum (s:=univ) (fun i _ => row i)
  rw [jSum] at upper
  have tally : (top.card:ℝ)*40 ≤ 46 := by
    simpa [top,Finset.sum_ite] using upper
  have card_le : top.card ≤ 1 := by
    by_contra! h
    have hn : (2:ℝ) ≤ top.card := by exact_mod_cast h
    linarith
  have nonempty : top.Nonempty := by
    by_contra! empty
    have zero (i : Fin 46) : j i = 0 := by
      apply (other i _).1
      intro hi
      have h : i ∈ top := mem_filter.mpr ⟨mem_univ _,hi⟩
      simp [empty] at h
    simp [zero] at jSum
  obtain ⟨t,ht⟩ := Finset.card_eq_one.mp (le_antisymm card_le (Finset.card_pos.mpr nonempty))
  have ft : f t = 7 := (mem_filter.mp (show t ∈ top by rw [ht]; simp)).2
  let S := univ.erase t
  have Ssize : S.card = 45 := by simp [S]
  have band (i : Fin 46) (h : i ∈ S) : 3 ≤ (f i)^2 ∧ (f i)^2 ≤ 9 := by
    apply (other i _).2
    intro hi
    have mem : i ∈ top := mem_filter.mpr ⟨mem_univ _,hi⟩
    rw [ht,mem_singleton] at mem
    exact (mem_erase.mp h).1 mem
  let m (k : ℕ) := ∑ i ∈ S, (f i)^k
  have apart (k : ℕ) : m k + (7:ℝ)^k = ∑ i, (f i)^k := by
    simpa only [m,S,←ft] using (Finset.sum_erase_add univ (fun i => (f i)^k) (mem_univ t))
  have m0 : m 0 = 45 := by simp [m,Ssize]
  have m1 : m 1 = -7 := by linarith only [apart 1,p1]
  have m2 : m 2 = 273 := by linarith only [apart 2,p2]
  have m3 : m 3 = -67 := by linarith only [apart 3,p3]
  have m4 : m 4 = 1785 := by linarith only [apart 4,p4]
  have m5 : -615 ≤ m 5 := by linarith only [apart 5,p5]
  have m5' : m 5 ≤ -523 := by linarith only [apart 5,p5']
  let positive := (S.filter (fun i => 0 < f i)).card
  have indicator : (∑ i ∈ S, if 0 < f i then (1000000:ℝ) else 0) =
      (positive:ℝ) * 1000000 := by simp [positive,Finset.sum_ite]
  have low := Finset.sum_le_sum (s:=S) fun i hi => (dual (f i) (band i hi).1 (band i hi).2).1
  have high := Finset.sum_le_sum (s:=S) fun i hi => (dual (f i) (band i hi).1 (band i hi).2).2
  rw [indicator] at low high
  simp only [upperPoly,lowerPoly,Finset.sum_add_distrib,←Finset.mul_sum] at low high
  change 459756*m 0 + 395916*m 1 + 11122*m 2 + (-45053)*m 3 +
    (-812)*m 4 + 2200*m 5 ≤ (positive:ℝ)*1000000 at low
  change (positive:ℝ)*1000000 ≤ 555946*m 0 + 390143*m 1 + (-16348)*m 2 +
    (-43595)*m 3 + 1216*m 4 + 2115*m 5 at high
  have lb : (21:ℝ) < positive := by linarith only [low,m0,m1,m2,m3,m4,m5]
  have ub : (positive:ℝ) < 22 := by linarith only [high,m0,m1,m2,m3,m4,m5']
  have l : 21 < positive := by exact_mod_cast lb
  have h : positive < 22 := by exact_mod_cast ub
  omega

end Deldor14.Star.Waddle39

/- Waddle's fifth-moment obstruction read in an orthonormal eigenbasis. -/
namespace Deldor14.Star.Waddle39
open Finset Matrix Unitary SimpleGraph

theorem spectral_impossible (A J : Matrix (Fin 46) (Fin 46) ℝ) (D : SimpleGraph (Fin 46))
    [DecidableRel D.Adj] (regD : ∀ i, D.degree i = 3) (hermA : A.IsHermitian)
    (square : A^2 = (6:ℝ) • 1 + J - D.adjMatrix ℝ)
    (rightJ : J*A = (7:ℝ) • J) (trJ : J.trace = 46) (trA : A.trace = 0)
    (tr2 : (A^2).trace = 322) (tr3 : (A^3).trace = 276) (tr4 : (A^4).trace = 4186)
    (tr5 : 16192 ≤ (A^5).trace ∧ (A^5).trace ≤ 16284) : False := by
  classical
  let f := hermA.eigenvalues
  let e := conjStarAlgAut ℝ _ (star hermA.eigenvectorUnitary)
  let j (i : Fin 46) := (e J) i i
  have diagA : e A = diagonal f := by
    simpa [e,f,Function.comp_def] using hermA.conjStarAlgAut_star_eigenvectorUnitary
  have traceConj (B : Matrix (Fin 46) (Fin 46) ℝ) : (e B).trace = B.trace := by
    dsimp only [e]
    rw [conjStarAlgAut_apply,trace_mul_cycle,coe_star_mul_self,one_mul]
  have sumPow (k : ℕ) : ∑ i, (f i)^k = (A^k).trace := by
    rw [←traceConj (A^k),map_pow,diagA,diagonal_pow,trace_diagonal]
    simp only [Pi.pow_apply]
  have jSum : ∑ i, j i = 46 := (traceConj J).trans trJ
  have relation (i : Fin 46) : j i * f i = 7*j i := by
    have eq := congrArg e rightJ
    rw [map_mul,map_smul,diagA] at eq
    have entry := congrArg (fun B : Matrix (Fin 46) (Fin 46) ℝ => B i i) eq
    simpa only [j,mul_diagonal,Matrix.smul_apply,smul_eq_mul] using entry
  have row (i : Fin 46) : f i ^ 2 = 6 + j i - (e (D.adjMatrix ℝ)) i i := by
    have eq := congrArg e square
    rw [map_pow,map_sub,map_add,map_smul,map_one,diagA,diagonal_pow] at eq
    have entry := congrArg (fun B : Matrix (Fin 46) (Fin 46) ℝ => B i i) eq
    simpa only [j,diagonal_apply_eq,Pi.pow_apply,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
      Matrix.one_apply_eq,smul_eq_mul,mul_one] using entry
  have bounds (i : Fin 46) : -3 ≤ (e (D.adjMatrix ℝ)) i i ∧ (e (D.adjMatrix ℝ)) i i ≤ 3 :=
    signed_diag_bound D regD hermA.eigenvectorUnitary i
  apply eigenvalue_count_impossible f j jSum
  · intro i top
    have eq := row i
    rw [top] at eq
    linarith only [eq,(bounds i).1]
  · intro i off
    have product : j i * (f i - 7) = 0 := by linear_combination relation i
    have zero := (mul_eq_zero.mp product).resolve_right (sub_ne_zero.mpr off)
    have eq := row i
    rw [zero] at eq
    exact ⟨zero, by linarith only [eq,(bounds i).2], by linarith only [eq,(bounds i).1]⟩
  · rw [sumPow,pow_one,trA]
  · rw [sumPow,tr2]
  · rw [sumPow,tr3]
  · rw [sumPow,tr4]
  · rw [sumPow]
    exact tr5.1
  · rw [sumPow]
    exact tr5.2

end Deldor14.Star.Waddle39

/- The nonprincipal moment calculation for Zach Waddle's 46-vertex obstruction.
Source https://github.com/zach7036/c4-star-ramsey (2026). -/
namespace Deldor14.Star.Waddle39
open Matrix
theorem moment_traces (A D J : Matrix (Fin 46) (Fin 46) ℝ)
    (aa : A^2=(6:ℝ) • (1:Matrix _ _ ℝ)+J-D)
    (aj : A*J=(7:ℝ) • J) (dj : D*J=(3:ℝ) • J) (jd : J*D=(3:ℝ) • J)
    (jj : J*J=(46:ℝ) • J)
    (ta : A.trace=0) (td : D.trace=0) (tj : J.trace=46)
    (dd : (D^2).trace=138)
    (ad : (A*D).trace=46) (fifth : 0≤(A*D^2).trace ∧ (A*D^2).trace≤92) :
    (A^2).trace=322 ∧ (A^3).trace=276 ∧ (A^4).trace=4186 ∧
    16192≤(A^5).trace ∧ (A^5).trace≤16284 := by
  let I : Matrix (Fin 46) (Fin 46) ℝ := 1
  let P := (6:ℝ) • I - D
  have a2 : A^2=P+J := by rw [aa]; dsimp [P,I]; abel
  have p2 : P*P = (36:ℝ) • I - (12:ℝ) • D + D^2 := by
    dsimp only [P,I]
    simp only [sub_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,
        smul_sub,smul_smul,sq]
    module
  have pj : P*J=(3:ℝ) • J := by
    dsimp only [P,I]
    rw [sub_mul,Matrix.smul_mul,one_mul,dj]
    module
  have jp : J*P=(3:ℝ) • J := by
    dsimp only [P,I]
    rw [mul_sub,Matrix.mul_smul,mul_one,jd]
    module
  have a3 : A^3 = (6:ℝ) • A + (7:ℝ) • J - A*D := by
    rw [show A^3=A*A^2 by rw [←pow_succ'],aa,mul_sub,mul_add,Matrix.mul_smul,mul_one,aj]
  have a4 : A^4 = (36:ℝ) • I - (12:ℝ) • D + D^2 + (52:ℝ) • J := by
    rw [show A^4=A^2*A^2 by rw [←pow_add],a2,add_mul,mul_add,mul_add,p2,pj,jp,jj]
    module
  have a5 : A^5 = (36:ℝ) • A -(12:ℝ) • (A*D) + A*D^2 + (364:ℝ) • J := by
    rw [show A^5=A*A^4 by rw [←pow_succ'],a4,mul_add,mul_add,mul_sub]
    dsimp only [I]
    simp only [Matrix.mul_smul,mul_one,aj,smul_smul]
    norm_num
  have t1 : I.trace=46 := by simp [I]
  have t1' : (1:Matrix (Fin 46) (Fin 46) ℝ).trace=46 := t1
  simp only [aa,a3,a4,a5,trace_sub,trace_add,trace_smul,t1,t1',ta,td,tj,dd,ad,smul_eq_mul]
  obtain ⟨lo,hi⟩ := fifth
  norm_num at *
  constructor <;> linarith
end Deldor14.Star.Waddle39

/- Transfer the 46-vertex obstruction and certified lower-bound graph to the Ramsey number. -/
namespace Deldor14.Star.Waddle39
open Finset SimpleGraph Matrix ExcessOne OMA.ChenStar

theorem field_ones_adj {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (reg : ∀ i,G.degree i=d) :
    ones V ℝ * G.adjMatrix ℝ = (d:ℝ) • ones V ℝ := by
  ext i j
  rw [mul_adjMatrix_apply]
  simp [ones,reg]

theorem of_finite_obstruction
    (local_structure : ∀ (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj],
      ¬(cycleGraph 4).IsContained G → (∀ v,G.degree v=7) →
      let A := G.adjMatrix ℝ
      let D := (Deficiency.graph G).adjMatrix ℝ
      (A*D).trace=46 ∧ 0≤(A*D^2).trace ∧ (A*D^2).trace≤92)
    (spectrum : ∀ (A J : Matrix (Fin 46) (Fin 46) ℝ) (D : SimpleGraph (Fin 46))
      [DecidableRel D.Adj], (∀ i,D.degree i=3) → A.IsHermitian →
      A^2=(6:ℝ) • (1:Matrix _ _ ℝ)+J-D.adjMatrix ℝ → J*A=(7:ℝ) • J →
      J.trace=46 → A.trace=0 → (A^2).trace=322 → (A^3).trace=276 → (A^4).trace=4186 →
      (16192≤(A^5).trace ∧ (A^5).trace≤16284) → False) : number 39=46 := by
  classical
  apply Nat.le_antisymm _ Host45.lower
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra nonstar
  have minimum (v) : 7≤G.degree v := by
    have l : Gᶜ.degree v<39 := lt_of_not_ge (fun ge => nonstar (star_isContained_of_le_degree Gᶜ ge))
    rw [degree_compl,Fintype.card_fin] at l
    omega
  have reg := Deficiency.regular_of_bounds G red minimum (by decide)
  let D := Deficiency.graph G
  have dr (v) : D.degree v=3 := Deficiency.degree G red (d:=7) (e:=3) (by decide) reg v
  let A := G.adjMatrix ℝ
  let B := D.adjMatrix ℝ
  let J := ones (Fin 46) ℝ
  have aa : A^2=(6:ℝ) • (1:Matrix _ _ ℝ)+J-B := by
    simpa only [Nat.cast_ofNat,show (7:ℝ)-1=6 by norm_num] using Deficiency.adj_square G red reg
  have ta := Deficiency.adj_trace G
  have tb := Deficiency.adj_trace D
  have tj : J.trace=46 := by simp [J,ones,Matrix.trace,Matrix.diag]
  have jj : J*J=(46:ℝ) • J := by ext i j; simp [J,ones,mul_apply]
  have dd : (B^2).trace=138 := by
    have ent (i : Fin 46) : (B^2) i i=3 := by
      rw [show B=D.adjMatrix ℝ by rfl,adj_square_entries D]
      simp [common,dr]
    norm_num [trace,Matrix.diag,ent]
  obtain ⟨ad,lo,hi⟩ := local_structure G red reg
  obtain ⟨m2,m3,m4,m5⟩ := moment_traces A B J aa
    (adj_ones G reg _) (adj_ones D dr _) (field_ones_adj D dr) jj ta tb tj dd ad ⟨lo,hi⟩
  exact spectrum A J D dr (by
    change Aᴴ=A
    rw [conjTranspose_eq_transpose_of_trivial]
    exact G.isSymm_adjMatrix) aa (field_ones_adj G reg) tj ta m2 m3 m4 m5

end Deldor14.Star.Waddle39

namespace Deldor14.Star.Waddle39
theorem ramsey_star_39 : Deldor14.Star.number 39=46 :=
  of_finite_obstruction (@traces_46) (@spectral_impossible)
end Deldor14.Star.Waddle39


/- For R(C₄,K₁,₅₁) the following Lean development formalizes the spectral
and cyclotomic argument of Zach Waddle, The Ramsey number R(C₄,K₁,₅₁)
(2026). The universal tables below check all cycle lengths from 1 to 59.
The lower bound also has an independent finite-field construction.
Original mathematical argument (CC BY 4.0), graph data and code (MIT):
https://github.com/zach7036/c4-star-ramsey/tree/86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33
Formalization for Left to Solve by Deldor14. -/
/- Affine points with nonzero first coordinate in characteristic two.
Adjoining any chosen points at infinity preserves the minimum degree q−1. -/
namespace Deldor14.Star.UnitsRows
open Finset SimpleGraph
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] {s : ℕ}

abbrev Vertex (F : Type*) [Field F] (s : ℕ) := (Fˣ × F) ⊕ Fin s

def point (r : Fin s ↪ Fˣ) : Vertex F s → Point F
  | .inl (a,b) => .aff a b
  | .inr i => .inf (r i)

theorem injective_point (r : Fin s ↪ Fˣ) : Function.Injective (point r) := by
  rintro (⟨a,b⟩|i) (⟨c,d⟩|j) e <;> simp_all [point]
  · exact Units.ext e.1
  · exact r.injective (Units.ext e)

def host (r : Fin s ↪ Fˣ) := Point.graph.comap (point r)

theorem no_square (r : Fin s ↪ Fˣ) : ¬(cycleGraph 4).IsContained (host r) := by
  have sub : (host r).IsContained Point.graph := ⟨⟨⟨point r,fun h=>h⟩,injective_point r⟩⟩
  exact fun bad=>Point.no_square (bad.trans sub)

def neighbor (r : Fin s ↪ Fˣ) (v : Vertex F s) (j : Fˣ) : Vertex F s :=
  match v with
  | .inl (a,b) => .inl (j,(a:F)*j-b)
  | .inr i => .inl (r i,(j:F))

theorem minimum (r : Fin s ↪ Fˣ) [DecidableRel (host r).Adj] (v : Vertex F s) :
    Fintype.card F-1 ≤ (host r).degree v := by
  have inj : Function.Injective (neighbor r v) := by
    intro j k h
    cases v with
    | inl ax => obtain ⟨a,b⟩ := ax; exact (Prod.mk.inj (Sum.inl.inj h)).1
    | inr i => exact Units.ext (Prod.mk.inj (Sum.inl.inj h)).2
  have adj (j : Fˣ) : (host r).Adj v (neighbor r v j) := by
    cases v with
    | inl ax =>
      obtain ⟨a,b⟩ := ax
      have no : ¬((a:F)=(j:F) ∧ b=(a:F)*j-b) := by
        rintro ⟨e,h⟩
        have t : (a:F)*(a:F)=b+b := by rw [e] at h ⊢; linear_combination -h
        rw [CharTwo.add_self_eq_zero] at t
        exact a.ne_zero (mul_self_eq_zero.mp t)
      simp [host,Point.graph,Point.inc,neighbor,point,no]
    | inr i => simp [host,Point.graph,Point.inc,neighbor,point]
  let f (j : Fˣ) : ↥((host r).neighborFinset v) := ⟨neighbor r v j,(mem_neighborFinset ..).mpr (adj j)⟩
  have fi : Function.Injective f := fun _ _ e=>inj (congrArg Subtype.val e)
  simpa only [Fintype.card_units,Fintype.card_coe,card_neighborFinset_eq_degree] using
    Fintype.card_le_of_injective f fi

theorem lower (F : Type*) [Field F] [Fintype F] [CharP F 2] {s : ℕ} (room : s≤Fintype.card F-1) :
    (Fintype.card F-1)^2+s+Fintype.card F ≤ number ((Fintype.card F-1)^2+s) := by
  classical
  let q := Fintype.card F
  let e := (Fintype.equivFin Fˣ).symm.toEmbedding
  let r : Fin s ↪ Fˣ := (Fin.castLEEmb (by simpa only [Fintype.card_units] using room)).trans e
  let G := host r
  have size : Fintype.card (Vertex F s) = (q-1)*q+s := by simp [Vertex,Fintype.card_units,q]
  have two : 2≤q := Fintype.one_lt_card
  have key : (q-1)*q=(q-1)^2+(q-1) := by
    have h : q-1+1=q := by omega
    calc
      (q-1)*q = (q-1)*(q-1+1) := by conv_lhs => rw [←h]; simp only [Nat.add_sub_cancel]
      _ = _ := by ring
  have positive : 0<(q-1)^2 := by exact pow_pos (by omega) _
  have blue : ∀ v,Gᶜ.degree v < (q-1)^2+s := by
    intro v
    have d := minimum r v
    change q-1≤G.degree v at d
    rw [degree_compl,size,key]
    omega
  have lb : Fintype.card (Vertex F s)<number ((q-1)^2+s) := lower_from_host G (no_square r) blue
  rw [size,key] at lb
  change (q-1)^2+s+q ≤ number ((q-1)^2+s)
  omega

theorem power_two_lower {m s : ℕ} (hm : m≠0) (room : s≤2^m-1) :
    (2^m-1)^2+s+2^m ≤ number ((2^m-1)^2+s) := by
  letI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 m)=2^m := by rw [← Nat.card_eq_fintype_card,GaloisField.card 2 m hm]
  simpa only [hq] using lower (GaloisField 2 m) (s:=s) (by simpa only [hq] using room)

theorem lower_51 : 59≤number 51 := by
  simpa using power_two_lower (m:=3) (s:=2) (by decide) (by decide)

end Deldor14.Star.UnitsRows

/- In a finite 2-regular graph a non-backtracking walk can repeat a vertex
only in the same direction. The period of its ordered edges is accordingly
bounded by the number of vertices. -/
namespace Deldor14.Star.Waddle51
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem complete_pair (reg : ∀ i, G.degree i = 2) {a b : V} (h : G.Adj a b) :
    ∃ c, c ≠ a ∧ G.neighborFinset b = {a,c} := by
  classical
  have mem := (G.mem_neighborFinset _ _).mpr h.symm
  have card : ((G.neighborFinset b).erase a).card = 1 := by
    rw [card_erase_of_mem mem,card_neighborFinset_eq_degree,reg]
  obtain ⟨c,e⟩ := card_eq_one.mp card
  have cm : c ∈ (G.neighborFinset b).erase a := by rw [e]; simp
  exact ⟨c,(mem_erase.mp cm).1,by rw [←e,insert_erase mem]⟩

private def vertexSeq (s : V → V → V) (a b : V) : ℕ → V
  | 0 => a
  | 1 => b
  | n+2 => s (vertexSeq s a b n) (vertexSeq s a b (n+1))

private theorem no_reverse (p : ℕ → V) (edge : ∀ n, G.Adj (p n) (p (n+1)))
    (back : ∀ n, p (n+2) ≠ p n)
    (row : ∀ n, G.neighborFinset (p (n+1)) = {p n,p (n+2)}) :
    ∀ k t : ℕ, ¬ (p t = p (t+k+1) ∧ p (t+1) = p (t+k)) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => intro t eq; exact (edge t).ne (by simpa using eq.1)
  | one => intro t eq; exact back t (by simpa [Nat.add_assoc] using eq.1.symm)
  | more k ih _ =>
    intro t h
    have end_eq : p t = p ((t+k+1)+2) := by convert h.1 using 2 <;> omega
    have mid_eq : p (t+1) = p ((t+k+1)+1) := by convert h.2 using 2 <;> omega
    have m := (G.mem_neighborFinset _ _).mpr (edge (t+1))
    rw [mid_eq,row (t+k+1),mem_insert,mem_singleton] at m
    have prev : p (t+2) = p (t+k+1) := m.resolve_right (fun e => back t (e.trans end_eq.symm))
    apply ih (t+1)
    exact ⟨by convert mid_eq using 2 <;> omega,by convert prev using 2 <;> omega⟩

theorem closed_walk (reg : ∀ i, G.degree i = 2) (a : V) :
    ∃ (p : ℕ → V) (i d : ℕ), p 0 = a ∧ 0 < d ∧ d ≤ Fintype.card V ∧
      p i = p (i+d) ∧ p (i+1) = p (i+d+1) ∧
      ∀ n, p (n+2) ≠ p n ∧ G.neighborFinset (p (n+1)) = {p n,p (n+2)} := by
  classical
  let s (x y : V) := if h : G.Adj x y then (complete_pair G reg h).choose else x
  have step {x y : V} (xy : G.Adj x y) :
      s x y ≠ x ∧ G.neighborFinset y = {x,s x y} := by
    simpa only [s,dif_pos xy] using (complete_pair G reg xy).choose_spec
  obtain ⟨b,bm⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset a).card by
    rw [card_neighborFinset_eq_degree,reg]; decide)
  let p := vertexSeq s a b
  have advance (n : ℕ) : p (n+2) = s (p n) (p (n+1)) := rfl
  have edge (n : ℕ) : G.Adj (p n) (p (n+1)) := by
    induction n with
    | zero => exact (G.mem_neighborFinset _ _).mp bm
    | succ n ih =>
      apply (G.mem_neighborFinset _ _).mp
      rw [(step ih).2,advance]
      simp
  have back (n : ℕ) : p (n+2) ≠ p n := (step (edge n)).1
  have row (n : ℕ) : G.neighborFinset (p (n+1)) = {p n,p (n+2)} := (step (edge n)).2
  obtain ⟨x,y,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun z : Fin (Fintype.card V + 1) => p z.val) (by simp)
  have coll : ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card V ∧ p i = p j := by
    rcases lt_or_gt_of_ne ne with lt | gt
    · exact ⟨x.val,y.val,lt,by have := y.isLt; omega,eq⟩
    · exact ⟨y.val,x.val,gt,by have := x.isLt; omega,eq.symm⟩
  obtain ⟨i,j,lt,lim,dup⟩ := coll
  obtain ⟨k,hj⟩ : ∃ k, j = i+k+1 := ⟨j-i-1,by omega⟩
  subst j
  have mem := (G.mem_neighborFinset _ _).mpr (edge i)
  rw [dup,row (i+k),mem_insert,mem_singleton] at mem
  have same := mem.resolve_left (fun e => no_reverse G p edge back row k i ⟨dup,e⟩)
  exact ⟨p,i,k+1,rfl,by omega,by omega,by convert dup using 2 <;> omega,
    by convert same using 2 <;> omega,fun n => ⟨back n,row n⟩⟩

end Deldor14.Star.Waddle51

/- Vieta–Lucas polynomials in a scalar recurrence on a periodic walk. -/
namespace Deldor14.Star.Waddle51

def vieta (μ : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => μ
  | n+2 => μ * vieta μ (n+1) - vieta μ n

private theorem double_shift (μ : ℝ) (x : ℕ → ℝ)
    (rec : ∀ n, x n + x (n+2) = μ*x (n+1)) :
    ∀ k n, vieta μ k * x (n+k) = x n + x (n+k+k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => intro n; simp [vieta]; ring
  | one => intro n; simpa [vieta,Nat.add_assoc] using (rec n).symm
  | more k small big =>
    intro n
    have r : μ*x (n+(k+2)) = x (n+(k+1)) + x ((n+2)+(k+1)) := by
      convert (rec (n+k+1)).symm using 2 <;> congr 1 <;> omega
    have h := big n
    have h' := big (n+2)
    have h'' := small (n+2)
    have re1 : (n+2)+k = n+(k+2) := by omega
    have re2 : (n+2)+k+k = n+(k+1)+(k+1) := by omega
    have re3 : (n+2)+(k+1)+(k+1) = n+(k+2)+(k+2) := by omega
    rw [re2,re1] at h''
    rw [re3] at h'
    change (μ*vieta μ (k+1)-vieta μ k)*x (n+(k+2)) = _
    linear_combination vieta μ (k+1) * r + h + h' - h''

theorem period_value (μ : ℝ) (x : ℕ → ℝ) (nz : x 0 ≠ 0)
    (rec : ∀ n, x n + x (n+2) = μ*x (n+1))
    (i d : ℕ) (at_i : x i = x (i+d)) (at_succ : x (i+1) = x (i+d+1)) :
    vieta μ d = 2 := by
  let z (n : ℕ) := x n - x (n+d)
  have rz (n : ℕ) : z n + z (n+2) = μ*z (n+1) := by
    dsimp [z]
    have r := rec (n+d)
    rw [show n+d+2 = n+2+d by omega,show n+d+1 = n+1+d by omega] at r
    linear_combination rec n - r
  have back (n : ℕ) : z n = 0 → z (n+1) = 0 → z 0 = 0 ∧ z 1 = 0 := by
    induction n with
    | zero => exact fun h h' => ⟨h,h'⟩
    | succ n ih =>
      intro h h'
      apply ih _ h
      have r := rz n
      rw [h,h'] at r
      linarith
  have start := back i (sub_eq_zero.mpr at_i) (sub_eq_zero.mpr (by
    convert at_succ using 2 <;> omega))
  have zero (n : ℕ) : z n = 0 := by
    induction n using Nat.twoStepInduction with
    | zero => exact start.1
    | one => exact start.2
    | more n h h' =>
      have r := rz n
      rw [h,h'] at r
      linarith
  have shift (n : ℕ) : x (n+d) = x n := (sub_eq_zero.mp (zero n)).symm
  have h := double_shift μ x rec d 0
  rw [shift (0+d),shift 0] at h
  exact (mul_right_cancel₀ nz) (by linarith : vieta μ d*x 0 = 2*x 0)

end Deldor14.Star.Waddle51

/-
The spectrum of a finite 2-regular graph obeys a Vieta–Lucas equation
whose degree is at most its number of vertices. This implements the
cycle observation in §3 of Zach Waddle, *The Ramsey number R(C₄,K₁,₅₁)*
(2026), © Zach Waddle, CC BY 4.0. Lean formalization by Deldor14.
https://github.com/zach7036/c4-star-ramsey/blob/86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33/R_C4_K1_51.md
https://creativecommons.org/licenses/by/4.0/
-/
namespace Deldor14.Star.Waddle51
open Matrix Finset SimpleGraph

theorem cycle_spectrum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (reg : ∀ i, G.degree i = 2)
    (μ : ℝ) (x : V → ℝ) (nz : x ≠ 0) (eig : G.adjMatrix ℝ *ᵥ x = μ • x) :
    ∃ d : ℕ, 0 < d ∧ d ≤ Fintype.card V ∧ vieta μ d = 2 := by
  classical
  obtain ⟨a,ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra! h
    exact nz (funext h)
  obtain ⟨p,i,d,pa,pos,le,repeat0,repeat1,rows⟩ := closed_walk G reg a
  refine ⟨d,pos,le,period_value μ (fun n => x (p n)) (pa ▸ ha) ?_ i d
    (congrArg x repeat0) (congrArg x repeat1)⟩
  intro n
  have eq := congrFun eig (p (n+1))
  rw [G.adjMatrix_mulVec_apply,(rows n).2] at eq
  simpa [((rows n).1).symm] using eq

end Deldor14.Star.Waddle51

/- Real eigenvalues of an adjacency matrix with a 2-regular deficiency graph. -/
namespace Deldor14.Star.Waddle51
open Finset Matrix Unitary SimpleGraph

private theorem lower_diag {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (reg : ∀ x, G.degree x = 2) (U : Matrix.unitaryGroup V ℝ) (i : V) :
    -2 ≤ (conjStarAlgAut ℝ _ (star U) (G.adjMatrix ℝ)) i i := by
  let e := conjStarAlgAut ℝ _ (star U)
  have deg : G.degMatrix ℝ = (2:ℝ) • (1:Matrix V V ℝ) := by
    ext i j
    simp [degMatrix,Matrix.smul_apply,Matrix.one_apply,diagonal_apply,reg]
  have plus := (Waddle39.signless_pos G).mul_mul_conjTranspose_same
    ((star U : Matrix.unitaryGroup V ℝ) : Matrix V V ℝ)
  have p : 0 ≤ (e (G.degMatrix ℝ + G.adjMatrix ℝ)) i i := plus.diag_nonneg
  rw [deg,map_add,map_smul,map_one,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,
    smul_eq_mul,mul_one] at p
  change -2 ≤ e (G.adjMatrix ℝ) i i
  linarith

private theorem transfer {V : Type*} [Fintype V] [DecidableEq V]
    (A J : Matrix V V ℝ) (D : SimpleGraph V) [DecidableRel D.Adj] (x : V → ℝ)
    (θ : ℝ) (eig : A *ᵥ x = θ • x) (off : θ ≠ 8) (rightJ : J*A = (8:ℝ) • J)
    (square : A^2 = (7:ℝ) • 1 + J - D.adjMatrix ℝ) :
    D.adjMatrix ℝ *ᵥ x = (7-θ^2) • x := by
  have jr := congrArg (fun B : Matrix V V ℝ => B *ᵥ x) rightJ
  change (J*A) *ᵥ x = ((8:ℝ) • J) *ᵥ x at jr
  rw [←mulVec_mulVec,eig,mulVec_smul,smul_mulVec] at jr
  have jzero : J *ᵥ x = 0 := by
    ext i
    have eq := congrFun jr i
    change θ * (J *ᵥ x) i = 8 * (J *ᵥ x) i at eq
    have v : (θ-8) * (J *ᵥ x) i = 0 := by linear_combination eq
    exact (mul_eq_zero.mp v).resolve_left (sub_ne_zero.mpr off)
  have aq := congrArg (fun B : Matrix V V ℝ => B *ᵥ x) square
  change (A^2) *ᵥ x = ((7:ℝ) • 1 + J - D.adjMatrix ℝ) *ᵥ x at aq
  rw [sq,←mulVec_mulVec,eig,mulVec_smul,eig,sub_mulVec,add_mulVec,smul_mulVec,one_mulVec,jzero,add_zero] at aq
  ext i
  have entry := congrFun aq i
  change θ*(θ*x i) = 7*x i - (D.adjMatrix ℝ *ᵥ x) i at entry
  change (D.adjMatrix ℝ *ᵥ x) i = (7-θ^2)*x i
  linear_combination entry

theorem spectral_rows (A J : Matrix (Fin 59) (Fin 59) ℝ) (D : SimpleGraph (Fin 59))
    [DecidableRel D.Adj] (reg : ∀ i, D.degree i = 2) (herm : A.IsHermitian)
    (square : A^2 = (7:ℝ) • 1 + J - D.adjMatrix ℝ)
    (rightJ : J*A = (8:ℝ) • J) (trJ : J.trace = 59) :
    ∃ t : Fin 59, herm.eigenvalues t = 8 ∧ (∀ i, herm.eigenvalues i = 8 → i = t) ∧
      ∀ i, herm.eigenvalues i ≠ 8 → ∃ d : ℕ, 0 < d ∧ d ≤ 59 ∧
        vieta (7 - (herm.eigenvalues i)^2) d = 2 := by
  classical
  let f := herm.eigenvalues
  let e := conjStarAlgAut ℝ _ (star herm.eigenvectorUnitary)
  let j (i : Fin 59) := (e J) i i
  have diagA : e A = diagonal f := by
    simpa [e,f,Function.comp_def] using herm.conjStarAlgAut_star_eigenvectorUnitary
  have traceConj (B : Matrix (Fin 59) (Fin 59) ℝ) : (e B).trace = B.trace := by
    dsimp only [e]
    rw [conjStarAlgAut_apply,trace_mul_cycle,coe_star_mul_self,one_mul]
  have jSum : ∑ i, j i = 59 := (traceConj J).trans trJ
  have relation (i : Fin 59) : j i * (f i - 8) = 0 := by
    have eq := congrArg e rightJ
    rw [map_mul,map_smul,diagA] at eq
    have entry := congrArg (fun B : Matrix (Fin 59) (Fin 59) ℝ => B i i) eq
    simp only [mul_diagonal,Matrix.smul_apply,smul_eq_mul] at entry
    dsimp only [j]
    linear_combination entry
  have off (i : Fin 59) (h : f i ≠ 8) : j i = 0 :=
    (mul_eq_zero.mp (relation i)).resolve_right (sub_ne_zero.mpr h)
  have near (i : Fin 59) (h : f i = 8) : 55 ≤ j i := by
    have eq := congrArg e square
    rw [map_pow,map_sub,map_add,map_smul,map_one,diagA,diagonal_pow] at eq
    have entry := congrArg (fun B : Matrix (Fin 59) (Fin 59) ℝ => B i i) eq
    simp only [diagonal_apply_eq,Pi.pow_apply,h,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
      Matrix.one_apply_eq,smul_eq_mul,mul_one] at entry
    have lo : -2 ≤ (e (D.adjMatrix ℝ)) i i := lower_diag D reg herm.eigenvectorUnitary i
    dsimp only [j]
    linarith only [lo,entry]
  let top := univ.filter (fun i => f i = 8)
  have row (i : Fin 59) : (if f i = 8 then (55:ℝ) else 0) ≤ j i := by
    split
    · exact near i ‹_›
    · rw [off i ‹_›]
  have upper := Finset.sum_le_sum (s:=univ) (fun i _ => row i)
  rw [jSum] at upper
  have tally : (top.card:ℝ)*55 ≤ 59 := by simpa [top,Finset.sum_ite] using upper
  have card_le : top.card ≤ 1 := by
    by_contra! h
    have hn : (2:ℝ) ≤ top.card := by exact_mod_cast h
    linarith
  have nonempty : top.Nonempty := by
    by_contra! empty
    have zero (i : Fin 59) : j i = 0 := by
      apply off i
      intro hi
      have h : i ∈ top := mem_filter.mpr ⟨mem_univ _,hi⟩
      simp [empty] at h
    simp [zero] at jSum
  obtain ⟨t,ht⟩ := Finset.card_eq_one.mp (le_antisymm card_le (Finset.card_pos.mpr nonempty))
  refine ⟨t,(mem_filter.mp (show t ∈ top by rw [ht]; simp)).2,?_,?_⟩
  · intro i fi
    have m : i ∈ top := mem_filter.mpr ⟨mem_univ _,fi⟩
    rwa [ht,mem_singleton] at m
  · intro i fi
    let x := (herm.eigenvectorBasis i : Fin 59 → ℝ)
    have nonzero : x ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 (herm.eigenvectorBasis.orthonormal.ne_zero i)
    have eig := transfer A J D x (herm.eigenvalues i) (herm.mulVec_eigenvectorBasis i) fi rightJ square
    simpa using cycle_spectrum D reg _ x nonzero eig

end Deldor14.Star.Waddle51

/- Deflation of the unique principal eigenvalue over the rationals. -/
namespace Deldor14.Star.Waddle51
open Matrix Finset Polynomial SimpleGraph

theorem rational_factor (A J : Matrix (Fin 59) (Fin 59) ℝ) (D : SimpleGraph (Fin 59))
    [DecidableRel D.Adj] (reg : ∀ i, D.degree i = 2) (herm : A.IsHermitian)
    (square : A^2 = (7:ℝ) • 1 + J - D.adjMatrix ℝ)
    (rightJ : J*A = (8:ℝ) • J) (trJ : J.trace = 59)
    (F : ℚ[X]) (monic : F.Monic) (rational : F.map (algebraMap ℚ ℝ) = A.charpoly) :
    ∃ Q : ℚ[X], Q.Monic ∧ F = (X - C 8)*Q ∧ Q.eval 8 ≠ 0 ∧
      (F.map (algebraMap ℚ ℝ)).Splits ∧
      ∀ θ : ℝ, (F.map (algebraMap ℚ ℝ)).IsRoot θ → θ ≠ 8 →
        ∃ d : ℕ, 0 < d ∧ d ≤ 59 ∧ vieta (7-θ^2) d = 2 := by
  classical
  obtain ⟨t,ft,unique,other⟩ := spectral_rows A J D reg herm square rightJ trJ
  let f := herm.eigenvalues
  let S := univ.erase t
  let g (i : Fin 59) := (X - C (f i) : ℝ[X])
  have full : F.map (algebraMap ℚ ℝ) = ∏ i, g i := by
    rw [rational]
    simpa [g,f] using herm.charpoly_eq
  have fact : F.map (algebraMap ℚ ℝ) = (X-C 8) * ∏ i ∈ S, g i := by
    rw [full,←Finset.mul_prod_erase univ g (mem_univ t)]
    simp only [g, f, ft, S]
  have root8 : F.IsRoot (8:ℚ) := by
    have real8 : (F.map (algebraMap ℚ ℝ)).eval (8:ℝ) = 0 := by rw [fact]; simp
    apply (algebraMap ℚ ℝ).injective
    change algebraMap ℚ ℝ (F.eval 8) = _
    rw [map_zero,←eval_map_apply]
    simpa using real8
  obtain ⟨Q,eq⟩ := Polynomial.dvd_iff_isRoot.mpr root8
  have small : Q.map (algebraMap ℚ ℝ) = ∏ i ∈ S, g i := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero (8:ℝ))
    conv_lhs => rw [show (X-C 8 : ℝ[X]) =
      (X-C 8 : ℚ[X]).map (algebraMap ℚ ℝ) by simp]
    rw [←Polynomial.map_mul,←eq,fact]
  refine ⟨Q,(monic_X_sub_C (8:ℚ)).of_mul_monic_left (eq ▸ monic),eq,?_,rational ▸ herm.splits_charpoly,?_⟩
  · intro h
    have hz := congrArg (algebraMap ℚ ℝ) h
    rw [map_zero,←eval_map_apply] at hz
    have zero : (Q.map (algebraMap ℚ ℝ)).eval (8:ℝ) = 0 := by simpa using hz
    rw [small,eval_prod,Finset.prod_eq_zero_iff] at zero
    obtain ⟨i,hi,vanish⟩ := zero
    have fi : f i = 8 := by
      simp only [g,eval_sub,eval_X,eval_C] at vanish
      linarith
    exact (mem_erase.mp hi).1 (unique i fi)
  · intro θ root ne
    rw [full,IsRoot,eval_prod,Finset.prod_eq_zero_iff] at root
    obtain ⟨i,_,hi⟩ := root
    have eqf : θ = f i := by exact sub_eq_zero.mp (by simpa [g] using hi)
    subst θ
    exact other i ne

end Deldor14.Star.Waddle51

/- Transfer the 59-vertex obstruction and Waddle's verified 58-vertex graph
to the Ramsey number for the star with 51 leaves. -/
namespace Deldor14.Star.Waddle51
open Finset SimpleGraph Matrix Polynomial ExcessOne OMA.ChenStar

theorem star_51_of_classification
    (cyclo : ∀ (θ : ℝ) {d : ℕ}, 0 < d → d ≤ 59 → vieta (7-θ^2) d = 2 →
      θ = 3 ∨ θ = -3 ∨ (minpoly ℚ θ).comp (-X) = minpoly ℚ θ)
    (obstruction : ∀ {F Q : ℚ[X]}, Q.Monic → F = (X-C 8)*Q → Q.eval 8 ≠ 0 →
      (F.map (algebraMap ℚ ℝ)).Splits →
      (∀ θ : ℝ, (F.map (algebraMap ℚ ℝ)).IsRoot θ → θ ≠ 8 →
        θ = 3 ∨ θ = -3 ∨ (minpoly ℚ θ).comp (-X) = minpoly ℚ θ) → F.nextCoeff ≠ 0) :
    Deldor14.Star.number 51 = 59 := by
  classical
  apply Nat.le_antisymm _ Waddle39.Host58.lower
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra nonstar
  have minimum (v) : 8 ≤ G.degree v := by
    have l : Gᶜ.degree v < 51 :=
      lt_of_not_ge (fun ge => nonstar (star_isContained_of_le_degree Gᶜ ge))
    rw [degree_compl,Fintype.card_fin] at l
    omega
  have reg := Deficiency.regular_of_bounds G red minimum (by decide)
  let D := Deficiency.graph G
  have dr (v) : D.degree v = 2 := Deficiency.degree G red (d:=8) (e:=2) (by decide) reg v
  let A := G.adjMatrix ℝ
  let J := ones (Fin 59) ℝ
  have aa : A^2 = (7:ℝ) • 1 + J - D.adjMatrix ℝ := by
    simpa only [Nat.cast_ofNat,show (8:ℝ)-1=7 by norm_num] using Deficiency.adj_square G red reg
  have rightJ : J*A = (8:ℝ) • J := by
    ext i j
    change (ones (Fin 59) ℝ * G.adjMatrix ℝ) i j = _
    rw [mul_adjMatrix_apply]
    simp [J,ones,reg]
  have trJ : J.trace = 59 := by simp [J,ones,Matrix.trace,Matrix.diag]
  have herm : A.IsHermitian := by
    change Aᴴ = A
    rw [conjTranspose_eq_transpose_of_trivial]
    exact G.isSymm_adjMatrix
  let F := (G.adjMatrix ℚ).charpoly
  have rational : F.map (algebraMap ℚ ℝ) = A.charpoly := by
    dsimp only [F]
    rw [←Matrix.charpoly_map]
    apply congrArg Matrix.charpoly
    ext i j
    by_cases h : G.Adj i j <;> simp [A,Matrix.map_apply,adjMatrix_apply,h]
  obtain ⟨Q,hm,eq,h8,split,roots⟩ := rational_factor A J D dr herm aa rightJ trJ F
    (Matrix.charpoly_monic _) rational
  have no := obstruction hm eq h8 split (fun θ hθ ne => by
    obtain ⟨d,pos,le,h⟩ := roots θ hθ ne
    exact cyclo θ pos le h)
  apply no
  have ht := Matrix.trace_eq_neg_charpoly_nextCoeff (G.adjMatrix ℚ)
  rw [G.trace_adjMatrix ℚ] at ht
  dsimp only [F]
  linarith

end Deldor14.Star.Waddle51

/- Reflected integer polynomial arithmetic for the finite cyclotomic norm certificates. -/
namespace Deldor14.Star.Cyclo51
open Polynomial
def val {R : Type*} [CommRing R] (x : R) : List ℤ → R
  | [] => 0
  | a::as => (a:R)+x*val x as

def plus : List ℤ → List ℤ → List ℤ
  | [],b => b
  | a,[] => a
  | a::as,b::bs => (a+b)::plus as bs

def shift : List ℤ → List ℤ
  | [] => []
  | a::as => 0::a::as

def times : List ℤ → List ℤ → List ℤ
  | [],_ => []
  | a::as,b => plus (b.map (a*·)) (shift (times as b))

def substAt (p q : List ℤ) : List ℤ :=
  p.foldr (fun a tail => plus [a] (times q tail)) []

theorem val_plus {R : Type*} [CommRing R] (x:R) (a b : List ℤ) :
    val x (plus a b) = val x a + val x b := by
  induction a generalizing b with
  | nil => simp [plus,val]
  | cons c cs ih =>
    cases b with
    | nil => simp [plus,val]
    | cons d ds => simp [plus,val,ih]; ring

theorem val_scale {R : Type*} [CommRing R] (x : R) (c : ℤ) (p : List ℤ) :
    val x (p.map (c*·)) = (c:R)*val x p := by
  induction p with
  | nil => simp [val]
  | cons a as ih => simp [val,ih]; ring

theorem val_shift {R : Type*} [CommRing R] (x:R) (p : List ℤ) :
    val x (shift p) = x*val x p := by cases p <;> simp [shift,val]

theorem val_times {R : Type*} [CommRing R] (x:R) (a b : List ℤ) :
    val x (times a b) = val x a * val x b := by
  induction a with
  | nil => simp [times,val]
  | cons c cs ih =>
    rw [times,val_plus,val_shift,val_scale,ih,val]
    ring

theorem val_subst {R : Type*} [CommRing R] (x:R) (p q : List ℤ) :
    val x (substAt p q) = val (val x q) p := by
  induction p with
  | nil => simp [substAt,val]
  | cons a as ih =>
    change val x (plus [a] (times q (substAt as q))) = _
    simp [val_plus,val_times,ih,val]

def vs : ℕ → List ℤ
  | 0 => [2]
  | 1 => [0,1]
  | n+2 => plus (shift (vs (n+1))) ((vs n).map ((-1)*·))

theorem val_vs {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    val x (vs (n+2))=x*val x (vs (n+1))-val x (vs n) := by
  rw [vs,val_plus,val_shift,val_scale]
  push_cast
  ring

theorem vs_primitive (z : ℂ) (nz : z≠0) (n : ℕ) :
    val (z+z⁻¹) (vs n)=z^n+(z⁻¹)^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [vs,val]; norm_num
  | one => simp [vs,val]
  | more n ih ih' =>
    rw [val_vs,ih',ih]
    simp only [pow_succ]
    field_simp
    ring

def prodCodes : List (List ℤ) → List ℤ
  | [] => [1]
  | c::cs => times c (prodCodes cs)

theorem val_prod {R : Type*} [CommRing R] (x:R) (cs : List (List ℤ)) :
    val x (prodCodes cs) = (cs.map (val x)).prod := by
  induction cs with
  | nil => simp [val,prodCodes]
  | cons a as ih => simp [prodCodes,val_times,ih]

noncomputable def poly (p : List ℤ) : ℚ[X] := val X p

theorem aeval_poly {R : Type*} [Field R] [Algebra ℚ R] (x:R) (p : List ℤ) :
    aeval x (poly p)=val x p := by
  induction p with
  | nil => simp [poly,val]
  | cons a as ih =>
    change aeval x ((a:ℚ[X])+X*poly as)=_
    simp only [map_add,map_mul,aeval_X,map_intCast,ih,val]

theorem monic_code (p : List ℤ) : (poly (p++[1])).Monic ∧ (poly (p++[1])).natDegree=p.length := by
  induction p with
  | nil => simp [poly,val]
  | cons a as ih =>
    change (((a:ℚ[X])+X*poly (as++[1])).Monic ∧ ((a:ℚ[X])+X*poly (as++[1])).natDegree=as.length+1)
    have high : (X * poly (as++[1])).natDegree=as.length+1 := by rw [natDegree_X_mul ih.1.ne_zero,ih.2]
    have lt : (a:ℚ[X]).degree < (X * poly (as++[1])).degree := by
      have ac : (a:ℚ[X])=C (a:ℚ) := by simp
      rw [ac,degree_eq_natDegree (mul_ne_zero X_ne_zero ih.1.ne_zero),high]
      exact degree_C_le.trans_lt (by exact_mod_cast Nat.succ_pos _)
    exact ⟨(monic_X.mul ih.1).add_of_right lt, by
      rw [natDegree_add_eq_right_of_degree_lt lt,high]⟩

end Deldor14.Star.Cyclo51

/- Finite data for the real cyclotomic polynomials of orders up to 59.
Inspired by the square-norm certificates of Zach Waddle. The kernel checks each
polynomial product, shift, degree, and non-square norm from integer lists. -/
namespace Deldor14.Star.Cyclo51
open Polynomial
set_option maxHeartbeats 4000000 in
def rows : Array (List ℤ) := #[
  [],
  [-2],
  [2],
  [1],
  [0],
  [-1, 1],
  [-1],
  [-1, -2, 1],
  [-2, 0],
  [1, -3, 0],
  [-1, -1],
  [1, 3, -3, -4, 1],
  [-3, 0],
  [-1, 3, 6, -4, -5, 1],
  [1, -2, -1],
  [1, 4, -4, -1],
  [2, 0, -4, 0],
  [1, -4, -10, 10, 15, -6, -7, 1],
  [-1, -3, 0],
  [1, 5, -10, -20, 15, 21, -7, -8, 1],
  [5, 0, -5, 0],
  [1, -8, 8, 6, -6, -1],
  [-1, 3, 3, -4, -1],
  [-1, -6, 15, 35, -35, -56, 28, 36, -9, -10, 1],
  [1, 0, -4, 0],
  [-1, 5, 25, -5, -50, 1, 35, 0, -10, 0],
  [-1, -3, 6, 4, -5, -1],
  [1, 9, 0, -30, 0, 27, 0, -9, 0],
  [-7, 0, 14, 0, -7, 0],
  [-1, 7, 28, -56, -126, 126, 210, -120, -165, 55, 66, -12, -13, 1],
  [1, -4, -4, 1],
  [-1, -8, 28, 84, -126, -252, 210, 330, -165, -220, 66, 78, -13, -14, 1],
  [2, 0, -16, 0, 20, 0, -8, 0],
  [1, -12, 12, 43, -43, -34, 34, 10, -10, -1],
  [1, 4, -10, -10, 15, 6, -7, -1],
  [1, 8, -40, -46, 110, 71, -113, -43, 54, 11, -12, -1],
  [-3, 0, 9, 0, -6, 0],
  [-1, 9, 45, -120, -330, 462, 924, -792, -1287, 715, 1001, -364, -455, 105, 120, -16, -17, 1],
  [-1, 5, 10, -20, -15, 21, 7, -8, -1],
  [1, 12, -12, -79, 79, 103, -103, -53, 53, 12, -12, -1],
  [1, 0, -12, 0, 19, 0, -8, 0],
  [1, -10, -55, 165, 495, -792, -1716, 1716, 3003, -2002, -3003, 1365, 1820, -560, -680, 136, 153, -18, -19, 1],
  [1, 8, 8, -6, -6, 1],
  [1, 11, -55, -220, 495, 1287, -1716, -3432, 3003, 5005, -3003, -4368, 1820, 2380, -680, -816, 153, 171, -19, -20, 1],
  [-11, 0, 55, 0, -77, 0, 44, 0, -11, 0],
  [1, -12, -36, 31, 105, -27, -112, 9, 54, -1, -12, 0],
  [1, -6, -15, 35, 35, -56, -28, 36, 9, -10, -1],
  [-1, -12, 66, 286, -715, -2002, 3003, 6435, -6435, -11440, 8008, 12376, -6188, -8568, 3060, 3876, -969, -1140, 190, 210, -21, -22, 1],
  [1, 0, -16, 0, 20, 0, -8, 0],
  [-1, 14, 49, -371, -196, 2072, 294, -5147, -210, 7007, 77, -5733, -14, 2940, 1, -952, 0, 189, 0, -21, 0],
  [-1, -5, 25, 5, -50, -1, 35, 0, -10, 0],
  [1, 16, -16, -188, 188, 526, -526, -596, 596, 339, -339, -103, 103, 16, -16, -1],
  [13, 0, -91, 0, 182, 0, -156, 0, 65, 0, -13, 0],
  [-1, 13, 91, -364, -1365, 3003, 8008, -11440, -24310, 24310, 43758, -31824, -50388, 27132, 38760, -15504, -20349, 5985, 7315, -1540, -1771, 253, 276, -24, -25, 1],
  [-1, 9, 0, -30, 0, 27, 0, -9, 0],
  [1, 12, -108, -151, 951, 877, -2891, -2058, 4489, 2442, -4080, -1639, 2289, 650, -801, -151, 170, 19, -20, -1],
  [1, 0, -24, 0, 86, 0, -104, 0, 53, 0, -12, 0],
  [1, -20, 20, 265, -265, -989, 989, 1519, -1519, -1198, 1198, 531, -531, -134, 134, 18, -18, -1],
  [-1, -7, 28, 56, -126, -126, 210, 120, -165, -55, 66, 12, -13, -1],
  [1, 15, -105, -560, 1820, 6188, -12376, -31824, 43758, 92378, -92378, -167960, 125970, 203490, -116280, -170544, 74613, 100947, -33649, -42504, 10626, 12650, -2300, -2600, 325, 351, -27, -28, 1]
]
set_option maxHeartbeats 4000000 in
def shiftedRows : Array (List ℤ) := #[
  [],
  [-5],
  [-9],
  [-8],
  [-7],
  [55, -15],
  [-6],
  [-377, 159, -22],
  [47, -14],
  [-323, 144, -21],
  [41, -13],
  [-17711, 12750, -3637, 514, -36],
  [46, -14],
  [121393, -105486, 37897, -7206, 765, -43],
  [-281, 131, -20],
  [1891, -1173, 269, -27],
  [2207, -1316, 290, -28],
  [5702887, -6655869, 3379044, -974697, 174735, -19937, 1414, -57],
  [-321, 144, -21],
  [-39088169, 51446925, -29942049, 10114098, -2185317, 313229, -29785, 1812, -64],
  [2161, -1302, 289, -28],
  [88831, -81591, 30955, -6208, 694, -41],
  [-13201, 10090, -3055, 458, -34],
  [-1836311903, 2964392796, -2166254294, 945910392, -274236795, 55429234, -7970368, 815382, -58161, 2755, -78],
  [2206, -1316, 290, -28],
  [228841255, -341125125, 227723500, -89652425, 23051300, -4044755, 490525, -40600, 2195, -70],
  [90481, -82646, 31205, -6234, 695, -41],
  [-33385283, 44791056, -26563005, 9139401, -2010582, 293292, -28371, 1755, -63],
  [101521, -91434, 33971, -6664, 728, -42],
  [591286729879, -1218956738475, 1162965616211, -680611350482, 272970902673, -79368664417, 17253149865, -2848536648, 358949811, -34355684, 2458599, -127570, 4537, -99],
  [2521, -1459, 311, -29],
  [-4052739537881, 8959000518075, -9214594231136, 5849505442347, -2563111725363, 821161467301, -198715889890, 36987570873, -5339066106, 597680479, -51465480, 3347695, -159237, 5229, -106],
  [4870847, -5808824, 3011916, -886872, 162210, -18872, 1364, -56],
  [196049701, -296972790, 201452410, -80586493, 21051715, -3752442, 462202, -38846, 2132, -69],
  [4250681, -5149911, 2713890, -812487, 151145, -17891, 1316, -55],
  [9182179441, -16658934678, 13795962273, -6895880638, 2317105432, -551383946, 95281122, -12047279, 1106187, -71936, 3145, -83],
  [103681, -92736, 34260, -6692, 729, -42],
  [1304969544928657, -3468370465774314, 4342285076813463, -3402625384275774, 1870113398305410, -765555631560167, 241908508809394, -60332574868320, 12039583426585, -1936733434350, 251745829335, -26379342990, 2211797952, -146380941, 7478780, -284632, 7599, -127],
  [-29134601, 39641145, -23849115, 8326914, -1859437, 275401, -27055, 1700, -62],
  [9210162781, -16697339706, 13819246310, -6904064991, 2318943433, -551657426, 95308082, -12048977, 1106249, -71937, 3145, -83],
  [4868641, -5807508, 3011626, -886844, 162209, -18872, 1364, -56],
  [61305790721611591, -181217438733968025, 253877256481481998, -224134274081147091, 139850851860411354, -65557095770547310, 23955397234642600, -6987450993353370, 1652350975931565, -319903725781185, 50984950005990, -6700929393795, 725006677122, -64224222804, 4612627816, -264461452, 11820780, -396987, 9424, -141],
  [118441, -103853, 37563, -7176, 764, -43],
  [-420196140727489673, 1304721945448537641, -1925056287654706963, 1795069324618684804, -1186808363557185150, 591601839703490230, -230809358814088410, 72208659049649820, -18410265621889785, 3866220162652575, -673115546953395, 97456530067260, -11734220022252, 1171345594986, -96314122540, 6454393536, -346869207, 14591202, -462821, 10410, -148],
  [224056801, -335396460, 224742230, -88771732, 22889783, -4025924, 489162, -40544, 2194, -70],
  [10716572161, -19185316992, 15677693352, -7732811208, 2564083998, -602160924, 102702761, -12818493, 1162026, -74619, 3222, -84],
  [-1368706081, 2270359316, -1704721010, 764819328, -227808385, 47301898, -6986588, 734070, -53769, 2615, -76],
  [-19740274219868223167, 67179571489855274424, -109130646950328608860, 112596020379261794080, -82819738045957154850, 46208524197932565420, -20314838466069246540, 7216080943295803140, -2106869427535021245, 511639268507030550, -104170095776965680, 17869859807466030, -2588973552829482, 316785622701366, -32659623616460, 2823090342294, -202978147068, 11996340441, -572898488, 21559965, -615517, 12529, -162],
  [4870846, -5808824, 3011916, -886872, 162210, -18872, 1364, -56],
  [-358890855025747337, 1123505560688668521, -1671180049017349591, 1570935653409341576, -1046957756371744399, 526044815911522068, -206853977407772142, 65221210699497571, -16757914982788812, 3546316469467954, -622130599305607, 90755600797141, -11009213349575, 1107121372280, -91701494725, 6189932084, -335048427, 14194215, -453397, 10269, -147],
  [228811001, -341102575, 227716850, -89651455, 23051230, -4044753, 490525, -40600, 2195, -70],
  [20326825084231, -48971597873571, 55143720180015, -38523511844994, 18687974638752, -6675052562935, 1815952769903, -383832662751, 63702640415, -8329075695, 855101755, -68207680, 4143970, -185383, 5759, -111],
  [10525900321, -18894711444, 15479514106, -7653178876, 2543204797, -598428292, 102241970, -12779704, 1159895, -74550, 3221, -84],
  [6356306993006846248183, -24474240289955688532551, 45228218493905722774485, -53401018864202365208580, 45240565892006797858350, -29278768588171172100870, 15047192034523714209690, -6302106561606767788140, 2190346091135283304245, -639989260395862227675, 158679113441776591455, -33605876015140388580, 6106119851102834232, -954254249626814766, 128371828277754160, -14853492256085624, 1474521679472478, -125036195207441, 8997577757938, -544340987190, 27330040122, -1118326539, 36342162, -902276, 16075, -183],
  [-33385281, 44791056, -26563005, 9139401, -2010582, 293292, -28371, 1755, -63],
  [44724928276576801, -134480662783780500, 191622682668556458, -172045764714903376, 109159263653786863, -52025956118853530, 19326436180440697, -5730024787162599, 1377110796676967, -270927202449266, 43871084744565, -5857460442644, 643706402535, -57909325249, 4223116748, -245817197, 11152969, -380140, 9157, -139],
  [10745088481, -19224300396, 15701244710, -7741063764, 2565932371, -602435344, 102729768, -12820192, 1162088, -74620, 3222, -84],
  [954928097357851, -2585327230964745, 3296791767732105, -2631054159852369, 1472588248585455, -613817333825834, 197473969540234, -50136074257227, 10183318162591, -1667105268793, 220497221449, -23506141357, 2004771511, -134936164, 7010004, -271226, 7360, -125],
  [440719107401, -928144225505, 904592020535, -540797088286, 221557632583, -65801527603, 14609948745, -2463587400, 317039943, -30986824, 2264251, -119950, 4355, -97],
  [-2046711111473984623691759, 8795946400787227711945350, -18221150272997455324674497, 24228194294457282720326274, -23231392942595259410066106, 17109008379958053767671785, -10064771099571163809032850, 4856161455971452190149920, -1958062480660677420942165, 668877297159945763852710, -195552398330608163445315, 49300987102079616911670, -10777664791934946396972, 2050953319912744534329, -340582700880374456816, 49413824048631771992, -6263761306147972830, 692887930360044657, -66720879100036714, 5571210752287026, -401170702583266, 24724365399525, -1291013027370, 56338701640, -2016615835, 57663684, -1266525, 20062, -204]
]

def psi (n : ℕ) : List ℤ := rows[n]?.getD [] ++ [1]
def gc (n : ℕ) : List ℤ := shiftedRows[n]?.getD [] ++ [1]
def width (n : ℕ) := (shiftedRows[n]?.getD []).length

def codes (n : ℕ) : List ℕ :=
  ((List.range (n+1)).filter (fun d => decide (0<d ∧ n%d=0))).flatMap
    (fun d => if d≤2 then [d] else [d,d])

def vpair : ℕ → List ℤ × List ℤ
  | 0 => ([2],[0,1])
  | n+1 => let q := vpair n; (q.2,plus (shift q.2) (q.1.map ((-1)*·)))

theorem vpair_ok (n : ℕ) : vpair n = (vs n,vs (n+1)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [vpair,ih,vs]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
private theorem data : ∀ i : Fin 59,
    let n := i.val+1
    plus (vpair n).1 [-2]=prodCodes ((codes n).map psi) ∧
    gc n = (substAt (psi n) [7,-1]).map (((-1:ℤ)^width n)*·) ∧
    (3≤n → 2*width n=n.totient) ∧
    (n≠2 → ¬ IsSquare (((-1:ℤ)^width n) * (gc n).headD 0)) := by decide +kernel

theorem data_at (n : ℕ) (pos : 0<n) (le : n≤59) :
    plus (vs n) [-2]=prodCodes ((codes n).map psi) ∧
    gc n = (substAt (psi n) [7,-1]).map (((-1:ℤ)^width n)*·) ∧
    (3≤n → 2*width n=n.totient) ∧
    (n≠2 → ¬ IsSquare (((-1:ℤ)^width n) * (gc n).headD 0)) := by
  have h := data (⟨n-1,by omega⟩)
  simpa only [show n-1+1=n by omega,vpair_ok] using h

theorem mem_codes {n k : ℕ} : k∈codes n ↔ 0<k ∧ k≤n ∧ n%k=0 := by
  simp only [codes,List.mem_flatMap,List.mem_filter,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨j,⟨lt,hj,r⟩,mem⟩
    have eq : k=j := by split_ifs at mem <;> simpa using mem
    subst k
    exact ⟨hj,by omega,r⟩
  · rintro ⟨hp,hle,hr⟩
    exact ⟨k,⟨by omega,hp,hr⟩,by split_ifs <;> simp⟩

theorem factored {R : Type*} [Field R] (x : R) (n : ℕ) (pos : 0<n) (bound : n≤59) :
    val x (vs n)=2 ↔ ∃ k∈codes n, val x (psi k)=0 := by
  have eq := congrArg (val x) (data_at n pos bound).1
  simp [val_plus,val_prod,List.map_map,Function.comp_def,val] at eq
  constructor
  · intro h
    have z : ((codes n).map fun k => val x (psi k)).prod=0 := by rw [←eq,h]; ring
    simpa using z
  · intro h
    have z : ((codes n).map fun k => val x (psi k)).prod=0 := by simpa using h
    rw [z] at eq
    linear_combination eq

theorem at_primitive {n : ℕ} (pos : 0<n) (bound : n≤59)
    {z : ℂ} (p : IsPrimitiveRoot z n) : val (z+z⁻¹) (psi n)=0 := by
  have zn : z≠0 := p.ne_zero pos.ne'
  have v (k : ℕ) : val (z+z⁻¹) (vs k)=2 ↔ z^k=1 := by
    rw [vs_primitive z zn,inv_pow]
    constructor
    · intro h
      have y := pow_ne_zero k zn
      field_simp [y] at h
      have zero : (z^k-1)^2=0 := by linear_combination h
      exact sub_eq_zero.mp (pow_eq_zero_iff (by decide : 2≠0) |>.mp zero)
    · intro h
      rw [h]; norm_num
  obtain ⟨k,hk,zero⟩ := (factored _ n pos bound).mp ((v n).mpr p.pow_eq_one)
  obtain ⟨kp,kle,_⟩ := mem_codes.mp hk
  have selfmem : k∈codes k := mem_codes.mpr ⟨kp,le_rfl,Nat.mod_self _⟩
  have zk := (v k).mp ((factored _ k kp (kle.trans bound)).mpr ⟨k,selfmem,zero⟩)
  have nk := p.dvd_of_pow_eq_one k zk
  rwa [Nat.le_antisymm kle (Nat.le_of_dvd kp nk)] at zero

end Deldor14.Star.Cyclo51

/- The real cyclotomic generator has degree at least half the totient.
Adjoining a primitive root to its sum with its inverse is quadratic. -/
namespace Deldor14.Star.Poly51
open Polynomial IntermediateField
open scoped Polynomial IntermediateField

theorem totient_le_twice_degree {k : ℕ} {ζ : ℂ} (prim : IsPrimitiveRoot ζ k)
    (f : ℚ[X]) (nf : f≠0) (van : aeval (ζ+ζ⁻¹) f=0) :
    Nat.totient k ≤ 2*f.natDegree := by
  classical
  rcases k.eq_zero_or_pos with rfl|kp
  · simp
  let z := ζ+ζ⁻¹
  let L := ℚ⟮z⟯
  let M := L⟮ζ⟯
  have iz : IsIntegral ℚ z := IsAlgebraic.isIntegral ⟨f,nf,van⟩
  let : FiniteDimensional ℚ L := IntermediateField.adjoin.finiteDimensional iz
  let P : L[X] := X^2-C (AdjoinSimple.gen ℚ z)*X+1
  have z0 : ζ≠0 := prim.ne_zero kp.ne'
  have root : aeval ζ P=0 := by
    simp [P,z]
    field_simp
    ring
  have degP : P.natDegree=2 := by
    simpa [P,sub_eq_add_neg] using
      (natDegree_quadratic (a:=(1:L)) (b:= -(AdjoinSimple.gen ℚ z)) (c:=(1:L)) one_ne_zero)
  have p0 : P≠0 := by intro e; simp [e] at degP
  have iζ : IsIntegral L ζ := IsAlgebraic.isIntegral ⟨P,p0,root⟩
  let : FiniteDimensional L M := IntermediateField.adjoin.finiteDimensional iζ
  let : FiniteDimensional ℚ M := Module.Finite.trans L M
  have lbound : Module.finrank ℚ L ≤ f.natDegree := by
    rw [show Module.finrank ℚ L = (minpoly ℚ z).natDegree from IntermediateField.adjoin.finrank iz]
    exact natDegree_le_of_dvd (minpoly.dvd ℚ z van) nf
  have mbound : Module.finrank L M ≤ 2 := by
    rw [show Module.finrank L M = (minpoly L ζ).natDegree from IntermediateField.adjoin.finrank iζ,←degP]
    exact natDegree_le_of_dvd (minpoly.dvd L ζ root) p0
  let y : M := AdjoinSimple.gen L ζ
  have eq : minpoly ℚ y = minpoly ℚ ζ := by
    rw [← minpoly.algebraMap_eq (algebraMap M ℂ).injective]
    rfl
  have cy : (minpoly ℚ ζ).natDegree=Nat.totient k := by
    rw [← cyclotomic_eq_minpoly_rat prim kp,natDegree_cyclotomic]
  have low := minpoly.natDegree_le (A:=ℚ) (x:=y)
  rw [eq,cy,← Module.finrank_mul_finrank ℚ L M] at low
  exact low.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul lbound mbound)

theorem irreducible_at_half_totient {k : ℕ} {ζ : ℂ} (prim : IsPrimitiveRoot ζ k)
    (g : ℚ[X]) (mon : g.Monic) (van : aeval (ζ+ζ⁻¹) g=0)
    (degree : 2*g.natDegree=k.totient) : Irreducible g := by
  let z := ζ+ζ⁻¹
  have integral : IsIntegral ℚ z := ⟨g,mon,van⟩
  have bound := totient_le_twice_degree prim (minpoly ℚ z) (minpoly.ne_zero integral) (minpoly.aeval ℚ z)
  have eq : minpoly ℚ z = g := eq_of_dvd_of_natDegree_le_of_leadingCoeff
    (minpoly.dvd ℚ z van) (by omega) ((minpoly.monic integral).trans mon.symm)
  rw [←eq]
  exact minpoly.irreducible integral

end Deldor14.Star.Poly51
namespace Deldor14.Star.Poly51
open Polynomial
open scoped Polynomial

theorem totient_le_twice_shift_degree {k : ℕ} {ζ : ℂ} (prim : IsPrimitiveRoot ζ k)
    (c : ℚ) (f : ℚ[X]) (nf : f≠0) (van : aeval ((c:ℂ)-(ζ+ζ⁻¹)) f=0) :
    k.totient ≤ 2*f.natDegree := by
  let h : ℚ[X] := C c-X
  have hd : h.natDegree=1 := by
    exact (natDegree_sub_eq_right_of_natDegree_lt (by simp : (C c).natDegree < (X:ℚ[X]).natDegree)).trans natDegree_X
  have nz : f.comp h≠0 := by
    intro eq
    rcases comp_eq_zero_iff.mp eq with e|⟨_,eh⟩
    · exact nf e
    · have e := congrArg natDegree eh
      simp only [hd,natDegree_C] at e
      omega
  have root : aeval (ζ+ζ⁻¹) (f.comp h) = 0 := by
    simpa [aeval_comp,h] using van
  have bound := totient_le_twice_degree prim (f.comp h) nz root
  simpa [natDegree_comp,hd] using bound

theorem irreducible_at_shifted_half_totient {k : ℕ} {ζ : ℂ} (prim : IsPrimitiveRoot ζ k)
    (c : ℚ) (g : ℚ[X]) (mon : g.Monic) (van : aeval ((c:ℂ)-(ζ+ζ⁻¹)) g=0)
    (degree : 2*g.natDegree=k.totient) : Irreducible g := by
  let z := (c:ℂ)-(ζ+ζ⁻¹)
  have integral : IsIntegral ℚ z := ⟨g,mon,van⟩
  have bound := totient_le_twice_shift_degree prim c (minpoly ℚ z) (minpoly.ne_zero integral) (minpoly.aeval ℚ z)
  have eq : minpoly ℚ z = g := eq_of_dvd_of_natDegree_le_of_leadingCoeff
    (minpoly.dvd ℚ z van) (by omega) ((minpoly.monic integral).trans mon.symm)
  rw [←eq]
  exact minpoly.irreducible integral
end Deldor14.Star.Poly51

/- A norm obstruction to reducibility after substituting a square.
Capelli's composition criterion reduces the question to the root of the
inner quadratic. Its square would give a square norm in the ground field. -/
namespace Deldor14.Star.Poly51
open Polynomial IntermediateField
open scoped Polynomial

theorem irreducible_comp_square {K : Type*} [Field K] (g : K[X])
    (mon : g.Monic) (irr : Irreducible g)
    (ns : ¬IsSquare ((-1:K)^g.natDegree * g.coeff 0)) :
    Irreducible (g.comp (X^2)) := by
  apply Polynomial.irreducible_comp mon (monic_X_pow 2) irr
  intro E _ _ x min
  rw [Polynomial.map_pow,map_X]
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b eq
  have integral : IsIntegral K x := ⟨g,mon,by rw [← min]; exact minpoly.aeval K x⟩
  have norm := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis integral)
  rw [adjoin.powerBasis_dim,adjoin.powerBasis_gen,minpoly_gen,min] at norm
  apply ns
  refine ⟨Algebra.norm K b,?_⟩
  rw [←norm,←eq,map_pow,pow_two]

end Deldor14.Star.Poly51
namespace Deldor14.Star.Poly51
open Polynomial
open scoped Polynomial

theorem minpoly_even_of_nonsquare_norm {E : Type*} [Field E] [Algebra ℚ E]
    (g : ℚ[X]) (mon : g.Monic) (irr : Irreducible g)
    (ns : ¬IsSquare ((-1:ℚ)^g.natDegree*g.coeff 0)) (θ : E)
    (van : aeval (θ^2) g=0) :
    (minpoly ℚ θ).comp (-X)=minpoly ℚ θ := by
  have pmon : (g.comp (X^2)).Monic := mon.comp (monic_X_pow 2) (by simp)
  have root : aeval θ (g.comp (X^2))=0 := by simpa [aeval_comp] using van
  have poly := minpoly.eq_of_irreducible_of_monic (irreducible_comp_square g mon irr ns) root pmon
  rw [←poly,comp_assoc]
  simp

end Deldor14.Star.Poly51

namespace Deldor14.Star.Cyclo51
open Polynomial
theorem val_vieta (x : ℝ) (n : ℕ) : val x (vs n) = Waddle51.vieta x n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [vs,val,Waddle51.vieta]
  | one => norm_num [vs,val,Waddle51.vieta]
  | more n ih ih' => rw [val_vs,ih,ih',Waddle51.vieta]

theorem coeff_zero_code (a : List ℤ) : (poly a).coeff 0 = ((a.headD 0 : ℤ):ℚ) := by
  cases a with
  | nil => simp [poly,val]
  | cons a as =>
    change ((a : ℚ[X])+X*poly as).coeff 0=(a:ℚ)
    simp

theorem eval_g {R : Type*} [Field R] [Algebra ℚ R] (x : R) {n : ℕ} (pos : 0<n) (le : n≤59) :
    aeval x (poly (gc n)) = ((-1:R)^width n)*val (7-x) (psi n) := by
  rw [aeval_poly,(data_at n pos le).2.1,val_scale,val_subst]
  push_cast
  congr 2
  simp [val]
  ring

theorem classify (θ : ℝ) {d : ℕ} (pos : 0<d) (le : d≤59) (v : Waddle51.vieta (7-θ^2) d=2) :
    θ=3 ∨ θ= -3 ∨ (minpoly ℚ θ).comp (-X)=minpoly ℚ θ := by
  rw [←val_vieta] at v
  obtain ⟨k,hk,root⟩ := (factored _ d pos le).mp v
  obtain ⟨kp,kd,_⟩ := mem_codes.mp hk
  have bound := kd.trans le
  by_cases two : k=2
  · subst k
    change val (7-θ^2) [2,1] = 0 at root
    norm_num [val] at root
    have zero : (θ-3)*(θ+3)=0 := by nlinarith
    rcases mul_eq_zero.mp zero with plus|minus
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
  right; right
  have mon : (poly (gc k)).Monic := (monic_code (shiftedRows[k]?.getD [])).1
  have degree : (poly (gc k)).natDegree=width k := (monic_code _).2
  have irreducible : Irreducible (poly (gc k)) := by
    by_cases one : k=1
    · subst k
      apply Polynomial.irreducible_of_degree_eq_one
      rw [degree_eq_natDegree mon.ne_zero,degree]
      rfl
    · let z := Complex.exp (2*Real.pi*Complex.I / k)
      have prim : IsPrimitiveRoot z k := Complex.isPrimitiveRoot_exp k kp.ne'
      apply Poly51.irreducible_at_shifted_half_totient prim 7 _ mon
      · rw [eval_g _ kp bound]
        push_cast
        rw [show (7:ℂ)-(7-(z+z⁻¹)) = z+z⁻¹ by ring, at_primitive kp bound prim,mul_zero]
      · rw [degree]
        exact (data_at k kp bound).2.2.1 (by omega)
  apply Poly51.minpoly_even_of_nonsquare_norm _ mon irreducible _ θ
  · rw [eval_g _ kp bound,root,mul_zero]
  · rw [degree,coeff_zero_code]
    intro sq
    have h : IsSquare ((((-1:ℤ)^width k*(gc k).headD 0 : ℤ):ℚ)) := by push_cast; exact sq
    exact (data_at k kp bound).2.2.2 two (Rat.isSquare_intCast_iff.mp h)

end Deldor14.Star.Cyclo51

open Polynomial
open scoped Polynomial

namespace Erdos552Trace51

private lemma coeff_comp_neg (p : ℚ[X]) (j : ℕ) :
    (p.comp (-X)).coeff j = (-1 : ℚ)^j * p.coeff j := by
  induction p using Polynomial.induction_on' with
  | add f g hf hg => simp [add_comp, hf, hg, mul_add]
  | monomial k a =>
    have negPow : (-(X : ℚ[X]))^k = C ((-1 : ℚ)^k) * X^k := by
      rw [map_pow, ← mul_pow]
      simp
    simp only [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp,
      negPow, ← mul_assoc, ← map_mul]
    rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
    split <;> rename_i h
    · subst_vars
      exact mul_comm _ _
    · simp

private lemma nextCoeff_even {p : ℚ[X]} (hm : p.Monic)
    (he : p.comp (-X) = p) : p.nextCoeff = 0 := by
  have c (j : ℕ) : p.coeff j = (-1 : ℚ)^j * p.coeff j := by
    simpa only [he] using coeff_comp_neg p j
  by_cases h : p.natDegree = 0
  · simp [nextCoeff, h]
  have hc := c p.natDegree
  rw [coeff_natDegree, hm.leadingCoeff, mul_one] at hc
  have d : p.natDegree - 1 + 1 = p.natDegree := by omega
  have hs : (-1 : ℚ)^(p.natDegree - 1) = -1 := by
    nth_rw 1 [← d] at hc
    rw [pow_succ] at hc
    linarith
  have hh := c (p.natDegree - 1)
  rw [hs] at hh
  rw [nextCoeff_of_natDegree_pos (Nat.pos_of_ne_zero h)]
  linarith

theorem three_divides_nextCoeff {Q : ℚ[X]} (hm : Q.Monic)
    (clas : ∀ p : ℚ[X], Irreducible p → p.Monic → p ∣ Q →
      p = X - C 3 ∨ p = X - C (-3) ∨ p.comp (-X) = p) :
    ∃ z : ℤ, Q.nextCoeff = 3 * (z : ℚ) := by
  classical
  let L := UniqueFactorizationMonoid.normalizedFactors Q
  have hpL : ∀ p ∈ L, p.Monic ∧ ∃ a : ℤ, p.nextCoeff = 3 * (a : ℚ) := by
    intro p hp
    obtain ⟨hi,hmon,hd⟩ := (Polynomial.mem_normalizedFactors_iff hm.ne_zero).mp hp
    refine ⟨hmon, ?_⟩
    rcases clas p hi hmon hd with rfl | rfl | he
    · exact ⟨-1, by norm_num [nextCoeff_X_sub_C]⟩
    · exact ⟨1, by norm_num [nextCoeff_X_sub_C]⟩
    · exact ⟨0, by simp [nextCoeff_even hmon he]⟩
  have sum (s : Multiset ℚ[X])
      (hs : ∀ p ∈ s, p.Monic ∧ ∃ a : ℤ, p.nextCoeff = 3 * (a : ℚ)) :
      s.prod.Monic ∧ ∃ z : ℤ, s.prod.nextCoeff = 3 * (z : ℚ) := by
    induction s using Multiset.induction_on with
    | empty => exact ⟨monic_one, 0, by simp [nextCoeff]⟩
    | cons p t ih =>
      obtain ⟨hp, a, ha⟩ := hs p (by simp)
      obtain ⟨ht, z, hz⟩ := ih (fun q hq => hs q (by simp [hq]))
      rw [Multiset.prod_cons]
      refine ⟨hp.mul ht, a+z, ?_⟩
      rw [hp.nextCoeff_mul ht, ha, hz, Int.cast_add, mul_add]
  have hp : L.prod = Q := (UniqueFactorizationMonoid.prod_normalizedFactors_eq hm.ne_zero).trans hm.normalize_eq_self
  simpa only [hp] using (sum L hpL).2


theorem trace_obstruction {F Q : ℚ[X]} (hm : Q.Monic)
    (eq : F = (X - C 8) * Q) (h8 : Q.eval 8 ≠ 0)
    (splits : (F.map (algebraMap ℚ ℝ)).Splits)
    (classify : ∀ θ : ℝ, (F.map (algebraMap ℚ ℝ)).IsRoot θ → θ ≠ 8 →
      θ = 3 ∨ θ = -3 ∨ (minpoly ℚ θ).comp (-X) = minpoly ℚ θ) :
    F.nextCoeff ≠ 0 := by
  have hF : F.Monic := eq ▸ (monic_X_sub_C _).mul hm
  have cls (p : ℚ[X]) (hi : Irreducible p) (hp : p.Monic) (hd : p ∣ Q) :
      p = X - C 3 ∨ p = X - C (-3) ∨ p.comp (-X) = p := by
    have hdF : p ∣ F := eq ▸ dvd_mul_of_dvd_right hd _
    let ι := algebraMap ℚ ℝ
    have hmF : p.map ι ∣ F.map ι := Polynomial.map_dvd ι hdF
    have hs : (p.map ι).Splits := splits.of_dvd (hF.map ι).ne_zero hmF
    have hn : (p.map ι).natDegree ≠ 0 := by
      rw [hp.natDegree_map ι]
      exact hi.natDegree_pos.ne'
    obtain ⟨θ,hθ⟩ := hs.exists_eval_eq_zero (degree_ne_of_natDegree_ne hn)
    have hr : (p.map ι).IsRoot θ := hθ
    have hnr : θ ≠ 8 := by
      rintro rfl
      have H := hr.dvd (Polynomial.map_dvd ι hd)
      have h : (Q.map ι).eval (ι 8) = 0 := by simpa [ι] using H
      rw [eval_map_apply] at h
      exact h8 (ι.injective (by simpa using h))
    have hmnp : p = minpoly ℚ θ :=
      minpoly.eq_of_irreducible_of_monic hi (by simpa [aeval_def, eval_map, ι] using hθ) hp
    rcases classify θ (hr.dvd hmF) hnr with rfl | rfl | he
    · left
      apply hmnp.trans
      simpa [ι] using minpoly.eq_X_sub_C_of_algebraMap_inj (B := ℝ) (3 : ℚ) ι.injective
    · right; left
      apply hmnp.trans
      simpa [ι] using minpoly.eq_X_sub_C_of_algebraMap_inj (B := ℝ) (-3 : ℚ) ι.injective
    · exact Or.inr (Or.inr (hmnp ▸ he))
  obtain ⟨z,hz⟩ := three_divides_nextCoeff hm cls
  rw [eq, (monic_X_sub_C _).nextCoeff_mul hm, nextCoeff_X_sub_C, hz]
  intro h
  have H : (-8 : ℤ) + 3 * z = 0 := by exact_mod_cast h
  omega


theorem obstruction_of_simple {F : ℚ[X]} (hm : F.Monic) (simple : F.rootMultiplicity 8 = 1)
    (split : (F.map (algebraMap ℚ ℝ)).Splits)
    (classify : ∀ θ : ℝ, (F.map (algebraMap ℚ ℝ)).IsRoot θ → θ ≠ 8 →
      θ = 3 ∨ θ = -3 ∨ (minpoly ℚ θ).comp (-X) = minpoly ℚ θ) :
    F.nextCoeff ≠ 0 := by
  obtain ⟨Q,he,hn⟩ := F.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hm.ne_zero 8
  rw [simple, pow_one] at he
  have mon : Q.Monic := (monic_X_sub_C (8 : ℚ)).of_mul_monic_left (he ▸ hm)
  exact trace_obstruction mon he (fun h => hn (dvd_iff_isRoot.mpr h)) split classify

end Erdos552Trace51

theorem Deldor14.Star.Waddle51.ramsey_star_51 : Deldor14.Star.number 51 = 59 :=
  Deldor14.Star.Waddle51.star_51_of_classification Deldor14.Star.Cyclo51.classify Erdos552Trace51.trace_obstruction
end

/- Verified finite-field and spectral calculations for quadrilateral–star
Ramsey numbers. For q=32 and q=128, the affine polarity construction has
q(q−1)+2 vertices and the first possible counterexample above it must be a
regular graph with a 2-regular deficiency graph. The spectral argument adapts
Zach Waddle’s treatment of q=8, cited above. We use square classes of products
of evaluated Chebyshev polynomials to certify the real cyclotomic norms for
every order up to q(q−1)+3, without trusting the generator of the certificates.
The table gives one modulus per order. Lean checks all modular recurrences and
all nonresidue tests. Related finite-field bounds: Luis Boza, arXiv:2409.12770.
-/
section
/- Recover the order of a root of unity from a single scalar Viète equation.
The norm of a shifted real cyclotomic factor then determines parity of the minimal polynomial. -/
namespace Deldor14.Star.Lift963
open Polynomial
open scoped Polynomial

private theorem cast_vieta {μ : ℝ} {z : ℂ} (nz : z≠0) (eq : (μ:ℂ)=z+z⁻¹) (n : ℕ) :
    ((Waddle51.vieta μ n : ℝ):ℂ) = z^n+(z⁻¹)^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Waddle51.vieta]; norm_num
  | one => simpa [Waddle51.vieta] using eq
  | more n ih ih' =>
    rw [Waddle51.vieta]
    push_cast
    rw [ih',ih,eq]
    simp only [pow_succ]
    field_simp
    ring

theorem primitive_of_vieta {μ : ℝ} {d : ℕ} (hd : 0 < d) (v : Waddle51.vieta μ d=2) :
    ∃ (z : ℂ) (k : ℕ), 0<k ∧ k≤d ∧ IsPrimitiveRoot z k ∧ (μ:ℂ)=z+z⁻¹ := by
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq ((μ:ℂ)^2-4) (by decide : 0<2)
  let z := ((μ:ℂ)+s)/2
  have quad : z^2-(μ:ℂ)*z+1=0 := by dsimp [z]; linear_combination hs/4
  have nz : z≠0 := by intro eq; simp [eq] at quad
  have eq : (μ:ℂ)=z+z⁻¹ := by field_simp; linear_combination -quad
  have vl := cast_vieta nz eq d
  rw [v] at vl
  have nz' : z^d≠0 := pow_ne_zero _ nz
  have s2 : z^d+(z^d)⁻¹=2 := by simpa [inv_pow] using vl.symm
  have zpow : z^d=1 := by
    field_simp at s2
    have zero : (z^d-1)^2=0 := by linear_combination s2
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero zero)
  have div := orderOf_dvd_of_pow_eq_one zpow
  exact ⟨z,orderOf z,Nat.pos_of_dvd_of_pos div hd,Nat.le_of_dvd hd div,IsPrimitiveRoot.orderOf z,eq⟩

private theorem even_of_rat_square {θ : ℝ} {b : ℚ} (ns : ¬IsSquare b) (root : θ^2=(b:ℝ)) :
    (minpoly ℚ θ).comp (-X)=minpoly ℚ θ := by
  apply Poly51.minpoly_even_of_nonsquare_norm (X-C b) (monic_X_sub_C _) (irreducible_X_sub_C _)
  · simpa using ns
  · simp [root]

theorem even_of_vieta {t : ℚ} {θ : ℝ} {d : ℕ}
    (hd : 0<d) (v : Waddle51.vieta ((t:ℝ)-θ^2) d=2)
    (lo : ¬IsSquare (t-2)) (hi : ¬IsSquare (t+2))
    (data : ∀ k, 3≤k → k≤d → ∃ g : ℚ[X], g.Monic ∧ 2*g.natDegree=k.totient ∧
      ¬IsSquare ((-1:ℚ)^g.natDegree*g.coeff 0) ∧
      ∀ z : ℂ, IsPrimitiveRoot z k → aeval ((t:ℂ)-(z+z⁻¹)) g=0) :
    (minpoly ℚ θ).comp (-X)=minpoly ℚ θ := by
  obtain ⟨z,k,kpos,kd,prim,eq⟩ := primitive_of_vieta hd v
  by_cases small : k≤2
  · rcases (show k=1 ∨ k=2 by omega) with rfl|rfl
    · have z1 : z=1 := by simpa using prim.pow_eq_one
      have θeq : (t:ℝ)-θ^2=2 := by exact_mod_cast (by norm_num [z1] at eq ⊢; exact eq : (((t:ℝ)-θ^2:ℝ):ℂ)=2)
      apply even_of_rat_square lo
      push_cast
      linarith
    · have zn : z=-1 := prim.eq_neg_one_of_two_right
      have θeq : (t:ℝ)-θ^2= -2 := by exact_mod_cast (by norm_num [zn] at eq ⊢; exact eq : (((t:ℝ)-θ^2:ℝ):ℂ)= -2)
      apply even_of_rat_square hi
      push_cast
      linarith
  · obtain ⟨g,mon,deg,ns,atRoot⟩ := data k (by omega) kd
    have hr := atRoot z prim
    have irr := Poly51.irreducible_at_shifted_half_totient prim t g mon hr deg
    apply Poly51.minpoly_even_of_nonsquare_norm g mon irr ns
    have heq : (t:ℂ)-(z+z⁻¹)=((θ^2:ℝ):ℂ) := by rw [←eq]; push_cast; ring
    rw [heq] at hr
    exact (aeval_algebraMap_eq_zero_iff_of_injective (algebraMap ℝ ℂ).injective).mp hr

end Deldor14.Star.Lift963
end

section
namespace Deldor14.Star.Lift963
open Polynomial
open scoped Polynomial

/-- Shift a monic polynomial by the affine involution q ↦ t − q and restore monicity. -/
noncomputable def shifted (t : ℚ) (f : ℚ[X]) : ℚ[X] :=
  C ((-1:ℚ)^f.natDegree) * f.comp (C t-X)

private lemma line_degree (t : ℚ) : (C t-X).natDegree=1 :=
  (natDegree_sub_eq_right_of_natDegree_lt (by simp : (C t).natDegree < (X:ℚ[X]).natDegree)).trans natDegree_X

theorem shifted_degree (t : ℚ) (f : ℚ[X]) : (shifted t f).natDegree=f.natDegree := by
  rw [shifted,natDegree_C_mul (pow_ne_zero _ (by norm_num : (-1:ℚ)≠0)),natDegree_comp,line_degree,mul_one]

theorem shifted_monic (t : ℚ) {f : ℚ[X]} (mon : f.Monic) : (shifted t f).Monic := by
  have deg : (C t).degree < (X:ℚ[X]).degree := degree_C_le.trans_lt (by simp)
  have coeff : (C t-X).leadingCoeff = -1 := by simp [leadingCoeff_sub_of_degree_lt' deg]
  rw [Monic.def,shifted,leadingCoeff_mul,leadingCoeff_C,leadingCoeff_comp (by rw [line_degree]; decide),
    mon.leadingCoeff,coeff,one_mul,← mul_pow]
  simp

theorem shifted_norm (t : ℚ) (f : ℚ[X]) :
    (-1:ℚ)^(shifted t f).natDegree*(shifted t f).coeff 0 = f.eval t := by
  rw [shifted_degree, coeff_zero_eq_eval_zero]
  simp only [shifted,eval_mul,eval_C,eval_comp,eval_sub,eval_X,sub_zero]
  rw [← mul_assoc,← mul_pow]
  simp

theorem even_of_real_factors {t : ℚ} {θ : ℝ} {d : ℕ}
    (hd : 0<d) (v : Waddle51.vieta ((t:ℝ)-θ^2) d=2)
    (lo : ¬IsSquare (t-2)) (hi : ¬IsSquare (t+2))
    (data : ∀ k, 3≤k → k≤d → ∃ f : ℚ[X], f.Monic ∧ 2*f.natDegree=k.totient ∧
      ¬IsSquare (f.eval t) ∧ ∀ z : ℂ, IsPrimitiveRoot z k → aeval (z+z⁻¹) f=0) :
    (minpoly ℚ θ).comp (-X)=minpoly ℚ θ := by
  apply even_of_vieta hd v lo hi
  intro k hk kd
  obtain ⟨f,mon,deg,ns,roots⟩ := data k hk kd
  refine ⟨shifted t f, shifted_monic t mon, (by rwa [shifted_degree]), (by rwa [shifted_norm]), ?_⟩
  intro z pr
  have point : (t:ℂ)-((t:ℂ)-(z+z⁻¹))=z+z⁻¹ := by ring
  simp [shifted,aeval_comp,point,roots z pr]
end Deldor14.Star.Lift963
end

section
/- Real eigenvalues of an adjacency matrix with a 2-regular deficiency graph. -/
namespace Deldor14.Star.CycleParity
open Waddle51 Finset Matrix Unitary SimpleGraph

private theorem lower_diag {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (reg : ∀ x, G.degree x = 2) (U : Matrix.unitaryGroup V ℝ) (i : V) :
    -2 ≤ (conjStarAlgAut ℝ _ (star U) (G.adjMatrix ℝ)) i i := by
  let e := conjStarAlgAut ℝ _ (star U)
  have deg : G.degMatrix ℝ = (2:ℝ) • (1:Matrix V V ℝ) := by
    ext i j
    simp [degMatrix,Matrix.smul_apply,Matrix.one_apply,diagonal_apply,reg]
  have plus := (Waddle39.signless_pos G).mul_mul_conjTranspose_same
    ((star U : Matrix.unitaryGroup V ℝ) : Matrix V V ℝ)
  have p : 0 ≤ (e (G.degMatrix ℝ + G.adjMatrix ℝ)) i i := plus.diag_nonneg
  rw [deg,map_add,map_smul,map_one,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,
    smul_eq_mul,mul_one] at p
  change -2 ≤ e (G.adjMatrix ℝ) i i
  linarith

private theorem transfer {q : ℕ} {b : ℝ} {V : Type*} [Fintype V] [DecidableEq V]
    (A J : Matrix V V ℝ) (D : SimpleGraph V) [DecidableRel D.Adj] (x : V → ℝ)
    (θ : ℝ) (eig : A *ᵥ x = θ • x) (off : θ ≠ q) (rightJ : J*A = (q:ℝ) • J)
    (square : A^2 = (b:ℝ) • 1 + J - D.adjMatrix ℝ) :
    D.adjMatrix ℝ *ᵥ x = (b-θ^2) • x := by
  have jr := congrArg (fun B : Matrix V V ℝ => B *ᵥ x) rightJ
  change (J*A) *ᵥ x = ((q:ℝ) • J) *ᵥ x at jr
  rw [←mulVec_mulVec,eig,mulVec_smul,smul_mulVec] at jr
  have jzero : J *ᵥ x = 0 := by
    ext i
    have eq := congrFun jr i
    change θ * (J *ᵥ x) i = q * (J *ᵥ x) i at eq
    have v : (θ-q) * (J *ᵥ x) i = 0 := by linear_combination eq
    exact (mul_eq_zero.mp v).resolve_left (sub_ne_zero.mpr off)
  have aq := congrArg (fun B : Matrix V V ℝ => B *ᵥ x) square
  change (A^2) *ᵥ x = ((b:ℝ) • 1 + J - D.adjMatrix ℝ) *ᵥ x at aq
  rw [sq,←mulVec_mulVec,eig,mulVec_smul,eig,sub_mulVec,add_mulVec,smul_mulVec,one_mulVec,jzero,add_zero] at aq
  ext i
  have entry := congrFun aq i
  change θ*(θ*x i) = b*x i - (D.adjMatrix ℝ *ᵥ x) i at entry
  change (D.adjMatrix ℝ *ᵥ x) i = (b-θ^2)*x i
  linear_combination entry

theorem spectral_rows {N q : ℕ} {b low : ℝ} (pos : 0<N) (cut : (N:ℝ)<2*low) (bound : low ≤ (q:ℝ)^2-b-2) (A J : Matrix (Fin N) (Fin N) ℝ) (D : SimpleGraph (Fin N))
    [DecidableRel D.Adj] (reg : ∀ i, D.degree i = 2) (herm : A.IsHermitian)
    (square : A^2 = (b:ℝ) • 1 + J - D.adjMatrix ℝ)
    (rightJ : J*A = (q:ℝ) • J) (trJ : J.trace = N) :
    ∃ t : Fin N, herm.eigenvalues t = q ∧ (∀ i, herm.eigenvalues i = q → i = t) ∧
      ∀ i, herm.eigenvalues i ≠ q → ∃ d : ℕ, 0 < d ∧ d ≤ N ∧
        vieta (b - (herm.eigenvalues i)^2) d = 2 := by
  classical
  let f := herm.eigenvalues
  let e := conjStarAlgAut ℝ _ (star herm.eigenvectorUnitary)
  let j (i : Fin N) := (e J) i i
  have diagA : e A = diagonal f := by
    simpa [e,f,Function.comp_def] using herm.conjStarAlgAut_star_eigenvectorUnitary
  have traceConj (B : Matrix (Fin N) (Fin N) ℝ) : (e B).trace = B.trace := by
    dsimp only [e]
    rw [conjStarAlgAut_apply,trace_mul_cycle,coe_star_mul_self,one_mul]
  have jSum : ∑ i, j i = N := (traceConj J).trans trJ
  have relation (i : Fin N) : j i * (f i - q) = 0 := by
    have eq := congrArg e rightJ
    rw [map_mul,map_smul,diagA] at eq
    have entry := congrArg (fun B : Matrix (Fin N) (Fin N) ℝ => B i i) eq
    simp only [mul_diagonal,Matrix.smul_apply,smul_eq_mul] at entry
    dsimp only [j]
    linear_combination entry
  have off (i : Fin N) (h : f i ≠ q) : j i = 0 :=
    (mul_eq_zero.mp (relation i)).resolve_right (sub_ne_zero.mpr h)
  have near (i : Fin N) (h : f i = q) : low ≤ j i := by
    have eq := congrArg e square
    rw [map_pow,map_sub,map_add,map_smul,map_one,diagA,diagonal_pow] at eq
    have entry := congrArg (fun B : Matrix (Fin N) (Fin N) ℝ => B i i) eq
    simp only [diagonal_apply_eq,Pi.pow_apply,h,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
      Matrix.one_apply_eq,smul_eq_mul,mul_one] at entry
    have lo : -2 ≤ (e (D.adjMatrix ℝ)) i i := lower_diag D reg herm.eigenvectorUnitary i
    dsimp only [j]
    linarith only [lo,entry,bound]
  let top := univ.filter (fun i => f i = q)
  have row (i : Fin N) : (if f i = q then (low:ℝ) else 0) ≤ j i := by
    split
    · exact near i ‹_›
    · rw [off i ‹_›]
  have upper := Finset.sum_le_sum (s:=univ) (fun i _ => row i)
  rw [jSum] at upper
  have tally : (top.card:ℝ)*low ≤ N := by simpa [top,Finset.sum_ite] using upper
  have card_le : top.card ≤ 1 := by
    by_contra! h
    have hn : (2:ℝ) ≤ top.card := by exact_mod_cast h
    have nn : (0:ℝ) ≤ N := by positivity
    nlinarith only [tally,cut, mul_nonneg (sub_nonneg.mpr hn) (show 0≤low by linarith)]
  have nonempty : top.Nonempty := by
    by_contra! empty
    have zero (i : Fin N) : j i = 0 := by
      apply off i
      intro hi
      have h : i ∈ top := mem_filter.mpr ⟨mem_univ _,hi⟩
      simp [empty] at h
    simp [zero] at jSum
    exact (Nat.cast_ne_zero.mpr pos.ne' : (N:ℝ)≠0) jSum.symm
  obtain ⟨t,ht⟩ := Finset.card_eq_one.mp (le_antisymm card_le (Finset.card_pos.mpr nonempty))
  refine ⟨t,(mem_filter.mp (show t ∈ top by rw [ht]; simp)).2,?_,?_⟩
  · intro i fi
    have m : i ∈ top := mem_filter.mpr ⟨mem_univ _,fi⟩
    rwa [ht,mem_singleton] at m
  · intro i fi
    let x := (herm.eigenvectorBasis i : Fin N → ℝ)
    have nonzero : x ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 (herm.eigenvectorBasis.orthonormal.ne_zero i)
    have eig := transfer A J D x (herm.eigenvalues i) (herm.mulVec_eigenvectorBasis i) fi rightJ square
    simpa using cycle_spectrum D reg _ x nonzero eig

end Deldor14.Star.CycleParity
/- Deflation of the unique principal eigenvalue over the rationals. -/
namespace Deldor14.Star.CycleParity
open Waddle51 Matrix Finset Polynomial SimpleGraph

theorem rational_factor {N q : ℕ} {b low : ℝ} (pos : 0<N) (cut : (N:ℝ)<2*low) (bound : low ≤ (q:ℝ)^2-b-2) (A J : Matrix (Fin N) (Fin N) ℝ) (D : SimpleGraph (Fin N))
    [DecidableRel D.Adj] (reg : ∀ i, D.degree i = 2) (herm : A.IsHermitian)
    (square : A^2 = (b:ℝ) • 1 + J - D.adjMatrix ℝ)
    (rightJ : J*A = (q:ℝ) • J) (trJ : J.trace = N)
    (F : ℚ[X]) (monic : F.Monic) (rational : F.map (algebraMap ℚ ℝ) = A.charpoly) :
    ∃ Q : ℚ[X], Q.Monic ∧ F = (X - C (q:ℚ))*Q ∧ Q.eval (q:ℚ) ≠ 0 ∧
      (F.map (algebraMap ℚ ℝ)).Splits ∧
      ∀ θ : ℝ, (F.map (algebraMap ℚ ℝ)).IsRoot θ → θ ≠ q →
        ∃ d : ℕ, 0 < d ∧ d ≤ N ∧ vieta (b-θ^2) d = 2 := by
  classical
  obtain ⟨t,ft,unique,other⟩ := spectral_rows pos cut bound A J D reg herm square rightJ trJ
  let f := herm.eigenvalues
  let S := univ.erase t
  let g (i : Fin N) := (X - C (f i) : ℝ[X])
  have full : F.map (algebraMap ℚ ℝ) = ∏ i, g i := by
    rw [rational]
    simpa [g,f] using herm.charpoly_eq
  have fact : F.map (algebraMap ℚ ℝ) = (X-C (q:ℝ)) * ∏ i ∈ S, g i := by
    rw [full,←Finset.mul_prod_erase univ g (mem_univ t)]
    simp only [g, f, ft, S]
  have root8 : F.IsRoot (q:ℚ) := by
    have real8 : (F.map (algebraMap ℚ ℝ)).eval (q:ℝ) = 0 := by rw [fact]; simp
    apply (algebraMap ℚ ℝ).injective
    change algebraMap ℚ ℝ (F.eval (q:ℚ)) = _
    rw [map_zero,←eval_map_apply]
    simpa using real8
  obtain ⟨Q,eq⟩ := Polynomial.dvd_iff_isRoot.mpr root8
  have small : Q.map (algebraMap ℚ ℝ) = ∏ i ∈ S, g i := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero (q:ℝ))
    conv_lhs => rw [show (X-C (q:ℝ) : ℝ[X]) =
      (X-C (q:ℚ) : ℚ[X]).map (algebraMap ℚ ℝ) by simp]
    rw [←Polynomial.map_mul,←eq,fact]
  refine ⟨Q,(monic_X_sub_C (q:ℚ)).of_mul_monic_left (eq ▸ monic),eq,?_,rational ▸ herm.splits_charpoly,?_⟩
  · intro h
    have hz := congrArg (algebraMap ℚ ℝ) h
    rw [map_zero,←eval_map_apply] at hz
    have zero : (Q.map (algebraMap ℚ ℝ)).eval (q:ℝ) = 0 := by simpa using hz
    rw [small,eval_prod,Finset.prod_eq_zero_iff] at zero
    obtain ⟨i,hi,vanish⟩ := zero
    have fi : f i = q := by
      simp only [g,eval_sub,eval_X,eval_C] at vanish
      linarith
    exact (mem_erase.mp hi).1 (unique i fi)
  · intro θ root ne
    rw [full,IsRoot,eval_prod,Finset.prod_eq_zero_iff] at root
    obtain ⟨i,_,hi⟩ := root
    have eqf : θ = f i := by exact sub_eq_zero.mp (by simpa [g] using hi)
    subst θ
    exact other i ne

end Deldor14.Star.CycleParity

namespace Deldor14.Star.CycleParity
open Polynomial Erdos552Trace51
set_option maxHeartbeats 2000000 in
theorem trace_obstruction {q : ℕ} (mod3 : ¬ (3:ℤ) ∣ (q:ℤ)) {F Q : ℚ[X]} (hm : Q.Monic)
    (eq : F = (X - C (q:ℚ)) * Q) (h8 : Q.eval (q:ℚ) ≠ 0)
    (splits : (F.map (algebraMap ℚ ℝ)).Splits)
    (classify : ∀ θ : ℝ, (F.map (algebraMap ℚ ℝ)).IsRoot θ → θ ≠ q →
      θ = 3 ∨ θ = -3 ∨ (minpoly ℚ θ).comp (-X) = minpoly ℚ θ) :
    F.nextCoeff ≠ 0 := by
  have hF : F.Monic := eq ▸ (monic_X_sub_C _).mul hm
  have cls (p : ℚ[X]) (hi : Irreducible p) (hp : p.Monic) (hd : p ∣ Q) :
      p = X - C 3 ∨ p = X - C (-3) ∨ p.comp (-X) = p := by
    have hdF : p ∣ F := eq ▸ dvd_mul_of_dvd_right hd _
    let ι := algebraMap ℚ ℝ
    have hmF : p.map ι ∣ F.map ι := Polynomial.map_dvd ι hdF
    have hs : (p.map ι).Splits := splits.of_dvd (hF.map ι).ne_zero hmF
    have hn : (p.map ι).natDegree ≠ 0 := by
      rw [hp.natDegree_map ι]
      exact hi.natDegree_pos.ne'
    obtain ⟨θ,hθ⟩ := hs.exists_eval_eq_zero (degree_ne_of_natDegree_ne hn)
    have hr : (p.map ι).IsRoot θ := hθ
    have hnr : θ ≠ q := by
      rintro rfl
      have H := hr.dvd (Polynomial.map_dvd ι hd)
      have h : (Q.map ι).eval (ι (q:ℚ)) = 0 := by simpa [ι] using H
      rw [eval_map_apply] at h
      exact h8 (ι.injective (by simpa using h))
    have hmnp : p = minpoly ℚ θ :=
      minpoly.eq_of_irreducible_of_monic hi (by simpa [aeval_def, eval_map, ι] using hθ) hp
    rcases classify θ (hr.dvd hmF) hnr with rfl | rfl | he
    · left
      apply hmnp.trans
      simpa [ι] using minpoly.eq_X_sub_C_of_algebraMap_inj (B := ℝ) (3 : ℚ) ι.injective
    · right; left
      apply hmnp.trans
      simpa [ι] using minpoly.eq_X_sub_C_of_algebraMap_inj (B := ℝ) (-3 : ℚ) ι.injective
    · exact Or.inr (Or.inr (hmnp ▸ he))
  obtain ⟨z,hz⟩ := three_divides_nextCoeff hm cls
  rw [eq, (monic_X_sub_C _).nextCoeff_mul hm, nextCoeff_X_sub_C, hz]
  intro h
  have H : (-q : ℤ) + 3 * z = 0 := by exact_mod_cast h
  exact mod3 ⟨z,by linarith⟩



end Deldor14.Star.CycleParity
/- Transfer the 59-vertex obstruction and Waddle's verified 58-vertex graph
to the Ramsey number for the star with 51 leaves. -/
namespace Deldor14.Star.CycleParity
open Waddle51 Finset SimpleGraph Matrix Polynomial ExcessOne OMA.ChenStar

theorem upper_of_classification {q n N : ℕ} (hq : 4≤q)
    (sz : N=q*(q-1)+3) (size : n+q=N) (mod3 : ¬ (3:ℤ) ∣ (q:ℤ))
    (cyclo : ∀ (θ:ℝ) {d:ℕ}, 0<d → d≤N → vieta ((q:ℝ)-1-θ^2) d=2 →
      θ=3 ∨ θ= -3 ∨ (minpoly ℚ θ).comp (-X)=minpoly ℚ θ) :
    Deldor14.Star.number n ≤ N := by
  classical
  have hq1 : 1≤q := by omega
  have hsizeR : (N:ℝ)=(q:ℝ)*((q:ℝ)-1)+3 := by exact_mod_cast (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hq1,Nat.cast_one,Nat.cast_ofNat] using congrArg (Nat.cast : ℕ → ℝ) sz : (N:ℝ)=(q:ℝ)*((q:ℝ)-1)+3)
  have hN : 9≤N := by
    have prod := Nat.mul_le_mul hq (by omega : 3≤q-1)
    omega
  have hNr : (9:ℝ)≤N := by exact_mod_cast hN
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra nonstar
  have minimum (v) : q ≤ G.degree v := by
    have l : Gᶜ.degree v < n :=
      lt_of_not_ge (fun ge => nonstar (star_isContained_of_le_degree Gᶜ ge))
    rw [degree_compl,Fintype.card_fin] at l
    omega
  have reg := Deficiency.regular_of_bounds G red minimum (by rw [Fintype.card_fin,sz,Nat.add_mul,one_mul]; omega)
  let D := Deficiency.graph G
  have dr (v) : D.degree v = 2 := Deficiency.degree G red (d:=q) (e:=2) (by rw [Fintype.card_fin,sz]) reg v
  let A := G.adjMatrix ℝ
  let J := ones (Fin N) ℝ
  have aa : A^2 = (((q:ℝ)-1):ℝ) • 1 + J - D.adjMatrix ℝ := by
    exact Deficiency.adj_square G red reg
  have rightJ : J*A = (q:ℝ) • J := by
    ext i j
    change (ones (Fin N) ℝ * G.adjMatrix ℝ) i j = _
    rw [mul_adjMatrix_apply]
    simp [J,ones,reg]
  have trJ : J.trace = N := by simp [J,ones,Matrix.trace,Matrix.diag]
  have herm : A.IsHermitian := by
    change Aᴴ = A
    rw [conjTranspose_eq_transpose_of_trivial]
    exact G.isSymm_adjMatrix
  let F := (G.adjMatrix ℚ).charpoly
  have rational : F.map (algebraMap ℚ ℝ) = A.charpoly := by
    dsimp only [F]
    rw [←Matrix.charpoly_map]
    apply congrArg Matrix.charpoly
    ext i j
    by_cases h : G.Adj i j <;> simp [A,Matrix.map_apply,adjMatrix_apply,h]
  obtain ⟨Q,hm,eq,h8,split,roots⟩ := rational_factor (q:=q) (low:=(N:ℝ)-4) (by omega) (by linarith [hNr]) (by nlinarith [hsizeR]) A J D dr herm aa rightJ trJ F
    (Matrix.charpoly_monic _) rational
  have no := trace_obstruction mod3 hm eq h8 split (fun θ hθ ne => by
    obtain ⟨d,pos,le,h⟩ := roots θ hθ ne
    exact cyclo θ pos le h)
  apply no
  have ht := Matrix.trace_eq_neg_charpoly_nextCoeff (G.adjMatrix ℚ)
  rw [G.trace_adjMatrix ℚ] at ht
  dsimp only [F]
  linarith

end Deldor14.Star.CycleParity
end

section
/- An explicit finite criterion for exact values at (2^m−1)^2+2. -/
namespace Deldor14.Star.CycleParity
open Polynomial

theorem upper_from_factors {q n N : ℕ} (hq:4≤q) (sz:N=q*(q-1)+3) (size:n+q=N)
    (mod3 : ¬ (3:ℤ) ∣ (q:ℤ))
    (lo : ¬IsSquare ((q:ℚ)-1-2)) (hi : ¬IsSquare ((q:ℚ)-1+2))
    (rows : ∀ k, 3≤k → k≤N → ∃ f : ℚ[X], f.Monic ∧ 2*f.natDegree=k.totient ∧
      ¬IsSquare (f.eval ((q:ℚ)-1)) ∧ ∀ z : ℂ, IsPrimitiveRoot z k → aeval (z+z⁻¹) f=0) :
    number n≤N := by
  apply upper_of_classification hq sz size mod3
  intro θ d hd bound eq
  right; right
  apply Lift963.even_of_real_factors (t:=(q:ℚ)-1) hd _ lo hi
  · exact fun k a b => rows k a (b.trans bound)
  · simpa using eq

theorem exact_power_two {m : ℕ} (second : 2 ≤ m) (q : ℕ) (fieldOrder : q = (2:ℕ)^m)
    (lo : ¬IsSquare ((q:ℚ)-1-2)) (hi : ¬IsSquare ((q:ℚ)-1+2))
    (rows : ∀ k, 3≤k → k≤q*(q-1)+3 → ∃ f : ℚ[X], f.Monic ∧ 2*f.natDegree=k.totient ∧
      ¬IsSquare (f.eval ((q:ℚ)-1)) ∧ ∀ z : ℂ, IsPrimitiveRoot z k → aeval (z+z⁻¹) f=0) :
    number ((q-1)^2+2)=q*(q-1)+3 := by
  have hq : 4≤q := by
    rw [fieldOrder]; exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) second
  have eqsize : (q-1)^2+2+q=q*(q-1)+3 := by
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
    simp [Nat.succ_eq_add_one];ring
  have mod3 : ¬(3:ℤ) ∣ (q:ℤ) := by
    rw [fieldOrder]
    intro e
    have h : 3∣2^m := by exact_mod_cast e
    exact (by decide : ¬3∣(2:ℕ)) ((by decide : Nat.Prime 3).dvd_of_dvd_pow h)
  apply Nat.le_antisymm (upper_from_factors hq rfl eqsize mod3 lo hi rows)
  rw [←eqsize,fieldOrder]
  exact UnitsRows.power_two_lower (by omega) (by omega)
end Deldor14.Star.CycleParity
end

section
/- Monic polynomials for the distinct nontrivial real traces on cycles of
even and odd length. These omit the eigenvalues 2 and −2. -/
namespace Deldor14.Star.CycleFactors
open Polynomial

noncomputable def U : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | n+2 => X*U (n+1)-U n

theorem U_degree (n:ℕ) : (U n).Monic ∧ (U n).natDegree=n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [U]
  | one => simp [U]
  | more n h h' =>
    have top : (X*U (n+1)).natDegree=n+2 := by rw [natDegree_X_mul h'.1.ne_zero,h'.2]
    have lt : (U n).degree < (X*U (n+1)).degree := by
      rw [degree_eq_natDegree h.1.ne_zero,degree_eq_natDegree (mul_ne_zero X_ne_zero h'.1.ne_zero),h.2,top]
      exact_mod_cast (by omega : n<n+2)
    change (X*U (n+1)-U n).Monic ∧ (X*U (n+1)-U n).natDegree=n+2
    exact ⟨(monic_X.mul h'.1).sub_of_left lt,by rw [sub_eq_add_neg,natDegree_add_eq_left_of_degree_lt (by simpa using lt),top]⟩

theorem U_eval (z:ℂ) (nz:z≠0) (n:ℕ) :
    (z^2-1)*z^n*aeval (z+z⁻¹) (U n)=z^(2*n+2)-1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [U]
  | one =>
    simp [U]
    field_simp
    ring
  | more n h h' =>
    simp only [U,map_sub,map_mul,aeval_X]
    calc
      _ = (z^2+1)*((z^2-1)*z^(n+1)*aeval (z+z⁻¹) (U (n+1))) -
          z^2*((z^2-1)*z^n*aeval (z+z⁻¹) (U n)) := by
        simp only [pow_succ];field_simp <;> ring
      _ = _ := by
        rw [h,h']
        simp only [show 2*(n+1)+2=2*n+4 by omega,show 2*(n+2)+2=2*n+6 by omega,
          pow_add]
        ring

noncomputable def D (n:ℕ) : ℚ[X] :=
  if n%2=0 then U ((n-2)/2) else U ((n-1)/2)+U ((n-3)/2)

theorem D_even (m:ℕ) : D (2*m+2)=U m := by
  unfold D
  rw [if_pos (by omega)]
  congr 1 <;> omega

theorem D_odd (m:ℕ) : D (2*m+3)=U (m+1)+U m := by
  unfold D
  rw [if_neg (by omega)]
  congr 2 <;> omega

theorem split (n:ℕ) (hn:2≤n) : (∃m,n=2*m+2) ∨ (∃m,n=2*m+3) := by
  by_cases e:n%2=0
  · exact Or.inl ⟨(n-2)/2,by omega⟩
  · exact Or.inr ⟨(n-3)/2,by omega⟩

theorem D_degree {n:ℕ} (hn:2≤n) : (D n).Monic ∧ (D n).natDegree=(n-1)/2 := by
  rcases split n hn with ⟨m,rfl⟩|⟨m,rfl⟩
  · rw [D_even]
    exact ⟨(U_degree m).1,(U_degree m).2.trans (by omega)⟩
  · rw [D_odd]
    have a := U_degree (m+1); have b := U_degree m
    have lt : (U m).degree < (U (m+1)).degree := by
      rw [degree_eq_natDegree b.1.ne_zero,degree_eq_natDegree a.1.ne_zero,b.2,a.2]
      exact_mod_cast Nat.lt_succ_self m
    exact ⟨a.1.add_of_left lt,by rw [natDegree_add_eq_left_of_degree_lt lt,a.2];omega⟩

theorem D_root {k n:ℕ} (hk:3≤k) (hn:2≤n) {z:ℂ} (pr:IsPrimitiveRoot z k) :
    aeval (z+z⁻¹) (D n)=0 ↔ k∣n := by
  have nz := pr.ne_zero (by omega)
  have z2 : z^2≠1 := pr.pow_ne_one_of_pos_of_lt (by decide) (by omega)
  have zm : z+1≠0 := by
    intro h
    have e:z= -1 := by linear_combination h
    exact z2 (by rw [e];norm_num)
  have root (i:ℕ) : z^i=1 ↔ k∣i := ⟨pr.dvd_of_pow_eq_one i, fun h => by obtain ⟨s,rfl⟩:=h;rw [pow_mul,pr.pow_eq_one,one_pow]⟩
  rcases split n hn with ⟨m,rfl⟩|⟨m,rfl⟩
  · rw [D_even,←root]
    have h := U_eval z nz m
    have non := mul_ne_zero (sub_ne_zero.mpr z2) (pow_ne_zero m nz)
    constructor
    · intro e;rw [e,mul_zero] at h;linear_combination -h
    · intro e;rw [e,sub_self] at h;exact (mul_eq_zero.mp h).resolve_left non
  · rw [D_odd,map_add,←root]
    have h : (z^2-1)*z^(m+1)*(aeval (z+z⁻¹) (U (m+1))+aeval (z+z⁻¹) (U m)) =
        (z+1)*(z^(2*m+3)-1) := by
      have f := U_eval z nz (m+1)
      have g := U_eval z nz m
      rw [show 2*(m+1)+2=2*m+4 by omega] at f
      simp only [pow_add] at f g ⊢
      linear_combination f+z*g
    have non := mul_ne_zero (sub_ne_zero.mpr z2) (pow_ne_zero (m+1) nz)
    constructor
    · intro e; rw [e,mul_zero] at h
      exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left zm)
    · intro e;rw [e,sub_self,mul_zero] at h;exact (mul_eq_zero.mp h).resolve_left non

end Deldor14.Star.CycleFactors
end

section
namespace Deldor14.Star.Universal
open Polynomial Finset
open scoped Polynomial Function

theorem sum_half_totient (n : ℕ) :
    (∑ d ∈ n.divisors.filter (fun d => 3 ≤ d), d.totient / 2) = (n-1)/2 := by
  by_cases nz : n=0
  · simp [nz]
  have pos := Nat.pos_of_ne_zero nz
  let s := n.divisors.filter (fun d => 3 ≤ d)
  have twice : 2*(∑ d ∈ s, d.totient/2) = ∑ d ∈ s, d.totient := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro d hd
    obtain ⟨a,ha⟩ := Nat.totient_even (mem_filter.mp hd).2
    omega
  have partition := sum_filter_add_sum_filter_not n.divisors (fun d => 3≤d) Nat.totient
  change (∑ d ∈ s, d.totient) + _ = _ at partition
  rw [Nat.sum_totient] at partition
  have small : n.divisors.filter (fun d => ¬3≤d) = if 2∣n then {1,2} else {1} := by
    ext d
    by_cases even : 2∣n
    · simp only [if_pos even,mem_filter,Nat.mem_divisors,ne_eq,nz,not_false_eq_true,and_true,
        mem_insert,mem_singleton]
      constructor
      · rintro ⟨dvd,lt⟩
        have := Nat.pos_of_dvd_of_pos dvd pos
        omega
      · rintro (rfl|rfl) <;> simp [even]
    · simp only [if_neg even,mem_filter,Nat.mem_divisors,ne_eq,nz,not_false_eq_true,and_true,
        mem_singleton]
      constructor
      · rintro ⟨dvd,lt⟩
        have := Nat.pos_of_dvd_of_pos dvd pos
        have ne : d≠2 := fun e => even (e ▸ dvd)
        omega
      · rintro rfl
        simp
  rw [small] at partition
  change (∑ d ∈ s, d.totient / 2) = _
  by_cases even : 2∣n
  · rw [if_pos even] at partition
    norm_num at partition
    obtain ⟨u,hu⟩ := even
    omega
  · rw [if_neg even] at partition
    simp at partition
    omega

theorem monic_product_eq_of_degree {I : Type*} (s : Finset I) (f : I → ℚ[X]) (P : ℚ[X])
    (mon : P.Monic) (fmon : ∀ i ∈ s, (f i).Monic)
    (cop : (s:Set I).Pairwise (fun i j => IsCoprime (f i) (f j)))
    (dv : ∀ i ∈ s, f i ∣ P) (deg : P.natDegree ≤ ∑ i ∈ s, (f i).natDegree) :
    (∏ i ∈ s, f i)=P := by
  apply eq_of_dvd_of_natDegree_le_of_leadingCoeff (Finset.prod_dvd_of_coprime cop dv)
  · simpa only [natDegree_prod_of_monic s f fmon] using deg
  · exact (monic_prod_of_monic s f fmon).trans mon.symm

end Deldor14.Star.Universal
end

section
/- Factor the cycle polynomial intrinsically using the minimal polynomials of
primitive real traces. Degree counts prove the identity for every order. -/
namespace Deldor14.Star.CycleFactors
open Finset Polynomial
noncomputable def ζ (k:ℕ) := Complex.exp (2*Real.pi*Complex.I/k)
noncomputable def μ (k:ℕ) := ζ k + (ζ k)⁻¹
noncomputable def F (k:ℕ) := minpoly ℚ (μ k)
def divs (n:ℕ) := n.divisors.filter (fun k => 3≤k)
theorem prim {k:ℕ} (h:0<k) : IsPrimitiveRoot (ζ k) k := Complex.isPrimitiveRoot_exp k h.ne'

theorem integral {k:ℕ} (h:3≤k) : IsIntegral ℚ (μ k) := by
  refine ⟨D k,(D_degree (by omega : 2≤k)).1,?_⟩
  exact (D_root h (by omega) (prim (by omega))).mpr dvd_rfl

theorem eval_F (k:ℕ) : aeval (μ k) (F k)=0 := minpoly.aeval ℚ _
theorem monic_F {k:ℕ} (h:3≤k) : (F k).Monic := minpoly.monic (integral h)
theorem irred_F {k:ℕ} (h:3≤k) : Irreducible (F k) := minpoly.irreducible (integral h)
theorem divides_D {k n:ℕ} (h:3≤k) (hn:2≤n) : F k ∣ D n ↔ k∣n := by
  have root := D_root h hn (prim (by omega))
  constructor
  · rintro ⟨q,eq⟩
    apply root.mp
    change aeval (μ k) (D n)=0
    rw [eq,map_mul,eval_F,zero_mul]
  · intro hd
    exact minpoly.dvd _ _ (root.mpr hd)

theorem coprime_F {i j : ℕ} (hi : 3 ≤ i) (hj : 3 ≤ j) (ne : i ≠ j) : IsCoprime (F i) (F j) := by
  have left {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (lt : a < b) : IsCoprime (F b) (F a) := by
    apply ((irred_F hb).isCoprime_or_dvd _).resolve_right
    intro divides
    have bad := (divides_D hb (by omega : 2≤a)).mp
      (divides.trans ((divides_D ha (by omega : 2≤a)).mpr dvd_rfl))
    exact (not_lt_of_ge (Nat.le_of_dvd (by omega) bad)) lt
  rcases lt_or_gt_of_ne ne with h|h
  · exact (left hi hj h).symm
  · exact left hj hi h

theorem degree_lower {k:ℕ} (h:3≤k) : k.totient/2 ≤ (F k).natDegree := by
  have b := Poly51.totient_le_twice_degree (prim (by omega : 0<k)) (F k) (monic_F h).ne_zero (eval_F k)
  omega

theorem product_D {n:ℕ} (hn:2≤n) : (∏ k∈divs n,F k) = D n := by
  apply Universal.monic_product_eq_of_degree _ _ _ (D_degree hn).1
  · intro k hk;exact monic_F (mem_filter.mp hk).2
  · intro k hk j hj ne
    exact coprime_F (mem_filter.mp hk).2 (mem_filter.mp hj).2 ne
  · intro k hk
    exact (divides_D (mem_filter.mp hk).2 hn).mpr (Nat.mem_divisors.mp (mem_filter.mp hk).1).1
  · rw [(D_degree hn).2,←Universal.sum_half_totient n]
    exact sum_le_sum (fun k hk => degree_lower (mem_filter.mp hk).2)

theorem degree_exact {n:ℕ} (hn:3≤n) : 2*(F n).natDegree=n.totient := by
  have hnm : n∈divs n := mem_filter.mpr ⟨Nat.mem_divisors_self _ (by omega),hn⟩
  have upper : ∑k∈divs n,(F k).natDegree=∑k∈divs n,k.totient/2 := by
    calc
      _ = (∏ k∈divs n,F k).natDegree := (natDegree_prod_of_monic (divs n) F (fun k hk => monic_F (mem_filter.mp hk).2)).symm
      _ = (n-1)/2 := (congrArg natDegree (product_D (by omega))).trans (D_degree (by omega)).2
      _ = _ := (Universal.sum_half_totient n).symm
  have eq := (Finset.sum_eq_sum_iff_of_le (fun k hk => degree_lower (mem_filter.mp hk).2)).mp upper.symm n hnm
  obtain ⟨a,ha⟩ := Nat.totient_even hn
  omega

theorem F_at_primitive {n:ℕ} (hn:3≤n) {z:ℂ} (pr:IsPrimitiveRoot z n) :
    aeval (z+z⁻¹) (F n)=0 := by
  have root := (D_root hn (by omega : 2≤n) pr).mpr dvd_rfl
  rw [←product_D (by omega),map_prod,Finset.prod_eq_zero_iff] at root
  obtain ⟨j,hj,zero⟩ := root
  have lj := (mem_filter.mp hj).2
  have jn := (Nat.mem_divisors.mp (mem_filter.mp hj).1).1
  have nj : n∣j := by
    apply (D_root hn (by omega) pr).mp
    obtain ⟨g,eq⟩ := (divides_D lj (by omega : 2≤j)).mpr dvd_rfl
    rw [eq,map_mul,zero,zero_mul]
  rwa [Nat.dvd_antisymm jn nj] at zero
end Deldor14.Star.CycleFactors
end

section
namespace Deldor14.Star.SquareExtraction
open Finset

theorem nonsquare_of_product {I J M : Type*} [CommMonoid M]
    (s : Finset I) (u : Finset J) (keep : I → J → Prop) [∀ i, DecidablePred (keep i)]
    [∀ j, DecidablePred (fun i => keep i j)] (F : I → M) (f : J → M) (n : J)
    (factor : ∀ i ∈ s, F i = ∏ j ∈ u.filter (keep i), f j)
    (other : ∀ j ∈ u, j≠n → Even (s.filter (fun i => keep i j)).card)
    (ns : ¬IsSquare (∏ i ∈ s, F i)) : ¬IsSquare (f n) := by
  classical
  intro sq
  apply ns
  have eq : (∏ i ∈ s, F i) = ∏ j ∈ u, (f j)^(s.filter (fun i => keep i j)).card := calc
    _ = ∏ i ∈ s, ∏ j ∈ u, (if keep i j then f j else 1) := by
      apply prod_congr rfl
      intro i hi
      rw [factor i hi,prod_filter]
    _ = ∏ j ∈ u, ∏ i ∈ s, (if keep i j then f j else 1) := prod_comm
    _ = _ := by
      apply prod_congr rfl
      intro j _
      rw [←prod_filter,prod_const]
  rw [eq]
  apply isSquare_prod
  intro j hj
  by_cases e : j=n
  · subst j
    exact sq.pow _
  · exact (other j hj e).isSquare_pow _

def primesProduct (s : Finset ℕ) : ℕ := ∏ p ∈ s, p
def selected (n : ℕ) : Finset (Finset ℕ) :=
  n.primeFactors.powerset.filter (fun s => 3≤n/primesProduct s)

private theorem product_dvd {s : Finset ℕ} {m : ℕ} (sub : s⊆m.primeFactors) :
    primesProduct s∣m :=
  (prod_dvd_prod_of_subset s m.primeFactors (fun t=>t) sub).trans (Nat.prod_primeFactors_dvd m)

theorem selected_fibre {n j : ℕ} (npos : 0<n) (j3 : 3≤j) (dvd : j∣n) :
    (selected n).filter (fun s => j∣n/primesProduct s) = (n/j).primeFactors.powerset := by
  have jp : 0<j := by omega
  have qp : 0<n/j := Nat.div_pos (Nat.le_of_dvd npos dvd) jp
  have mono := Nat.primeFactors_mono (Nat.div_dvd_of_dvd dvd) npos.ne'
  ext s
  simp only [selected,mem_filter,mem_powerset]
  constructor
  · rintro ⟨⟨sub,_⟩,jdiv⟩ p hp
    have ps := product_dvd sub
    have sd : primesProduct s∣n/j := (Nat.dvd_div_iff_mul_dvd dvd).mpr
      (by simpa only [Nat.mul_comm] using (Nat.dvd_div_iff_mul_dvd ps).mp jdiv)
    exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp (sub hp)).1,
      (dvd_prod_of_mem (fun t=>t) hp).trans sd, qp.ne'⟩
  · intro sub
    have sn := sub.trans mono
    have sd := product_dvd sub
    have ps := product_dvd sn
    have jd : j∣n/primesProduct s := (Nat.dvd_div_iff_mul_dvd ps).mpr
      (by simpa only [Nat.mul_comm] using (Nat.dvd_div_iff_mul_dvd dvd).mp sd)
    have pp := Nat.pos_of_dvd_of_pos ps npos
    exact ⟨⟨sn,j3.trans (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd npos ps) pp) jd)⟩,jd⟩

theorem selected_count {n j : ℕ} (npos : 0<n) (j3 : 3≤j) (dvd : j∣n) :
    ((selected n).filter (fun s => j∣n/primesProduct s)).card = 2^(n/j).primeFactors.card := by
  rw [selected_fibre npos j3 dvd,card_powerset]

theorem selected_even {n j : ℕ} (npos : 0<n) (j3 : 3≤j) (dvd : j∣n) (diff : j≠n) :
    Even ((selected n).filter (fun s => j∣n/primesProduct s)).card := by
  rw [selected_count npos j3 dvd]
  have jpos : 0<j := by omega
  have pos := Nat.div_pos (Nat.le_of_dvd npos dvd) jpos
  have more : 1<n/j := by
    by_contra! le
    have one : n/j=1 := by omega
    have eq := Nat.div_mul_cancel dvd
    rw [one,one_mul] at eq
    exact diff eq
  obtain ⟨b,eq⟩ := Nat.exists_eq_succ_of_ne_zero (card_pos.mpr (Nat.nonempty_primeFactors.mpr more)).ne'
  rw [eq,pow_succ]
  exact ⟨2^b, by omega⟩


theorem nonsquare_of_selected_product {M : Type*} [CommMonoid M] {n : ℕ} (npos : 0<n)
    (D f : ℕ → M)
    (factor : ∀ d, 3≤d → d∣n → D d=∏ j ∈ d.divisors.filter (fun j => 3≤j), f j)
    (ns : ¬IsSquare (∏ s ∈ selected n, D (n/primesProduct s))) : ¬IsSquare (f n) := by
  apply nonsquare_of_product (selected n) (n.divisors.filter (fun j => 3≤j))
    (fun s j => j∣n/primesProduct s) (fun s => D (n/primesProduct s)) f n _ _ ns
  · intro s hs
    obtain ⟨sub,large⟩ : s⊆n.primeFactors ∧ 3≤n/primesProduct s := by
      simpa only [selected,mem_filter,mem_powerset] using hs
    have dvd := Nat.div_dvd_of_dvd (product_dvd sub)
    rw [factor _ large dvd]
    apply prod_congr _ (fun _ _ => rfl)
    ext j
    simp only [mem_filter,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨d,_⟩,jl⟩
      exact ⟨⟨⟨d.trans dvd,npos.ne'⟩,jl⟩,d⟩
    · rintro ⟨⟨_,jl⟩,d⟩
      exact ⟨⟨d,by omega⟩,jl⟩
  · intro j hj dif
    obtain ⟨dv,jl⟩ := mem_filter.mp hj
    exact selected_even npos jl (Nat.mem_divisors.mp dv).1 dif

end Deldor14.Star.SquareExtraction
end

section
namespace Deldor14.Star.Modular127
open SquareExtraction Finset

variable {R : Type*} [CommRing R]

def step (t : R) : R×R → R×R
  | (a,b) => (t*a-b,a)

def combine (t : R) : R×R → R×R → R×R
  | (a,b),(c,d) => (a*c-b*d,b*c+a*d-t*b*d)

def fastPair (t : R) : ℕ → ℕ → R×R
  | 0,_ => (1,0)
  | h+1,n =>
    let P := fastPair t h (n/2)
    let doubled := combine t P P
    if n%2=0 then doubled else step t doubled

def fastD (t p n : ℕ) : ℕ :=
  let m := (n-1)/2
  let A := fastPair (t:ZMod p) (m.log2+1) m
  if n%2=0 then A.1.val else (A.1+A.2).val

def residueProduct (t p n : ℕ) : ℕ :=
  (∏ s ∈ selected n, fastD t p (n/primesProduct s)) % p

def avoidsSquare (p : ℕ) : ℕ → Bool
  | 0 => false
  | k+1 => (List.range p).all (fun a => decide (a*a%p ≠ k+1))

def passes (t p n : ℕ) : Bool :=
  decide (0<p) && avoidsSquare p (residueProduct t p n)

end Deldor14.Star.Modular127
end

section
namespace Deldor14.Star.Modular127

variable {R : Type*} [CommRing R]

def slow (t : R) : ℕ → R×R
  | 0 => (1,0)
  | n+1 => step t (slow t n)

private lemma step_combine (t : R) (P Q : R×R) :
    step t (combine t P Q) = combine t P (step t Q) := by
  cases P; cases Q
  ext <;> simp [step,combine] <;> ring

theorem slow_add (t : R) (n m : ℕ) : slow t (n+m) = combine t (slow t n) (slow t m) := by
  induction m with
  | zero => simp only [Nat.add_zero,slow]; cases slow t n; simp [combine]
  | succ m ih => rw [Nat.add_succ,slow,ih,step_combine]; rfl

theorem fastPair_correct (t : R) (h n : ℕ) (hn : n<2^h) : fastPair t h n=slow t n := by
  induction h generalizing n with
  | zero =>
    have eq : n=0 := by simpa using hn
    simp [eq,fastPair,slow]
  | succ h ih =>
    have half : n/2<2^h := by rw [pow_succ] at hn; omega
    rw [fastPair,ih _ half,←slow_add]
    split <;> rename_i e
    · congr 1
      omega
    · rw [←slow]
      congr 1
      omega

theorem map_slow {S : Type*} [CommRing S] (f : R →+* S) (t : R) (n : ℕ) :
    (f (slow t n).1, f (slow t n).2)=slow (f t) n := by
  induction n with
  | zero => simp [slow]
  | succ n ih =>
    rw [slow,slow,←ih]
    cases slow t n
    simp [step]

def slowD (t : R) (n : ℕ) : R :=
  let A := slow t ((n-1)/2)
  if n%2=0 then A.1 else A.1+A.2

theorem map_slowD {S : Type*} [CommRing S] (f : R →+* S) (t : R) (n : ℕ) :
    f (slowD t n)=slowD (f t) n := by
  simp only [slowD,← map_slow f]
  split <;> simp

end Deldor14.Star.Modular127
end

section
namespace Deldor14.Star.Modular127
open Polynomial Finset CycleFactors SquareExtraction

private theorem step_fst {R : Type*} [CommRing R] (t : R) (a : R×R) :
    (step t a).1=t*a.1-a.2 := by cases a; rfl
private theorem step_snd {R : Type*} [CommRing R] (t : R) (a : R×R) :
    (step t a).2=a.1 := by cases a; rfl

private theorem slow_eval (t : ℚ) (n : ℕ) : (slow t n).1=(U n).eval t := by
  induction n using Nat.twoStepInduction with
  | zero => simp [slow,U]
  | one => simp [slow,step,U]
  | more n ih ih' =>
    rw [slow,step_fst,ih']
    rw [slow,step_snd,ih,U,eval_sub,eval_mul,eval_X]

theorem evalD_integer (t n : ℕ) (hn : 2≤n) :
    ((slowD (t:ℤ) n:ℤ):ℚ)=(D n).eval (t:ℚ) := by
  have cast : ((slowD (t:ℤ) n:ℤ):ℚ)=slowD (t:ℚ) n := by
    simpa using map_slowD (Int.castRingHom ℚ) (t:ℤ) n
  rw [cast]
  rcases CycleFactors.split n hn with ⟨m,rfl⟩|⟨m,rfl⟩
  · rw [D_even,slowD,if_pos (by omega),show (2*m+2-1)/2=m by omega,slow_eval]
  · rw [D_odd,slowD,if_neg (by omega),show (2*m+3-1)/2=m+1 by omega,eval_add]
    rw [slow_eval,slow,step_snd,slow_eval]

theorem fastD_zmod (t p n : ℕ) (hp : 0<p) :
    ((fastD t p n:ℕ):ZMod p)=((slowD (t:ℤ) n:ℤ):ZMod p) := by
  let : NeZero p := ⟨hp.ne'⟩
  have cast : ((slowD (t:ℤ) n:ℤ):ZMod p)=slowD (t:ZMod p) n := by
    simpa using map_slowD (Int.castRingHom (ZMod p)) (t:ℤ) n
  rw [cast,fastD,fastPair_correct _ _ _ Nat.lt_log2_self,slowD]
  split <;> exact ZMod.natCast_zmod_val _

private lemma avoids_sound {p v : ℕ} (h : avoidsSquare p v=true) :
    ∀ a<p, a*a%p≠v := by
  cases v with
  | zero => simp [avoidsSquare] at h
  | succ k =>
    intro a ha
    have ok := List.all_eq_true.mp h a (List.mem_range.mpr ha)
    exact of_decide_eq_true ok

theorem passes_sound {t p n : ℕ} (ok : passes t p n=true) :
    ¬IsSquare (∏ s ∈ selected n, (D (n/primesProduct s)).eval (t:ℚ)) := by
  simp only [passes,Bool.and_eq_true,decide_eq_true_eq] at ok
  let : NeZero p := ⟨ok.1.ne'⟩
  let A : ℤ := ∏ s ∈ selected n, slowD (t:ℤ) (n/primesProduct s)
  have rat : (∏ s ∈ selected n, (D (n/primesProduct s)).eval (t:ℚ)) = (A:ℚ) := by
    dsimp only [A]
    rw [Int.cast_prod]
    apply prod_congr rfl
    intro s hs
    exact (evalD_integer t _ (by have h := (mem_filter.mp hs).2; omega)).symm
  have modp : ((residueProduct t p n:ℕ):ZMod p)=(A:ZMod p) := by
    rw [residueProduct,ZMod.natCast_mod]
    simp only [A,Nat.cast_prod,Int.cast_prod]
    apply prod_congr rfl
    intro s _
    exact fastD_zmod _ _ _ ok.1
  rw [rat,Rat.isSquare_intCast_iff]
  rintro ⟨x,hx⟩
  have residue : ((residueProduct t p n:ℕ):ZMod p)=(x:ZMod p)*(x:ZMod p) := by
    rw [modp,hx,Int.cast_mul]
  have val := congrArg ZMod.val residue
  have small : residueProduct t p n < p := Nat.mod_lt _ ok.1
  rw [ZMod.val_natCast,ZMod.val_mul,Nat.mod_eq_of_lt small] at val
  exact avoids_sound ok.2 (x:ZMod p).val (ZMod.val_lt _) val.symm

end Deldor14.Star.Modular127
end

section
/- A modular certificate for quadrilateral versus star Ramsey numbers. -/
namespace Deldor14.Star.Modular127
open Polynomial CycleFactors

theorem trace_value_nonsquare {t n p : ℕ} (large : 3 ≤ n) (ok : passes t p n = true) :
    ¬ IsSquare ((F n).eval (t : ℚ)) := by
  apply SquareExtraction.nonsquare_of_selected_product (by omega : 0<n)
    (fun d => (D d).eval (t:ℚ)) (fun d => (F d).eval (t:ℚ)) _ (passes_sound ok)
  intro d hd _
  simpa only [divs, Polynomial.eval_prod] using
    congrArg (Polynomial.eval (t:ℚ)) (product_D (by omega : 2≤d)).symm

theorem exact_of_witnesses {m q t : ℕ} (exponent : 2 ≤ m) (order : q = 2^m)
    (shift : t+1=q) (minus : ¬IsSquare ((q:ℚ)-1-2)) (plus : ¬IsSquare ((q:ℚ)-1+2))
    (witness : ∀ {k}, 3≤k → k≤q*(q-1)+3 → ∃p, passes t p k=true) :
    number ((q-1)^2+2)=q*(q-1)+3 := by
  apply CycleParity.exact_power_two exponent q order minus plus
  intro k hk bound
  obtain ⟨p,ok⟩ := witness hk bound
  have eqNat : (t:ℚ)+1=(q:ℚ) := by exact_mod_cast shift
  have eq : (q:ℚ)-1=(t:ℚ) := by linarith
  refine ⟨F k,monic_F hk,degree_exact hk,?_,fun _ z => F_at_primitive hk z⟩
  rw [eq]
  exact trace_value_nonsquare hk ok

end Deldor14.Star.Modular127
end

section
namespace Deldor14.Star.ModCert32
open Deldor14.Star.Modular127
private def packed0 : ℕ → ℕ
  | 0 => 0x3070303070717030b070d03070d0703070d030703070703030303030b110703
  | 1 => 0x707030d03070d03030711070b0d071703030d030707070311070d07031d0711
  | 2 => 0x31311070b110d1107070d07030d170303031103070d070707072b03130d1703
  | 3 => 0x7070303250d11110b03250d0707070d0711110707070703030d29030d0d0707
  | 4 => 0x7110d070307110d110d0d030711071107070d07070d11030d070d0703170d03
  | 5 => 0x110d0d0307250d170d070d07131f0d0303070d0d070707070d111103110d1103
  | 6 => 0x307250307170d250b0d0d07072507031307112903130d1103071103071f1113
  | 7 => 0x711030d030d350303070d07111107030d0d0d03290d070d0707111111110d03
  | 8 => 0x70d0d11072f2b030d07110d030d0d0703110d030707070d17070d030d072517
  | 9 => 0x13070d0707070d2b110725030d0d1103290735070311111303070d0713112913
  | 10 => 0x70d3b07110717030313110307110d110711110707070703131117070307070d
  | 11 => 0xb0d0d030b172f033b070d070d110d0d072f1103070d110707030d030b2b0d25
  | 12 => 0x70711070d0d0d1311070d071107071307110d0d03072b0d0307110d110d2507
  | 13 => 0x7171107030d0d03172511030d0d0711131d250307110711290d0d2903131103
  | 14 => 0xb070d0311072b070d070d07130d2503030d11031107250d0707291111131111
  | 15 => 0x307030d170717070d0735030711070307290d0d0717110311070d030b11070d
  | 16 => 0x1307250703072b1303070d070d132b0707031125070d070307071107170d170d
  | 17 => 0x30d2b11130d11030d07290d03130d03030d2507250707170711290707071703
  | 18 => 0x7110d030707170711070d031117070d07172b07070d110303430d0711111111
  | 19 => 0x70d112507110d1703070d03250d070d07071129070d0d030d072b13030d2511
  | 20 => 0xb13250707131111070d1117030d1103110d11070707071107070d030d111103
  | 21 => 0x3110d070707250d0b2f1107070d07030d071107030d0d030d07251111130707
  | 22 => 0x65070d1103070d170d031103070707130311250307110711350d0d2925130d0d
  | 23 => 0x111111070b0d0d0d25070d0d031d3b0d0707110307170d0707070d0317172b03
  | 24 => 0x3250d0d1707170d0d070d1113130703070725070d292917030d110d070d110d
  | 25 => 0x725290707070d0313130d030d13252f07072507070d110307070d07110d0d25
  | 26 => 0x29070d032511110313070d0d1113250d17070d0d0d070713071111030b0d0d13
  | 27 => 0x3131107070d1707172f2b03070d290335170d0703070d0d29250d07130d110d
  | 28 => 0x11132b290307112503070d030d11071107070d03110707030d07171113170d11
  | 29 => 0x703250d1111110d0707250707290d03070d0d130707110d1307250d0b110d17
  | 30 => 0x250711030d11290d170725030707110d070d111103110703130d1103130d2907
  | 31 => 0xd
  | _ => 0
private def byte0 (a : ℕ) := (packed0 (a/32) >>> (8*(a%32)))%256
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem block0 : ∀ j : Fin 993, passes 31 (byte0 j.val) (3+j.val)=true := by decide +kernel
theorem slice0 {n : ℕ} (lo : 3≤n) (hi : n≤995) : ∃p, passes 31 p n=true := by
  let j : Fin 993 := ⟨n-3,by omega⟩
  exact ⟨_,by simpa only [j,show 3+(n-3)=n by omega] using block0 j⟩
end Deldor14.Star.ModCert32
end

section
namespace Deldor14.Star.ModCert32
open Deldor14.Star.Modular127
theorem all_orders {n:ℕ} (lo : 3≤n) (hi : n≤995) : ∃p,passes 31 p n=true := by
  exact slice0 (by omega) hi

end Deldor14.Star.ModCert32
end

section
namespace Deldor14.Star.Modular127

theorem ramsey_star_963 : number 963 = 995 := by
  apply exact_of_witnesses (m:=5) (q:=32) (t:=31) (by decide) (by decide) (by decide)
  · rw [show ((32:ℕ):ℚ)-1-2 = ((29:ℤ):ℚ) by norm_num]
    rw [Rat.isSquare_intCast_iff]
    decide +kernel
  · rw [show ((32:ℕ):ℚ)-1+2 = ((33:ℤ):ℚ) by norm_num]
    rw [Rat.isSquare_intCast_iff]
    decide +kernel
  · exact fun lo hi => ModCert32.all_orders lo hi

end Deldor14.Star.Modular127
end

section
namespace Deldor14.Star.PeriodicMod
open SquareExtraction Finset

structure Cache where
  length : ℕ
  pairs : ℕ
  squares : ℕ
deriving Inhabited

def Cache.a (c : Cache) (i : ℕ) := (c.pairs >>> (16*i))%256
def Cache.b (c : Cache) (i : ℕ) := (c.pairs >>> (16*i+8))%256

def Cache.valid (c : Cache) (t p : ℕ) : Bool :=
  ((decide (0<p) && decide (0<c.length)) &&
    (decide (c.a 0 % p=1%p) && decide (c.b 0 % p=0))) &&
  ((List.range c.length).all (fun i =>
    let j := (i+1)%c.length
    (decide (c.b i ≤ p) && decide ((t*c.a i+p-c.b i)%p=c.a j%p)) &&
      decide (c.a i%p=c.b j%p)) &&
    (List.range p).all (fun u=>c.squares.testBit (u*u%p)))

def Cache.term (c : Cache) (p n : ℕ) : ℕ :=
  let i := ((n-1)/2)%c.length
  if n%2=0 then c.a i%p else (c.a i+c.b i)%p

def Cache.test (c : Cache) (p n : ℕ) : Bool :=
  !c.squares.testBit ((∏ s ∈ selected n, c.term p (n/primesProduct s))%p)

end Deldor14.Star.PeriodicMod
end

section
namespace Deldor14.Star.PeriodicMod
open Finset SquareExtraction Modular127

private lemma cast_modular {p a b : ℕ} (eq : a%p=b%p) : (a:ZMod p)=(b:ZMod p) := by
  rw [←ZMod.natCast_mod a p,←ZMod.natCast_mod b p,eq]

private lemma pair_valid {c : Cache} {t p : ℕ} (ok : c.valid t p=true) (m : ℕ) :
    (((c.a (m%c.length):ℕ):ZMod p),((c.b (m%c.length):ℕ):ZMod p))=slow (t:ZMod p) m := by
  simp only [Cache.valid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  induction m with
  | zero =>
    rw [Nat.zero_mod,slow]
    apply Prod.ext
    · simpa only [Nat.cast_one] using cast_modular (p:=p) (a:=c.a 0) (b:=1) ok.1.2.1
    · simpa only [Nat.cast_zero] using cast_modular (p:=p) (a:=c.b 0) (b:=0)
        (by simpa only [Nat.zero_mod] using ok.1.2.2)
  | succ m ih =>
    let i := m%c.length
    have h := ok.2.1 i (List.mem_range.mpr (Nat.mod_lt _ ok.1.1.2))
    let j := (i+1)%c.length
    have eq : (m+1)%c.length=j := by simp [j,i,Nat.add_mod]
    rw [slow,←ih,eq]
    change (((c.a j:ℕ):ZMod p),((c.b j:ℕ):ZMod p)) =
      ((t:ZMod p)*c.a i-c.b i,(c.a i:ZMod p))
    apply Prod.ext
    · have sub : c.b i ≤ t*c.a i+p := by omega
      have h1 := (cast_modular h.1.2).symm
      simp only [Nat.cast_sub sub,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,add_zero] at h1
      exact h1
    · exact (cast_modular h.2).symm

theorem Cache.term_eq {c : Cache} {t p : ℕ} (ok : c.valid t p=true) (n : ℕ) :
    c.term p n=fastD t p n := by
  have hp : 0<p := by
    simp only [Cache.valid,Bool.and_eq_true,decide_eq_true_eq] at ok
    exact ok.1.1.1
  let : NeZero p := ⟨hp.ne'⟩
  have cert := pair_valid ok ((n-1)/2)
  rw [fastD,fastPair_correct _ _ _ Nat.lt_log2_self,←cert]
  unfold Cache.term
  split
  · exact (ZMod.val_natCast _ _).symm
  · rw [ZMod.val_add,ZMod.val_natCast,ZMod.val_natCast,←Nat.add_mod]

theorem Cache.test_sound {c : Cache} {t p n : ℕ} (ok : c.valid t p=true)
    (cert : c.test p n=true) : passes t p n=true := by
  have equiv : (∏ s ∈ selected n, c.term p (n/primesProduct s))%p=residueProduct t p n := by
    simp only [residueProduct,Cache.term_eq ok]
  rw [Cache.test,equiv] at cert
  have info := ok
  simp only [Cache.valid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at info
  rw [passes,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨info.1.1.1,?_⟩
  cases val : residueProduct t p n with
  | zero =>
    have hits := info.2.2 0 (List.mem_range.mpr info.1.1.1)
    simp only [Nat.zero_mul,Nat.zero_mod] at hits
    simp [val,hits] at cert
  | succ k =>
    apply List.all_eq_true.mpr
    intro a ha
    apply decide_eq_true
    intro eq
    have hits := info.2.2 a ha
    rw [eq] at hits
    simp [val,hits] at cert

theorem table_sound {keys : List ℕ} {row : ℕ → Cache} {t p n : ℕ}
    (valid : keys.all (fun q => (row q).valid t q)=true)
    (ok : (decide (p∈keys) && (row p).test p n)=true) : passes t p n=true := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at ok
  exact Cache.test_sound (List.all_eq_true.mp valid p ok.1) ok.2

end Deldor14.Star.PeriodicMod
end

section
namespace Deldor14.Star.CacheData128
open PeriodicMod

def row : ℕ → Cache
  | 3 => ⟨6, 0x20002020002010001010001, 0x3⟩
  | 5 => ⟨5, 0x4000304020301020001, 0x13⟩
  | 11 => ⟨12, 0xa00050a090505090a05000a010006010206060201060001, 0x23b⟩
  | 13 => ⟨7, 0xc00030c050308050a08010a0001, 0x161b⟩
  | 17 => ⟨16, 0x1000091005090e05050e090510090010010008010c08030c0c03080c01080001, 0x1a317⟩
  | 19 => ⟨20, 0x1200061203060e03080e0e08030e06031206001201000d01100d05100b05050b10050d10010d0001, 0x30af3⟩
  | 23 => ⟨22, 0x16000b16120b151204150404150412150b12160b001601000c01050c020513021313021305020c05010c0001, 0x5335f⟩
  | 29 => ⟨14, 0x1c00121c1912191912191c12001c01000b01040b04040b04010b0001, 0x13d122f3⟩
  | 31 => ⟨15, 0x1e001c1e171c0a17070a0b071a0b051a1405181415180815030801030001, 0x121d47b7⟩
  | 37 => ⟨36, 0x24001524041506041206171211171b11081b1b08111b17111217061204061504241500240100100121101f21131f0e13140e0a141d0a0a1d140a0e14130e1f13211f102101100001, 0x165e211e9b⟩
  | 41 => ⟨14, 0x280025281a251a1a251a28250028010004010f040f0f040f01040001, 0x1b382b50737⟩
  | 43 => ⟨86, 0x2a00022a28020428260406262406082422080a22200a0c201e0c0e1e1c0e101c1a10121a18121418161416161416181412181a12101a1c100e1c1e0e0c1e200c0a20220a08222408062426060426280402282a02002a01002901032927030527250507252307092321090b211f0b0d1f1d0d0f1d1b0f111b1911131917131517151517151317191311191b110f1b1d0f0d1d1f0d0b1f210b0921230907232507052527050327290301290001, 0x35883a3ee53⟩
  | 47 => ⟨46, 0x2e000e2e280e2528062514062b14242b112408110c080c0c080c110824112b24142b0614250628250e282e0e002e0100210107210a07290a1b29041b0b041e0b271e2327232327231e270b1e040b1b04291b0a29070a210701210001, 0x4351b2753df⟩
  | 53 => ⟨52, 0x34002034252003251a030d1a230d2123162105161e052a1e042a2a041e2a051e1605211623210d231a0d031a250320253420003401001501101532101b32281b122814121f14301f17300b17310b0b31170b30171f30141f121428121b28321b1032151001150001, 0x12dd703303aed3⟩
  | 59 => ⟨60, 0x3a00323a263238263538083513082d13202d07201f07241f392405392f05052f390524391f24071f20072d20132d081335083835263832263a32003a01000901150903150603330628330e281b0e341b1c34171c021736020c36360c023617021c17341c1b340e1b280e3328063303061503091501090001, 0x22b62183e7b92bb⟩
  | 61 => ⟨62, 0x3c00383c253807253b072c3b272c1d272d1d0d2d140d1a14311a243109240909240931241a31141a0d142d0d1d2d271d2c273b2c073b250738253c38003c0100050118053618023611021611201610203010293023290c23190c3419343419340c19230c292330291030201016201116021136021836051801050001, 0x1713e6940a59f23b⟩
  | 67 => ⟨17, 0x4200074213073d13173d2e17392e18392b180a2b150a2c15062c30063c30013c0001, 0x359c281ba27ebc653⟩
  | 71 => ⟨35, 0x46000f463c0f083c2108412139410339280324283b24023b350237352d37332d2a331d2a141d1a14101a121045120c45230c1f23441f0e44060e26063f260b3f380b01380001, 0x1164729716b1d977f⟩
  | 73 => ⟨72, 0x48001348051320052c20082c17084217254222252f22162f2e16352e2a35192a43191043431019432a19352a2e35162e2f16222f25224225174208172c08202c052013054813004801003601443629441d29411d32410732240727241a27331a1b33141b1f14301f06303906063930061f30141f1b14331b1a33271a24270724320741321d41291d4429364401360001, 0x1eb22c742790b8d135f⟩
  | 79 => ⟨13, 0x4e001f4e431f19431b19071b4807344836340c36300c01300001, 0x130b409e755186fd2f37⟩
  | 83 => ⟨82, 0x5200275239273e390f3e110f45111f45321f0b32130b4e130a4e1e0a411e084126080426370409370909370904372604082641081e410a1e4e0a134e0b13320b1f32451f11450f113e0f393e27395227005201002c011a2c151a441542440e42340e21344821404805404905354912354b122d4b4f2d1c4f4a1c4a4a1c4a4f1c2d4f4b2d124b35124935054940054840214834210e34420e444215441a152c1a012c0001, 0x26873a80b1372fea31e9b⟩
  | 101 => ⟨102, 0x64004b64204b322038325d38275d0c27470c10472a10422a3a421c3a401c14403414133426133c26073c1507221537225337535337532237152207153c07263c13263413143440141c403a1c423a2a42102a47100c47270c5d27385d323820324b20644b006401001a01451a33452d33082d3e08593e1e59551e3b55233b2b23492b25495125315152313f52293f5e29505e43502e43122e12122e12432e50435e50295e3f29523f31525131255149252b49232b3b23553b1e55591e3e59083e2d08332d45331a45011a0001, 0x1391b7f0d30552a832c3fb6273⟩
  | 103 => ⟨52, 0x66004f662b4f1a2b421a0d42280d14281c14221c43221d430b1d1d0b431d22431c22141c28140d28420d1a422b1a4f2b664f0066010018013c184d3c254d5a253f5a533f4b53454b24454a245c4a4a5c244a45244b45534b3f535a3f255a4d253c4d183c01180001, 0x16380e9115bd964257768fe397⟩
  | 107 => ⟨106, 0x6a00576a1d57411d5e41675e28673728613742612e42692e1569651549654b49244b032418033118643119644f19394f623954625454625439624f39194f641931641831031824034b24494b6549156569152e69422e61423761283767285e67415e1d41571d6a57006a010014014e142a4e0d2a040d430434430a34290a3d29023d56020656220620224720684753683a53073a52071c52321c093217091717091732091c32521c07523a07533a68534768204722200622560602563d02293d0a29340a433404430d042a0d4e2a144e01140001, 0x27816ea9821633397be6a897e1b⟩
  | 109 => ⟨18, 0x6c005b6c045b5a045a5a045a5b046c5b006c010012016912136913136913126901120001, 0x1752639f4e85b003685cbe7192bb⟩
  | 113 => ⟨57, 0x700063701f636d1f1a6d1d1a291d5d29125d2e123d2e113d40115840265869264c69374c103738105a384a5a2a4a3e2a233e592351591c51551c205518204e18334e473327471727391761393a61253a08254b08194b31196031346043345f43145f481454485754045752040e52010e0001, 0x1a75e89ae2121f33e1211d645eb97⟩
  | _ => default

def primes : List ℕ := [3, 5, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 101, 103, 107, 109, 113]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem rows_valid : primes.all (fun p => (row p).valid 127 p)=true := by decide +kernel

end Deldor14.Star.CacheData128
end

section
namespace Deldor14.Star.PeriodicMod

def byteAt (packed j : ℕ) := (packed >>> (8*j))%256

def sliceOK (keys : List ℕ) (row : ℕ → Cache) (start len packed : ℕ) : Bool :=
  (List.range len).all fun j =>
    let p := byteAt packed j
    decide (p ∈ keys) && (row p).test p (start+j)

structure Witness (keys : List ℕ) (row : ℕ → Cache) where
  start : ℕ
  len : ℕ
  packed : ℕ
  checked : sliceOK keys row start len packed=true

def fetch {keys : List ℕ} {row : ℕ → Cache} (a : Array (Witness keys row)) (i : ℕ) :
    Witness keys row := (a[i]?).getD ⟨0,0,0,rfl⟩

theorem range_covered {n lo hi count : ℕ} {keys : List ℕ} {row : ℕ → Cache}
    (a : Array (Witness keys row)) (length : hi < lo+32*count)
    (layout : ∀ i : Fin count, (fetch a i.val).start = lo+32*i.val ∧
       (fetch a i.val).len = min 32 (hi+1-(lo+32*i.val)))
    (lower : lo ≤ n) (upper : n≤hi) :
    ∃ p, (decide (p∈keys) && (row p).test p n)=true := by
  let i : Fin count := ⟨(n-lo)/32,by omega⟩
  let r := fetch a i.val
  have first : r.start=lo+32*i.val := (layout i).1
  have last : r.len=min 32 (hi+1-(lo+32*i.val)) := (layout i).2
  have left : r.start≤n := by rw [first];dsimp [i];omega
  have right : n-r.start<r.len := by rw [first,last];dsimp [i];omega
  have h := List.all_eq_true.mp r.checked (n-r.start) (List.mem_range.mpr right)
  change (decide (byteAt r.packed (n-r.start) ∈ keys) &&
    (row (byteAt r.packed (n-r.start))).test (byteAt r.packed (n-r.start)) (r.start+(n-r.start)))=true at h
  rw [show r.start+(n-r.start)=n by omega] at h
  exact ⟨_,h⟩
end Deldor14.Star.PeriodicMod
end

section
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3 : Witness primes row := ⟨3,32,0x30d03030d0b0b030b0b0d030b110b030b05031103050d0303030303110b0503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r35 : Witness primes row := ⟨35,32,0xd110311030b1703031713170b05110d030313030d0d0d031117171303051111,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r67 : Witness primes row := ⟨67,32,0x3050d0d0d0d0d110d0d0d130313130303030d0313110b0d0b050d0311110b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r99 : Witness primes row := ⟨99,32,0x11110303110b0b110b030d130b110b0d0d0513110d0b0d03031313030d0b0b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r131 : Witness primes row := ⟨131,32,0xb130d0d03051329110d1d031d0b0d1113110d11171325030d050d0d03110d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r163 : Witness primes row := ⟨163,32,0x17050d0311110d0d0d0d1329110b0d03030d1d1113050b0d0d0517030b0d0b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r195 : Witness primes row := ⟨195,32,0x31113030d131d0d0b1313130b110b031311130d03110d11030d0d0313050b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r227 : Witness primes row := ⟨227,32,0x1105030d03111303032f0d1711110d030b0d0d0313170d0d11051717110b1703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r259 : Witness primes row := ⟨259,32,0x11051317110d13030d17170d0305130d03131303110b0b11111f1d030b111f11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r291 : Witness primes row := ⟨291,32,0x131117110d050b1d0b051f030d112503130d0d0d03110d110311132911050d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r323 : Witness primes row := ⟨323,32,0xd050d13110b2f03030d13030d0d1d130b051711130d110311171f0d03170d1f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r355 : Witness primes row := ⟨355,32,0x131313030d130d031113130d0d050d111d110d030d11130d0b031d030b130b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r387 : Witness primes row := ⟨387,32,0xd1113110d110b0d110d1d1311170b130d0d0d1f03050d0d0313131f110b1313,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r419 : Witness primes row := ⟨419,32,0xd171311030d130313110d030d0d0d1113050d0335110d11110d0d0d030b1703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r451 : Witness primes row := ⟨451,32,0x17111703250d130d0d130d0d13111303030d1703250b0d170b050d1f0b0d0b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r483 : Witness primes row := ⟨483,32,0x30d0317170b0b110d2917030b110b0317131d1117131703111717030b131113,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r515 : Witness primes row := ⟨515,32,0x13110d11030b0d11030d0d0d0d112f0d0d030d0d1d1d0d03110d2f131113130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r547 : Witness primes row := ⟨547,32,0x3050d0d171325030d0d1711031f1303031f251113050b0d0b1d0d17110d0b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r579 : Witness primes row := ⟨579,32,0x112f0d030d0d0b0d112f0d03110d0b130d050d110d17130303110d0d1711250d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r611 : Witness primes row := ⟨611,32,0xd0d0d1111110d1703131703171f0d0d0d0b1713170d1d030d05253d03050d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r643 : Witness primes row := ⟨643,32,0x1f0517110d1717110d1d1313030b0d03170d1f0d0d050b17250d0d030d111303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r675 : Witness primes row := ⟨675,32,0x30d0d0d130b3d110b1f17430b170b030d11131103110d030d0d0d131305110d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r707 : Witness primes row := ⟨707,32,0x110d0d17030517250d031f031317110d03130d030d170d1113131d0d110b0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r739 : Witness primes row := ⟨739,32,0x132f0d110d130d11130d0d0d0305131113110d030d110d110b0d1d0311110d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r771 : Witness primes row := ⟨771,32,0x30d171325050b0d0b470d17170d0b030d1113130d1117110313130d13050d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r803 : Witness primes row := ⟨803,32,0x1117130d110b0d03110d13030d0b17131d110d0d0d1317030d0d0d0d13130d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r835 : Witness primes row := ⟨835,32,0x130d0d03171f1f031105130d1105170d170d13110d250b110b0b17030b131d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r867 : Witness primes row := ⟨867,32,0x31313110d0d0b0d11250d030b0d1303111f0d1103050d1111130d1f1117170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r899 : Witness primes row := ⟨899,32,0x130d250d030d251103130d030d110d0d0d110d031f0d0d030d171313110d1d2f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r931 : Witness primes row := ⟨931,32,0x11030d131d11250d1d0517170d111d031313171f0d0b0d111105170d0b0d0b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r963 : Witness primes row := ⟨963,32,0x13110d030d113b13131317030b0d1f110d050d1103111103170d0d0313170d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r995 : Witness primes row := ⟨995,32,0x1d1103171f0b0d03031f131311051d170d1743111f0d110d11250d0d03051311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows0 := #[r3,r35,r67,r99,r131,r163,r195,r227,r259,r291,r323,r355,r387,r419,r451,r483,r515,r547,r579,r611,r643,r675,r707,r739,r771,r803,r835,r867,r899,r931,r963,r995]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice0 {n : ℕ} (lo : 3≤n) (hi:n≤1026) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows0 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1027 : Witness primes row := ⟨1027,32,0xd130d110d110d03171f1d13030d1711030d17030d17130d0d051f0311110b1f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1059 : Witness primes row := ⟨1059,32,0xd110d0311130b0d0b0d0d1311110b110d111313130b1d1311131703170b1d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1091 : Witness primes row := ⟨1091,32,0xd11171111050d130313170d0d0b0d1125130d03170d0d110d050d0d03051703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1123 : Witness primes row := ⟨1123,32,0x1d050d030d1725130d0d251f03110d0d0311171111110b11130d0d1f0b0d0b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1155 : Witness primes row := ⟨1155,32,0x30d0d11110b1d0d0d13170d0b0d0b03111f130d0d0d13031111170d0d110b1d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1187 : Witness primes row := ⟨1187,32,0x1705170d03050d110d170d131125131f250d1d0d1717132f0d05172913111d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1219 : Witness primes row := ⟨1219,32,0x30d1f1113110d13110d0d1d03051311030d4303170b0b0d0b110d03170d0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1251 : Witness primes row := ⟨1251,32,0x3290d031105250d111f1d17130d0b11130d0d1103132f030d490d3d11110d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1283 : Witness primes row := ⟨1283,32,0x1111170d111d0d0303111303170b25130d051313130d170311171f11030d1303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1315 : Witness primes row := ⟨1315,32,0x1311171f0d0d1d111713130d11130d0317111303130d0b110b0d0d030b111311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1347 : Witness primes row := ⟨1347,32,0x110d130d0d050b110d0517030b130d130d0d0d0d1311130d0317131d0d111313,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1379 : Witness primes row := ⟨1379,32,0xd0d1d131111130d031353030d131113171d17111f250d112f13131f030b0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1411 : Witness primes row := ⟨1411,32,0x13110d030d0d0d1f17050d11110b17030d110d030d111f110b131713110d0b17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1443 : Witness primes row := ⟨1443,32,0xd11130325170b0d0b1f0d171f0d1d030b13171703050d03171317030d0d0b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1475 : Witness primes row := ⟨1475,32,0x11130d11030d0d0311171d1311050d1f1d0d0d031f0d1303110d0d250311170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1507 : Witness primes row := ⟨1507,32,0x17110d1111130d030d251713110d130303131d131d110b0d0b1317030d11170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1539 : Witness primes row := ⟨1539,32,0xd111303130d130d11132f03110d0b111305130d1d0b1313030d0d030d113511,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1571 : Witness primes row := ⟨1571,32,0xd0d0d1f0d05171103110d1f11110d0d170d1d0317170d030d1f131703131d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1603 : Witness primes row := ⟨1603,32,0x11130d1d112f1d030d111717030b1d0303171d0d0d05530d13171d030d0d0b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1635 : Witness primes row := ⟨1635,32,0x1f0d13030d0d25170b051d0d0b11171f0d1f0d0d031d0d0d03131f1713050d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1667 : Witness primes row := ⟨1667,32,0xd050d1311050d0d130d171d1113110d031f25131711110d0d170d0d110b1f03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1699 : Witness primes row := ⟨1699,32,0x1117130d0d290d032f17250d030d2511030d0d11110b25110b0d1f1311110d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1731 : Witness primes row := ⟨1731,32,0x3111d0311110b110b05172511110d0313111d131f0b170d0d0d251713051f0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1763 : Witness primes row := ⟨1763,32,0x1311130d0d0b1703171313030d110d131f050d110d130d25112f1f0d031f1311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1795 : Witness primes row := ⟨1795,32,0x110d17031f1317131d0d0d1103110d0335131311130d25110d0d0d13490d0b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1827 : Witness primes row := ⟨1827,32,0x30d35290d0d0b110d03250311170b1713131d0d0311131f111317030d0d0d2f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1859 : Witness primes row := ⟨1859,32,0x13170d0d25110d1103110d030d0513291f052f0313250d030d0d1311110b0d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1891 : Witness primes row := ⟨1891,32,0x3130d1113110d0d110525131d110d0303131f110d0b0d1111130d170b112525,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1923 : Witness primes row := ⟨1923,32,0x31d0d03110b0b1111290d130b0d251117110d1103051f030d250d170d17130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1955 : Witness primes row := ⟨1955,32,0xd0d0d0d03111d03112f3d0d13052f11250d1f1f1d0d1111111317130d0d130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r1987 : Witness primes row := ⟨1987,32,0x170517130d0d1303111717130d0d13032f25170311050b1d0b052f170d132f03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2019 : Witness primes row := ⟨2019,32,0x110d030d0d11130d0b130d030b130b0d250d1311130b1303030d0d1717131d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows1 := #[r1027,r1059,r1091,r1123,r1155,r1187,r1219,r1251,r1283,r1315,r1347,r1379,r1411,r1443,r1475,r1507,r1539,r1571,r1603,r1635,r1667,r1699,r1731,r1763,r1795,r1827,r1859,r1891,r1923,r1955,r1987,r2019]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice1 {n : ℕ} (lo : 1027≤n) (hi:n≤2050) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows1 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2051 : Witness primes row := ⟨2051,32,0xd0d1729030d13170d131729130b1d11131725030d0d0d11110d130d17050d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2083 : Witness primes row := ⟨2083,32,0x13051d03110d0d1111250d1703292f03030d0d1113130b1f0d0d170311110b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2115 : Witness primes row := ⟨2115,32,0x11170d03130b0d0d0b050d17130d3b0313171711030d0d0d03170d130d111d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2147 : Witness primes row := ⟨2147,32,0xd13131103111711130d171311470d13130d171313172f290d050d3511110d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2179 : Witness primes row := ⟨2179,32,0x13031d0317132f030d2f0d1311050d0d0313131d130d0b030b1f1f170b111d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2211 : Witness primes row := ⟨2211,32,0xd1725030d05130d0b170d2f17110b13130d17110d0b0d11030d0d0d11051711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2243 : Witness primes row := ⟨2243,32,0x11051f110d0b13030d0d0d0d112917130d0d0d2f1f130d031717171303251d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2275 : Witness primes row := ⟨2275,32,0xd11131317110d0d0d05170d0d051d3b171d2503250d0b1111431d130d290b17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2307 : Witness primes row := ⟨2307,32,0x1f170d0d0d050d13110d43170b0d13111111250d17110d13110d0d03350b0d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2339 : Witness primes row := ⟨2339,32,0xd0d130d1111131f030d0d130d051d0d0d1117030d1111031329132f030b1703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2371 : Witness primes row := ⟨2371,32,0x1d030d030d0d0d1717051f25170b0d1d03110d030d0b1f1111050d110b130b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2403 : Witness primes row := ⟨2403,32,0x3110d350d110b0d0b171d03110d0d1117051d13131f0d030d171f130d112f0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2435 : Witness primes row := ⟨2435,32,0x11132511030d3d03031313490d130d11112917030d0d1311110d0d0d0d051711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2467 : Witness primes row := ⟨2467,32,0x170d170d110d2f17110d0d0d13130d130d110d1117050b0d0b050d1d110d0b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2499 : Witness primes row := ⟨2499,32,0xd110d11110d0b11131743170b1113112517130d172f0d111113130317110b13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2531 : Witness primes row := ⟨2531,32,0x1711171103051717030d25030d0b130d0d0d0d03171d35031325131111132503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2563 : Witness primes row := ⟨2563,32,0xd050d0313290d110d0d0d170311250303111f0d11130b0d1d170d0d0b110b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2595 : Witness primes row := ⟨2595,32,0x111d17110d0b0d1f25051d0d0b110b11110d0d0d03111711031f251313110d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2627 : Witness primes row := ⟨2627,32,0xd0513110311170d11171d03110d0d1f0d111d351d17110d0d0517170d170d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2659 : Witness primes row := ⟨2659,32,0xd1725030d0d1d030d130d0d1105130d130d13030d0d2513131717030b111703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2691 : Witness primes row := ⟨2691,32,0x30d1703111113110d0517031d130b03250d13131f110d031117131313051713,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2723 : Witness primes row := ⟨2723,32,0xd05131f0d0b1d11030d13130d0b1d110b130d110d130d03131f1d11130d0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2755 : Witness primes row := ⟨2755,32,0x2511170d110d1f111f050d110d172f290d170d031f1d0b110b171d2511111311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2787 : Witness primes row := ⟨2787,32,0x30d0d1113130d111105171d110d0b030d1f170d03051311131f1f030d0b1713,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2819 : Witness primes row := ⟨2819,32,0xd170d13030d0d0311131f1311050d2913050d0d0d1f171311170d0d1f170d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2851 : Witness primes row := ⟨2851,32,0xd111d031d130d110d1f17111711170d030d1d130d0b25110b0517290b0d1d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2883 : Witness primes row := ⟨2883,32,0xd111f3b250b0b170b130d030b112f131305170d030d0d110d0d0d031113130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2915 : Witness primes row := ⟨2915,32,0x110d0d1303132503170d0d250d110d0d13110d032511130d0d130d1f03050d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2947 : Witness primes row := ⟨2947,32,0xd110d17130d13030d1f1f13030d3b0303131d0d17050b111105172f110d0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r2979 : Witness primes row := ⟨2979,32,0x1325131311110b17170d1d030b1313110d170d0d13111311030d131717250d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3011 : Witness primes row := ⟨3011,32,0x130d0d1113050d0d11131717111111130d2517031f0d1703111325110d0d1f03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3043 : Witness primes row := ⟨3043,32,0x111d1311110d170313291317030b171d250d0d170d112f130d0d430d0b170b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows2 := #[r2051,r2083,r2115,r2147,r2179,r2211,r2243,r2275,r2307,r2339,r2371,r2403,r2435,r2467,r2499,r2531,r2563,r2595,r2627,r2659,r2691,r2723,r2755,r2787,r2819,r2851,r2883,r2915,r2947,r2979,r3011,r3043]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice2 {n : ℕ} (lo : 2051≤n) (hi:n≤3074) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows2 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3075 : Witness primes row := ⟨3075,32,0x32913111d110d0d0b0d3d2913110b110d0d1311031113030d172f030d171317,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3107 : Witness primes row := ⟨3107,32,0xd051329032f170d11290d0d0d0b350d131717030d0d17130d0d0d0d0d0b1717,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3139 : Witness primes row := ⟨3139,32,0x110d0d031f1113030d2f0d1303170d111711131f431f0b11130d0d130b111711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3171 : Witness primes row := ⟨3171,32,0x3170d13171113130b13530311110b030d131d0d1f0b0d0d110d13171111251d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3203 : Witness primes row := ⟨3203,32,0x25110d0d0d0b0d1103111713110b1f111f050d1113130d110d0d171311290d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3235 : Witness primes row := ⟨3235,32,0x130d1d111f130d032f050d1703051d03111717130d0d0b0d0b130d170b110b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3267 : Witness primes row := ⟨3267,32,0x17130d11170d0b11172f1d0d0d290b11130d1f110d132f0d03130d0311112f0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3299 : Witness primes row := ⟨3299,32,0x110d130d031d0d030d111f0317130d130d050d351d0d11031129170d170b0d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3331 : Witness primes row := ⟨3331,32,0x31735030d0d3d0d111d250d1d351d03172f0d030d131f130b1317130b111303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3363 : Witness primes row := ⟨3363,32,0x3110d03130b35110b0d170d1113250d0d113511250517031f0d2f130d250b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3395 : Witness primes row := ⟨3395,32,0xd0d0d13110d0d11031317130d0511251d171f03130d0d1111170d0d031f0d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3427 : Witness primes row := ⟨3427,32,0x17050d0d0d0d0d170d0d0d0d03111711030d1f110d110b0d0d05251711130b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3459 : Witness primes row := ⟨3459,32,0x11110d11131713130b031713130d1d111d1317250d0b0d03032913030d0b0d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3491 : Witness primes row := ⟨3491,32,0x11130d130305131111131d0311250d1313110d130d0d17030d130d0d03111303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3523 : Witness primes row := ⟨3523,32,0x170d170d11130d03130d1317350b0d03250d171f17050b0d0d17170311170b13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3555 : Witness primes row := ⟨3555,32,0xd2f1303110b170d0b130d110b0d0d031311132f030d0d11110d0d030d05130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3587 : Witness primes row := ⟨3587,32,0xd05130d11051f110d0d250311130d0d0d110d111311170d0d051717112f1f13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3619 : Witness primes row := ⟨3619,32,0x11250d171d0d13030d2917130d050d111d1313030d0d0b17111117030b172f17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3651 : Witness primes row := ⟨3651,32,0x130d0d110d050b1711050d030d11251f130d0d1103110d030d0d132f43112517,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3683 : Witness primes row := ⟨3683,32,0xd0d25111f0b0d130d25131f110b0d110305471113133b03171d1f0d170d1313,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3715 : Witness primes row := ⟨3715,32,0x131d3d110d110d03251f131103050d1713170d030d0d17130b0b0d03131d0b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3747 : Witness primes row := ⟨3747,32,0x3110d0d13113b11110d170311110b110d0d1d1d0317130d03111f0d0d0d130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3779 : Witness primes row := ⟨3779,32,0x131117170d0d1303035317251105132513050d251f350d11111325130d111703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3811 : Witness primes row := ⟨3811,32,0x13131d110d17131111050d0d17112511030d2f03130b0d0d110d0d130b350b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3843 : Witness primes row := ⟨3843,32,0x110d1d1f110d0b110b1f1f030b111d0d17251d0d17050d0325171f030d3d0b1d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3875 : Witness primes row := ⟨3875,32,0x171717110313171103170d250d1317290d0d0d1113130d0d0d0d1f0d11050d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3907 : Witness primes row := ⟨3907,32,0xd131711250d0d030d0d1725110d0d030d111f030d051d1111130d030d110b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3939 : Witness primes row := ⟨3939,32,0x111117030d110b1111130d0d0b0d1335250d170d0d111703030d17030d111f11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r3971 : Witness primes row := ⟨3971,32,0x250d0d2f03110d0d0311171f2f0b0d0d0d111f13350d1d0d1317170d03111d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4003 : Witness primes row := ⟨4003,32,0x17111711130d1d03111d130d030b0d0325131f0d13050d1f1d171f030b0d2f03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4035 : Witness primes row := ⟨4035,32,0x110d13250d292f430b0517250b130b03110d0d2f1711131113130d13130d130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4067 : Witness primes row := ⟨4067,32,0xd0d031313051d030d3517251111110d131d1d030d110d0d13051d0d0d111311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows3 := #[r3075,r3107,r3139,r3171,r3203,r3235,r3267,r3299,r3331,r3363,r3395,r3427,r3459,r3491,r3523,r3555,r3587,r3619,r3651,r3683,r3715,r3747,r3779,r3811,r3843,r3875,r3907,r3939,r3971,r4003,r4035,r4067]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice3 {n : ℕ} (lo : 3075≤n) (hi:n≤4098) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows3 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4099 : Witness primes row := ⟨4099,32,0x2f2f1f030d110d170d130d1311111311130d0d031711250d0b0d0d1311112503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4131 : Witness primes row := ⟨4131,32,0x30d1f0335050b0d0d050d1d17111d110d1117110d110d0303130d4311050d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4163 : Witness primes row := ⟨4163,32,0xd1d0d1f1111171f130d130d17130d1d17052f111311251f11170d1303170d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4195 : Witness primes row := ⟨4195,32,0x13110d171d1335030d051d1711131303170d131717170b0d0d3517170b110b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4227 : Witness primes row := ⟨4227,32,0x31117290d050b110d1d0d0d0d0d0b0317170d1713170d1311130d03170b2513,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4259 : Witness primes row := ⟨4259,32,0x350d0d110311470303130d0d1d130d0d0d050d03171725131d172f25030b1703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4291 : Witness primes row := ⟨4291,32,0xd110d13130d130d0d172f0d0d3b1d0d032f17112f0d2f111105170d170d1711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4323 : Witness primes row := ⟨4323,32,0x13110d0d110b0b13110d2f1f111117031d050d1313110d1113111703130d0d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4355 : Witness primes row := ⟨4355,32,0x130d0d0d1f130d110d0d13110b05110d0d251f110d13110311130d0d03051d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4387 : Witness primes row := ⟨4387,32,0xd130d110d130d171317171303250d13170d1d110d0513110b0d1d03111d0b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4419 : Witness primes row := ⟨4419,32,0xd111f0311170d0d0b0d171311350b0d0d2513171711170d030d25030d0b1f13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4451 : Witness primes row := ⟨4451,32,0x171f1f11030d130d032f1f0d0d110d13351f1d031f0d171111050d0d0d111703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4483 : Witness primes row := ⟨4483,32,0x11051711251113030d0d0d0d03110d0d1711172f13050b0d17030d170b131d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4515 : Witness primes row := ⟨4515,32,0x311171711171d0d0b1347170b111d11131d13110d111703171f1f0313050d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4547 : Witness primes row := ⟨4547,32,0x2f1f4311030d1311110d0d030d111311170d0d13132f0d250d131d1f170b1703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4579 : Witness primes row := ⟨4579,32,0x11110d1313110d0311131d130d05130d031117030d1f17110b130d03250d0d25,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4611 : Witness primes row := ⟨4611,32,0x111717030d050d0d11171d17250d3d110d290d0d030b2f29030d0d1313110d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4643 : Witness primes row := ⟨4643,32,0x17050d0d11350d11030d1d0313250d130d051717172911030d1f17130d0d1303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4675 : Witness primes row := ⟨4675,32,0x11111f031f130d131125130d03110d031f0d13112f110b130b0d17030b11130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4707 : Witness primes row := ⟨4707,32,0x1d0d0d0d11051311110d1f13251d0b030d0d0d1113110d1f030d0d1f110d1d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4739 : Witness primes row := ⟨4739,32,0xd110d1303111313031117031111250d1d1f0d030d350d17132f130d030d0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4771 : Witness primes row := ⟨4771,32,0x3170d030d170d1313050d170d0b2f0303251f031711170d0b171d0d47110b1f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4803 : Witness primes row := ⟨4803,32,0x3170d0313112f11170d0d130b0d1d0d0d051f0d1305170d1117170d110d0d1f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4835 : Witness primes row := ⟨4835,32,0x11170d0d3d0b0d131117130d0d110d172f110d0d17171311110d1d0d11114311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4867 : Witness primes row := ⟨4867,32,0xd110d0d13130d0d0d0d1f1111130d0d030d1d350d0513110b1325030d0d0b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4899 : Witness primes row := ⟨4899,32,0x131725110d110b11111d2f030b0d0b11130513111f0b0d1113110d031111171f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4931 : Witness primes row := ⟨4931,32,0x111117110d05172503130d0311110d130d1f0d031f1117170d05131303050d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4963 : Witness primes row := ⟨4963,32,0xd051f25110d2503131335170d1317131d1d1d0d0d05251113170d03130d0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r4995 : Witness primes row := ⟨4995,32,0x2f0d0d030d0b1f2517130d0d0d0d2f03130d0d0d032f170311131d0313110d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5027 : Witness primes row := ⟨5027,32,0x1111174911131703110d1717113513112b0317030d0d110d11170d11110d2511,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5059 : Witness primes row := ⟨5059,32,0x11470d030d172f132f1f1f1303050d17250d0d1111112f0d0d0d25170b1d0d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5091 : Witness primes row := ⟨5091,32,0x110d0d0311130b0d0b052f291f110b030d113511030b0d03031f1f2513131d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows4 := #[r4099,r4131,r4163,r4195,r4227,r4259,r4291,r4323,r4355,r4387,r4419,r4451,r4483,r4515,r4547,r4579,r4611,r4643,r4675,r4707,r4739,r4771,r4803,r4835,r4867,r4899,r4931,r4963,r4995,r5027,r5059,r5091]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice4 {n : ℕ} (lo : 4099≤n) (hi:n≤5122) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows4 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5123 : Witness primes row := ⟨5123,32,0xd051f170d0d3d03131313170d130d0d1f110d1f0d110d110d1f0d130d111713,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5155 : Witness primes row := ⟨5155,32,0x130d0d131f111f030d130d0d11110d030d110d0317110b111113251d0b0d0b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5187 : Witness primes row := ⟨5187,32,0x30d0d131d1f0b130d17251f0d0d0b110d13430d13051317110d1d170d0b0d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5219 : Witness primes row := ⟨5219,32,0x17111f0d11110d11030d0d1335052f1117050d031d130d031111131711113513,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5251 : Witness primes row := ⟨5251,32,0x110d0d03171f0d1717053d17130d1d0d031117110d0b1d0d35130d17110d2511,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5283 : Witness primes row := ⟨5283,32,0x31d13170d0b0b1111171f030d170d1117050d0d031f13110d1f0d0d1f130d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5315 : Witness primes row := ⟨5315,32,0x110d131303110d110d0d25131305252f2f050d1d17170d030d13171103111311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5347 : Witness primes row := ⟨5347,32,0x1f11172513111d1111350d0d03110d1313110d0d0d0d13130b0d17030d111703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5379 : Witness primes row := ⟨5379,32,0x111113030d1313110d2f1d030b1317111705130d13253d03030d1313130b1d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5411 : Witness primes row := ⟨5411,32,0xd0d0d1303050d0d11131f03110d1d0d13171f250d110d031305131103052511,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5443 : Witness primes row := ⟨5443,32,0x13110d03110d0d2f133d0d0d03132511030d0d110d2f250d1d0d1735110d0b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5475 : Witness primes row := ⟨5475,32,0x30d1303250b0d130b3d0d13110d0b0d11111317130d130303170d031105110d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5507 : Witness primes row := ⟨5507,32,0x2f130d2f03111f03251f170311250d132f0d0d030d0d13130d0d171711110d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5539 : Witness primes row := ⟨5539,32,0xd0d17110d1313031113171f1105130d031113250d0d1d130d292f290d111d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5571 : Witness primes row := ⟨5571,32,0x311251111130b0d0b130d03110d2f1117111f11030b1711031135170d053b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5603 : Witness primes row := ⟨5603,32,0xd110d110d351f13130d0d0311171f0d031f3d113d130d2f0d351f1d030d1313,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5635 : Witness primes row := ⟨5635,32,0xd0d0d1311131703250525170d050d032f1d13030d0d130d2f171d030b0d0b1f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5667 : Witness primes row := ⟨5667,32,0x2f131d0d13050b25110d170d0b1117030d251f111311250d030d1717170b2f13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5699 : Witness primes row := ⟨5699,32,0xd1f0d13130d1335030d25251105113517111f030d0d11110d130d0d030b1d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5731 : Witness primes row := ⟨5731,32,0x11130d110d0d0d29131317110d0b0d11170d0d03110b17110d05170d17130b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5763 : Witness primes row := ⟨5763,32,0x3112f0313110b110d131d0311170d03110d0d1d031117110d0d171f130d1d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5795 : Witness primes row := ⟨5795,32,0xd0d1f0d170b170d031313130d050d1113111d030d110d11110d351313294711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5827 : Witness primes row := ⟨5827,32,0x1105170d13132f03110d1f0d1d1f0d03130d0d0317130b0d0b1f131311111d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5859 : Witness primes row := ⟨5859,32,0xd250d110d0d0b0d0d2f25030b0d13251d17130d130b0d03111313170d0b3b17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5891 : Witness primes row := ⟨5891,32,0x13250d110d351713030d0d0d11111711130d17031f1f0d0d0d051d0d11111f11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5923 : Witness primes row := ⟨5923,32,0x11051711250d0d0d0d35131303110d030311171113130b11131117030b170b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5955 : Witness primes row := ⟨5955,32,0x17170d0d0d0b1f11111f2f1711110b111d1f0d130d1117110d130d0d0d130d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r5987 : Witness primes row := ⟨5987,32,0xd110d0d1311130311431d032f290d3d0d0d0d13170d110d0d1f17290d171d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6019 : Witness primes row := ⟨6019,32,0xd2917031f2f130311130d11030513131311170d0d0b0d1f110d1f0d0b171f13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6051 : Witness primes row := ⟨6051,32,0x30d0d030d1117170b050d3d13133503130d17131f110d111117131d13051d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6083 : Witness primes row := ⟨6083,32,0xd050d131f11171311294329130b0d0d1d131f0d0d0d0d03171717130d131329,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6115 : Witness primes row := ⟨6115,32,0x25110d03110d2f110d0d430d030517030d130d0d17110b110b0d0d2f3511250d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows5 := #[r5123,r5155,r5187,r5219,r5251,r5283,r5315,r5347,r5379,r5411,r5443,r5475,r5507,r5539,r5571,r5603,r5635,r5667,r5699,r5731,r5763,r5795,r5827,r5859,r5891,r5923,r5955,r5987,r6019,r6051,r6083,r6115]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice5 {n : ℕ} (lo : 5123≤n) (hi:n≤6146) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows5 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6147 : Witness primes row := ⟨6147,32,0x33b0d1111050b0d110d0d1f0b13130317112511030d173b35131f032f11170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6179 : Witness primes row := ⟨6179,32,0xd17130d110d0d0311110d030d050d17170d35170d2917110d0d0d0d11110d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6211 : Witness primes row := ⟨6211,32,0x1703170d1d170d110d0d1729130b0d350d111713170b170d0b051f13170d0b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6243 : Witness primes row := ⟨6243,32,0x31713030d0b0b0d3d2917030d110d1117050d110d170d1d030d35031d171317,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6275 : Witness primes row := ⟨6275,32,0x1113130d0d0b53030d170d17112f250d0d0d0d0313110d0d110d0d1f11051311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6307 : Witness primes row := ⟨6307,32,0xd050d17130d1311111f170d032517033b13173513050b1143171d0311111713,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6339 : Witness primes row := ⟨6339,32,0x131f0d030d0d131d0b0d0d03131113171d050d2f17110d0d1113250325130d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6371 : Witness primes row := ⟨6371,32,0x250d172913053b0d110d0d25130b11130d111711170d2f031113132503051711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6403 : Witness primes row := ⟨6403,32,0x1d1d0d0d11170d03130d1d17110b0d1103290d0d0d0d17110d3b1d130b1d0b17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6435 : Witness primes row := ⟨6435,32,0xd0d0d1f0d2f0d0d0b131d2911170b03110d171313110d1703171f1311111317,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6467 : Witness primes row := ⟨6467,32,0xd1325130d111d031113351f0d0d0d2913170d0d17130d1711050d0d0d0b3513,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6499 : Witness primes row := ⟨6499,32,0x110d0d0d111113130d0d0d1f0311171103130d1f25110b290b470d130b111713,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6531 : Witness primes row := ⟨6531,32,0xd031713111f1d0d130517030d0d0b0313171d1103350d11111f350d0d173b1d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6563 : Witness primes row := ⟨6563,32,0x13111313110d0d11110d0d130d0b171325050d0d17130d030d0d172511111303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6595 : Witness primes row := ⟨6595,32,0xd0d0d1135130d030d13132f030d17110d111703170d13170b251d030b0d1311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6627 : Witness primes row := ⟨6627,32,0x313130d0d050b0d17291d0d0b0d0d13111125110305171f0d0d0d1713110d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6659 : Witness primes row := ⟨6659,32,0x170d1d1103130d11130d350313130d2913051717131111170d131729030b0d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6691 : Witness primes row := ⟨6691,32,0x17172503251f130d0d17350d0d0b1f1f250d2f030d0b0d2f1f2f0d130b132503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6723 : Witness primes row := ⟨6723,32,0x110d17110d1f25110b171f0d0b132f110d05251313050d43130d2513110d0b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6755 : Witness primes row := ⟨6755,32,0x110d131d030b2f0303112f0d0d11110d1d350d0d0d2f0d03131f170d0d110d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6787 : Witness primes row := ⟨6787,32,0x171717130d132f11110d0d13112913030d111d111d110b132505170313170b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6819 : Witness primes row := ⟨6819,32,0x110d1317130d17110d0d0d1311110b0d0d052f0d0d0b170303351303250d0d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6851 : Witness primes row := ⟨6851,32,0x17132f0d11110d1111171d030d0b0d1d131125030d132f0313050d0d11250d25,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6883 : Witness primes row := ⟨6883,32,0x1f130d0311130d030d0d131125111d0303111d130d250b11110325130d0d0b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6915 : Witness primes row := ⟨6915,32,0xd2f2f1125111d0d0b130d0d0b110b172f111311030d0d1303130d0d0d051711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6947 : Witness primes row := ⟨6947,32,0x11050d0d0d171703170d1f03131f0d110b0d2503130d0d110d0d0d29110b0d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r6979 : Witness primes row := ⟨6979,32,0x11110d25130d130d1317251303051d1113131d030d2f0b13111317030b111711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7011 : Witness primes row := ⟨7011,32,0x13110d030d0d0b130b2f170d0d3517030d110d0d031743033517132513050d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7043 : Witness primes row := ⟨7043,32,0x13111711250b0d0d0311131311111d111705171f1313250d0d171f13130d1303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7075 : Witness primes row := ⟨7075,32,0x1d130d030d11172913131325031113111d1f0d0d0d11430d0b130d030b13250d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7107 : Witness primes row := ⟨7107,32,0x111113112f110b0d0d0d1d03110d13250d0d1d13030d130d031317171d0b130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7139 : Witness primes row := ⟨7139,32,0x17111311030d0d1103170d030d250d0d13130d03110d0d110d250d1f0313170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows6 := #[r6147,r6179,r6211,r6243,r6275,r6307,r6339,r6371,r6403,r6435,r6467,r6499,r6531,r6563,r6595,r6627,r6659,r6691,r6723,r6755,r6787,r6819,r6851,r6883,r6915,r6947,r6979,r7011,r7043,r7075,r7107,r7139]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice6 {n : ℕ} (lo : 6147≤n) (hi:n≤7170) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows6 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7171 : Witness primes row := ⟨7171,32,0x1111170d0d2913290d0525131d170d03030d3d112f110d111f051f2513111d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7203 : Witness primes row := ⟨7203,32,0x30d131d1d0b170d0b291f130d110d030d13251303052f0313111d030d0d0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7235 : Witness primes row := ⟨7235,32,0x13110d13030d1d17172f0d0d1705131711110d031d130d031713531f2505130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7267 : Witness primes row := ⟨7267,32,0x25050d1125170d0d171f1713030d13030d0d17110d0d13170b1d0d0d11110d1f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7299 : Witness primes row := ⟨7299,32,0x111f0d0d0d110b11111717130b0d0d1d13130d111f0b1703110d250d17110d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7331 : Witness primes row := ⟨7331,32,0x11130d1711110d3503111703170b250d0d170d131d0d1d110d25250d0d051f03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7363 : Witness primes row := ⟨7363,32,0x1f0525110d0d1f111313650d030d17132f111f0d0d0d3513110d2f1f13111311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7395 : Witness primes row := ⟨7395,32,0x171117110d1117110b05171313130d032517130d1f111313030d1d130d110b2f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7427 : Witness primes row := ⟨7427,32,0x25050d2f031313030d1717130d0d11170b1317110d0d2f2535051717110d0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7459 : Witness primes row := ⟨7459,32,0x17171703110d0d11110d0d1103053d250d0d0d0d11250b0d0b0d171f170d0d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7491 : Witness primes row := ⟨7491,32,0x30d0d132f050b171f0d0d35170d0b0311171f251d131d03111313430d250d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7523 : Witness primes row := ⟨7523,32,0x11131d11110b0d03112f350d110b17291d050d0d130d2f1f110d0d13113d1d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7555 : Witness primes row := ⟨7555,32,0x131f1d0317171f114305130d11053d3517132f13130d1d110d2f2f030b0d0b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7587 : Witness primes row := ⟨7587,32,0x11111f110d0d1d11111d0d030b110b0317110d0d25112f13030d1f030d0b1711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7619 : Witness primes row := ⟨7619,32,0x170d171103111f0303110d031111130d0d131d1113170d1117111329110b170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7651 : Witness primes row := ⟨7651,32,0x130d0d13111f1d2f0d051729110b2f2f0313171f0d0d0d0d1117250d110d0b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7683 : Witness primes row := ⟨7683,32,0x170d0d110d1f17130b0d17030b2525030d11170d03110d031f0d0d0317111311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7715 : Witness primes row := ⟨7715,32,0xd0d0d25170b2f110d0d1313110d110d0d111f031725110311130d170d051311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7747 : Witness primes row := ⟨7747,32,0x171d130d1113251113171d0d0d1f0d11031f1703130513290b050d3d0d173d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7779 : Witness primes row := ⟨7779,32,0x430d0d1111130b0d1325171711130b0d17051313170b1d110d0d17350d2f1d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7811 : Witness primes row := ⟨7811,32,0xd172511031f131703130d17110b0d13130d0d030d170d1111050d0d03116711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7843 : Witness primes row := ⟨7843,32,0x130517250d1125031d110d0d03110d1703131711250525111d170d290b0d130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7875 : Witness primes row := ⟨7875,32,0xd0d43130d0b0d110d131f170b0d0b1f1d132f1703111303111f2f0311050d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7907 : Witness primes row := ⟨7907,32,0x11050d1303050d1711250d030d0d13110d1f0d0313170d130d1f1f1117293d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7939 : Witness primes row := ⟨7939,32,0x11111713130d3d030d250d1f110d171117292f030d0b0b1111170d131d110d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r7971 : Witness primes row := ⟨7971,32,0x3130d1135110b2f11050d0d0d0d0b110d110d0d1f11172903170d110d130d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8003 : Witness primes row := ⟨8003,32,0x1311170d132913110311171317110d1317051713130d1103131f2f13030d250d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8035 : Witness primes row := ⟨8035,32,0xd111711111325031d130d1103050d2f3d11131111110b130b250d030b0d1711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8067 : Witness primes row := ⟨8067,32,0x30d1d0d1705132f0d0d17031117130d130d0d11131113170d131f1d110b1313,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8099 : Witness primes row := ⟨8099,32,0xd0d1313172513030d132f132f05110d171d1f03170d0d0d1329130d030b0d2f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8131 : Witness primes row := ⟨8131,32,0x25350d250d0d0d1d0d0d0d2f0d11170303110d0d1d110d0d110d171f11110d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8163 : Witness primes row := ⟨8163,32,0xd11030313170d110b130d130b0d1d032513170d0d110d03111d17030d13130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows7 := #[r7171,r7203,r7235,r7267,r7299,r7331,r7363,r7395,r7427,r7459,r7491,r7523,r7555,r7587,r7619,r7651,r7683,r7715,r7747,r7779,r7811,r7843,r7875,r7907,r7939,r7971,r8003,r8035,r8067,r8099,r8131,r8163]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice7 {n : ℕ} (lo : 7171≤n) (hi:n≤8194) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows7 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8195 : Witness primes row := ⟨8195,32,0xd1d0d0d030b0d031111170d13130d1d1d0d17110d1113110d17171303110d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8227 : Witness primes row := ⟨8227,32,0x170d2f17131d0d170d171d1317170d03131f1d1713052f110d0525030d110d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8259 : Witness primes row := ⟨8259,32,0xd131f030d0d1d1111110d0d0b0d0b0d13050d0d130b1f11032f0d031d172513,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8291 : Witness primes row := ⟨8291,32,0x1d0d250d03052f13030d0d0311110d170d0d0d0d1f13171311050d1711051d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8323 : Witness primes row := ⟨8323,32,0xd05171d111f1f13112917111f0d170d2513171113170b111f171d13110d0b35,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8355 : Witness primes row := ⟨8355,32,0x25131d112513352f1105170d0d1125110d0d0d0d13252f03130d1d1325110d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8387 : Witness primes row := ⟨8387,32,0xd0d0d0d25171711250d171d0d111d17172517112f11110d111d170d110b0d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8419 : Witness primes row := ⟨8419,32,0x11170d03170d0d0313132f1703110d2503110d03170b130d0d1743030b1f1703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8451 : Witness primes row := ⟨8451,32,0x30d17110d111317170d1d25130d170313110d25030b0d2f031717290d0d1f0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8483 : Witness primes row := ⟨8483,32,0x110517110d2517350313130d110b0d131f111d0d0d0d0d11111f0d2f0313171f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8515 : Witness primes row := ⟨8515,32,0x13111d03171335030d05250d13130d1713111703350d0b0d0b0d17130b130b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8547 : Witness primes row := ⟨8547,32,0x311131111050b110d1735350b0d0b0313131d0d0d110d111313171f0d110d1d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8579 : Witness primes row := ⟨8579,32,0x251f0d0d111117111d0d2f030d05130d1f110d111d17170d0d0d171f110b250d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8611 : Witness primes row := ⟨8611,32,0x110d0d111317130d0d131f131d0b1d030d0d25031d0d1d1325130d130d110b29,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8643 : Witness primes row := ⟨8643,32,0x3250d3b0d0b351711170d03110d1f11110d0d0d031317110d130d0311170d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8675 : Witness primes row := ⟨8675,32,0xd0d0d11111753030313131313052f170d0d2f132529130d0d17171f03050d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8707 : Witness primes row := ⟨8707,32,0xd051f110d2f17031325170d03171311130d0d030d110b130b050d3b11112503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8739 : Witness primes row := ⟨8739,32,0x110d0d1111111313130d0d2511350d0d0d05131111350d03030d1313170b1d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8771 : Witness primes row := ⟨8771,32,0x1d110d25111f130d030d1729110d111113130d030d130d0325131311110d1f11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8803 : Witness primes row := ⟨8803,32,0x130d0d03110d0d13130d0d0d0d0b17030311171f13110b291f0d170313112f03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8835 : Witness primes row := ⟨8835,32,0x2f110d03170b0d11110d2f1d11110b110d17170d03111d1703351f0313051325,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8867 : Witness primes row := ⟨8867,32,0x11171f0d03052f1717171d030d130d1317110d110d111311170d0d0d11110d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8899 : Witness primes row := ⟨8899,32,0xd0d0d171d1d13030d17250d1129130d030d1329110d1d110d131f130b130d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8931 : Witness primes row := ⟨8931,32,0x36d170d0d130b290d170d031d0d0b1117111f0d0d0b0d11110d0d0d0d052511,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8963 : Witness primes row := ⟨8963,32,0x110d1f0d25111711030d0d130d11491f030d0d0d170d0d03130d0d17030d1303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r8995 : Witness primes row := ⟨8995,32,0xd110d131117251111131f2503051703132f13030d0d0b1111170d030d0d1313,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9027 : Witness primes row := ⟨9027,32,0x1f110d0d110d0d17110d25130b0d17030d0d250d0311351103131729130b0d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9059 : Witness primes row := ⟨9059,32,0xd0d17132f1f131317130d131d11110d131117290d171103111f0d1111170d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9091 : Witness primes row := ⟨9091,32,0x1d130d0d130d131317171d35170b1d11130d0d033b25251f0b131f0d0b130b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9123 : Witness primes row := ⟨9123,32,0xd1725030d110b0d0d0d3d1711110d110d051d3d03051d0d11291f03110d250d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9155 : Witness primes row := ⟨9155,32,0xd131711030b0d0d1f1d0d0d11050d0d13110d0d0d1317170d0d0d1f0d052f11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9187 : Witness primes row := ⟨9187,32,0x11110d170d111311110d0d0d0313170313110d0313290d0d0b130d1711110b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows8 := #[r8195,r8227,r8259,r8291,r8323,r8355,r8387,r8419,r8451,r8483,r8515,r8547,r8579,r8611,r8643,r8675,r8707,r8739,r8771,r8803,r8835,r8867,r8899,r8931,r8963,r8995,r9027,r9059,r9091,r9123,r9155,r9187]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice8 {n : ℕ} (lo : 8195≤n) (hi:n≤9218) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows8 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9219 : Witness primes row := ⟨9219,32,0xd0d131d13110b170b2f35030d110b110d1d131713111f03112f130d110b1f1f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9251 : Witness primes row := ⟨9251,32,0x5317250d03050d1703350d1f13252513170d0d0d25111f130d052f3511110d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9283 : Witness primes row := ⟨9283,32,0xd112503251143110d25131303110d13030d1f110d051d0d1d172f130b0d2503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9315 : Witness primes row := ⟨9315,32,0x31d1303130b0d112505170d11290b3b13110d11030d17030d350d0313110d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9347 : Witness primes row := ⟨9347,32,0x1105130d111343031111173513290d170d0d17131d0d110d0d1f1f0d0d0b2f3d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9379 : Witness primes row := ⟨9379,32,0xd0517131f0d13031325173d13051711251713030d110b1d11130d130b111f13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9411 : Witness primes row := ⟨9411,32,0x3111703110513130d051d033b170b0d0d110d131f0b0d030d130d130d054317,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9443 : Witness primes row := ⟨9443,32,0xd050d25110d0d0303131703110b2f131713350d130d35111725170d03250d2f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9475 : Witness primes row := ⟨9475,32,0x17111d130d0d17293b050d110d1317031f110d0d0d130b110d0d1d0311110d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9507 : Witness primes row := ⟨9507,32,0x110d171113050b13112f0d1713170b0d0d17171f0313170d111717030d0d0d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9539 : Witness primes row := ⟨9539,32,0x2f171f11030d131111136b0d0d110d1325170d030d0d350311250d0d1f351703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9571 : Witness primes row := ⟨9571,32,0x250d1d1117130d0d2f3d1d1f13350d030313171117111d0d0b292f0d0b110b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9603 : Witness primes row := ⟨9603,32,0x3111f03110b250d0b1d0d030d0d17031711170d0d050d110d0d0d1f0d130b17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9635 : Witness primes row := ⟨9635,32,0xd110d11030b25110d1135171111170d170d1d1113110d030d0d0d1317111d1f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9667 : Witness primes row := ⟨9667,32,0x11050d13110d13250d17171311110d11131f0d030d0535111113170d11110b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9699 : Witness primes row := ⟨9699,32,0x250d1d130d0d2f130b0d1703132f13110d110d1117290d0d110d13134f113d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9731 : Witness primes row := ⟨9731,32,0xd110d1117110d0d030d0d1f110b110d0d112f031f0d17030d13130d0d051711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9763 : Witness primes row := ⟨9763,32,0x111f0d030d110d03131f130d0d0b0d25030d1725111325110d0d0d0317290b13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9795 : Witness primes row := ⟨9795,32,0x311130d111d1f110b051d13111125030d0d1313030d3b03110d2517351f1d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9827 : Witness primes row := ⟨9827,32,0xd052f0d11111d0311134313110d0d13171117030d170d1711050d3b0d0b2f13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9859 : Witness primes row := ⟨9859,32,0x1f2517031f1113030d253d0d25130d17030d130313110b650b1f0d130b0d3503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9891 : Witness primes row := ⟨9891,32,0x110d0d351113130d0b1325290d130b0313131d0d030b0d111129130d13110d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9923 : Witness primes row := ⟨9923,32,0x17110d0d110b0d110313250d0d0b2f13170d1d11132f17030d0d170d110d1303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9955 : Witness primes row := ⟨9955,32,0xd0d2511350d0d130d0d251703050d170d113d030d0d13111313171313110d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r9987 : Witness primes row := ⟨9987,32,0x3130d110d0d0b1f353d17030b251711130d0d0d03131f250d130d1f0d110d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10019 : Witness primes row := ⟨10019,32,0xd110d1303170d1303131f0325051313131f1d17170d1d0d110d171303171711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10051 : Witness primes row := ⟨10051,32,0x1713170317171d17131d170d0d0b17034f170d11110b171d1713250d0d0d170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10083 : Witness primes row := ⟨10083,32,0x110d0d031711170d0d1317030b170d031d0d17131f051703171117251113173d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10115 : Witness primes row := ⟨10115,32,0xd110d13110b25030d29172511051d11131d1725250d0d1325171d13030d1717,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10147 : Witness primes row := ⟨10147,32,0x1f0517110d0d0d11170d2f1313113b03030d350313110b0d0b2f0d03171f2511,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10179 : Witness primes row := ⟨10179,32,0x111f251111110b0d0b0b17170b170b0d0d051f1f0d0d0d1113130d0d0d0b0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10211 : Witness primes row := ⟨10211,32,0xd170d0d0313131313111d1f0d0d0d13130d17030d131f1711250d1103110d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows9 := #[r9219,r9251,r9283,r9315,r9347,r9379,r9411,r9443,r9475,r9507,r9539,r9571,r9603,r9635,r9667,r9699,r9731,r9763,r9795,r9827,r9859,r9891,r9923,r9955,r9987,r10019,r10051,r10083,r10115,r10147,r10179,r10211]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice9 {n : ℕ} (lo : 9219≤n) (hi:n≤10242) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows9 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10243 : Witness primes row := ⟨10243,32,0xd0517032f130d03110d131711291d031f131d1713051d0d112917030d0d1303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10275 : Witness primes row := ⟨10275,32,0x30d1f030d0b0d0d17132f170b0d2511131f13173b130d13130d0d0d1325130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10307 : Witness primes row := ⟨10307,32,0x1105171303052f030d0d0d1311172f29130d251335110d0d1305171f11111d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10339 : Witness primes row := ⟨10339,32,0xd0d1317130d132f0d131f0d0305130d1317130d0d0d3b1111251d030b0d0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10371 : Witness primes row := ⟨10371,32,0x131117030d1113170b1717030d111313130d0d0d17110d13030d13113b250d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10403 : Witness primes row := ⟨10403,32,0xd05130d130b0d03171113130d0d1d0d17112511172f1711111d1f0d110d1311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10435 : Witness primes row := ⟨10435,32,0x13130d030d0d0d031305131703051f110d110d130d11130d0d132f2f13170b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10467 : Witness primes row := ⟨10467,32,0x11111f110d11251111251d03110d0b110d131d1f1305133503132f1711111313,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10499 : Witness primes row := ⟨10499,32,0x111717110d11130d03130d0d0d11251113051d0d3b2f3517130d17110d0b2503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10531 : Witness primes row := ⟨10531,32,0x1d0d0d03250d3d290d0d0d0d351d130d030d251117130d0d0d170d25110d0b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10563 : Witness primes row := ⟨10563,32,0x3110d29130b0b110d13171711110d113b131d0d0d131f0d13171d0317253d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10595 : Witness primes row := ⟨10595,32,0x3525131117111d2f030d0d0d11052f110d03170317170d110d0d0d1311051311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10627 : Witness primes row := ⟨10627,32,0xd050d112f110d03351f1d13031713130d11350311110b0d11130d03110d0b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10659 : Witness primes row := ⟨10659,32,0x11291303130d0b0d11171d2f110d0d170d11251113171703031725031711170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10691 : Witness primes row := ⟨10691,32,0xd351d0d13110d130d131f03130b0d110d11251717170d110d171729030d0d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10723 : Witness primes row := ⟨10723,32,0xd0517113d171f0d0d2f0d0d110d0d03170d0d1f0d050b13110d1d130d171303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10755 : Witness primes row := ⟨10755,32,0x30d131f110b25110d133d0d0b290b030d0d13131311430d03170d25110d1317,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10787 : Witness primes row := ⟨10787,32,0x11111313030d170d0d0d17170d0d13112f130d030d0d0d1313132f0d110b1713,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10819 : Witness primes row := ⟨10819,32,0x1711170325290d1111130d1303054311030d0d030d130b0d0b17251f11110d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10851 : Witness primes row := ⟨10851,32,0x32f0d2513110b110b130d35130d6b030d171735030b1703111d0d250d050d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10883 : Witness primes row := ⟨10883,32,0x13170d0d110b1d11351317030d0d0d13170d0d0d251317030d0d0d0d03130d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10915 : Witness primes row := ⟨10915,32,0x110d1d0d1d1d17030d05131135111f17130d13170d0d0b0d131317290d0d0b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10947 : Witness primes row := ⟨10947,32,0xd11130d0d053d1311250d0d0b130b1f17130d170305251703130d0d0d0b3b25,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r10979 : Witness primes row := ⟨10979,32,0x130d130d03172503030d1d0d13110d0d25050d11130d35030d1113130d350d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11011 : Witness primes row := ⟨11011,32,0xd110d251d111d0d1d291f170d111703132f170d2f0d17111129170d0b0d0b25,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11043 : Witness primes row := ⟨11043,32,0x13111303170b0b17111f1f130b0d170317050d0d0311133517251703130d3511,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11075 : Witness primes row := ⟨11075,32,0x110d0d112f131d170d0d0d1313051d2f0d1147030d0d130311130d13250d170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11107 : Witness primes row := ⟨11107,32,0x1d13250d110d0d0313291f1303110d1113171f030d0513430b051f1711130b13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11139 : Witness primes row := ⟨11139,32,0xd0d171111170b0d0b0d0d0311110b2511113517250b1711031735131d111d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11171 : Witness primes row := ⟨11171,32,0xd1317110d050d171317170d0d110d3513110d110d0d1f110d0535110d051703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11203 : Witness primes row := ⟨11203,32,0x171717110d1125110d170d1117110d1317111f1135050b0d0d0d0d1d13110b25,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11235 : Witness primes row := ⟨11235,32,0x110d1d13110b1d171f051f250d0d17030d1d170d031113032f0d1f030d0d0b13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows10 := #[r10243,r10275,r10307,r10339,r10371,r10403,r10435,r10467,r10499,r10531,r10563,r10595,r10627,r10659,r10691,r10723,r10755,r10787,r10819,r10851,r10883,r10915,r10947,r10979,r11011,r11043,r11075,r11107,r11139,r11171,r11203,r11235]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice10 {n : ℕ} (lo : 10243≤n) (hi:n≤11266) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows10 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11267 : Witness primes row := ⟨11267,32,0x17250d1103110d1111171f030d11171f17110d0317170d170d051d131f170d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11299 : Witness primes row := ⟨11299,32,0xd0d1729130d0d110d0d0d170305350d032f170347111d0d0b1d0d130b112503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11331 : Witness primes row := ⟨11331,32,0x25171711111113111105250317130b111d110d0d0d112f2f03433d3513110d3d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11363 : Witness primes row := ⟨11363,32,0x13050d0d1311170d030d130317110d130d0d0d170d13111111174311030d130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11395 : Witness primes row := ⟨11395,32,0x110d1f03170d1d111113130d11170d0313110d0d0d110b350b130d0311117111,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11427 : Witness primes row := ⟨11427,32,0x1f110d3b131f17110d030d032f1d0b030d132f172505130d030d1f2f2f0d1311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11459 : Witness primes row := ⟨11459,32,0xd0d0d1303113d03032517130d0d171717252f030d250d03131713170d0d0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11491 : Witness primes row := ⟨11491,32,0x13350d0311110d1311130d0d0d1717110d170d0311171d0d0b051d0d110d1303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11523 : Witness primes row := ⟨11523,32,0xd111d03250b0b0d112f1f13110d1d111d1117130d0d0d1113170d0313431313,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11555 : Witness primes row := ⟨11555,32,0x11131711030d0d031113132511110d25132f0d111f0d171317171d0d03130d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11587 : Witness primes row := ⟨11587,32,0xd050d0d131f0d0d11351d1311111311031117131305130d0d0543290d110b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11619 : Witness primes row := ⟨11619,32,0xd1f1711110d170d0b13251311130b1113051311173b171703170d25110b1f0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11651 : Witness primes row := ⟨11651,32,0xd0d170d0305170d130d0d0d11110d0d2f0d0d1113130d0d11050d130313170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11683 : Witness primes row := ⟨11683,32,0xd130d1711251f0d0d293513030b170303131f110d110d131f2f17170b171311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11715 : Witness primes row := ⟨11715,32,0x17110d030d0d1f1f0b13170d0b1125030d0d0d113d1d0d110313170335051717,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11747 : Witness primes row := ⟨11747,32,0x1705130d11171d0d0d0d25171111130d25112f11171711250d131f0d0d250d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11779 : Witness primes row := ⟨11779,32,0x112f17030d0d131117170d290d130d13030d0d11110b2511110d1703111d0d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11811 : Witness primes row := ⟨11811,32,0xd110d03111d0d131705170313110b030d111d131d0b43130d1125170d051717,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11843 : Witness primes row := ⟨11843,32,0xd131f0d0d111f031313130311110d111113170d0d0d0d110d170d0d031f4313,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11875 : Witness primes row := ⟨11875,32,0x13110d030d1317111d050d2511110d0d170d130313110b0d110b1d130b0d0b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11907 : Witness primes row := ⟨11907,32,0x170d0d1d1305171f0d1717030d0d1d03132f1d3d0d1f0d13130d171f0d0b3b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11939 : Witness primes row := ⟨11939,32,0x2f1f1d110d110d11030d1f030d1343113b05170d25291711110d130d110b0d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r11971 : Witness primes row := ⟨11971,32,0xd110d11132f0d0d0d0d251d111113032513171f0d0b1d0d17350d0d0b113503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12003 : Witness primes row := ⟨12003,32,0x111d0d0d0d0d2511111117130b0d251d25110d1303113d030d250d0335110d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12035 : Witness primes row := ⟨12035,32,0xd173d0d11111d0d03171d2917130d131d0d171f170d1103351f1f1313051711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12067 : Witness primes row := ⟨12067,32,0xd05473d1311131717171717030d0d1113110d0d0d130b290b05170313131711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12099 : Witness primes row := ⟨12099,32,0x111f1f1113171313110d0d03111313112f051317170b170303110d25170b1d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12131 : Witness primes row := ⟨12131,32,0xd0d1713030513170d1325250d0b110d13171d0317170d111313170d030d1311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12163 : Witness primes row := ⟨12163,32,0x1313172f0d250d110d130d0d0311171703170d0d13130d0d2f353d032f110b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12195 : Witness primes row := ⟨12195,32,0x3111d29130d1711111f0d1313293b030d112f130d0d130303131d0d0d050d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12227 : Witness primes row := ⟨12227,32,0xd130d2f0d052503110d170d110d0d171d0d0d034f1735170d1f250d11110d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12259 : Witness primes row := ⟨12259,32,0xd0d0d0d171313110d0d1f1311050d111d0d1717130b0b170b131f030b0d1725,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows11 := #[r11267,r11299,r11331,r11363,r11395,r11427,r11459,r11491,r11523,r11555,r11587,r11619,r11651,r11683,r11715,r11747,r11779,r11811,r11843,r11875,r11907,r11939,r11971,r12003,r12035,r12067,r12099,r12131,r12163,r12195,r12227,r12259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice11 {n : ℕ} (lo : 11267≤n) (hi:n≤12290) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows11 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12291 : Witness primes row := ⟨12291,32,0xd1125130d130b0d131d0d352f0d2f1313131f0d030b2511110d3d0d13112525,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12323 : Witness primes row := ⟨12323,32,0x170d0d0d11111303030d0d030d2f1f0d0d110d1125130d0d0d0d0d1303172503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12355 : Witness primes row := ⟨12355,32,0xd112f17170d17030d05170d0d0517111d171311110d25111113171311110b29,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12387 : Witness primes row := ⟨12387,32,0x1f1113130d053513130d0d0d0b111317110d1d0d03250d0d0313170317110d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12419 : Witness primes row := ⟨12419,32,0x11110d3d13110d0d03170d130d05110d1f051f29130d3d131117132f030b1d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12451 : Witness primes row := ⟨12451,32,0x31317030d1f0d0d2f051d2f11170d1313112f0d0d1335110b05170d17130d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12483 : Witness primes row := ⟨12483,32,0x3131d0311110d111f171703251f0b2f0d052f1303130d030d3517030d0d5317,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12515 : Witness primes row := ⟨12515,32,0x17171313030b1d03031d130d0d112517172917030d170d1111250d110d051711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12547 : Witness primes row := ⟨12547,32,0x11051d1113351711110d0d2f1117170d0d0d0d112513130d0b050d25110d0b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12579 : Witness primes row := ⟨12579,32,0x130d13171d1113110b1743130b2f130d171713112f0b25111725250311110d1d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12611 : Witness primes row := ⟨12611,32,0x13170d0d2f05131d030d0d1711113d0d0d0d0d111d3d3d03110d2f1113051703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12643 : Witness primes row := ⟨12643,32,0xd2f1d03171f0d170d0d1313110d17030311171111050b0d0d250d030b2f2f13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12675 : Witness primes row := ⟨12675,32,0x3290d031713171311050d0d0d0d2f110d0d1711031117130d0d0d0d13110d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12707 : Witness primes row := ⟨12707,32,0xd0d0d1103130d110d171f35170d0d1f0d0d171d170d0d0d1105171725110d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12739 : Witness primes row := ⟨12739,32,0xd052f13110d13030d133d0d03051311131113170d0d0b130b3b0d030d171703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12771 : Witness primes row := ⟨12771,32,0x11170d030d1313110b131703172f3b170d0d0d11250b1711030d1317130d1711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12803 : Witness primes row := ⟨12803,32,0xd1f0d17110b1d1f110d25030d0b170d35130d0d13130d112f17170d1711251d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12835 : Witness primes row := ⟨12835,32,0x25131d0d0d131f2517130d0d030517110d110d1117173b110b0d1d1311110b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12867 : Witness primes row := ⟨12867,32,0x30d251113052511110d0d1f3b0d0b1317111f0d0d0d171111131f252f1f0d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12899 : Witness primes row := ⟨12899,32,0x131f171725170d03432917030d050d1713110d030d1125033d2f0d0d03173503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12931 : Witness primes row := ⟨12931,32,0x2f111d031d1325171305170d1711170d030d17110d0b1d0d0b1f2f1f13171d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12963 : Witness primes row := ⟨12963,32,0xd17171113351d1111130d030b110d031311471125050d1d1d110d030d291311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r12995 : Witness primes row := ⟨12995,32,0x130d1d0d0d2525130d1f0d0d0d170d0d170d0d03130d0d03110d251d13111713,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13027 : Witness primes row := ⟨13027,32,0xd0d0d1d110d3b1711171f130d0d13030313172517050b1711053d2f11110b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13059 : Witness primes row := ⟨13059,32,0x25110d0d11110b2f17130d17110d130d0d13350d13110d0d17134f0325130d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13091 : Witness primes row := ⟨13091,32,0xb0d1f111313131117170d171d0b250d131117031f0d0d031113131703051f11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13123 : Witness primes row := ⟨13123,32,0x171d0d0311110d0313251713030d1d11032f0d130d11130d110d17030b170d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13155 : Witness primes row := ⟨13155,32,0xd110d031311250d0d050d0d11110d030d11131713111303031717031317250d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13187 : Witness primes row := ⟨13187,32,0xd052f2503110d0d11171f1f2f110d1135110d110d110d170d1f1f170d0d1703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13219 : Witness primes row := ⟨13219,32,0xd0d1d110d11252f0d0d0d1303250d11130d1311170b0b110d11351311131d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13251 : Witness primes row := ⟨13251,32,0x110d171311170b0d0b2f25290d111d030d17170d170d3d031111130d1d110d25,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13283 : Witness primes row := ⟨13283,32,0x130513171d0b0d11030d0d1311132f170d050d110d350d030d1f1d131313170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows12 := #[r12291,r12323,r12355,r12387,r12419,r12451,r12483,r12515,r12547,r12579,r12611,r12643,r12675,r12707,r12739,r12771,r12803,r12835,r12867,r12899,r12931,r12963,r12995,r13027,r13059,r13091,r13123,r13155,r13187,r13219,r13251,r13283]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice12 {n : ℕ} (lo : 12291≤n) (hi:n≤13314) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows12 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13315 : Witness primes row := ⟨13315,32,0xd0d17111f13250311051313170d1d03130d1f030d170b0d0b170d170b0d0b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13347 : Witness primes row := ⟨13347,32,0x3130d2911110b1113351703111113131d0d170d030d2f290d130d1f0d111713,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13379 : Witness primes row := ⟨13379,32,0x110d252f03130d11030d0d033505130d350d0d1d130d11131313170d030b250d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13411 : Witness primes row := ⟨13411,32,0x254f1725250d354917170d110d110d131f0d25130d0b0d170b051f0d0d132503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13443 : Witness primes row := ⟨13443,32,0x30d170d130b3b0d0b0d1d03171d1f110d05251313110d03170d171311171717,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13475 : Witness primes row := ⟨13475,32,0xd0d171311111d030d172529110d112f17251f030d170d1f1317171311050d25,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13507 : Witness primes row := ⟨13507,32,0x1f050d0d0d110d11251f0d11030d1f030311170d0d110d0d11051d29170d2f1f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13539 : Witness primes row := ⟨13539,32,0xd110d0335110b0d0b2f35250b0d0b0d110525110d171d0d111313130d2f0d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13571 : Witness primes row := ⟨13571,32,0x112f0d1111050d25111317030d1f251313170d0d1f1117130d050d1111113d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13603 : Witness primes row := ⟨13603,32,0xd051f1113250d03130d3d1711130d030d291d13130517110d2917130b0d1735,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13635 : Witness primes row := ⟨13635,32,0x31317110d0d1d110b130d2f0b170b292f17131103111711110d0d0d0d11130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13667 : Witness primes row := ⟨13667,32,0xd050d17170517030d13170311130d0d0d0d1d031313131711131717110b1d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13699 : Witness primes row := ⟨13699,32,0x110d3d131d0d13030d1f1f1703111311031313030d0b0d0d25291d13250d0d1d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13731 : Witness primes row := ⟨13731,32,0x13111f030d05171d110d17030d111711170d0d0d03170d0d030d1d1f35130d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13763 : Witness primes row := ⟨13763,32,0xd110d11130b0d13170d1317110b1f0d0b29171113131d1713171713030d0d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13795 : Witness primes row := ⟨13795,32,0x1317132f0d0d0d1113171d1103110d111d0d0d0311112f110d0d0d030b130b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13827 : Witness primes row := ⟨13827,32,0x110d130d11110b0d11171d29132f0b13130d1d351d0d130d03112f03110b1311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13859 : Witness primes row := ⟨13859,32,0x252f250d0d0d3d03111d0d031d050d0d13051d350d130d11110d0d3d17112f03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13891 : Witness primes row := ⟨13891,32,0x170d2f2517172f0d1d050d0d11110d030d170d03250b25170b130d130b111d2f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13923 : Witness primes row := ⟨13923,32,0x30d1d1d1d111d110d1717130b0d170d1d3d1f0d0305130335291d0d110d112f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13955 : Witness primes row := ⟨13955,32,0x13110d0d03170d1125170d110d111717130d3d031d170d03110d1f0d111f130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r13987 : Witness primes row := ⟨13987,32,0x110d171125112f030d0d0d2f13350d0d03172f030d050b130b170d0d11112f11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14019 : Witness primes row := ⟨14019,32,0x11130d0d0d0d0b292f1717490b0d2f1717050d0d0d0b171103170d1f3511170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14051 : Witness primes row := ⟨14051,32,0xd0d1d1103111d0d0d131d0313170d11171317171d1117132f05351703131703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14083 : Witness primes row := ⟨14083,32,0x17111729172f1f031317251f0d171d1117131f0d130d171d1d0d17030b0d1303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14115 : Witness primes row := ⟨14115,32,0x113b1f030d17170d0b130d0d13130b1f0d2f131313350d11110d0d131111130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14147 : Witness primes row := ⟨14147,32,0x17050d1d11051d0d11173513110d110d13131d030d110d111305170d110b0d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14179 : Witness primes row := ⟨14179,32,0x13110d030d0d0d110d0d2f130d051f130d110d1f2f110b0d110d2f1311110d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14211 : Witness primes row := ⟨14211,32,0x30d0d1113110b130d130d1d1d0d0b110d0d1f17170b0d0d031313130d0d0d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14243 : Witness primes row := ⟨14243,32,0x1117131f110d1713110d13250d110d131d0d0d0d13132503110d1f1325170d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14275 : Witness primes row := ⟨14275,32,0xd0d17031713252f0d13131311050d351f171d1317110b0d0d172f291111130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14307 : Witness primes row := ⟨14307,32,0xd0d13170d110b17111d0d0311250b03351f0d1103110d1317130d170d111311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows13 := #[r13315,r13347,r13379,r13411,r13443,r13475,r13507,r13539,r13571,r13603,r13635,r13667,r13699,r13731,r13763,r13795,r13827,r13859,r13891,r13923,r13955,r13987,r14019,r14051,r14083,r14115,r14147,r14179,r14211,r14243,r14275,r14307]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice13 {n : ℕ} (lo : 13315≤n) (hi:n≤14338) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows13 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14339 : Witness primes row := ⟨14339,32,0x170d17110d1f2f1311130d131111132f0d131f2517172f03110d0d13110b2f13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14371 : Witness primes row := ⟨14371,32,0x110d0d1d130d1d0d0d13173d0d0b1d03031317110d110d1125131d0d0b110b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14403 : Witness primes row := ⟨14403,32,0x13132f03131f0b1d0b0d17030b291f030d110d1303170d030d0d1d031111132f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14435 : Witness primes row := ⟨14435,32,0xd0d130d1f0b0d0d030d3d430d1311250d171f030d11131111131d0d03050d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14467 : Witness primes row := ⟨14467,32,0x11290d130d130d1f1317170d03131711131147031713250d0b1f0d17111f0b0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14499 : Witness primes row := ⟨14499,32,0xd170d0d0d170b0d0d130d03170d0d0d251313171d0d170d03131f030d13170d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14531 : Witness primes row := ⟨14531,32,0x111717351105131717170d03170b0d112f111d030d0d251d11050d0d1f051711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14563 : Witness primes row := ⟨14563,32,0x170517030d0d17112f0d0d0d11110d2f1f131f0d13110b0d0d0d0d1d0b0d1d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14595 : Witness primes row := ⟨14595,32,0x13110d13110b1f0d0b13431f0b1125251317350d0d13131f11290d13130d2f17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14627 : Witness primes row := ⟨14627,32,0x2505170d0d051d13110d0d130d11130d17030d03133b0d2513051d17250b0d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14659 : Witness primes row := ⟨14659,32,0x1f0d1d1113290d030d0d0d13111113113d132517110b170d0b2517250b170d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14691 : Witness primes row := ⟨14691,32,0x131f1d172505130d1105170d170d0b17110d0d1103291703032f253517110d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14723 : Witness primes row := ⟨14723,32,0xd051f110d110d030d0d2f1f130b0d1f0d051f252513350311251f130d170d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14755 : Witness primes row := ⟨14755,32,0x131125030d111d030d131311110d4903131317030d110b1d0d172f030d111711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14787 : Witness primes row := ⟨14787,32,0x1717130d110513110d351f1313130b130d110d111305130d110d131f2f11130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14819 : Witness primes row := ⟨14819,32,0xd0d171f111113031113172f0d0d11131d130d0317172503130d1d0d030b3d3b,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14851 : Witness primes row := ⟨14851,32,0x13130d0311110d1711172f170d0b1703030d0d13171d2f130d2f172511110d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14883 : Witness primes row := ⟨14883,32,0x30d13172f1f0b11130d0d130b0d0d0d1705170d0d1117031d1f17033b111125,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14915 : Witness primes row := ⟨14915,32,0x13170d130d131703251313130d0d0d17130d0d0d0d0d170311130d0d0311250d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14947 : Witness primes row := ⟨14947,32,0x171f3d0d131d350d0d0d1d0d111f2513030d1d130d050b0d0b1f35033d0d1703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r14979 : Witness primes row := ⟨14979,32,0xd111f11170d0d1113130d0d0b110d111317130d172f0d11250d0d030d111713,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15011 : Witness primes row := ⟨15011,32,0x1d110d1f0d11171303130d032f2f130d0d110d112f0d0d0d0d0513170305172f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15043 : Witness primes row := ⟨15043,32,0xd050d17130d17111313171f0d0b170d0317171113052f1125290d170b0d0b11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15075 : Witness primes row := ⟨15075,32,0x13290d11110b0d290b0d0d0d0b112503170d250d1d132f03030d171317050d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15107 : Witness primes row := ⟨15107,32,0x1305251313111f030d110d1d110d1d11172f35111735111311132f1311111703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15139 : Witness primes row := ⟨15139,32,0x17250d110d13131717171f0d11111717030d0d110d0b17170b1f171f1f133503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15171 : Witness primes row := ⟨15171,32,0xd1f0d031713250d1105171713110b030d11171d030d1d13031f170d11051711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15203 : Witness primes row := ⟨15203,32,0xd051f110d17130311170d13112f0d0d1f050d0d0d110d17110d0d0d03171711,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15235 : Witness primes row := ⟨15235,32,0x13130d0311132f030d0d0d131111470d0d1f131f2f110d110b0d17131711130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15267 : Witness primes row := ⟨15267,32,0x30d172511110b0d112f1f030b0d0b350d291d1f03050d17110d1f030d0b0d13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15299 : Witness primes row := ⟨15299,32,0x13170d11170d0d1d130d0d03130d131117052f1117112f030d0d131711110d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15331 : Witness primes row := ⟨15331,32,0xd0d0d03131725112f1f0d1f2f0b170d030d1f110d11170d0b132f1f350d0b03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows14 := #[r14339,r14371,r14403,r14435,r14467,r14499,r14531,r14563,r14595,r14627,r14659,r14691,r14723,r14755,r14787,r14819,r14851,r14883,r14915,r14947,r14979,r15011,r15043,r15075,r15107,r15139,r15171,r15203,r15235,r15267,r15299,r15331]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice14 {n : ℕ} (lo : 14339≤n) (hi:n≤15362) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=32) rows14 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.PeriodicMod Deldor14.Star.CacheData128
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15363 : Witness primes row := ⟨15363,32,0x11131f030d110b13112f17030b111f111d050d1703054311110d1f13111d130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15395 : Witness primes row := ⟨15395,32,0x11110d1311110d0d1f11171313050d0d0d110d3d172511110d1f2511030d1311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15427 : Witness primes row := ⟨15427,32,0xd171f17130d13030d17170d030d2f0313110d0325110d170b0d1f2f0d111703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15459 : Witness primes row := ⟨15459,32,0x11110d13251117110b132f1311250d0d0d051313132949030d0d13130d0b1713,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15491 : Witness primes row := ⟨15491,32,0x25171717030d0d1103131f030d111113131317111f130d252f053d0d25050d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15523 : Witness primes row := ⟨15523,32,0x2f130d03111f1311133d250d0d0b17110d110d170d110d1713251d03110d0b1f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15555 : Witness primes row := ⟨15555,32,0x30d0d03130b2f170b170d1d11111d0d111f17112f0d131f17170d030d0d0d29,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15587 : Witness primes row := ⟨15587,32,0x17130d1111431711131117030d251313250d430d0d0d131713130d0d11291311,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15619 : Witness primes row := ⟨15619,32,0xd0d1d03171d0d030d0d1d171111130d030d1317170b0b11110b17170d1f3503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15651 : Witness primes row := ⟨15651,32,0x3111703110d0b0d251f0d03130d0b0313250d0d170b171103130d0d0d132f0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15683 : Witness primes row := ⟨15683,32,0x13111f110d1135170311251711110d0d17111d1317130d170d2f0d131d131303,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15715 : Witness primes row := ⟨15715,32,0xd0d17131f0d1d031105171303050d03111313030d170b0d11251d2f25250b13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15747 : Witness primes row := ⟨15747,32,0x130d17112f050b2911170d030b111311170d1f130311250d030d1d17170b2f11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15779 : Witness primes row := ⟨15779,32,0xd0d172913110d03030d1d1711051d110d1317030d0d11030d25130d17130d17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15811 : Witness primes row := ⟨15811,32,0x31d1d130d2f0d2925131d0d1f0d0d1717111f03111317110d052f130b2f0d1f,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15843 : Witness primes row := ⟨15843,32,0x3170d0d0d110b350b171d13471f2503250d1d1d03131d0d0d111713110d130d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15875 : Witness primes row := ⟨15875,32,0xd11170d030b0d1103131313110d25251f170d0313290d11110d0d0d0d051325,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15907 : Witness primes row := ⟨15907,32,0x11051f0d0d1325110d1f430d03170d0325110d0317110d0d0d051717110d2503,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15939 : Witness primes row := ⟨15939,32,0x110d0d170d0d130d0d2917030d130b111713131711110d131325130d0d111f29,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r15971 : Witness primes row := ⟨15971,32,0x131f1d11110d251311130d032f17250d131f170d1d170d110d13131711051d03,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r16003 : Witness primes row := ⟨16003,32,0xd051f2513130d0d0d0d131f03130d13032525110d2f0b0d1d1d25030d170b13,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r16035 : Witness primes row := ⟨16035,32,0x111317030d0b0d1117051711110d0b110d0d0d0d1311171111130d130d253d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r16067 : Witness primes row := ⟨16067,32,0xd051317111d0d03110d170313130d0d25111d131d0d11171d0517170d0b1703,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r16099 : Witness primes row := ⟨16099,32,0xd0317030d1117111317170d03110d11132f0d030d110b170b250d03170d2513,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r16131 : Witness primes row := ⟨16131,32,0x30d17170d11130d11131f0d0d1f0d0d130d1f111f0b0d030311131f13131d0d,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r16163 : Witness primes row := ⟨16163,32,0xd050d13110b2f0303131f0317171d0d1713170d0d113b112f291f0d0d0d2f11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r16195 : Witness primes row := ⟨16195,32,0x170d17030d0d17110d050d0d131317110d0d0d1113130b110b130d133b110b17,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r16227 : Witness primes row := ⟨16227,32,0xd11131113051711170d0d250b0d1d0d0d1125110d13350d031317030d0b0d11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def r16259 : Witness primes row := ⟨16259,1,0x11,by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private def rows15 := #[r15363,r15395,r15427,r15459,r15491,r15523,r15555,r15587,r15619,r15651,r15683,r15715,r15747,r15779,r15811,r15843,r15875,r15907,r15939,r15971,r16003,r16035,r16067,r16099,r16131,r16163,r16195,r16227,r16259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem slice15 {n : ℕ} (lo : 15363≤n) (hi:n≤16259) : ∃p, (decide (p∈primes) && (row p).test p n)=true :=
  range_covered (count:=29) rows15 (by decide) (by decide +kernel) lo hi
end Deldor14.Star.PeriodicRows128
end
section
namespace Deldor14.Star.PeriodicRows128
open Deldor14.Star.CacheData128
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem all_orders {n:ℕ} (lo:3≤n) (hi:n≤16259) : ∃p, (decide (p∈primes) && (row p).test p n)=true := by
  by_cases h0 : n≤1026
  · exact slice0 (by omega) h0
  by_cases h1 : n≤2050
  · exact slice1 (by omega) h1
  by_cases h2 : n≤3074
  · exact slice2 (by omega) h2
  by_cases h3 : n≤4098
  · exact slice3 (by omega) h3
  by_cases h4 : n≤5122
  · exact slice4 (by omega) h4
  by_cases h5 : n≤6146
  · exact slice5 (by omega) h5
  by_cases h6 : n≤7170
  · exact slice6 (by omega) h6
  by_cases h7 : n≤8194
  · exact slice7 (by omega) h7
  by_cases h8 : n≤9218
  · exact slice8 (by omega) h8
  by_cases h9 : n≤10242
  · exact slice9 (by omega) h9
  by_cases h10 : n≤11266
  · exact slice10 (by omega) h10
  by_cases h11 : n≤12290
  · exact slice11 (by omega) h11
  by_cases h12 : n≤13314
  · exact slice12 (by omega) h12
  by_cases h13 : n≤14338
  · exact slice13 (by omega) h13
  by_cases h14 : n≤15362
  · exact slice14 (by omega) h14
  exact slice15 (by omega) hi
end Deldor14.Star.PeriodicRows128
end
end

section
namespace Deldor14.Star.Modular127

theorem ramsey_star_16131 : number 16131 = 16259 := by
  apply exact_of_witnesses (m:=7) (q:=128) (t:=127) (by decide) (by decide) (by decide)
  · rw [show ((128:ℕ):ℚ)-1-2 = ((125:ℤ):ℚ) by norm_num]
    rw [Rat.isSquare_intCast_iff]
    decide +kernel
  · rw [show ((128:ℕ):ℚ)-1+2 = ((129:ℤ):ℚ) by norm_num]
    rw [Rat.isSquare_intCast_iff]
    decide +kernel
  · intro k lo hi
    obtain ⟨p,ok⟩ := PeriodicRows128.all_orders lo hi
    exact ⟨p,PeriodicMod.table_sound CacheData128.rows_valid ok⟩

end Deldor14.Star.Modular127
end

theorem Deldor14.Star.square_and_star_values :
    OMA.R_Erdos552_erdos_552_parts_ii_R1.H1 ∧ number 39=46 ∧ number 51=59 ∧
    number 963=995 ∧ number 16131=16259 := by
  exact ⟨fun p hp => prime_square hp, Waddle39.ramsey_star_39, Waddle51.ramsey_star_51,
    Modular127.ramsey_star_963, Modular127.ramsey_star_16131⟩
theorem OMA.solution : OMA.R_Erdos552_erdos_552_parts_ii_R1.H1 := Deldor14.Star.square_and_star_values.1
