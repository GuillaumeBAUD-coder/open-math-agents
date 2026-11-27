import OMAReductions.R_Erdos552_erdos_552_parts_ii_R1
import Mathlib

/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller
-/

/-!
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

/-!
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

namespace Deldor14.Star
open SimpleGraph OMA.ChenStar

theorem star_number_mono (a b : ℕ) (hab : a ≤ b) :
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin a)) ≤
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin b)) := by
  classical
  let m := graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin b))
  have hm : m ∈ ramseySet b := Nat.sInf_mem (ramseySet_nonempty b)
  apply Nat.sInf_le
  intro G
  rcases hm G with red | blue
  · exact Or.inl red
  · obtain ⟨v,hv⟩ := exists_le_degree_of_star_isContained Gᶜ blue
    exact Or.inr (star_isContained_of_le_degree Gᶜ (hab.trans hv))
end Deldor14.Star

theorem OMA.solution : OMA.R_Erdos552_erdos_552_parts_ii_R1.H2 := by
  intro n hn
  exact ⟨Deldor14.Star.star_number_mono _ _ (Nat.le_succ n), OMA.ChenStar.erdos_552.variants.succ_le_add_two n hn⟩
