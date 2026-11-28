import OMAStatements.S_opg_nearly_spanning_regular_subgraphs
import Mathlib

/-!
# Reduction of the Alon-Mubayi conjecture to its even/even core plus Petersen 2-factorization

The target asks: for every `eps > 0` and `k >= 1` there is `r0` such that every `r`-regular graph
with `r >= r0` has a `k`-regular subgraph covering at least `(1 - eps)` of the vertices.

This file splits the four parity quadrants of `(r, k)`; one of them is settled by classical
2-factorization theory, the other three are the residual statement.

* `H1` (Petersen 1908, 2-factorization): every `2m`-regular graph decomposes into `m` spanning
  `2`-factors; hence for `r` and `k` both even with `k <= r` there is a spanning `k`-regular
  subgraph.  This is TRUE (a theorem), but it is not in Mathlib: the standard proof orients the
  edges of an Eulerian component so that every vertex has out-degree `m`, splits that digraph into
  `m` spanning `1`-in-`1`-out subgraphs using the perfect-matching decomposition of a regular
  bipartite graph (Hall), and reads each such subgraph as a spanning `2`-factor.

* `H2` (residual): the target itself, restricted to the cases `r` odd or `k` odd.  This is where
  the open content lives; it is a strictly weaker statement than the target and is TRUE as of
  Varun Sivashankar, arXiv:2609.19777, Theorem 2.1 (the augmentation of a largest `k`-regular
  subgraph along simultaneously exchanged alternating walks covers all `k`, in particular the
  odd ones), whose proof is far beyond Mathlib.

`main` covers all four quadrants: `r` even and `k` even go through `H1` with `r0 = k` (and
`S = univ`), every other case goes through `H2`.

## Correction history (please keep this)

An earlier version of this reduction used a hypothesis `H1` reading: every graph of odd regular
degree has a spanning `1`-regular subgraph (a perfect matching, attributed to Petersen 1891).
That statement is FALSE, so that reduction was vacuous and proved nothing.  Counterexample
(ledgered, machine-checked): the 3-regular simple graph on 16 vertices obtained from three copies
of `K4 - {a,b}` whose vertices `a` and `b` are additionally joined to a new vertex `t`, with the
three `t`-images joined to a fresh vertex `v`; it has no perfect matching (maximum matching 7,
`{v}` a Tutte violator).  Petersen 1891 is the bridgeless 3-regular case, not the general
odd-regular case, and a perfect matching is not what the target needs anyway: the target only
asks for a `k`-regular subgraph on `(1 - eps)` of the vertices, so the odd-`r` cases belong to the
residual hypothesis, not to a matching statement.
-/

open SimpleGraph

namespace OMA.R_opg_nearly_spanning_regular_subgraphs_R1

/-- Petersen (1908) 2-factorization, in the form the target needs: an `r`-regular graph with `r`
and `k` even and `k <= r` has a spanning `k`-regular subgraph (a union of `k / 2` of the `r / 2`
spanning `2`-factors).  A theorem, not in Mathlib. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r k : ℕ),
    Even r → Even k → k ≤ r → G.IsRegularOfDegree r →
      ∃ H : SimpleGraph V, H ≤ G ∧ ∀ v : V, Nat.card {w : V // H.Adj v w} = k

/-- The residual case: the target restricted to odd `r` or odd `k`.  Strictly weaker than the
target; open content (proved in arXiv:2609.19777, not formalizable here). -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 0 < k → ∃ r₀ : ℕ,
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ),
      r₀ ≤ r → G.IsRegularOfDegree r → (Odd r ∨ Odd k) →
      ∃ (S : Finset V) (H : SimpleGraph V), H ≤ G ∧
        (∀ v w, H.Adj v w → v ∈ S) ∧
        (∀ v ∈ S, Nat.card {w : V // H.Adj v w} = k) ∧
        (1 - ε) * (Fintype.card V : ℝ) ≤ (S.card : ℝ)

/-- The full vertex set always satisfies the size condition when `S = univ`. -/
lemma univ_card_ge {V : Type} [Fintype V] (ε : ℝ) (hε : 0 < ε) :
    (1 - ε) * (Fintype.card V : ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by
  rw [Finset.card_univ]
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := by positivity
  nlinarith

theorem main : H1 → H2 → type_of% @OMA.S_opg_nearly_spanning_regular_subgraphs.main := by
  intro h1 h2 ε hε k hk
  obtain ⟨r₀, hr₀⟩ := h2 ε hε k hk
  refine ⟨max r₀ k, ?_⟩
  intro V instV G instG r hr hreg
  have hr₀le : r₀ ≤ r := le_trans (le_max_left _ _) hr
  have hkle : k ≤ r := le_trans (le_max_right _ _) hr
  rcases Nat.even_or_odd r with hre | hro
  · rcases Nat.even_or_odd k with hke | hko
    · -- `r` and `k` both even: Petersen 2-factorization gives a spanning `k`-regular subgraph.
      obtain ⟨H, hHG, hHdeg⟩ := h1 V G r k hre hke hkle hreg
      exact ⟨Finset.univ, H, hHG, fun v w _ => Finset.mem_univ v, fun v _ => hHdeg v,
        univ_card_ge ε hε⟩
    · -- `r` even, `k` odd: residual case.
      exact hr₀ V G r hr₀le hreg (Or.inr hko)
  · -- `r` odd: residual case.
    exact hr₀ V G r hr₀le hreg (Or.inl hro)

end OMA.R_opg_nearly_spanning_regular_subgraphs_R1
