import OMAStatements.S_opg_nearly_spanning_regular_subgraphs
import Mathlib

/-!
# Reduction of the Alon-Mubayi conjecture to its odd-k, even-r core

The target asks: for every `eps > 0` and `k >= 1` there is `r0` such that every `r`-regular graph
with `r >= r0` has a `k`-regular subgraph covering at least `(1 - eps)` of the vertices.

Two classical theorems of Petersen decide every case in which `k` or `r` is even:

* `H1` (Petersen 1891): every graph of odd regular degree has a spanning `1`-regular subgraph
  (a perfect matching).
* `H2` (Petersen 1908, 2-factorization): every graph of even regular degree `r` has, for every
  even `k <= r`, a spanning `k`-regular subgraph (take `k / 2` of the `r / 2` spanning
  `2`-factors).

Consequently:

* `k` even and `r <= k`: `H2` applies to `G` itself (answer: `S = univ`).
* `k` even and `r` odd: `H1` gives a perfect matching `F`; deleting it leaves an
  `(r - 1)`-regular graph (the lemma `card_adj_delete_one` below), to which `H2` applies.
* `k` odd and `r` odd: `H1` and the same deletion reduce to the even-`r` case of `H3`.
* `k` odd and `r` even: `H3`, the residual case.

So the whole conjecture reduces to the following three statements, of which `H3` is the only one
not settled by classical 2-factorization theory.  (`H3` is a theorem as of
Varun Sivashankar, the paper arXiv:2609.19777, Theorem 2.1, whose proof
runs by augmenting a largest `k`-regular subgraph along simultaneously exchanged alternating
paths; that proof covers all `k`, in particular the odd `k` of `H3`.)
-/

open SimpleGraph

namespace OMA.R_opg_nearly_spanning_regular_subgraphs_R1

/-- Petersen (1891): a graph of odd regular degree has a spanning `1`-regular subgraph. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ),
    Odd r → G.IsRegularOfDegree r →
      ∃ F : SimpleGraph V, F ≤ G ∧ ∀ v : V, Nat.card {w : V // F.Adj v w} = 1

/-- Petersen (1908): an `r`-regular graph with `r` and `k` even and `k <= r` has a spanning
`k`-regular subgraph (a union of `k / 2` spanning `2`-factors). -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r k : ℕ),
    Even r → Even k → k ≤ r → G.IsRegularOfDegree r →
      ∃ H : SimpleGraph V, H ≤ G ∧ ∀ v : V, Nat.card {w : V // H.Adj v w} = k

/-- The residual case: the target for odd `k` and even `r`. -/
def H3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 0 < k → Odd k → ∃ r₀ : ℕ,
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ),
      r₀ ≤ r → Even r → G.IsRegularOfDegree r →
      ∃ (S : Finset V) (H : SimpleGraph V), H ≤ G ∧
        (∀ v w, H.Adj v w → v ∈ S) ∧
        (∀ v ∈ S, Nat.card {w : V // H.Adj v w} = k) ∧
        (1 - ε) * (Fintype.card V : ℝ) ≤ (S.card : ℝ)

/-- Deleting a spanning `1`-regular subgraph drops every degree by exactly one. -/
lemma card_adj_delete_one {V : Type} [Fintype V] (G F : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hFG : F ≤ G) (hF : ∀ v : V, Nat.card {w : V // F.Adj v w} = 1)
    (hreg : G.IsRegularOfDegree r) (v : V) :
    Nat.card {w : V // (G.deleteEdges F.edgeSet).Adj v w} = r - 1 := by
  classical
  set A : Finset V := Finset.univ.filter (fun w => G.Adj v w) with hA
  set B : Finset V := Finset.univ.filter (fun w => (G.deleteEdges F.edgeSet).Adj v w) with hB
  set C : Finset V := Finset.univ.filter (fun w => F.Adj v w) with hC
  have hsub : C ⊆ A := by
    intro w hw
    simp only [hA, hC, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact hFG hw
  have hBA : B = A \ C := by
    ext w
    simp only [hB, hA, hC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      SimpleGraph.deleteEdges_adj, SimpleGraph.mem_edgeSet]
  have hcardC : C.card = 1 := by
    rw [hC, ← Fintype.card_subtype (fun w : V => F.Adj v w), ← Nat.card_eq_fintype_card]
    exact hF v
  have hcardA : A.card = r := by
    have h1 : A.card = G.degree v := by
      rw [hA, ← Fintype.card_subtype (fun w : V => G.Adj v w)]
      exact SimpleGraph.card_neighborSet_eq_degree ..
    rw [h1]
    exact hreg v
  have hcardB : B.card = A.card - C.card := by
    rw [hBA, Finset.card_sdiff_of_subset hsub]
  have hfin : Nat.card {w : V // (G.deleteEdges F.edgeSet).Adj v w} = B.card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype
      (fun w : V => (G.deleteEdges F.edgeSet).Adj v w)]
  rw [hfin, hcardB, hcardA, hcardC]

/-- With `eps >= 1` the empty subgraph already covers the required proportion. -/
lemma univ_card_ge {V : Type} [Fintype V] (ε : ℝ) (hε : 0 < ε) :
    (1 - ε) * (Fintype.card V : ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by
  rw [Finset.card_univ]
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := by positivity
  nlinarith

/-- Petersen (1891) plus deletion of a perfect matching leaves an even-regular graph. -/
lemma even_pred_of_odd_degree {r : ℕ} (hr : Odd r) : Even (r - 1) := by
  obtain ⟨m, hm⟩ := hr
  exact ⟨m, by omega⟩

theorem main : H1 → H2 → H3 → type_of% @OMA.S_opg_nearly_spanning_regular_subgraphs.main := by
  intro h1 h2 h3 ε hε k hk
  rcases Nat.even_or_odd k with hke | hko
  · refine ⟨k, ?_⟩
    intro V instV G instG r hr hreg
    classical
    rcases Nat.even_or_odd r with hre | hro
    · obtain ⟨H, hHG, hHdeg⟩ := h2 V G r k hre hke hr hreg
      exact ⟨Finset.univ, H, hHG, fun v w _ => Finset.mem_univ v, fun v _ => hHdeg v,
        univ_card_ge ε hε⟩
    · obtain ⟨F, hFG, hFdeg⟩ := h1 V G r hro hreg
      have hEr : Even (r - 1) := even_pred_of_odd_degree hro
      have hkle : k ≤ r - 1 := by
        obtain ⟨a, ha⟩ := hke
        obtain ⟨b, hb⟩ := hro
        omega
      have hreg' : (G.deleteEdges F.edgeSet).IsRegularOfDegree (r - 1) := by
        intro v
        rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        exact card_adj_delete_one G F r hFG hFdeg hreg v
      obtain ⟨H, hHG, hHdeg⟩ := h2 V (G.deleteEdges F.edgeSet) (r - 1) k hEr hke hkle hreg'
      exact ⟨Finset.univ, H, hHG.trans (SimpleGraph.deleteEdges_le F.edgeSet),
        fun v w _ => Finset.mem_univ v, fun v _ => hHdeg v, univ_card_ge ε hε⟩
  · obtain ⟨r₀, hr₀⟩ := h3 ε hε k hk hko
    refine ⟨max (r₀ + 1) (k + 1), ?_⟩
    intro V instV G instG r hr hreg
    classical
    have hr₀le : r₀ ≤ r := by omega
    rcases Nat.even_or_odd r with hre | hro
    · exact hr₀ V G r hr₀le hre hreg
    · obtain ⟨F, hFG, hFdeg⟩ := h1 V G r hro hreg
      have hEr : Even (r - 1) := even_pred_of_odd_degree hro
      have hr₀le' : r₀ ≤ r - 1 := by omega
      have hreg' : (G.deleteEdges F.edgeSet).IsRegularOfDegree (r - 1) := by
        intro v
        rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        exact card_adj_delete_one G F r hFG hFdeg hreg v
      obtain ⟨S, H, hHG, hmem, hdeg, hcard⟩ :=
        hr₀ V (G.deleteEdges F.edgeSet) (r - 1) hr₀le' hEr hreg'
      exact ⟨S, H, hHG.trans (SimpleGraph.deleteEdges_le F.edgeSet), hmem, hdeg, hcard⟩

end OMA.R_opg_nearly_spanning_regular_subgraphs_R1
