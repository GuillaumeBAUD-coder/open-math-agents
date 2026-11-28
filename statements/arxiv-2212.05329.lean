import Mathlib

/-!
# Super edge-magic total strength of some unicyclic graphs

Source: N. S. Deepthi, arXiv:2212.05329, Conjecture 1.6 (Conjecture 1 of the journal
version, Ars Combinatoria 159 (2024) 73-85). Credit: @mjkang-estrella

For a finite simple `(p,q)`-graph `G`, a super edge-magic total labeling is a bijection
`f : V(G) ∪ E(G) → {1, …, p + q}` with `f(V(G)) = {1, …, p}` and a constant `c(f)` (the
magic constant) such that `f(u) + f(v) + f(uv) = c(f)` for every edge `uv`. The super
edge-magic total strength of a super edge-magic total graph is the minimum of `c(f)` over
all such labelings.

`G(n; k_1, …, k_n)` is the unicyclic graph made of an odd cycle `C_n = a_1 a_2 ⋯ a_n` with
`k_i` pendant vertices adjacent to `a_i` (each `k_i ≥ 0`). The conjecture: for every super
edge-magic total graph `G(n; k_1, …, k_n)`, its super edge-magic total strength equals
`2q + (n + 3)/2`.

Encoding. Labels are stored in `Fin (p + q)`, so the label of `x` is `(f x).val + 1`.
The cycle vertices are `Sum.inl i` (`i : Fin n`, cycle order `i ↦ i + 1 mod n`), and the
pendant vertices at `a_i` are `Sum.inr ⟨i, t⟩` for `t : Fin (k i)`. `SimpleGraph.fromRel`
symmetrizes the relation and removes loops; for `n ≥ 3` this is exactly the cycle plus
the pendant edges. Since `n` is odd, `(n + 3) / 2` is exact.
-/

namespace OMA.S_arxiv_2212_05329

/-- The graph `G(n; k_1, …, k_n)`: the cycle on `Fin n` with `k i` pendant vertices
attached to the `i`-th cycle vertex. -/
def cycleWithPendants (n : ℕ) (k : Fin n → ℕ) :
    SimpleGraph (Fin n ⊕ (Σ i : Fin n, Fin (k i))) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | Sum.inl i, Sum.inl j => j.val = (i.val + 1) % n
    | Sum.inl i, Sum.inr t => t.1 = i
    | _, _ => False

/-- `f` is a super edge-magic total labeling of `G` with magic constant `c`: a bijection from
vertices and edges onto the labels `1, …, p + q` (stored as `Fin (p + q)`), whose vertex
labels are exactly `1, …, p`, with `f(u) + f(v) + f(uv) = c` on every edge `uv`. -/
def IsSuperEdgeMagicTotal {V : Type*} (G : SimpleGraph V)
    (f : V ⊕ G.edgeSet ≃ Fin (Nat.card V + Nat.card G.edgeSet)) (c : ℕ) : Prop :=
  (∀ x, (f x).val < Nat.card V ↔ x.isLeft) ∧
  ∀ u v (h : G.Adj u v),
    ((f (Sum.inl u)).val + 1) + ((f (Sum.inl v)).val + 1) +
      ((f (Sum.inr ⟨s(u, v), h⟩)).val + 1) = c

/-- The magic constants of the super edge-magic total labelings of `G`; the strength of a
super edge-magic total graph is the least element of this set. -/
def magicConstants {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {c | ∃ f, IsSuperEdgeMagicTotal G f c}

/-- Deepthi's conjecture: every super edge-magic total `G(n; k_1, …, k_n)` with `n ≥ 3` odd
has super edge-magic total strength `2q + (n + 3)/2`, where `q` is its number of edges. -/
theorem main : ∀ (n : ℕ) (k : Fin n → ℕ), 3 ≤ n → Odd n →
    (magicConstants (cycleWithPendants n k)).Nonempty →
    IsLeast (magicConstants (cycleWithPendants n k))
      (2 * Nat.card (cycleWithPendants n k).edgeSet + (n + 3) / 2) := by
  sorry

end OMA.S_arxiv_2212_05329
