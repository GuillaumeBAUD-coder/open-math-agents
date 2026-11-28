import Mathlib

/-!
# Erdős Problem 129

Source: https://www.erdosproblems.com/129
Credit: @jarrettbranch

## The problem

Let $R(n;k,r)$ be the smallest $N$ such that if the edges of $K_N$ are $r$-coloured then there
is a set of $n$ vertices which does not contain a copy of $K_k$ in at least one of the $r$
colours. Prove that there is a constant $C = C(r) > 1$ such that
$$R(n;3,r) < C^{\sqrt{n}}.$$

Conjectured by Erdős and Gyárfás, who proved that $R(n;3,r) > C^{\sqrt{n}}$ for some $C > 1$.
The source notes (thanks to Antonio Girão) that the problem as written is easily disproved:
a random 2-colouring gives $R(n;3,2) \ge C^n$. It is stated here exactly as written.

## Formalization notes

* An $r$-colouring of the edges of $K_N$ is a map `c : Sym2 (Fin N) → Fin r`; the diagonal
  elements of `Sym2` are not edges and their colours are ignored.
* `colourGraph c i` is the graph of the edges of colour `i` (`SimpleGraph.fromRel`, which
  adds `x ≠ y`; since `s(x, y) = s(y, x)` its symmetrisation changes nothing).
* A set `S` of vertices does not contain a copy of $K_k$ in colour `i` when no `k`-subset of
  `S` is a `k`-clique of `colourGraph c i`.
* `R n k r` is the least such `N` (`sInf`). For `r ≥ 2` the set is nonempty (by Ramsey's
  theorem some colour has a monochromatic $K_n$, on which any other colour has no edge at
  all), so no junk value arises in the statement.
* The constant depends on `r` only, so the statement is `∀ r, ∃ C > 1, ∀ n`. It is stated
  for `r ≥ 2`: with one colour there is no $N$ at all once $n \ge 3$, and the source's
  context (classical Ramsey numbers at $r = k = 2$) concerns $r \ge 2$.
-/

namespace OMA.S_erdos_129

/-- The graph on `Fin N` whose edges are those of colour `i` under the colouring `c`. -/
def colourGraph {N r : ℕ} (c : Sym2 (Fin N) → Fin r) (i : Fin r) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun x y => c s(x, y) = i

/-- Every `r`-colouring of the edges of `K_N` has a set of `n` vertices containing no copy
of `K_k` in at least one of the `r` colours. -/
def Good (n k r N : ℕ) : Prop :=
  ∀ c : Sym2 (Fin N) → Fin r, ∃ S : Finset (Fin N), S.card = n ∧
    ∃ i : Fin r, ∀ T ⊆ S, ¬ (colourGraph c i).IsNClique k T

/-- `R(n;k,r)`: the smallest `N` with property `Good n k r N`. -/
noncomputable def R (n k r : ℕ) : ℕ := sInf {N : ℕ | Good n k r N}

theorem main :
    ∀ r : ℕ, 2 ≤ r → ∃ C : ℝ, 1 < C ∧ ∀ n : ℕ, (R n 3 r : ℝ) < C ^ Real.sqrt n := by
  sorry

end OMA.S_erdos_129
