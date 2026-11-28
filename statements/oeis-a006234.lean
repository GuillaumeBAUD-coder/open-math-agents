import Mathlib

/-!
# A006234: a(n) = n*3^(n-4).

Source: https://oeis.org/A006234
Credit: @maaaakks

OEIS A006234 has offset 3: a(3), a(4), a(5), ... = 1, 4, 15, 54, 189, ...
with a(n) = n*3^(n-4) (so a(3) = 3*3^(-1) = 1).

The conjecture formalized here is the comment

> Number of spanning trees in the book graph of order n-2, i.e., S_{n-2} X P_2
> (S_k = the star graph on k nodes) (conjectured). This conjecture is true -
> see Doslic (2013). - N. J. A. Sloane, Dec 28 2013

(The entry also contains an unrelated conjecture about compositions, which is not
formalized here.)

Conventions.
* `S_k` is the star graph on `k` nodes: one center and `k - 1` leaves. We model it
  as `star k : SimpleGraph (Fin k)` with center `0`, where `i ~ j` iff `i ≠ j` and
  one of them is `0` (this is Mathlib's `starGraph 0` written so that it makes sense
  for every `k`).
* `P_2` is the path graph on two vertices, `SimpleGraph.pathGraph 2` (a single edge).
* `X` is the Cartesian (box) product, `SimpleGraph.boxProd` (`□`).
  So the book graph of order `k` is `bookGraph k = star k □ pathGraph 2` on
  `Fin k × Fin 2`: `k - 1` four-cycles ("pages") sharing the spine edge
  `(0,0) - (0,1)`; it has `2k` vertices.
* A spanning tree of `G` is a subgraph `H ≤ G` on the full vertex set with
  `H.IsTree`; the number of spanning trees is the `Set.ncard` of these `H`.
* Indexing: for `n ≥ 3` the book graph of order `n - 2` has
  `n * 3^(n-4)` spanning trees. Since `n = 3` gives the exponent `-1`, the
  right-hand side is stated in `ℚ` with an integer exponent (`zpow`), so that
  `n = 3` (book graph `K_2`, one spanning tree) is covered exactly.

The star-graph convention "`k` nodes" (rather than "`k` leaves") is the one that matches
the data: `S_1 X P_2 = K_2` has 1 spanning tree, `S_2 X P_2 = C_4` has 4, and
`S_3 X P_2` (two squares sharing an edge) has 15.
-/

namespace OMA.S_oeis_a006234

/-- The star graph `S_k` on `k` nodes `Fin k`, with center `0`. -/
def star (k : ℕ) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun i _ => i.val = 0

/-- The book graph of order `k`: `S_k □ P_2`. -/
def bookGraph (k : ℕ) : SimpleGraph (Fin k × Fin 2) :=
  star k □ SimpleGraph.pathGraph 2

theorem main :
    ∀ n : ℕ, 3 ≤ n →
      (({H : SimpleGraph (Fin (n - 2) × Fin 2) | H ≤ bookGraph (n - 2) ∧ H.IsTree}.ncard : ℕ)
          : ℚ) = (n : ℚ) * (3 : ℚ) ^ ((n : ℤ) - 4) := by
  sorry

end OMA.S_oeis_a006234
