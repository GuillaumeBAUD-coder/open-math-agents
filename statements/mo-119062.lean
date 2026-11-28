import Mathlib

/-!
# Square-sum graphs are Hamiltonian from 32 on

Source: https://mathoverflow.net/questions/119062 (CC BY-SA 4.0).

Let `G_k(n)` be the graph on `{1, …, n}` in which `i ≠ j` are adjacent iff `i + j` is a `k`-th power.
A 1993 note found that `G_2(32)` is Hamiltonian (and that 32 is the first such `n`), and conjectured
that `G_2(n)` is Hamiltonian for every `n ≥ 32`. The question asks about the status of that conjecture.

We state the conjecture (the case `k = 2`).

Formalization notes:
* The vertex `i : Fin n` stands for the integer `i + 1`, so `{1, …, n}` is `Fin n`.
* `SimpleGraph.fromRel` symmetrizes the relation and removes loops, so `i ~ j` iff `i ≠ j` and
  `(i + 1) + (j + 1)` is a perfect square.
* `SimpleGraph.IsHamiltonian` asks for a Hamiltonian cycle (vacuous only on one vertex, which `n ≥ 32`
  excludes).
-/

namespace OMA.S_mo_119062

/-- For every `n ≥ 32`, the graph on `{1, …, n}` joining `i ≠ j` when `i + j` is a square is Hamiltonian. -/
theorem main : ∀ n : ℕ, 32 ≤ n →
    (SimpleGraph.fromRel (fun i j : Fin n => IsSquare ((i : ℕ) + 1 + ((j : ℕ) + 1)))).IsHamiltonian := by
  sorry

end OMA.S_mo_119062
