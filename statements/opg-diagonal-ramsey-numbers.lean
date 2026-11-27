import Mathlib

/-!
# Diagonal Ramsey numbers

Source: https://www.openproblemgarden.org/op/diagonal_ramsey_numbers
Credit: @John-A-McMahon

Source statement (Open Problem Garden, Erdős; prize offered by Erdős, now Graham): let `R(k,k)`
denote the `k`-th diagonal Ramsey number. Conjecture: `lim_{k → ∞} R(k,k)^(1/k)` exists.
(The page's second question, to determine the limit, is the formal-conjectures statement
`Erdos77.erdos_77`; this file states only the existence conjecture.)

`R(k,k)` is the least `N` such that every simple graph on `N` vertices contains a clique of
size `k` or an independent set of size `k` (a clique of size `k` in the complement). By
Ramsey's theorem the defining set is nonempty for every `k`. The limit is a finite real limit.
-/

namespace OMA.S_opg_diagonal_ramsey_numbers

open Filter Topology

/-- `N` forces a `k`-clique or a `k`-independent set in every simple graph on `N` vertices. -/
def ForcesCliqueOrIndep (k N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), (∃ s : Finset (Fin N), G.IsNClique k s) ∨
    ∃ s : Finset (Fin N), Gᶜ.IsNClique k s

/-- The diagonal Ramsey number `R(k,k)`. -/
noncomputable def diagonalRamsey (k : ℕ) : ℕ :=
  sInf {N : ℕ | ForcesCliqueOrIndep k N}

theorem main :
    ∃ L : ℝ, Tendsto (fun k : ℕ => (diagonalRamsey k : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop (𝓝 L) := by
  sorry

end OMA.S_opg_diagonal_ramsey_numbers
