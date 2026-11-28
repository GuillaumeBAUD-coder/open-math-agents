import Mathlib

/-!
# Hamiltonian paths in the prime sum graph

Source: https://mathoverflow.net/questions/450427 (2023).
Credit: @jagraj28

For `n ≥ 2` and distinct `a, b ∈ [n] = {1, …, n}`, the post asks when `[n]` can be listed as
`x₁, …, xₙ` with `x₁ = a`, `xₙ = b` and `xᵢ + xᵢ₊₁` prime for `1 ≤ i ≤ n - 1` (no wrap-around):
a Hamiltonian path from `a` to `b` in the graph on `[n]` with an edge `vw` when `v + w` is prime.
The post lists the necessary conditions
* if `n` is odd, `a` and `b` are both odd;
* if `n` is even, `a` and `b` have opposite parity;
* neither `n = 5, {a, b} = {1, 3}` nor `n = 6, {a, b} = {1, 2}` holds,
and conjectures that they are also sufficient. The post has no answer.

Formalization notes:
* A listing of `[n]` is a list `l` that is a permutation of `List.range' 1 n = [1, …, n]`. Its
  first entry is `a`, its last entry is `b`, and consecutive entries have a prime sum
  (`List.IsChain`).
* `main` states that, for `n ≥ 2` and distinct `a, b ∈ [n]`, such a listing exists if and only if
  the conditions hold (the conjecture, together with the necessity that the post notes).
* A direct search confirms the equivalence for every `n ≤ 16`.
-/

namespace OMA.S_mo_450427

/-- `[n]` can be listed from `a` to `b` so that consecutive entries have a prime sum. -/
def HasPrimeSumPath (n a b : ℕ) : Prop :=
  ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ l.head? = some a ∧ l.getLast? = some b ∧
    l.IsChain (fun x y => (x + y).Prime)

/-- The necessary conditions listed in the post. -/
def Admissible (n a b : ℕ) : Prop :=
  ((Odd n ∧ Odd a ∧ Odd b) ∨ (Even n ∧ (Odd a ↔ Even b))) ∧
    ¬ (n = 5 ∧ ({a, b} : Finset ℕ) = {1, 3}) ∧ ¬ (n = 6 ∧ ({a, b} : Finset ℕ) = {1, 2})

/-- The conjecture: the necessary conditions are also sufficient. -/
theorem main :
    ∀ n a b : ℕ, 2 ≤ n → a ∈ Finset.Icc 1 n → b ∈ Finset.Icc 1 n → a ≠ b →
      (HasPrimeSumPath n a b ↔ Admissible n a b) := by
  sorry

end OMA.S_mo_450427
