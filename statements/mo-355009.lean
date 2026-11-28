import Mathlib

/-!
# About semiprimal representations of 1

Source: https://mathoverflow.net/questions/355009
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture `A₁`: for every `m ≥ 2` there exist mutually different primes `p_1, …, p_m`, mutually
different primes `b_1, …, b_m` and `i_1, …, i_m ∈ {1, 2}` with
`Sum_{k=1..m} (-1)^{i_k} b_k p_k = 1`.
Conjecture `B`: for every `m ≥ 2` the number of such representations is infinite.
This file states both (as a conjunction).

Formalized: a representation is a triple `(p, b, i)` of maps `Fin m → ℕ` with `p` and `b` injective
and prime-valued and `i k ∈ {1, 2}`; the sum is taken in `ℤ`.
-/

namespace OMA.S_mo_355009

/-- The representations of `1` with `m` terms. -/
def Rep (m : ℕ) : Set ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :=
  {r | Function.Injective r.1 ∧ Function.Injective r.2.1 ∧
    (∀ k, (r.1 k).Prime) ∧ (∀ k, (r.2.1 k).Prime) ∧ (∀ k, r.2.2 k = 1 ∨ r.2.2 k = 2) ∧
    ∑ k, (-1 : ℤ) ^ (r.2.2 k) * (r.2.1 k : ℤ) * (r.1 k : ℤ) = 1}

theorem main : (∀ m : ℕ, 2 ≤ m → (Rep m).Nonempty) ∧ (∀ m : ℕ, 2 ≤ m → (Rep m).Infinite) := by
  sorry

end OMA.S_mo_355009
