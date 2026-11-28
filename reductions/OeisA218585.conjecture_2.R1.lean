import FormalConjectures.OEIS.«218585»

-- Reduction OeisA218585.conjecture_2.R1 of A218585 — conjecture 2
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA218585.conjecture_2: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 12` has `0 < x`, `3x < n` with `n x + (n - x)^2` prime, for `n ≤ 951`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 951`. This is the open conjecture.
-/

namespace OMA.R_OeisA218585_conjecture_2_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 12 < n → n ≤ 951 →
    ∃ x : ℕ, 0 < x ∧ 3 * x < n ∧ Nat.Prime (n * x + (n - x) ^ 2)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 12 < n → 951 < n →
    ∃ x : ℕ, 0 < x ∧ 3 * x < n ∧ Nat.Prime (n * x + (n - x) ^ 2)

theorem main : H1 → H2 → type_of% @OeisA218585.conjecture_2 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 951
  · exact h1 n hn h
  · exact h2 n hn (by omega)

end OMA.R_OeisA218585_conjecture_2_R1
