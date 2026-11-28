import FormalConjectures.OEIS.«219023»

-- Reduction OeisA219023.conjecture_4.R1 of A219023 — conjecture 4
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA219023.conjecture_4: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 4517` has a prime `n < p < 2n` with `n^2 - n - p` and `n^2 + n + p` prime, for `n ≤ 4560`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 4560`. This is the open conjecture.
-/

namespace OMA.R_OeisA219023_conjecture_4_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 4517 < n → n ≤ 4560 →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n ∧
      Nat.Prime (n ^ 2 - n - p) ∧ Nat.Prime (n ^ 2 + n + p)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 4517 < n → 4560 < n →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n ∧
      Nat.Prime (n ^ 2 - n - p) ∧ Nat.Prime (n ^ 2 + n + p)

theorem main : H1 → H2 → type_of% @OeisA219023.conjecture_4 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 4560
  · exact h1 n hn h
  · exact h2 n hn (by omega)

end OMA.R_OeisA219023_conjecture_4_R1
