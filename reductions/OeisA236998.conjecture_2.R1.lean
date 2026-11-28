import FormalConjectures.OEIS.«236998»

-- Reduction OeisA236998.conjecture_2.R1 of A236998 — conjecture 2
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA236998.conjecture_2: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 20` has `0 < k`, `2k < n` with `φ(k) φ(n - k) + 1` a square, for `n ≤ 420`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 420`. This is the open conjecture.
-/

namespace OMA.R_OeisA236998_conjecture_2_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 20 < n → n ≤ 420 →
    ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧ IsSquare (k.totient * (n - k).totient + 1)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 20 < n → 420 < n →
    ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧ IsSquare (k.totient * (n - k).totient + 1)

theorem main : H1 → H2 → type_of% @OeisA236998.conjecture_2 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 420
  · exact h1 n hn h
  · exact h2 n hn (by omega)

end OMA.R_OeisA236998_conjecture_2_R1
