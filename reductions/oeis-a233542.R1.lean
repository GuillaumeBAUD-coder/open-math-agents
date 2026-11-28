import OMAStatements.S_oeis_a233542

-- Reduction oeis-a233542.R1 of A233542: Number of ways to write n = k^2 + m with k > 0 and m > 0 such that phi(k^2)*phi(m) - 1 is prime, where phi(.) is Euler's totient function (A000010).
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a233542: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1005`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1005`. This is the open conjecture.
-/

namespace OMA.R_oeis_a233542_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 5 < n → n ≤ 1005 →
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k ^ 2 + m ∧
      (Nat.totient (k ^ 2) * Nat.totient m - 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 < n → 1005 < n →
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k ^ 2 + m ∧
      (Nat.totient (k ^ 2) * Nat.totient m - 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a233542.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1005
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a233542_R1
