import OMAStatements.S_oeis_a234347

-- Reduction oeis-a234347.R1 of A234347: a(n) = |{0 < k < n: 3^k + 3^{phi(n-k)/2} - 1 is prime}|, where phi(.) is Euler's totient function.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a234347: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 53`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 53`. This is the open conjecture.
-/

namespace OMA.R_oeis_a234347_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n ≤ 53 →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ (3 ^ k + 3 ^ (Nat.totient (n - k) / 2) - 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 3 < n → 53 < n →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ (3 ^ k + 3 ^ (Nat.totient (n - k) / 2) - 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a234347.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 53
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a234347_R1
