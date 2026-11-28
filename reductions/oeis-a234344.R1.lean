import OMAStatements.S_oeis_a234344

-- Reduction oeis-a234344.R1 of A234344: a(n) = |{0 < k < n: 2^{phi(k)/2} + 3^{phi(n-k)/2} is prime}|, where phi(.) is Euler's totient function.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a234344: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 55`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 55`. This is the open conjecture.
-/

namespace OMA.R_oeis_a234344_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 5 < n → n ≤ 55 →
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ Nat.totient k = 2 * a ∧
      Nat.totient (n - k) = 2 * b ∧ (2 ^ a + 3 ^ b).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 < n → 55 < n →
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ Nat.totient k = 2 * a ∧
      Nat.totient (n - k) = 2 * b ∧ (2 ^ a + 3 ^ b).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a234344.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 55
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a234344_R1
