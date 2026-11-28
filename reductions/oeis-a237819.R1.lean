import OMAStatements.S_oeis_a237819

-- Reduction oeis-a237819.R1 of A237819: Number of primes p < n such that floor(sqrt(n-p)) is a Sophie Germain prime.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a237819: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1005`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1005`. This is the open conjecture.
-/

namespace OMA.R_oeis_a237819_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 5 < n → n ≤ 1005 →
    ∃ p : ℕ, p.Prime ∧ p < n ∧ (Nat.sqrt (n - p)).Prime ∧
      (2 * Nat.sqrt (n - p) + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 < n → 1005 < n →
    ∃ p : ℕ, p.Prime ∧ p < n ∧ (Nat.sqrt (n - p)).Prime ∧
      (2 * Nat.sqrt (n - p) + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a237819.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1005
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a237819_R1
