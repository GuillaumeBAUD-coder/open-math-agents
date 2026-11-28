import OMAReductions.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2

-- Reduction OeisA56777.comesFromPrimeQuadruple_of_a.R2.H1.R1 of step R2.H1
-- Credit: @MBimrose

/-!
# Reduction of step R2.H1 of OEIS A056777 (the four-or-more-prime-factors cases)

Step `R2.H1` says: no `n` with `A n` (i.e. `totient (n+12) = totient n + 12` and
`sigma (n+12) = sigma n + 12`, `n` composite, `n > 1`) can simultaneously have

* at least four prime factors with multiplicity at both endpoints, at least five at one of them,
* at least one endpoint not squarefree,
* at least one odd prime with odd exponent at each endpoint, and at most two of them at one,

and it is the residual "four versus four" case of the reduction `R2`.

This file splits that obligation by the residue of `n` modulo `4`, which is exactly how the
residual case is attacked: a number and its shift by `12` have the same residue mod `4`, the
odd case is the one where both totients are shown to be divisible by eight, `n ≡ 0 (mod 4)` is
the case where both divisor sums are shown to be divisible by seven, and `n ≡ 2 (mod 4)` is
reduced by stripping a single factor of two from each endpoint.

* `H1`: the odd case, `n ≡ 1 or 3 (mod 4)`.
* `H2`: the case `n ≡ 0 (mod 4)`.
* `H3`: the case `n ≡ 2 (mod 4)`.

`main` derives the step from them by looking at `n % 4`; the split is exhaustive and disjoint.

Search audit: the conjunction of the hypotheses of `R2.H1` is not known to be satisfiable at
all — exhaustive search over all `n < 3·10^6` with `totient (n+12) = totient n + 12` and
`sigma (n+12) = sigma n + 12` (41698 candidates) finds NO `n` meeting them, so each sub-case is
a genuine disproof obligation about a set which is empty in every computed range, not a vacuous
restatement.  Every known member of A056777 is of the shape `p * (p+8)` for a prime quadruple
`(p, p+2, p+6, p+8)`, and those have exactly two prime factors.
-/

namespace OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H1_R1

open Nat

/-- **The odd case, `n ≡ 1` or `n ≡ 3 (mod 4)`.** -/
def H1 : Prop :=
  ∀ n : ℕ, OeisA56777.A n →
    4 ≤ n.primeFactorsList.length →
    4 ≤ (n + 12).primeFactorsList.length →
    (5 ≤ n.primeFactorsList.length ∨ 5 ≤ (n + 12).primeFactorsList.length) →
    (¬ Squarefree n ∨ ¬ Squarefree (n + 12)) →
    1 ≤ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card →
    1 ≤ ((n + 12).primeFactors.filter fun p =>
      p ≠ 2 ∧ Odd ((n + 12).factorization p)).card →
    ((n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ≤ 2 ∨
      ((n + 12).primeFactors.filter fun p =>
        p ≠ 2 ∧ Odd ((n + 12).factorization p)).card ≤ 2) →
    (n % 4 = 1 ∨ n % 4 = 3) →
    False

/-- **The case `n ≡ 0 (mod 4)`.** -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA56777.A n →
    4 ≤ n.primeFactorsList.length →
    4 ≤ (n + 12).primeFactorsList.length →
    (5 ≤ n.primeFactorsList.length ∨ 5 ≤ (n + 12).primeFactorsList.length) →
    (¬ Squarefree n ∨ ¬ Squarefree (n + 12)) →
    1 ≤ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card →
    1 ≤ ((n + 12).primeFactors.filter fun p =>
      p ≠ 2 ∧ Odd ((n + 12).factorization p)).card →
    ((n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ≤ 2 ∨
      ((n + 12).primeFactors.filter fun p =>
        p ≠ 2 ∧ Odd ((n + 12).factorization p)).card ≤ 2) →
    n % 4 = 0 →
    False

/-- **The case `n ≡ 2 (mod 4)`.** -/
def H3 : Prop :=
  ∀ n : ℕ, OeisA56777.A n →
    4 ≤ n.primeFactorsList.length →
    4 ≤ (n + 12).primeFactorsList.length →
    (5 ≤ n.primeFactorsList.length ∨ 5 ≤ (n + 12).primeFactorsList.length) →
    (¬ Squarefree n ∨ ¬ Squarefree (n + 12)) →
    1 ≤ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card →
    1 ≤ ((n + 12).primeFactors.filter fun p =>
      p ≠ 2 ∧ Odd ((n + 12).factorization p)).card →
    ((n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ≤ 2 ∨
      ((n + 12).primeFactors.filter fun p =>
        p ≠ 2 ∧ Odd ((n + 12).factorization p)).card ≤ 2) →
    n % 4 = 2 →
    False

theorem main : H1 → H2 → H3 → OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2.H1 := by
  intro h1 h2 h3 n hA h4 h5 h6 h7 h8 h9 h10
  have hlt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  rcases (show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega)
    with h | h | h | h
  · exact h2 n hA h4 h5 h6 h7 h8 h9 h10 h
  · exact h1 n hA h4 h5 h6 h7 h8 h9 h10 (Or.inl h)
  · exact h3 n hA h4 h5 h6 h7 h8 h9 h10 h
  · exact h1 n hA h4 h5 h6 h7 h8 h9 h10 (Or.inr h)

end OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H1_R1
