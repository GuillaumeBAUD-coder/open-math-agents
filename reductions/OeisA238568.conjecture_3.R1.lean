import FormalConjectures.OEIS.«238568»

/-!
# Reduction OeisA238568.conjecture_3.R1

A238568 conjecture 3: for every `n > 6` there is `0 < k < n` with
`n^2 + pi(k n) - 1` prime.

The statement quantifies over all `n > 6`, so it splits at a bound into

* `H1` -- the finite range `6 < n <= 106`: a finite, decidable verification (one hundred
  explicit cases, each a finite search over `k < n` together with a primality check).
* `H2` -- the tail `n > 106`: the open core of the conjecture.

`H1` and `H2` together cover exactly the range of the parent statement; `main` is the case
split on `n <= 106`.
-/

namespace OMA.R_OeisA238568_conjecture_3_R1

/-- The finite range `6 < n <= 106`: finitely many explicit cases. -/
def H1 : Prop :=
  ∀ n : ℕ, 6 < n → n ≤ 106 →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (n ^ 2 + Nat.primeCounting (k * n) - 1)

/-- The tail `n > 106`: the open core of the conjecture. -/
def H2 : Prop :=
  ∀ n : ℕ, 106 < n →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (n ^ 2 + Nat.primeCounting (k * n) - 1)

theorem main : H1 → H2 → type_of% @OeisA238568.conjecture_3 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 106
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_OeisA238568_conjecture_3_R1
