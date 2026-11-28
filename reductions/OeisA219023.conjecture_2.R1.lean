import FormalConjectures.OEIS.«219023»

/-!
# Reduction OeisA219023.conjecture_2.R1

A219023: for `n > 3512` there is a prime `p` with `n < p < 2 n` such that both
`n^2 - n + p` and `n^2 + n - p` are prime.

The statement is a statement about every `n` above `3512`, so it splits at a bound into

* `H1` -- the finite range: the claim holds for `3512 < n <= 3612`.  This is a finite,
  decidable verification (one hundred explicit cases, each a finite prime search).
* `H2` -- the tail: the claim holds for every `n > 3612`.  This is the open core, the part
  that needs an argument for arbitrarily large `n`.

The parent statement restricts to `3512 < n`, `H1` and `H2` together cover exactly that range,
so `main` is a case split on `n <= 3612`.
-/

namespace OMA.R_OeisA219023_conjecture_2_R1

/-- The finite range `3512 < n <= 3612`: finitely many explicit cases. -/
def H1 : Prop :=
  ∀ n : ℕ, 3512 < n → n ≤ 3612 →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n ∧
      Nat.Prime (n ^ 2 - n + p) ∧ Nat.Prime (n ^ 2 + n - p)

/-- The tail `n > 3612`: the open core of the conjecture. -/
def H2 : Prop :=
  ∀ n : ℕ, 3612 < n →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n ∧
      Nat.Prime (n ^ 2 - n + p) ∧ Nat.Prime (n ^ 2 + n - p)

theorem main : H1 → H2 → type_of% @OeisA219023.conjecture_2 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 3612
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_OeisA219023_conjecture_2_R1
