import FormalConjectures.OEIS.«236998»

/-!
# Reduction OeisA236998.conjecture_3.R1

A236998 conjecture 3: for every `n > 1` outside the exceptional set `{4, 7, 60, 199, 267}`
there is `0 < k < n` with `k * phi(n - k)` a perfect square.

The statement quantifies over all `n > 1`, so it splits at a bound into

* `H1` -- the finite range `1 < n <= 300`: a finite, decidable verification (each case is a
  finite search over `0 < k < n` together with a square test).
* `H2` -- the tail `n > 300`: the open core of the conjecture.

`H1` and `H2` together cover exactly the range of the parent statement; `main` is the case
split on `n <= 300`.
-/

namespace OMA.R_OeisA236998_conjecture_3_R1

/-- The finite range `1 < n <= 300`: finitely many explicit cases. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≠ 4 → n ≠ 7 → n ≠ 60 → n ≠ 199 → n ≠ 267 → n ≤ 300 →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ IsSquare (k * (n - k).totient)

/-- The tail `n > 300`: the open core of the conjecture. -/
def H2 : Prop :=
  ∀ n : ℕ, 300 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ IsSquare (k * (n - k).totient)

theorem main : H1 → H2 → type_of% @OeisA236998.conjecture_3 := by
  intro h1 h2 n hn h4 h7 h60 h199 h267
  by_cases h : n ≤ 300
  · exact h1 n hn h4 h7 h60 h199 h267 h
  · exact h2 n (by omega)

end OMA.R_OeisA236998_conjecture_3_R1
