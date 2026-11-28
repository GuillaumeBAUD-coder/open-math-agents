import FormalConjectures.OEIS.«215926»

/-!
# Reduction OeisA215926.conjecture_2.R2

A215926: `a n` is the smallest deficient `k` with `k * n` non-deficient, and `nextPrimeTwoPow m`
is the smallest prime above `2 ^ m` (A014210).  The conjecture says that the first `n >= 2` with
`a n = 2 ^ m` is `nextPrimeTwoPow m`.

`IsLeast S x` is `x ∈ S ∧ ∀ y ∈ S, x ≤ y`, so the claim has exactly two halves, and they are
different problems:

* `H1` -- the first-occurrence half: `nextPrimeTwoPow m` really is an occurrence,
  `a (nextPrimeTwoPow m) = 2 ^ m`.  This is the constructive/evaluative part (one value of `a`
  per `m`, involving the prime gap above `2 ^ m`).
* `H2` -- the minimality half: no `n >= 2` before `nextPrimeTwoPow m` has `a n = 2 ^ m`.
  This is the classifying part, the open core of the conjecture.

`main` reassembles them into the exact target.
-/

namespace OMA.R_OeisA215926_conjecture_2_R2

open OeisA215926

/-- The first-occurrence half: `nextPrimeTwoPow m` is a solution, `a (nextPrimeTwoPow m) = 2 ^ m`. -/
def H1 : Prop :=
  ∀ m : ℕ, 1 ≤ m → 2 ≤ nextPrimeTwoPow m ∧ a (nextPrimeTwoPow m) = 2 ^ m

/-- The minimality half: no `n` below `nextPrimeTwoPow m` has `a n = 2 ^ m`. -/
def H2 : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, 2 ≤ n → a n = 2 ^ m → nextPrimeTwoPow m ≤ n

theorem main : H1 → H2 → type_of% @OeisA215926.conjecture_2 := by
  intro h1 h2 m hm
  exact ⟨h1 m hm, fun n hn => h2 m hm n hn.1 hn.2⟩

end OMA.R_OeisA215926_conjecture_2_R2
