import FormalConjectures.OEIS.«249609»

/-!
# A249609: the five odious Pascal rows and the open direction

The conjecture `a n = 0 ↔ n ∈ {0, 1, 2, 7, 8}` says that exactly the rows `0, 1, 2, 7, 8` of
Pascal's triangle consist only of odious numbers.

`H1` is the finite direction: for each of those five indices, the least `1 ≤ m ≤ n` with
`C(n, m)` evil does not exist, i.e. `a n = 0`.  This is a direct computation of binomial
coefficients and binary digit counts.

`H2` is the open direction: no other row is entirely odious.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA249609_conjecture_R1

/-- The finite direction: the five listed rows have no evil binomial coefficient. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) → OeisA249609.a n = 0

/-- The open direction: a row is entirely odious only for those five indices. -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA249609.a n = 0 → n ∈ ({0, 1, 2, 7, 8} : Finset ℕ)

theorem main : H1 → H2 → type_of% @OeisA249609.conjecture := by
  intro h1 h2 n
  exact ⟨h2 n, h1 n⟩

end OMA.R_OeisA249609_conjecture_R1
