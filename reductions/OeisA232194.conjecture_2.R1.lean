import FormalConjectures.OEIS.«232194»

/-!
# A232194: the five indices with `a n = 1` and the open direction

`a n` counts the `0 < x < n` with `n x + (n - x)` and `n (n - x) - x` both prime.
The conjecture `a n = 1 ↔ n ∈ {3, 4, 6, 20, 24}` says that exactly those five indices
admit a unique such decomposition.

`H1` is the finite direction: at `3`, `4`, `6`, `20` and `24` the count is one.  This is a
direct computation of `a` on the five values.

`H2` is the open direction: no other index has count one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA232194_conjecture_2_R1

/-- The finite direction: the five listed indices have count one. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∈ ({3, 4, 6, 20, 24} : Finset ℕ) → OeisA232194.a n = 1

/-- The open direction: count one happens only at the five listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA232194.a n = 1 → n ∈ ({3, 4, 6, 20, 24} : Finset ℕ)

theorem main : H1 → H2 → type_of% @OeisA232194.conjecture_2 := by
  intro h1 h2 n
  constructor
  · exact h2 n
  · exact h1 n

end OMA.R_OeisA232194_conjecture_2_R1
