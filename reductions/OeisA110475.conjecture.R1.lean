import FormalConjectures.OEIS.«110475»

/-!
# A110475: exceptional integers versus sums of two weight-one integers

`a n` counts the symbols `*` and `^` in the canonical prime factorization of `n`.  Let
`exceptionalSet = {1,2,3,4,5,6,7,9,11}`.  The conjecture says that a positive integer is
*not* exceptional exactly when it is a sum `x + y` of two integers with a weight of one:

`∀ m > 0, m ∉ exceptionalSet ↔ ∃ x y : ℕ, a x = 1 ∧ a y = 1 ∧ m = x + y`.

`H1` is the finite direction: an exceptional `m` is not such a sum.

`H2` is the open direction: every non-exceptional positive `m` is such a sum.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA110475_conjecture_R1

/-- The finite direction: an exceptional `m` is not a sum of two weight-one integers. -/
def H1 : Prop :=
  ∀ m : ℕ, 0 < m →
    (∃ x y : ℕ, OeisA110475.a x = 1 ∧ OeisA110475.a y = 1 ∧ x + y = m) →
    m ∉ OeisA110475.exceptionalSet

/-- The open direction: every non-exceptional positive `m` is such a sum. -/
def H2 : Prop :=
  ∀ m : ℕ, 0 < m → m ∉ OeisA110475.exceptionalSet →
    ∃ x y : ℕ, OeisA110475.a x = 1 ∧ OeisA110475.a y = 1 ∧ x + y = m

theorem main : H1 → H2 → type_of% @OeisA110475.conjecture := by
  intro h1 h2 m hm
  exact ⟨h2 m hm, h1 m hm⟩

end OMA.R_OeisA110475_conjecture_R1
