import FormalConjectures.OEIS.«237578»

/-!
# A237578: the three indices with `a n = 1` and the open direction

`a n` counts the `0 < k < n` with `π(k n)` prime.  The conjecture `a n = 1 ↔ n ∈ {5, 8, 13}`
says that the count is one exactly at those three indices.

`H1` is the finite direction: at `5`, `8` and `13` the count is one.  This is a direct
computation of `π` on the finitely many products `k n`.

`H2` is the open direction: no other index has count one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA237578_conjecture_2_R1

/-- The finite direction: the three listed indices have count one. -/
def H1 : Prop :=
  ∀ n : ℕ, (n = 5 ∨ n = 8 ∨ n = 13) → OeisA237578.a n = 1

/-- The open direction: count one happens only at the three listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA237578.a n = 1 → n = 5 ∨ n = 8 ∨ n = 13

theorem main : H1 → H2 → type_of% @OeisA237578.conjecture_2 := by
  intro h1 h2 n
  constructor
  · intro hn
    simpa using h2 n hn
  · exact h1 n

end OMA.R_OeisA237578_conjecture_2_R1
