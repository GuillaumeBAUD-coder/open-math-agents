import FormalConjectures.OEIS.«238568»

/-!
# A238568: the seven indices with `a n = 1` and the open direction

`a n` counts the `0 < k < n` for which `n ^ 2 - π(k n)` is prime.  The conjecture
`a n = 1 ↔ n ∈ {2, 3, 4, 8, 10, 24, 41}` says that exactly those seven indices have a
single such `k`.

`H1` is the finite direction: at the seven listed indices the count is one.  This is a
direct computation of `a` on those values.

`H2` is the open direction: no other index has count one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA238568_conjecture_2_R1

/-- The finite direction: the seven listed indices have count one. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∈ ({2, 3, 4, 8, 10, 24, 41} : Set ℕ) → OeisA238568.a n = 1

/-- The open direction: count one happens only at the seven listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA238568.a n = 1 → n ∈ ({2, 3, 4, 8, 10, 24, 41} : Set ℕ)

theorem main : H1 → H2 → type_of% @OeisA238568.conjecture_2 := by
  intro h1 h2 n
  exact ⟨h2 n, h1 n⟩

end OMA.R_OeisA238568_conjecture_2_R1
