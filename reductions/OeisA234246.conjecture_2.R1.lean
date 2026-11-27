import FormalConjectures.OEIS.«234246»

/-!
# A234246: the nine indices with `a n = 1` and the open direction

The conjecture `a n = 1 ↔ n ∈ {4, 5, 8, 9, 12, 13, 24, 33, 49}` says that the count of
`0 < k < n` with `k * φ(n - k) + 1` a square equals one exactly at those nine indices.

`H1` is the finite direction: at each of the nine indices the count is one.  This is a direct
computation of totients and squares over the finitely many `k < n`.

`H2` is the open direction: no other index has count one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA234246_conjecture_2_R1

/-- The finite direction: the nine listed indices have count one. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∈ ({4, 5, 8, 9, 12, 13, 24, 33, 49} : Finset ℕ) → OeisA234246.a n = 1

/-- The open direction: count one happens only at the nine listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA234246.a n = 1 → n ∈ ({4, 5, 8, 9, 12, 13, 24, 33, 49} : Finset ℕ)

theorem main : H1 → H2 → type_of% @OeisA234246.conjecture_2 := by
  intro h1 h2 n
  exact ⟨h2 n, h1 n⟩

end OMA.R_OeisA234246_conjecture_2_R1
