import FormalConjectures.OEIS.«157237»

/-!
# A157237: the indices with `a n = 0` and the open direction

`a n` counts the representations of the odd number `2n - 1` as `p + 2^x + 11 · 2^y` with `p`
prime, `p ≡ 1 mod 6` and `x, y` positive.  The conjecture
`a n = 0 ↔ n ≤ 15 ∨ n = 18 ∨ n = 21 ∨ n = 24 ∨ n = 51 ∨ n = 84 ∨ n = 1011 ∨ n = 59586` says
that exactly those indices give no representation.

`H1` is the finite direction: at the listed indices the count is zero.  This is a direct
computation of `a` on those values.

`H2` is the open direction: zero happens only at the listed indices.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA157237_conjecture_R1

/-- The finite direction: the listed indices have count zero. -/
def H1 : Prop :=
  ∀ n : ℕ, n ≤ 15 ∨ n ∈ ({18, 21, 24, 51, 84, 1011, 59586} : Finset ℕ) → OeisA157237.a n = 0

/-- The open direction: zero happens only at the listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA157237.a n = 0 → n ≤ 15 ∨ n ∈ ({18, 21, 24, 51, 84, 1011, 59586} : Finset ℕ)

theorem main : H1 → H2 → type_of% @OeisA157237.conjecture := by
  intro h1 h2 n hn
  constructor
  · exact h2 n
  · intro h
    exact h1 n h

end OMA.R_OeisA157237_conjecture_R1
