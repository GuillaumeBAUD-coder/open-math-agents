import FormalConjectures.OEIS.«24356»

/-!
# A024356: the zero at index `4` and the uniqueness of that zero

The conjecture `∀ n, a n = 0 ↔ n = 4` splits into two statements of very different strength.

* `H1` records the zero at index `4`.  It is a concrete determinant computation: the `4 × 4`
  Hankel matrix of the primes `2, 3, 5, 7, 11, 13, 17` is singular, with `(6, -3, -2, 1)` in its
  kernel.  The module already proves this as `OeisA24356.a_4`.
* `H2` is the open direction: no other index vanishes.

`main` assembles the two directions into the biconditional.
-/

namespace OMA.R_OeisA24356_conjecture_R1

/-- The existence direction: the sequence vanishes at `4`. -/
def H1 : Prop :=
  OeisA24356.a 4 = 0

/-- The uniqueness direction: `4` is the only index at which the sequence vanishes. -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA24356.a n = 0 → n = 4

theorem main : H1 → H2 → type_of% @OeisA24356.conjecture := by
  intro h1 h2 n
  exact ⟨h2 n, fun hn => by rw [hn]; exact h1⟩

end OMA.R_OeisA24356_conjecture_R1
