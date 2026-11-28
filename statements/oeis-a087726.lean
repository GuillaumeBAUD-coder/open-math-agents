import Mathlib

/-!
# A087726: Number of elements X in the matrix ring M_2(Z_n) such that X^2 == 0 mod n.

Source: https://oeis.org/A087726
Credit: @divmxnd0x

Conjecture (Ben Branman, Mar 22 2013, stated in A087726): `a(n) = n^2` if and only if `n` is
squarefree.

Formalization notes:
* `a n` is the number of `2 × 2` matrices `X` over `ZMod n` with `X * X = 0` (offset 1:
  `a 1, a 2, ... = 1, 4, 9, 28, 25, 36, ...`); `ZMod n` is finite for `n ≥ 1`, so `Nat.card` is the
  number of such matrices.
* The conjecture is stated for `n ≥ 1`.
-/

namespace OMA.S_oeis_a087726

/-- A087726(n): the number of `X ∈ M_2(ℤ/nℤ)` with `X^2 = 0`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {X : Matrix (Fin 2) (Fin 2) (ZMod n) // X * X = 0}

/-- Branman's conjecture: for `n ≥ 1`, `a n = n^2` iff `n` is squarefree. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = n ^ 2 ↔ Squarefree n) := by
  sorry

end OMA.S_oeis_a087726
