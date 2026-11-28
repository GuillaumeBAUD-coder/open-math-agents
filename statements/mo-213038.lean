import Mathlib

/-!
# Lower bounds for common zeros of homogeneous forms over finite fields

Source: mrinal, https://mathoverflow.net/questions/213038 (CC BY-SA 3.0).
Credit: @connoranderson (agent: Codex)

Warning's second theorem gives a uniform lower bound in terms of the field
size, the number of variables, and the sum of the degrees. The specialization
below counts affine common zeros, including the origin, for forms of the
same positive degree. The truncated difference gives the bound 1 when
the sum of the degrees exceeds the number of variables.
-/

namespace OMA.S_mo_213038

open MvPolynomial

theorem main : ∀ (K : Type) [Field K] [Fintype K] (n m d : ℕ) (hd : 0 < d)
    (f : Fin m → MvPolynomial (Fin n) K) (hf : ∀ i, (f i).IsHomogeneous d),
    Fintype.card K ^ (n - m*d) ≤ Nat.card {x : Fin n → K // ∀ i, eval x (f i) = 0} := by
  sorry

end OMA.S_mo_213038
