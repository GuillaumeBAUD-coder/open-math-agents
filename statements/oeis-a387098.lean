import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset

namespace OMA.S_oeis_a387098

/-- A placement of kings on an `n × n` board is a set of squares `(r, c) : Fin n × Fin n`
having `k` kings in each row and each column such that no two distinct kings attack each other
(i.e. they do not lie in squares whose row and column indices both differ by at most `1`). -/
def IsValidKingPlacement (n k : ℕ) (S : Finset (Fin n × Fin n)) : Prop :=
  (∀ r : Fin n, (S.filter fun p => p.1 = r).card = k) ∧
  (∀ c : Fin n, (S.filter fun p => p.2 = c).card = k) ∧
  (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    1 < Int.natAbs ((p.1 : ℤ) - (q.1 : ℤ)) ∨ 1 < Int.natAbs ((p.2 : ℤ) - (q.2 : ℤ)))

/-- `T(n, k)` (OEIS A387098): the number of ways to place `k` non-attacking kings
in each row and each column of an `n × n` board. -/
noncomputable def T (n k : ℕ) : ℕ :=
  letI := Classical.decPred (IsValidKingPlacement n k)
  (Finset.univ.filter fun S : Finset (Fin n × Fin n) => IsValidKingPlacement n k S).card

/-- Conjecture (OEIS A387098): `T(n, k) = 0` for `n < 4 * k` (`1 ≤ n`), except for `T(1, 1) = 1`. -/
theorem main :
    T 1 1 = 1 ∧ ∀ n k : ℕ, 1 ≤ n → n < 4 * k → ¬ (n = 1 ∧ k = 1) → T n k = 0 := by
  sorry

end OMA.S_oeis_a387098
