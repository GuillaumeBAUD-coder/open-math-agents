import Mathlib.Data.Nat.Digits.Defs

/-!
The OEIS A110734 conjecture asks whether all sufficiently large positive `n`
have a multiple formed by inserting one decimal digit into every internal gap.
`Nat.digits 10 n` orders the original digits least significant first. Their
place values after insertion are `100^i`. The inserted digits, also listed
least significant first, have place values `10 * 100^i`.
-/

namespace OMA.S_oeis_a110734

def HasInsertedMultiple (n : ℕ) : Prop :=
  ∃ inserted : List ℕ,
    inserted.length + 1 = (Nat.digits 10 n).length ∧
      (∀ d ∈ inserted, d < 10) ∧
      n ∣ Nat.ofDigits 100 (Nat.digits 10 n) + 10 * Nat.ofDigits 100 inserted

theorem main : ∃ N : ℕ, ∀ n ≥ N, 0 < n → HasInsertedMultiple n := by
  sorry

end OMA.S_oeis_a110734
