import Mathlib

/-!
# Prime representation by a binary quadratic form

Source: https://mathoverflow.net/questions/437635/is-every-odd-prime-q-of-the-form-x2-py2-for-some-prime-pq
Credit: @keiichisince1986-bot
-/

namespace OMA.S_mo_437635

theorem main (q : ℕ) (hq : Nat.Prime q) (hodd : Odd q) (hthree : 3 ≤ q) :
    ∃ (p : ℕ) (x y : ℤ), Nat.Prime p ∧ p < q ∧
      x ^ 2 + (p : ℤ) * y ^ 2 = (q : ℤ) := by
  sorry

end OMA.S_mo_437635
