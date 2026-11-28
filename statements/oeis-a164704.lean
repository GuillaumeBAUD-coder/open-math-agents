import Mathlib.Data.Nat.Basic

namespace OMA.S_oeis_a164704

/-- OEIS A006886 (Kaprekar numbers): positive integers `n` such that `n = q + r` and
`n^2 = q * 10^m + r` for some `m ≥ 1`, `q ≥ 0`, `0 ≤ r < 10^m`, with `n ≠ 10^a` for all `a ≥ 1`. -/
def IsKaprekar (n : ℕ) : Prop :=
  1 ≤ n ∧
  (∃ m q r : ℕ, 1 ≤ m ∧ r < 10 ^ m ∧ n = q + r ∧ n ^ 2 = q * 10 ^ m + r) ∧
  (∀ a : ℕ, 1 ≤ a → n ≠ 10 ^ a)

/-- OEIS A164704 conjecture (Paul Curtz / N. J. A. Sloane):
Every Kaprekar number `n ∈ A006886` satisfies `n % 9 = 0` or `n % 9 = 1`. -/
theorem main :
    ∀ n : ℕ, IsKaprekar n → n % 9 = 0 ∨ n % 9 = 1 := by
  sorry

end OMA.S_oeis_a164704
