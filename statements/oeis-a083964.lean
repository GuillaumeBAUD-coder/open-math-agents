import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Find

/-!
# OEIS A083964

Source: https://oeis.org/A083964 (Amarnath Murthy and Meenakshi Srikanth,
OEIS Foundation, CC BY-SA 4.0). At positive index n, take the least
positive palindromic multiple of 2n - 1 whose decimal expansion begins
with the full expansion of 2n - 1. Set a(n) = 0 when no witness exists.
The source condition that n is not of the form (5k + 1) / 2 is rendered
as 5 not dividing 2n - 1. Lean stores the least significant digit first,
so a decimal prefix is a suffix of the digit list.
-/

namespace OMA.S_oeis_a083964

def admissible (n m : ℕ) : Prop := 0 < m ∧ (2*n-1) ∣ m ∧
    (Nat.digits 10 m).reverse = Nat.digits 10 m ∧
    ∃ tail : List ℕ, Nat.digits 10 m = tail ++ Nat.digits 10 (2*n-1)

noncomputable def a (n : ℕ) : ℕ := open Classical in
  if h : ∃ m, admissible n m then Nat.find h else 0

theorem main : ∀ n : ℕ, 0 < n → (¬ 5 ∣ (2*n-1)) → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a083964
