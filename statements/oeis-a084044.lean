import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Find

/-!
# OEIS A084044

Source: https://oeis.org/A084044 (Amarnath Murthy and Meenakshi Srikanth,
OEIS Foundation, CC BY-SA 4.0). For positive n, take the least positive
palindromic multiple of n containing its decimal expansion as a substring,
or zero when no such multiple exists. The substring may touch either end.
Lean stores the least significant digit first, which preserves substrings
and palindromicity.
-/

namespace OMA.S_oeis_a084044

def admissible (n m : ℕ) : Prop := 0 < m ∧ n ∣ m ∧
    (Nat.digits 10 m).reverse = Nat.digits 10 m ∧
    ∃ left right : List ℕ,
      Nat.digits 10 m = left ++ Nat.digits 10 n ++ right

noncomputable def a (n : ℕ) : ℕ := open Classical in
  if h : ∃ m, admissible n m then Nat.find h else 0

theorem main : ∀ n : ℕ, 0 < n → (a n = 0 ↔ 10 ∣ n) := by
  sorry

end OMA.S_oeis_a084044
