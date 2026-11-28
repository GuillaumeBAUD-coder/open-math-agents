import Mathlib

/-!
# A285802: Smallest number that when multiplied by n contains the digit 7.

Source: https://oeis.org/A285802
Credit: @ShoQo

Conjecture: "35 is the highest value to occur in this sequence." (Giovanni Resta, Apr 27 2017:
"Conjecture is true.")

Formalization notes:
* Offset 1: a(n) is the least k ≥ 1 such that the decimal expansion of k*n contains a 7
  (data: 7, 35, 9, 18, 14, ...).
* "35 is the highest value to occur" is stated as two parts: every n ≥ 1 has some k with
  1 ≤ k ≤ 35 and a digit 7 in k*n (so a(n) exists and a(n) ≤ 35), and the value 35 occurs,
  witnessed by a(2) = 35: no k in 1..34 works for n = 2, while 35*2 = 70 does.
* Digits are Mathlib's `Nat.digits 10` (least significant first); membership does not
  depend on the order.
-/

namespace OMA.S_oeis_a285802

/-- The decimal expansion of `x` contains the digit 7. -/
def HasSeven (x : ℕ) : Prop := 7 ∈ Nat.digits 10 x

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ 35 ∧ HasSeven (k * n)) ∧
    ((∀ k : ℕ, 1 ≤ k → k < 35 → ¬ HasSeven (k * 2)) ∧ HasSeven (35 * 2)) := by
  sorry

end OMA.S_oeis_a285802
