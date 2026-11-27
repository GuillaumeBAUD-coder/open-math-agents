import Mathlib

/-!
# A058128: a(1) = 1, a(n) = (n^n-n)/(n-1)^2 for n >= 2.

Source: https://oeis.org/A058128
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a058128

def a (n : ℕ) : ℕ :=
  if n = 1 then 1 else (n ^ n - n) / (n - 1) ^ 2

def IsWeakFermatPseudoprime (m base : ℕ) : Prop :=
  1 < m ∧ ¬ Nat.Prime m ∧ base ^ m ≡ base [MOD m]

theorem main : ∀ n : ℕ, 2 ≤ n → n % 2 = 0 →
    Nat.Prime (a n) ∨ IsWeakFermatPseudoprime (a n) n := by
  sorry

end OMA.S_oeis_a058128
