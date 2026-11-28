import Mathlib

/-!
# A248125: Least positive integer m such that m + n divides C(2m,m) + C(2n,n), where C(2k,k) = (2k)!/(k!)^2.

Source: https://oeis.org/A248125
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) exists for all n > 0. Moreover, for n > 66 we have
a(n) < n except for n = 364, 408.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m,
  and "a(n) ≤ B" is the existence of such an m with m ≤ B.
* The "moreover" part is stated as: for n > 66 with n ∉ {364, 408}, some m < n works (the claim
  that a(n) ≥ n at 364 and 408 is not part of the statement).
* Controls (computed): a(1..12) = 1, 2, 5, 16, 3, 6, 2, 22, 101, 6, 21, 86, as in the entry; a(n)
  exists for n ≤ 60.
-/

namespace OMA.S_oeis_a248125



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ (2 * m).choose m + (2 * n).choose n) ∧
      ∀ n : ℕ, 66 < n → n ≠ 364 → n ≠ 408 →
        ∃ m : ℕ, 0 < m ∧ m < n ∧ m + n ∣ (2 * m).choose m + (2 * n).choose n := by
  sorry

end OMA.S_oeis_a248125
