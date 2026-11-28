import Mathlib

/-!
# `φ(m)φ(n) ≡ 0 (mod m + n)`

Source: https://mathoverflow.net/questions/303516 (CC BY-SA 4.0).

Question (Z.-W. Sun, who conjectures a positive answer; OEIS A248007): is it true that for each integer
`m > 6` there is a positive integer `n` with `φ(m)φ(n) ≡ 0 (mod m + n)`?

We state the conjectured positive answer.

Formalization notes:
* `φ` is `Nat.totient`. For `m ≤ 6` the property can fail, hence `6 < m`.
* Checked for `7 ≤ m < 1500` (searching `n < 2·10^5`): a suitable `n` always exists.
-/

namespace OMA.S_mo_303516

/-- For every `m > 6` some `n ≥ 1` has `m + n ∣ φ(m) φ(n)`. -/
theorem main : ∀ m : ℕ, 6 < m → ∃ n : ℕ, 0 < n ∧ (m + n) ∣ Nat.totient m * Nat.totient n := by
  sorry

end OMA.S_mo_303516
