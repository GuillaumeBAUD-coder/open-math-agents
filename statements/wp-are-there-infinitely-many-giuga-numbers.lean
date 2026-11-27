import Mathlib

/-!
# Are there infinitely many Giuga numbers?

Source: https://en.wikipedia.org/wiki/Giuga_number
Credit: @LAPRAI

A Giuga number is a composite number `n` such that for each of its distinct prime factors `p`,
`p` divides `n / p - 1`. Equivalently, `∑_{p ∣ n} 1/p - ∏_{p ∣ n} 1/p` is an integer.
Known examples: 30, 858, 1722, 66198, ... It is open whether there are infinitely many.

## Encoding

* Composite: `1 < n` and `n` is not prime.
* For every prime `p ∣ n`, `p ∣ n / p - 1` (natural-number division and subtraction; since
  `p ∣ n` and `n ≥ 1`, `n / p ≥ 1`, so the subtraction does not truncate).
* Infinitely many: the set of Giuga numbers is `Set.Infinite`.
-/

namespace OMA.S_wp_are_there_infinitely_many_giuga_numbers

/-- `n` is a Giuga number. -/
def IsGiuga (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ n / p - 1

/-- **Open question.** There are infinitely many Giuga numbers. -/
theorem main : {n : ℕ | IsGiuga n}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_giuga_numbers
