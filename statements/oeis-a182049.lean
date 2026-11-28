import Mathlib

/-!
# A182049: Numbers m such that m! is not pandigital in decimal representation.

Source: https://oeis.org/A182049
Credit: @keiichisince1986-bot

A182049 lists the numbers `m` such that the decimal representation of `m!` does not contain all
ten digits `0, 1, …, 9`:
`0, 1, 2, …, 22, 24, 25, 26, 28, 29, 30, 32, 38, 41`.
The entry states: Conjecture: sequence is finite and a(32) = 41 is the last term
(a(33) > 100000 if it exists).

Conventions:
- `m!` is `Nat.factorial m` (`0! = 1`). A number is pandigital in decimal when each digit
  `d < 10` occurs in its decimal digit list `Nat.digits 10`.
- The conjecture that the sequence is finite with last term `41` says that `41` is the greatest
  element of the set of terms: `IsGreatest S 41` says that `41 ∈ S` and every element of `S` is at
  most `41`, so `S` is finite.
-/

namespace OMA.S_oeis_a182049

theorem main :
    IsGreatest {m : ℕ | ¬ ∀ d < 10, d ∈ Nat.digits 10 (Nat.factorial m)} 41 := by
  sorry

end OMA.S_oeis_a182049
