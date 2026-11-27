import Mathlib

/-!
# A000350: Numbers m such that Fibonacci(m) ends with m.

Source: https://oeis.org/A000350
Credit: @rabdelaal

OEIS A000350 records the conjecture that, other than `1` and `5`, there is no `m` such that
`Fibonacci(m)` in binary ends with `m` in binary (verified up to `m = 50000` by Ralf Stephan
and up to `2 ^ 25` by T. D. Noe). "Ends with" is read as: the binary representation of `m`
is a suffix of the binary representation of `Nat.fib m`, i.e. `Nat.fib m` agrees with `m`
modulo `2 ^ (Nat.log2 m + 1)`, the place value just above the top binary digit of `m`.
-/

namespace OMA.S_oeis_a000350

/-- The binary-suffix condition: the binary representation of `m` is a suffix of that of
`Nat.fib m` (for `m > 0`). -/
def BinarySuffixFib (m : Ôäò) : Prop :=
  Nat.fib m % 2 ^ (Nat.log2 m + 1) = m

/-- Other than `1` and `5`, no positive `m` has `Fibonacci(m)` ending with `m` in binary
(conjecture recorded in OEIS A000350). -/
theorem main : ÔêÇ m > 0, BinarySuffixFib m ÔåÆ m = 1 Ôê¿ m = 5 := by
  sorry

end OMA.S_oeis_a000350
