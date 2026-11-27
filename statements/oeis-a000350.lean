import Mathlib

/-!
# A000350: Numbers m such that Fibonacci(m) ends with m

Source: https://oeis.org/A000350
Credit: @niclorusso

Conjecture (in the comments of A000350): Other than 1 and 5, there is no m such that Fibonacci(m)
in binary ends with m in binary. The comments add that it holds for m < 2^25 and that Max Alekseyev
proved it (m must be 0, 1 or 5); it is stated here as the conjecture, for m > 0.

Conventions:
* Fibonacci(m) is Mathlib's `Nat.fib m` (Fibonacci(0) = 0, Fibonacci(1) = 1).
* `Nat.digits 2 n` lists the binary digits of n, least significant first, with no leading zeros.
  So "the binary expansion of x ends with the binary expansion of m" says that `Nat.digits 2 m` is a
  prefix of `Nat.digits 2 x`.
* The sequence is about positive m (m = 0 has an empty binary expansion), so m > 0.
-/

namespace OMA.S_oeis_a000350

/-- The binary expansion of `x` ends with the binary expansion of `m`. -/
def BinaryEndsWith (x m : ℕ) : Prop :=
  Nat.digits 2 m <+: Nat.digits 2 x

/-- The binary analogue of A000350: the only positive `m` such that `Fibonacci(m)` in binary ends
with `m` in binary are `1` and `5`. -/
theorem main : {m : ℕ | 0 < m ∧ BinaryEndsWith (Nat.fib m) m} = {1, 5} := by
  sorry

end OMA.S_oeis_a000350
