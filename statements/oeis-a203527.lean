import Mathlib

/-!
# A203527: a(n) = Product_{1 <= i < j <= n} (c(i) + c(j)); c = A018252 = nonprime numbers.

Source: https://oeis.org/A203527
Credit: @Evyrrun (agent: claude-code, model claude-opus-5-5)

Comment of A203527 (the entry is by Clark Kimberling):
  Each term divides its successor, as in A203528. It is conjectured that each term is
  divisible by the corresponding superfactorial, A000178(n); as in A203529.

Index convention. A203527 has offset 1 (data 1, 5, 350, 529200, ...) and A000178 has
offset 0 (data 1, 1, 2, 12, 288, ...). The companion entry A203529 is defined as
A203527(n)/A000178(n-1), and its comment reads: It is conjectured that every term is an
integer. So the corresponding superfactorial of A203527(n) is A000178(n-1): read with the
same index n, the divisibility already fails at n = 3 (12 does not divide 350), and it
also fails at n = 2, 4, 5, 6. The conjecture is therefore stated as in A203529:
A000178(n-1) divides A203527(n) for every n >= 1 (checked numerically for n <= 120).

Here c(i) is the i-th nonprime number (A018252: 1, 4, 6, 8, 9, 10, ...), the positive
integers that are not prime. Below the indices are shifted to start at 0, so c 0 = 1, and
a(n) is the product of c(i) + c(j) over 0 <= i < j < n (a(1) = 1, the empty product,
a(2) = 5, a(3) = 350).
-/

namespace OMA.S_oeis_a203527

/-- A018252, the nonprime positive integers, with 0-based index: c 0 = 1, c 1 = 4, c 2 = 6. -/
noncomputable def c (i : ℕ) : ℕ := Nat.nth (fun k => 0 < k ∧ ¬ Nat.Prime k) i

/-- A203527(n) = Product_{1 <= i < j <= n} (c(i) + c(j)), with 0-based indices. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (c i + c j)

/-- A000178(n) = Product_{k=0..n} k!, the superfactorial. -/
def sf (n : ℕ) : ℕ := ∏ k ∈ Finset.range (n + 1), k.factorial

/-- The conjecture of A203527 and A203529: A000178(n-1) divides A203527(n) for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → sf (n - 1) ∣ a n := by
  sorry

end OMA.S_oeis_a203527
