import Mathlib

/-!
# OEIS A372313: a row that starts at 33 mod 100 stays at 33 mod 100

Source: https://oeis.org/A372313 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A372313 (Ali Sada, Apr 26 2024), offset 1: Table read by antidiagonals: A(n,1) = 2n-1, and
for k > 1, A(n,k) = A372289(A(n,k-1)+A(n,1)). Comment: Conjecture: if A(n,1) is congruent to 33
(mod 100), then all terms on the n-th row are congruent to 33 (mod 100).
Entry A372289 (Antti Karttunen and Ali Sada, Apr 26 2024): a(n) = n*2^e + (4^e - 1)/3, where e is
the 2-adic valuation of n.

Formalization notes:
* `f` is A372289, with e = `padicValNat 2 n` and natural-number division (4^e - 1 is divisible
  by 3).
* `row n j` is A(n, j+1), so row n 0 = 2n - 1 = A(n,1) and row n (j+1) = f(row n j + (2n - 1)).
  The statement quantifies over every row n (for n = 0 the hypothesis fails) and every column.
* Control from the entry's example: row 3 begins 5, 21, 53, 117.
-/

namespace OMA.S_oeis_a372313

/-- A372289(n) = n*2^e + (4^e - 1)/3, e the 2-adic valuation of n. -/
def f (n : ℕ) : ℕ := n * 2 ^ padicValNat 2 n + (4 ^ padicValNat 2 n - 1) / 3

/-- row n j = A(n, j+1): A(n,1) = 2n - 1 and A(n,k) = A372289(A(n,k-1) + A(n,1)). -/
def row (n : ℕ) : ℕ → ℕ
  | 0 => 2 * n - 1
  | j + 1 => f (row n j + (2 * n - 1))

/-- Sada's conjecture: if A(n,1) = 33 mod 100, every term of row n is 33 mod 100. -/
theorem main : ∀ n : ℕ, (2 * n - 1) % 100 = 33 → ∀ j : ℕ, row n j % 100 = 33 := by
  sorry

end OMA.S_oeis_a372313
