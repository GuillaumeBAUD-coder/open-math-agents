import Mathlib

/-!
# The shifted-repunit identity recorded in OEIS A052379

Source: https://oeis.org/A052379
Comparison sequence: https://oeis.org/A023001
Credit: @Heart-galaxy

A052379 counts positive integers below 10^(n+1) whose decimal digits avoid
0 and 1, with offset 0 and initial value a(0)=8. We define it using the
source's recurrence a(n)=8*a(n-1)+8 at positive indices. A023001 has offset
0, b(0)=0, and source recurrence b(n)=8*b(n-1)+1 at positive indices.

Mathar conjectured a(n)=A023001(n+2)-1 on May 18, 2007. Wenders proved this
identity on March 26, 2008 in the OEIS entry. The shift preserves both
source index domains, and subtraction below is natural-number subtraction.
-/

namespace OMA.S_oeis_a052379

def a : ℕ → ℕ
  | 0 => 8
  | n + 1 => 8 * a n + 8

def b : ℕ → ℕ
  | 0 => 0
  | n + 1 => 8 * b n + 1


theorem main : ∀ n : ℕ, a n = b (n + 2) - 1 := by
  sorry

end OMA.S_oeis_a052379
