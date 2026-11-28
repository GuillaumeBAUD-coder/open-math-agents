import Mathlib

/-!
# A268597: every `n` is `(x - 1) mod φ(x)` for some `x ≥ 1`

Source: https://oeis.org/A268597
Credit: @R-Dson

`a(n)` is the smallest `x` such that `x - 1 mod φ(x) = n`, where `φ` is Euler's totient function,
or `0` if no such `x` exists.
Conjecture: `a(n) > 0` for all `n`.

Conventions.
- `x` ranges over the positive integers, as in the program of the entry (it starts at `x = 1`);
  `x - 1` is truncated subtraction in `ℕ`, which is plain subtraction for `x ≥ 1`.
- `a(n)` is the infimum in `ℕ` of the set of such `x`. Every `x` in the set is `> 0`, so
  `a(n) = 0` exactly when the set is empty.
- The offset of the entry is `0`, so `n` ranges over `ℕ`.
- First terms of the entry, as reproduced by these definitions: `a(0) = 1`, `a(1) = 4`,
  `a(2) = 9`, `a(3) = 8`.
-/

namespace OMA.S_oeis_a268597

/-- `x > 0` satisfies `(x - 1) mod φ(x) = n`. -/
def SubOneModTotientEq (n x : ℕ) : Prop := 0 < x ∧ (x - 1) % Nat.totient x = n

/-- Smallest `x` such that `x - 1 mod φ(x) = n`, or `0` if no such `x` exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {x : ℕ | SubOneModTotientEq n x}

theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a268597
