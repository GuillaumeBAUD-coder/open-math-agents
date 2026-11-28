import Mathlib

/-!
# A227533: some power `(2n)^e` with `e > 1` is a totient

Source: https://oeis.org/A227533
Credit: @R-Dson

`a(n)` is the smallest `e > 1` such that `(2n)^e` is a totient, or `0` if no such `e` exists.
Conjecture: `a(n) > 0` for all `n`.

Conventions.
- A totient is a value of Euler's totient function: `k` is a totient when `k = φ(m)` for some
  `m ≥ 1` (`Nat.totient`, with `φ(1) = 1`).
- `a(n)` is the infimum in `ℕ` of the set of such `e`. Every `e` in the set is `> 1`, so
  `a(n) = 0` exactly when the set is empty.
- The offset of the entry is `1`, so `n ≥ 1`.
- Examples from the entry: `a(1) = 2` because `φ(5) = 2^2`, and `a(11) = 3` because
  `φ(13315) = 22^3` while `22^2` is not a totient.
-/

namespace OMA.S_oeis_a227533

/-- `k` is a totient: `k = φ(m)` for some `m ≥ 1`. -/
def IsTotient (k : ℕ) : Prop := ∃ m : ℕ, Nat.totient m = k

/-- Smallest `e > 1` such that `(2n)^e` is a totient, or `0` if no such `e` exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {e : ℕ | 1 < e ∧ IsTotient ((2 * n) ^ e)}

theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a227533
