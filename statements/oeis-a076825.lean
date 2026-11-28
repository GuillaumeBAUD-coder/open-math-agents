import Mathlib

/-!
# A076825: indices n with u(n) = 1, where u(n) = 2^u(n-1) mod n (a(n)/n^2 -> oo)

Source: https://oeis.org/A076825 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A076825 (offset 1): let u(1) = 1, u(n) = 2^u(n-1) (mod n); the sequence gives the values of n
such that u(n) = 1; data 1, 3, 15, 21, 51, 65, 95, 165, 255, 261, ...

The entry records:

  Conjecture: a(n)/n^2 -> oo.

Reading of the source:
* `u 1 = 1` and, for `n ≥ 2`, `u n = 2^(u (n-1)) mod n` (the least nonnegative residue).
  `u 0` is not part of the source; it is set to 0 and never used, since the sequence only
  looks at indices `n ≥ 1`.
* `a n` (for `n ≥ 1`) is the `n`-th index `m ≥ 1` with `u m = 1`, in increasing order:
  `Nat.nth` (which counts from 0) at `n - 1`.
* "a(n)/n^2 -> oo" is divergence to `+∞` in `ℝ` as `n → ∞`. (It implies that there are
  infinitely many such indices, so `Nat.nth` enumerates all of them.)
-/

namespace OMA.S_oeis_a076825

open Filter

/-- `u(1) = 1`, `u(n) = 2^u(n-1) mod n` for `n ≥ 2` (and `u(0) = 0`, unused). -/
def u : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 ^ u (n + 1) % (n + 2)

/-- A076825(n): the `n`-th index `m ≥ 1` with `u(m) = 1` (`n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => 1 ≤ m ∧ u m = 1) (n - 1)

/-- The conjecture: `a(n)/n^2 → ∞`. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 2) atTop atTop := by
  sorry

end OMA.S_oeis_a076825
