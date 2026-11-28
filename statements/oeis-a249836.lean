import Mathlib

/-!
# A249836: numbers n with tan(n) > n (log a(n) / n tends to Pi)

Source: https://oeis.org/A249836 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A249836 (offset 1): numbers n for which tan(n) > n (n in radians); data
1, 260515, 37362253, 122925461, 534483448, 3083975227, ...

The entry records (M. F. Hasler, Sep 10 2020, corrected thanks to Vaclav Kotesovec):

  log(a(n)) / n ~ Pi, conjectured.

(The entry also notes that it is an open problem whether tan(n) > n for infinitely many integers
n.)

Reading of the source:
* The terms are the positive integers `m` with `tan m > m` (`Real.tan`, radians), in increasing
  order; `a n` (for `n ≥ 1`) is `Nat.nth` (which counts from 0) at `n - 1`.
* "log(a(n))/n ~ Pi" is read as `log(a(n)) / n → π` (equivalently the ratio to `π` tends to 1),
  natural logarithm. This implies that the sequence is infinite, so `Nat.nth` enumerates it.
-/

namespace OMA.S_oeis_a249836

open Filter Topology

/-- A249836(n): the `n`-th positive integer `m` with `tan m > m` (`n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m : ℕ => 0 < m ∧ (m : ℝ) < Real.tan m) (n - 1)

/-- Hasler's conjecture: `log(a(n)) / n → π`. -/
theorem main : Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 Real.pi) := by
  sorry

end OMA.S_oeis_a249836
