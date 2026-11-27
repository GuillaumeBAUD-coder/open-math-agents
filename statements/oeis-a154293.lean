import Mathlib

/-!
# A154293: Integers of the form t/6, where t is a triangular number (A000217).

Source: https://oeis.org/A154293
Credit: @maaaakks

OEIS A154293 contains the comment
  "Conjecture: A193828 divided by 2. - Omar E. Pol, Aug 19 2011"
(later annotated "The above conjecture is correct." by Charles R Greathouse IV).

Sequences and indexing:
* A154293 (offset 1): the integers `m` such that `6 * m` is a triangular number
  `k * (k + 1) / 2` (`k ≥ 0`), listed in increasing order:
  `0, 1, 6, 11, 13, 20, 35, 46, 50, 63, ...`. Since `t = 0` is triangular, `a(1) = 0`.
  We define `A154293 n = Nat.nth p (n - 1)`, so `A154293 1 = 0`, `A154293 2 = 1`, ...
  (the value at the unused index `0` is irrelevant).
* A193828 (offset 0): "Even generalized pentagonal numbers", i.e. the even numbers of the
  form `m * (3 * m - 1) / 2` with `m ∈ ℤ`, listed in increasing order:
  `0, 2, 12, 22, 26, 40, 70, 92, 100, 126, ...`.
  We define `A193828 n = Nat.nth q n`, so `A193828 0 = 0`, `A193828 1 = 2`, ...
  (`2 * x = m * (3 * m - 1)` is the division-free form of `x = m * (3 * m - 1) / 2`).

Conjecture (with both OEIS offsets respected): `A154293(n) = A193828(n - 1) / 2` for all `n ≥ 1`.
-/

namespace OMA.S_oeis_a154293

/-- A154293(n), offset 1: the `n`-th integer `m ≥ 0` such that `6 * m` is triangular. -/
noncomputable def A154293 (n : ℕ) : ℕ :=
  Nat.nth (fun m : ℕ => ∃ k : ℕ, k * (k + 1) / 2 = 6 * m) (n - 1)

/-- A193828(n), offset 0: the `n`-th even generalized pentagonal number. -/
noncomputable def A193828 (n : ℕ) : ℕ :=
  Nat.nth (fun x : ℕ => Even x ∧ ∃ m : ℤ, 2 * (x : ℤ) = m * (3 * m - 1)) n

theorem main : ∀ n : ℕ, 1 ≤ n → A154293 n = A193828 (n - 1) / 2 := by
  sorry

end OMA.S_oeis_a154293
