import Mathlib

/-!
# Pollock's conjectures

Source: https://en.wikipedia.org/wiki/Pollock's_conjectures
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The source lists several conjectures of Pollock (1850). Of these, the cube-numbers case
(Wieferich–Kempner), the icosahedral and dodecahedral cases (2025) and the centered nonagonal
case (2023) are reported there as settled. The two that the source still lists as open are:

* Pollock tetrahedral numbers conjecture: every positive integer is the sum of at most 5
  tetrahedral numbers;
* Pollock octahedral numbers conjecture: every positive integer is the sum of at most 7
  octahedral numbers (proved there only for all sufficiently large numbers).

`main` is the conjunction of these two open conjectures.

Conventions:
* the `k`-th tetrahedral number is `k (k + 1) (k + 2) / 6` and the `k`-th octahedral number is
  `k (2 k ^ 2 + 1) / 3`, both for `k : ℕ`; the divisions are exact in `ℕ`;
* `k = 0` gives the value `0`, so allowing index `0` in a sum of exactly `5` (resp. `7`) terms is
  the same as a sum of at most `5` (resp. `7`) positive figurate numbers; we state it directly as
  a list of at most `5` (resp. `7`) indices, which is equivalent;
* positive integers are `n : ℕ` with `0 < n`.
-/

namespace OMA.S_wp_pollock_s_conjectures

/-- The `k`-th tetrahedral number `k (k + 1) (k + 2) / 6`. -/
def tetrahedral (k : ℕ) : ℕ := k * (k + 1) * (k + 2) / 6

/-- The `k`-th octahedral number `k (2 k ^ 2 + 1) / 3`. -/
def octahedral (k : ℕ) : ℕ := k * (2 * k ^ 2 + 1) / 3

theorem main :
    (∀ n : ℕ, 0 < n → ∃ l : List ℕ, l.length ≤ 5 ∧ (l.map tetrahedral).sum = n) ∧
    (∀ n : ℕ, 0 < n → ∃ l : List ℕ, l.length ≤ 7 ∧ (l.map octahedral).sum = n) := by
  sorry

end OMA.S_wp_pollock_s_conjectures
