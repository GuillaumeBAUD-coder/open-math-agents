import Mathlib

/-!
# Erdős Problem 708 (corrected statement)

Source: https://www.erdosproblems.com/708
Credit: @YourFriendPollux (first version); correction by @schulzee (agent: Claude Code, model claude-fable-5-2)

## The problem

Let $g(n)$ be minimal such that for any $A \subseteq [2,\infty) \cap \mathbb{N}$ with
$|A| = n$ and any set $I$ of $\max(A)$ consecutive integers there exists some
$B \subseteq I$ with $|B| = g(n)$ such that $\prod_{a \in A} a \mid \prod_{b \in B} b$.
Is it true that $g(n) \le (2+o(1))n$? Or perhaps even $g(n) \le 2n$?
Erdős and Surányi proved $g(n) \ge (2-o(1))n$ and $g(3) = 4$.

## Why the earlier statement needs a correction

* It used the name `atTop` without `open Filter`. With `autoImplicit` on, `atTop` becomes an
  arbitrary filter; with `autoImplicit` off (the setting of the official checker) the file does
  not compile.
* It asked for `B.card = k` exactly. For `A = {2, ..., n+1}` every block `I` has only `n + 1`
  elements, so no size above `n + 1` is admissible and `g n ≤ n + 1` holds for a trivial
  reason. This contradicts the bound `g(n) ≥ (2 - o(1)) n` of the source. The source means
  `|B| ≤ g(n)`: a larger `B` inside `I` keeps the divisibility whenever `I` has room.

## Formalization notes

* `SizeSuffices n k` states `g(n) ≤ k`: for every `n`-element `A ⊆ [2, ∞) ∩ ℕ` and every block
  `I = {m, ..., m + max A - 1}` of `max A` consecutive positive integers there is `B ⊆ I` with
  at most `k` elements and `∏ A ∣ ∏ B`. No `sInf` is used, so there is no junk value.
* `A.sup id` is `max A` for nonempty `A`. For `n = 0` the block is empty and `B = ∅` works.
* Blocks of positive integers are enough: a block of integers that contains `0` is trivial
  (`B = {0}`), and a block of negative integers is the mirror image of a positive block.
* `g(n) ≤ (2 + o(1)) n` is stated as: for every `ε > 0`, for all large `n`, some natural
  `k ≤ (2 + ε) n` suffices. The stronger guess `g(n) ≤ 2n` is `∀ n, SizeSuffices n (2 * n)`.
-/

namespace OMA.S_erdos_708

/-- `SizeSuffices n k` means `g(n) ≤ k`. -/
def SizeSuffices (n k : ℕ) : Prop :=
  ∀ A : Finset ℕ, A.card = n → (∀ a ∈ A, 2 ≤ a) →
    ∀ m : ℕ, 1 ≤ m →
      ∃ B : Finset ℕ, B ⊆ Finset.Ico m (m + A.sup id) ∧ B.card ≤ k ∧
        (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)

theorem main : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∃ k : ℕ, (k : ℝ) ≤ (2 + ε) * n ∧ SizeSuffices n k := by
  sorry

end OMA.S_erdos_708
