import Mathlib

/-!
# Erdős Problem 708

Source: https://www.erdosproblems.com/708
Credit: @mgv27

Let $g(n)$ be minimal such that for any $A \subseteq [2,\infty) \cap \mathbb{N}$ with $|A| = n$
and any set $I$ of $\max(A)$ consecutive integers there exists some $B \subseteq I$ with
$|B| = g(n)$ such that $\prod_{a \in A} a \mid \prod_{b \in B} b$.
Is it true that $g(n) \le (2 + o(1)) n$? (Or perhaps even $g(n) \le 2n$?)

Reading choices (see the source):
* `|B| = g(n)` is read as `|B| ≤ g(n)`. Read literally with equality, `g(n)` would not exist
  once `g(n) > n + 1`: for `A = {2, ..., n + 1}` every `I` has only `n + 1` elements. Divisibility
  is preserved by enlarging `B`, so `≤` is the intended meaning.
* `g(n)` is not introduced as an `sInf` (which would silently be `0` if no bound existed).
  Instead `GLe n x` states `g(n) ≤ x` directly, and `g(n) ≤ (2 + o(1)) n` is stated as:
  for every `ε > 0`, eventually `g(n) ≤ (2 + ε) n`.
* `I` ranges over all runs of `max(A)` consecutive integers in `ℤ`. Runs containing `0` are
  trivial (`B = {0}`), and runs of negative integers mirror runs of positive ones up to sign,
  so this agrees with the reading over positive integers.
* `main` is the main question. The stronger `g(n) ≤ 2n` would be `∀ n, GLe n (2 * n)`.

Sanity check of this reading (by computer, not part of the file): for
`A = {23*29, 23*31, 29*31}` and `I = [20228, 21127)`, no `B` with `|B| ≤ 3` works, matching
`g(3) = 4` of Erdős and Surányi.
-/

namespace OMA.S_erdos_708

open Filter

/-- `GLe n x` means `g(n) ≤ x`: for every `A ⊆ [2, ∞) ∩ ℕ` with `|A| = n` and every run
`I = [m, m + max A)` of `max A` consecutive integers, some `B ⊆ I` with `|B| ≤ x` satisfies
`∏_{a ∈ A} a ∣ ∏_{b ∈ B} b`. (For nonempty `A`, `A.sup id = max A`.) -/
def GLe (n : ℕ) (x : ℝ) : Prop :=
  ∀ A : Finset ℕ, (∀ a ∈ A, 2 ≤ a) → A.card = n →
    ∀ m : ℤ, ∃ B : Finset ℤ, B ⊆ Finset.Ico m (m + ((A.sup id : ℕ) : ℤ)) ∧
      (B.card : ℝ) ≤ x ∧ (∏ a ∈ A, (a : ℤ)) ∣ ∏ b ∈ B, b

/-- Erdős Problem 708: `g(n) ≤ (2 + o(1)) n`. -/
theorem main : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, GLe n ((2 + ε) * n) := by
  sorry

end OMA.S_erdos_708
