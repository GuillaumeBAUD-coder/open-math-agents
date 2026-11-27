import Mathlib

/-!
# Erdős Problem 708

Source: https://www.erdosproblems.com/708
Credit: @JamesSlash

The source states (a problem of Erdős and Surányi, 1959): let `g(n)` be minimal such that for any
`A ⊆ [2, ∞) ∩ ℕ` with `|A| = n` and any set `I` of `max(A)` consecutive integers there exists some
`B ⊆ I` with `|B| = g(n)` such that `∏_{a ∈ A} a ∣ ∏_{b ∈ B} b`. Is it true that
`g(n) ≤ (2 + o(1)) n`? (Or perhaps even `g(n) ≤ 2n`?)

Reading used here.
* `|B| = g(n)` is read as `|B| ≤ g(n)`, i.e. `g(n)` is the worst case, over `A` and `I`, of the least
  size of a suitable `B`. Read literally, `|B| = g(n)` cannot hold when `|I| = max(A) < g(n)`
  (e.g. `A = {2, …, n + 1}`), which would contradict the lower bound `g(n) ≥ (2 - o(1)) n` of
  Erdős and Surányi recorded on the source page; the single comment on the source page makes the
  same point.
* `I` is a block `{x + 1, …, x + max(A)}` of consecutive integers with `x ∈ ℤ`, as in the source
  (consecutive integers). Blocks containing `0` are trivially covered by `B = {0}`, and negative
  blocks reflect to positive ones under `b ↦ -b`, so this agrees with the reading in positive
  integers.
* `max(A)` is `A.sup id`; for `n ≥ 1` this is the largest element of `A`.
* Since `g(n)` is the least admissible size, `g(n) ≤ c` holds exactly when every admissible pair
  `(A, I)` has a suitable `B` with `|B| ≤ c`. The statement `g(n) ≤ (2 + o(1)) n` is written in the
  standard form: for every `ε > 0`, for all sufficiently large `n`, `g(n) ≤ (2 + ε) n`. This avoids
  defining `g` through `sInf` (whose value would silently be `0` if no admissible size existed).
* The question is stated in its affirmative form, so a disproof settles it negatively. The
  stronger variant `g(n) ≤ 2n` is not part of this statement.
-/

namespace OMA.S_erdos_708

/-- The block `{x + 1, …, x + M}` of `M` consecutive integers. -/
noncomputable def block (x : ℤ) (M : ℕ) : Finset ℤ := Finset.Ioc x (x + M)

/-- Some `B` inside the block of `max(A)` consecutive integers after `x` has at most `k` elements
and a product divisible by `∏_{a ∈ A} a`. -/
def HasCover (A : Finset ℕ) (x : ℤ) (k : ℝ) : Prop :=
  ∃ B : Finset ℤ, B ⊆ block x (A.sup id) ∧ (B.card : ℝ) ≤ k ∧
    (∏ a ∈ A, (a : ℤ)) ∣ ∏ b ∈ B, b

theorem main :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ A : Finset ℕ, A.card = n → (∀ a ∈ A, 2 ≤ a) →
        ∀ x : ℤ, HasCover A x ((2 + ε) * n) := by
  sorry

end OMA.S_erdos_708
