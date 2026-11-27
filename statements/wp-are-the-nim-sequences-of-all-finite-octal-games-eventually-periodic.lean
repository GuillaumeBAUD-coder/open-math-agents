import Mathlib

-- Are the nim-sequences of all finite octal games eventually periodic?
-- Source: https://en.wikipedia.org/wiki/Octal_game
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source: an octal game has code `0.d₁d₂d₃...`, where the octal digit `dⱼ` is the sum of
1 if removing `j` tokens may leave zero heaps (a heap of exactly `j` is removed entirely),
2 if it may leave one heap (from a heap of more than `j`), and
4 if it may leave two nonempty heaps (from a heap of at least `j + 2`).
Finite octal games are those with finitely many nonzero digits. The nim-sequence is
`G(0), G(1), G(2), ...`, the Sprague–Grundy values of single heaps. Whether all finite octal games
have ultimately periodic nim-sequences is open (listed by Guy); stated here in the affirmative.

Conventions:
* A code is `d : ℕ → ℕ` with every digit `d j < 8` and `d j = 0` for all large `j`; `d 0` is
  never used (the code is `0.d₁d₂...`; the nonstandard digit left of the point, which the source
  mentions as an extension, is not part of the standard notation and is not included).
* Bit `b` of a digit is `Nat.testBit (d j) b` (bit 0 ↔ 1, bit 1 ↔ 2, bit 2 ↔ 4).
* `G(n)` is the minimal excludant (via `sInf` of the cofinite set of values not attained) of the
  values of the positions reachable in one move: `0` (heap removed), `G(n - j)` (one heap left),
  `G(a) xor G(n - j - a)` with `a ≥ 1`, `n - j - a ≥ 1` (two heaps left). Nim-sum is `^^^`.
* Ultimately periodic: there are `N` and `p > 0` with `G(n + p) = G(n)` for all `n ≥ N`.
-/

namespace OMA.S_wp_are_the_nim_sequences_of_all_finite_octal_games_eventually_periodic

/-- The nim-value of a heap of size `n` in the octal game with code `0.d₁d₂...`. -/
noncomputable def octalGrundy (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  sInf {m : ℕ |
    (∀ j : ℕ, 1 ≤ j → j = n → (d j).testBit 0 = true → m ≠ 0) ∧
    (∀ j : ℕ, (h : 1 ≤ j ∧ j < n) → (d j).testBit 1 = true → m ≠ octalGrundy d (n - j)) ∧
    (∀ j a : ℕ, (h : 1 ≤ j ∧ 1 ≤ a ∧ j + a < n) → (d j).testBit 2 = true →
      m ≠ octalGrundy d a ^^^ octalGrundy d (n - j - a))}
decreasing_by all_goals omega

/-- Every finite octal game has an ultimately periodic nim-sequence. -/
theorem main : ∀ d : ℕ → ℕ, (∀ j, d j < 8) → (∃ k, ∀ j, k < j → d j = 0) →
    ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → octalGrundy d (n + p) = octalGrundy d n := by
  sorry

end OMA.S_wp_are_the_nim_sequences_of_all_finite_octal_games_eventually_periodic
