import Mathlib

/-!
# Are the nim-sequences of all finite octal games eventually periodic?

Source: https://en.wikipedia.org/wiki/octal_game
Credit: @ishaanzee

An octal game is played with heaps of tokens; a move selects one heap and either removes all
of its tokens, removes some but not all of them (leaving one smaller heap), or removes some of
them and divides the rest into two nonempty heaps. The octal code `d₀ . d₁ d₂ d₃ …` says which
of these are allowed: the digit `dₙ` is the sum of
* `1` if, after removing `n` tokens, leaving zero heaps is permitted (a heap of exactly `n`
  tokens may be removed entirely),
* `2` if leaving one heap is permitted (removing `n` tokens from a heap of more than `n`),
* `4` if leaving two heaps is permitted (removing `n` tokens from a heap of at least `n + 2`
  and separating the remainder into two nonempty heaps).
The digit `d₀` to the left of the point may be `4`, allowing a heap to be split into two
nonempty heaps without removing any tokens; otherwise it is `0`. A finite octal game is one with
only finitely many non-zero digits.

By the Sprague–Grundy theorem a heap of size `n` is equivalent to a nim heap of size `G(n)`,
and `G(0), G(1), G(2), …` is the nim-sequence of the game: `G(n)` is the mex (least natural
number not attained) of the nim-values of the positions reachable from a heap of `n`, where a
position with two heaps `a`, `b` has nim-value `G(a) xor G(b)` and the empty position has
nim-value `0`. Wikipedia: all finite octal games analysed so far have ultimately periodic
nim-sequences, and whether all finite octal games do is an open question (Guy, Unsolved problems
in combinatorial games). We state the affirmative answer.

Formalization: the code is a function `d : ℕ → ℕ` (`d n` is the digit `dₙ`), with every digit
below `8`, `d 0 ∈ {0, 4}`, and `d n = 0` for all large `n`. Bit `0`, `1`, `2` of `dₙ`
(`Nat.testBit`) are the "zero heaps", "one heap" and "two heaps" permissions. For example Kayles
is `0.77` and Dawson's Kayles is `0.07`.
-/

namespace OMA.S_wp_are_the_nim_sequences_of_all_finite_octal_games_eventually_periodic

/-- The minimum excludant of a finite set of natural numbers: the least natural number not
in `s`. -/
def mex (s : Finset ℕ) : ℕ := Nat.find (Infinite.exists_notMem_finset s)

/-- The nim-value `G(h)` of a heap of `h` tokens in the octal game with code `d`. It is the mex
of the nim-values of the options:
* `0` (no heap left), if `0 < h` and the `1`-bit of `d h` is set;
* `G(h - n)` (one heap left), for `0 < n < h` with the `2`-bit of `d n` set;
* `G(a) xor G(h - n - a)` (two nonempty heaps left), for `n < h` and `0 < a < h - n` with the
  `4`-bit of `d n` set. -/
def nimValue (d : ℕ → ℕ) : ℕ → ℕ
  | h =>
    mex ((if 0 < h ∧ (d h).testBit 0 then {0} else ∅) ∪
      ((Finset.Ioo 0 h).attach.filter (fun n => (d n.1).testBit 1)).image
        (fun n => nimValue d (h - n.1)) ∪
      ((Finset.range h ×ˢ Finset.Ioo 0 h).attach.filter
          (fun p => p.1.2 < h - p.1.1 ∧ (d p.1.1).testBit 2)).image
        (fun p => nimValue d p.1.2 ^^^ nimValue d (h - p.1.1 - p.1.2)))
decreasing_by
  · have := Finset.mem_Ioo.mp n.2
    omega
  · have := Finset.mem_product.mp p.2
    have := Finset.mem_Ioo.mp this.2
    omega
  · have := Finset.mem_product.mp p.2
    have := Finset.mem_Ioo.mp this.2
    omega

/-- **Finite octal games** (Guy's question): the nim-sequence of every finite octal game is
ultimately periodic. -/
theorem main : ∀ d : ℕ → ℕ, (∀ n, d n < 8) → (d 0 = 0 ∨ d 0 = 4) → (∃ K, ∀ n ≥ K, d n = 0) →
    ∃ N p : ℕ, 0 < p ∧ ∀ n ≥ N, nimValue d (n + p) = nimValue d n := by
  sorry

end OMA.S_wp_are_the_nim_sequences_of_all_finite_octal_games_eventually_periodic
