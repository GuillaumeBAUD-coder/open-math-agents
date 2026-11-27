import Mathlib

/-!
# Are the nim-sequences of all finite octal games eventually periodic?

Source: https://en.wikipedia.org/wiki/octal_game
Credit: @caa1982

An octal game is a heap game with octal code $d_0 . d_1 d_2 d_3 \ldots$. For $n \ge 1$ the octal digit
$d_n$ is the sum of
* 1 if, after removing $n$ tokens, leaving zero heaps is permitted (a heap of exactly $n$ tokens may
  be removed entirely),
* 2 if leaving one heap is permitted (removing $n$ tokens from a heap of more than $n$),
* 4 if leaving two heaps is permitted (removing $n$ tokens from a heap of at least $n + 2$ and
  splitting the remainder into two nonempty heaps).
The digit $d_0$ to the left of the point may be 4, allowing a heap to be split into two nonempty
heaps without removing tokens; it is 0 otherwise. A finite octal game has only finitely many nonzero
digits.

By the Sprague–Grundy theorem a heap of size $n$ is equivalent to a nim heap of size $G(n)$, and the
nim-sequence of the game is $G(0), G(1), G(2), \ldots$: $G(n)$ is the least natural number that is not
the nim-value of an option of a heap of size $n$, where the option with no heap left has value 0, a
single heap of size $m$ has value $G(m)$, and two heaps of sizes $a, b$ have value $G(a) \oplus G(b)$
(bitwise xor). All finite octal games analysed so far have ultimately periodic nim-sequences; whether
all finite octal games do is an open question (Guy).

Below, `IsNimSequence d G` is the defining recursion of the nim-sequence. Every option of a heap
of size `h` only involves heaps of size `< h`, so exactly one `G` satisfies it (strong induction on
`h`); the conjecture is stated for that `G`.
-/

namespace OMA.S_wp_are_the_nim_sequences_of_all_finite_octal_games_eventually_periodic

/-- An octal code `d` (digit `d k` for removing `k` tokens) of a finite octal game: every digit is an
octal digit, `d 0` is 0 or 4, and only finitely many digits are nonzero. -/
def IsFiniteOctalCode (d : ℕ → ℕ) : Prop :=
  (∀ k, d k < 8) ∧ (d 0 = 0 ∨ d 0 = 4) ∧ {k : ℕ | d k ≠ 0}.Finite

/-- The nim-values of the options of a heap of size `h`, given the values `G` of smaller heaps:
removing a whole heap of `k ≥ 1` tokens (bit 1 of `d k`), leaving one heap of size `h - k` after
removing `1 ≤ k < h` tokens (bit 2), or removing `k` tokens and leaving two nonempty heaps of sizes
`a` and `b` with `a + b + k = h` (bit 4). -/
def optionValues (d G : ℕ → ℕ) (h : ℕ) : Set ℕ :=
  {g | ∃ k, 1 ≤ k ∧ k = h ∧ (d k).testBit 0 ∧ g = 0} ∪
  {g | ∃ k, 1 ≤ k ∧ k < h ∧ (d k).testBit 1 ∧ g = G (h - k)} ∪
  {g | ∃ k a b, 1 ≤ a ∧ 1 ≤ b ∧ a + b + k = h ∧ (d k).testBit 2 ∧ g = G a ^^^ G b}

/-- `G` is the nim-sequence of the octal game with code `d`: each value is the minimal excluded
value (mex) of the nim-values of the options. -/
def IsNimSequence (d G : ℕ → ℕ) : Prop :=
  ∀ h, G h = sInf (optionValues d G h)ᶜ

/-- Conjecture (Guy): the nim-sequence of every finite octal game is ultimately periodic. -/
theorem main : ∀ d : ℕ → ℕ, IsFiniteOctalCode d → ∀ G : ℕ → ℕ, IsNimSequence d G →
    ∃ p N : ℕ, 0 < p ∧ ∀ n ≥ N, G (n + p) = G n := by
  sorry

end OMA.S_wp_are_the_nim_sequences_of_all_finite_octal_games_eventually_periodic
