import Mathlib

/-!
# Are the nim-sequences of all finite octal games eventually periodic?

Source: https://en.wikipedia.org/wiki/octal_game
Credit: @cosmaticdev

Wikipedia (Octal game): octal games are played with heaps of tokens; a move selects one heap
and either removes all of its tokens, removes some but not all leaving one smaller heap, or
removes some and divides the remainder into two nonempty heaps. The octal code `c.d1 d2 d3 …`
specifies, for each `n`, whether the player may leave zero, one, or two heaps after removing
`n` tokens from a heap: the digit `dn` is the sum of 1 (leaving zero heaps), 2 (one heap) and
4 (two heaps). The digit left of the decimal point may be 4, allowing a heap to be split into
two without removing any tokens. Octal games with only a finite number of non-zero digits are
called finite octal games. The nim-sequence `G(0), G(1), G(2), …` of a game records the
Sprague-Grundy value `G(n)` of a single heap of `n` tokens. All finite octal games analyzed so
far have an ultimately periodic nim-sequence, and whether all finite octal games are ultimately
periodic is an open question (listed by Richard Guy).

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_are_the_nim_sequences_of_all_finite_octal_games_eventually_periodic

/-- Minimum excluded value of a finite set of naturals: the least `m` with `m ∉ s`. -/
def mex (s : Finset ℕ) : ℕ :=
  Nat.find (p := fun m => m ∉ s)
    ⟨s.sum id + 1, fun h => by
      have hle : id (s.sum id + 1) ≤ Finset.sum s id :=
        Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) h
      simp only [id_eq] at hle
      omega⟩

/-- The nim-values of the positions reachable in one move from a single heap of `m` tokens
in the octal game with code `d`, where `G k hk` is the nim-value of a heap of size `k < m`.
Per the source, a move removes `n'` tokens from the heap and leaves zero, one, or two heaps
according to the bits of the digit `d n'` (zero heaps only when the heap had exactly `n'`
tokens; two heaps only when at least `n' + 2` tokens were present). -/
def options (d : ℕ → ℕ) (m : ℕ) (G : ∀ k, k < m → ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).biUnion fun n' =>
    (if _h : n' = m ∧ 1 ≤ m ∧ d n' % 2 = 1 then {0} else ∅) ∪
    (if h : 1 ≤ n' ∧ n' < m ∧ d n' / 2 % 2 = 1 then
      {G (m - n') (by omega)} else ∅) ∪
    (if h : d n' / 4 % 2 = 1 ∧ n' + 2 ≤ m then
      (Finset.Icc 1 (m - n' - 1)).attach.image fun a =>
        Nat.xor (G a.1 (by have ha := a.2; rw [Finset.mem_Icc] at ha; omega))
                (G (m - n' - a.1) (by have ha := a.2; rw [Finset.mem_Icc] at ha; omega))
      else ∅)

/-- The nim-sequence of the octal game with code `d`: `grundy d n` is the Sprague-Grundy
value `G(n)` of a single heap of `n` tokens, the mex of the nim-values of its options (a move
leaving two heaps `a` and `b` has nim-value `G a` xor `G b`). -/
def grundy (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  mex (options d n fun k h => grundy d k)
termination_by n
decreasing_by exact h

/-- A sequence `a : ℕ → ℕ` is eventually (ultimately) periodic if for some preperiod `N` and
some period `p > 0`, `a (n + p) = a n` for all `n ≥ N`. -/
def EventuallyPeriodic (a : ℕ → ℕ) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + p) = a n

/-- A code for an octal game: `d 0` is the digit left of the decimal point (0, or 4 to allow
splitting a heap into two heaps without removing tokens) and `d n` for `n ≥ 1` is the octal
digit `dn`; every digit is at most 7. -/
def IsOctalCode (d : ℕ → ℕ) : Prop :=
  (∀ n, d n ≤ 7) ∧ (d 0 = 0 ∨ d 0 = 4)

/-- A finite octal game: an octal code with only a finite number of non-zero digits. -/
def IsFiniteOctalGame (d : ℕ → ℕ) : Prop :=
  IsOctalCode d ∧ {n : ℕ | d n ≠ 0}.Finite

/-- Are the nim-sequences of all finite octal games eventually periodic? -/
theorem main : ∀ d : ℕ → ℕ, IsFiniteOctalGame d → EventuallyPeriodic (grundy d) := by
  sorry

end OMA.S_wp_are_the_nim_sequences_of_all_finite_octal_games_eventually_periodic
