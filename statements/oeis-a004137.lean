import Mathlib

/-!
# A004137: Maximal number of edges in a graceful graph on n nodes.

Source: https://oeis.org/A004137
Credit: @azmiozgen

Conjecture (Peter Luschny, Oct 09 2011, updated Oct 01 2015): an optimal ruler with more than
12 segments is a Wichmann ruler, so that the sequence continues 232, 251, 270, 289, 308, 327, ...
The entry's example states it for rulers: a(21) = 153 is the greatest length of a complete ruler
with 21 marks.

Formalization notes:
* a(n), offset 1, is stated through rulers, as in the entry's example: the greatest L such that
  some set of n marks in {0, ..., L} measures every distance 1, ..., L (a complete, or sparse,
  ruler). This equals the maximal number of edges of a graceful graph on n nodes (the marks are
  the vertex labels; one edge per measured distance).
* A Wichmann ruler with parameters r, s ≥ 0 has segment lengths 1^r, r+1, (2r+1)^r, (4r+3)^s,
  (2r+2)^(r+1), 1^r: that is 4r+s+2 segments (4r+s+3 marks) and length 4r(r+s+2) + 3(s+1).
* The statement is the consequence for the sequence that the comment draws: for n ≥ 14 marks
  (more than 12 segments), a(n) is the greatest length of a Wichmann ruler with n marks.
* Controls: the Wichmann lengths for n = 14..27 are 68, 79, 90, 101, 112, 123, 138, 153, 168,
  183, 198, 213, 232, 251, matching the entry's terms a(14..26) and the predicted a(27) = 251;
  the ruler definition gives a(1..6) = 0, 1, 3, 6, 9, 13.
-/

namespace OMA.S_oeis_a004137

/-- `M` is a complete ruler of length `L`: marks in `{0, ..., L}` measuring every distance
`1, ..., L`. -/
def IsCompleteRuler (L : ℕ) (M : Finset ℕ) : Prop :=
  M ⊆ Finset.range (L + 1) ∧ ∀ d ∈ Finset.Icc 1 L, ∃ x ∈ M, x + d ∈ M

/-- A004137(n): the greatest length of a complete ruler with `n` marks. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {L : ℕ | ∃ M : Finset ℕ, M.card = n ∧ IsCompleteRuler L M}

/-- The length of the Wichmann ruler with parameters `r` and `s` (it has `4r+s+3` marks). -/
def wichmannLength (r s : ℕ) : ℕ := 4 * r * (r + s + 2) + 3 * (s + 1)

/-- Luschny's conjecture, length form: from 14 marks on, Wichmann rulers are optimal. -/
theorem main :
    ∀ n : ℕ, 14 ≤ n →
      a n = sSup {L : ℕ | ∃ r s : ℕ, 4 * r + s + 3 = n ∧ L = wichmannLength r s} := by
  sorry

end OMA.S_oeis_a004137
