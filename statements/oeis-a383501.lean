import Mathlib

/-!
# A383501: Nonnegative integers without the digit 9 such that every odd digit except the leftmost is immediately preceded by a larger digit

Source: https://oeis.org/A383501 and https://oeis.org/A382935
Credit: @xor2k

Formalizes the OEIS A383501 conjecture: these are the terms of A382935, sorted.

The statement adapts the accepted statement of the sibling entry A383246 (same pipeline,
round 4) to the rule of A382935.

A382935 is the lexicographically earliest sequence of distinct nonnegative integers such that
if a digit d in the digit stream (ignoring commas) is odd, the previous digit is > d. Its first
term is 0, the least nonnegative integer (its digit 0 is even, so it is unconstrained). The
digit 9 can never occur in the stream: it would need a larger previous digit, and the stream
starts with the digit 0. So a candidate term is possible exactly when it is `admissible` below
and obeys the rule across the boundary with the previous term (`follows`). Such a choice never
leads to a dead end: a fresh repdigit 88...8 may follow every term (its first digit is even),
and every admissible number may follow it (8 is larger than every odd digit other than 9).
Hence the lexicographically earliest sequence is the greedy sequence `a` below, which picks
the least unused possible value at each step.

Conventions: `a` is indexed from zero, with `a 0 = 0` representing the source's first term
a(1) = 0. Digits are `Nat.digits 10` read from most to least significant (the reversed list);
the number 0 has the empty digit list, its first and last digits are taken to be 0, and it is
admissible. The conjecture says that the range of `a` is precisely the defining set of
A383501; injectivity records that the terms of A382935 are distinct, so that sorting them
gives exactly that set.
-/

namespace OMA.S_oeis_a383501

/-- The digit rule: if the digit `e` is odd, the previous digit `d` is larger than `e`. -/
def digitStep (d e : ℕ) : Prop := e % 2 = 1 → e < d

/-- The defining property of A383501: no digit 9, and every odd digit except the leftmost is
immediately preceded by a larger digit. -/
def admissible (n : ℕ) : Prop :=
  9 ∉ Nat.digits 10 n ∧ ((Nat.digits 10 n).reverse).IsChain digitStep

/-- The leading decimal digit (0 for the number 0). -/
def firstDigit (n : ℕ) : ℕ := (Nat.digits 10 n).reverse.headD 0

/-- The last decimal digit (0 for the number 0). -/
def lastDigit (n : ℕ) : ℕ := (Nat.digits 10 n).headD 0

/-- The digit rule across the boundary between the term `n` and the next term `m`. -/
def follows (n m : ℕ) : Prop := digitStep (lastDigit n) (firstDigit m)

/-- The least unused admissible value that may follow `previous`. -/
noncomputable def next (used : Finset ℕ) (previous : ℕ) : ℕ :=
  sInf {m : ℕ | admissible m ∧ m ∉ used ∧ follows previous m}

/-- The set of used terms and the latest term after `n + 1` terms. -/
noncomputable def state : ℕ → Finset ℕ × ℕ
  | 0 => ({0}, 0)
  | n + 1 =>
    let m := next (state n).1 (state n).2
    (insert m (state n).1, m)

/-- A382935, indexed from zero: `a 0 = 0` and each later term is the greedy choice. -/
noncomputable def a (n : ℕ) : ℕ := (state n).2

/-- The terms of A382935 are distinct and, as a set, are exactly the terms of A383501. -/
theorem main : Function.Injective a ∧
    ∀ m : ℕ, (∃ n : ℕ, a n = m) ↔ admissible m := by
  sorry

end OMA.S_oeis_a383501
