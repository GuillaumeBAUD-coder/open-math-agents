import Mathlib.Data.Nat.Prime.Defs

/-!
# OEIS A110194: first differences of A110095
Source: https://oeis.org/A110194 and https://oeis.org/A110095
Credit: @LDJAI
The gaps are indexed from 1. Starting at index 5, the question asks
whether the infinite sequence is a concatenation of the blocks
(1,1,4) and (1,1,1,1,4,4).
-/

namespace OMA.S_oeis_a110194

-- Trial division, exactly testing for a proper divisor >= 2.
def primeBool (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun d => decide (d < 2 ∨ n % d ≠ 0))

def valid (x d : Nat) : Bool :=
  decide (0 < d) && !primeBool d && !primeBool (x+d)

-- The greedy minimum is always at most 8: for x = 0 use 1,
-- for x = 1 use 8, for even x >= 2 use 4, and for odd x >= 3 use 1.
-- Each candidate is a positive nonprime with nonprime sum x + d.
def gap (x : Nat) : Nat :=
  ((List.range 9).find? (valid x)).getD 0

def s : Nat → Nat
  | 0 => 0
  | n+1 => s n + gap (s n)

def a (n : Nat) : Nat := gap (s (n-1))

def Block (k l : Nat) : Prop :=
  (l = k+3 ∧ a k = 1 ∧ a (k+1) = 1 ∧ a (k+2) = 4) ∨
  (l = k+6 ∧ a k = 1 ∧ a (k+1) = 1 ∧ a (k+2) = 1 ∧
    a (k+3) = 1 ∧ a (k+4) = 4 ∧ a (k+5) = 4)

def GapLanguage : Prop :=
  ∃ b : Nat → Nat, b 0 = 5 ∧ ∀ n : Nat, Block (b n) (b (n+1))


theorem main : GapLanguage := by
  sorry

end OMA.S_oeis_a110194
