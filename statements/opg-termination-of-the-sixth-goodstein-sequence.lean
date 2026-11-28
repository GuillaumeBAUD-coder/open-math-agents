import Mathlib

/-!
# SixthGoodstein

Open Problem Garden asks for the first zero of the sixth hereditary Goodstein sequence.
The initial six is term one. The claimed term index is fastGrow 6 6 - 2,
equivalently fastGrow 6 6 - 3 base-change transitions.

Source: https://www.openproblemgarden.org/op/termination_of_the_sixth_goodstein_sequence
-/

namespace OMA.S_opg_termination_of_the_sixth_goodstein_sequence

/-- Replace the base b by b + 1 in the hereditary base-b notation.
The recursive calls change the exponents of the ordinary base-b digits. -/
def hereditaryBump (b n : ℕ) : ℕ :=
  if hb : 1 < b then
    ∑ i : Fin (Nat.digits b n).length,
      (Nat.digits b n)[i.val] * (b + 1) ^ hereditaryBump b i.val
  else n
termination_by n
decreasing_by
  have hpow : n < b ^ n := (Nat.lt_two_pow_self (n := n)).trans_le
    (Nat.pow_le_pow_left (Nat.succ_le_of_lt hb) n)
  exact i.isLt.trans_le ((Nat.digits_length_le_iff hb n).mpr hpow)

/-- The index is the number of transitions, starting in base two. -/
def goodstein (initial : ℕ) : ℕ → ℕ
  | 0 => initial
  | k + 1 => hereditaryBump (k + 2) (goodstein initial k) - 1

def FirstZeroAt (initial transitions : ℕ) : Prop :=
  goodstein initial transitions = 0 ∧ ∀ j < transitions, goodstein initial j ≠ 0

/-- The finite levels of the fast-growing hierarchy. -/
def fastGrow : ℕ → ℕ → ℕ
  | 0, b => b + 1
  | k + 1, b => (fastGrow k)^[b] b

/-- The first zero is term fastGrow 6 6 - 2, counting the initial six as term one. -/
def ClaimedOutcome : Prop := FirstZeroAt 6 (fastGrow 6 6 - 3)

theorem main : ClaimedOutcome := by
  sorry

end OMA.S_opg_termination_of_the_sixth_goodstein_sequence
