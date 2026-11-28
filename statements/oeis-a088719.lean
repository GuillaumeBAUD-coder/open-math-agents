import Mathlib

/-!
# A088719: sums of two seventh powers are unique

Source: https://oeis.org/A088719 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A088719 (offset 1): numbers that can be represented as a^7 + b^7, with 0 < a < b, in exactly one
way; data 129, 2188, 2315, 16385, ... (129 = 1^7 + 2^7).

The entry records:

  Conjecture: no number can be expressed as such a sum in more than one way.

(It adds that no solution of A^7 + B^7 = C^7 + D^7 is known.)

Reading of the source:
* "such a sum" is a^7 + b^7 with integers 0 < a < b, as in the name.
* "no number can be expressed ... in more than one way": two such representations of the same
  number are the same pair, i.e. a^7 + b^7 = c^7 + d^7 with 0 < a < b and 0 < c < d forces
  a = c and b = d.
-/

namespace OMA.S_oeis_a088719

/-- If `a^7 + b^7 = c^7 + d^7` with `0 < a < b` and `0 < c < d`, then `a = c` and `b = d`. -/
theorem main : ∀ a b c d : ℕ, 0 < a → a < b → 0 < c → c < d →
    a ^ 7 + b ^ 7 = c ^ 7 + d ^ 7 → a = c ∧ b = d := by
  sorry

end OMA.S_oeis_a088719
