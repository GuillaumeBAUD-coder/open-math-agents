import Mathlib

/-!
# Counting strings obtained by tandem duplication

Source: https://oeis.org/A137741, M. F. Hasler, February 10, 2008.
The duplication convention and generating procedure are also described at
https://oeis.org/A137743. Source text: OEIS Foundation, CC BY-SA 4.0.
Credit: @unknownuser17769 for this formal statement.

Start with n distinct symbols in their original order. A move copies a
nonempty contiguous block immediately next to itself. Count distinct final
strings of length n + 4, regardless of how many duplication histories yield
the same string. The alphabet Fin n relabels the n distinct source symbols;
it does not interpret their labels as decimal digits.

The theorem states the entry's closed-form conjecture for every n >= 1,
including the separate cases n = 1 and n = 2. Rational arithmetic preserves
the subtraction and division in the proposed formula without truncation.
-/

namespace OMA.S_oeis_a137741

/-- One tandem duplication of a nonempty contiguous substring. -/
def Duplicates {n : ℕ} (before after : List (Fin n)) : Prop :=
  ∃ left block right : List (Fin n),
    block ≠ [] ∧
    before = left ++ block ++ right ∧
    after = left ++ block ++ block ++ right

/-- The starting word contains each of the n symbols once, in order. -/
def initialWord (n : ℕ) : List (Fin n) :=
  List.ofFn (fun i : Fin n => i)

/-- A137741(n): count final words, represented uniquely by their symbol functions.
Reachability permits any finite number of tandem duplications. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin (n + 4) → Fin n)).filter
    fun word => Relation.ReflTransGen Duplicates (initialWord n) (List.ofFn word)).card

/-- The closed-form conjecture in OEIS A137741, with offset 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) =
      if n ≤ 2 then (n : ℚ) ^ 4
      else ((n : ℚ) + 3) * ((n : ℚ) ^ 3 + 15 * (n : ℚ) ^ 2 + 50 * (n : ℚ) - 96) / 24 := by
  sorry

end OMA.S_oeis_a137741
