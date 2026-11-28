import Mathlib

/-!
# A309200: Greedily choosing unused divisors of the Catalan numbers

Source: https://oeis.org/A309200

The sequence starts with the first positive Catalan index. The variable n in
candidates is one less than the index in the OEIS sequence.
-/

namespace OMA.S_oeis_a309200

/-- The positive divisors eligible for the next term. -/
def candidates (n : ℕ) (used : Set ℕ) : Set ℕ :=
  {m | 0 < m ∧ m ∣ catalan (n + 1) ∧ m ∉ used}

/-- The earlier choices, at the time of processing Catalan number n + 1. -/
noncomputable def used : ℕ → Set ℕ
  | 0 => ∅
  | n + 1 => insert (sInf (candidates n (used n))) (used n)

/-- The least positive divisor that has not appeared. -/
noncomputable def a (n : ℕ) : ℕ := sInf (candidates n (used n))

theorem main : Function.Injective a ∧ Set.range a = {m | 0 < m} := by
  sorry

end OMA.S_oeis_a309200
