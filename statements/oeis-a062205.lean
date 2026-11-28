import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.Powerset

/-!
# Bala's conjectures for the number of alignments of n strings of length four

Source: https://oeis.org/A062205 (Peter Bala, December 19, 2019).
Credit: @NOELOO6

For j ordered alignment columns a row chooses exactly four positions, which
receive its letters in order. All j columns must contain a letter. Since there
are 4n letters, an alignment has at most 4n columns.
-/

namespace OMA.S_oeis_a062205
open Finset

abbrev Row (j : ℕ) := {s : Finset (Fin j) // s.card = 4}

noncomputable def widths (n j : ℕ) : Finset (Fin n → Row j) :=
  univ.filter fun rows => ∀ p : Fin j, ∃ i : Fin n, p ∈ (rows i).val

noncomputable def a (n : ℕ) : ℕ := ∑ j ∈ range (4*n+1), (widths n j).card

theorem main : (∀ n : ℕ, a n ≡ 1 [MOD 80]) ∧
    ∀ k : ℕ, 0<k → ∃ N P : ℕ, 0<P ∧ ∀ n≥N, a (n+P) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a062205
