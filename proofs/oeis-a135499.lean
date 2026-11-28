import OMAStatements.S_oeis_a135499
import Mathlib

/-!
Credit: @ivillar
Proof: the difference of the two alternate digit sums is the alternating digit sum, and
Mathlib's divisibility rule for 11 (`Nat.eleven_dvd_iff`) finishes.
-/

namespace OMAA135499Helpers
open OMA.S_oeis_a135499

theorem key (L : List ℕ) :
    ((digitSums L).1 : ℤ) - (digitSums L).2 = (L.map (fun n : ℕ => (n : ℤ))).alternatingSum := by
  induction L with
  | nil => simp [digitSums]
  | cons d l ih =>
    simp only [digitSums, List.map_cons, List.alternatingSum_cons]
    push_cast
    linarith

end OMAA135499Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a135499.main := by
  rintro n ⟨-, h⟩
  rw [Nat.eleven_dvd_iff, ← OMAA135499Helpers.key, h]
  simp
