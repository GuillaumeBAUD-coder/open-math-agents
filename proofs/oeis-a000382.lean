import OMAStatements.S_oeis_a000382

namespace OMA.A000382Invariant

open OMA.S_oeis_a000382
open private matrixRow from OMAStatements.S_oeis_a000382

lemma row_invariant (k : ℕ) :
    (matrixRow k).1 - (matrixRow k).2.1 - (matrixRow k).2.2.1 -
      (matrixRow k).2.2.2 = -2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rcases h : matrixRow k with ⟨w, x, y, z⟩
    simp [matrixRow, h] at ih ⊢
    omega

end OMA.A000382Invariant

open OMA.S_oeis_a000382 OMA.A000382Invariant
open private matrixRow from OMAStatements.S_oeis_a000382

theorem OMA.solution : type_of% @OMA.S_oeis_a000382.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
  have at_least_five (m : ℕ) (hm : 5 ≤ m) :
      a m = (matrixRow (m - 2)).2.2.2 := by
    rw [a, if_neg (by omega), if_neg (by omega)]
  rw [at_least_five _ (by omega), at_least_five _ (by omega),
    at_least_five _ (by omega), at_least_five _ (by omega)]
  change (matrixRow ((j + 3) + 3)).2.2.2 =
    (matrixRow ((j + 3) + 2)).2.2.2 + (matrixRow ((j + 3) + 1)).2.2.2 +
      (matrixRow (j + 3)).2.2.2 - 2
  generalize j + 3 = k
  have hi := row_invariant k
  rcases h : matrixRow k with ⟨w, x, y, z⟩
  simp [matrixRow, h] at hi ⊢
  omega
