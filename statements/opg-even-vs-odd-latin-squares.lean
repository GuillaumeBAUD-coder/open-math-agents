import Mathlib

/-!
# Even vs. odd latin squares

Source: https://www.openproblemgarden.org/op/even_vs_odd_latin_squares
Credit: @sun-jiao

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_opg_even_vs_odd_latin_squares

/-- A matrix `M : Matrix (Fin n) (Fin n) (Fin n)` is a latin square of order `n` if every row
and every column is injective (i.e., a permutation of `Fin n`). -/
def IsLatinSquare {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin n)) : Prop :=
  (∀ i, Function.Injective (M i)) ∧ (∀ j, Function.Injective (fun i => M i j))

/-- The row permutation of `M` at row `i`, given a proof `h` that `M` is a latin square. -/
noncomputable def rowPerm {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin n))
    (h : IsLatinSquare M) (i : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (M i) (Finite.injective_iff_bijective.mp (h.1 i))

/-- The column permutation of `M` at column `j`, given a proof `h` that `M` is a latin square. -/
noncomputable def colPerm {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin n))
    (h : IsLatinSquare M) (j : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i => M i j) (Finite.injective_iff_bijective.mp (h.2 j))

/-- A latin square is even if the product of the signs of all of its row and column permutations
equals `1` (and odd otherwise). -/
noncomputable def IsEvenLatinSquare {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin n)) : Prop :=
  ∃ h : IsLatinSquare M,
    (∏ i : Fin n, Equiv.Perm.sign (rowPerm M h i)) *
      (∏ j : Fin n, Equiv.Perm.sign (colPerm M h j)) = 1

/-- The number of even latin squares of order `n`. -/
noncomputable def evenLatinSquareCount (n : ℕ) : ℕ :=
  open Classical in
  (Finset.univ.filter (fun M : Matrix (Fin n) (Fin n) (Fin n) =>
    IsLatinSquare M ∧ IsEvenLatinSquare M)).card

/-- The number of odd latin squares of order `n`. -/
noncomputable def oddLatinSquareCount (n : ℕ) : ℕ :=
  open Classical in
  (Finset.univ.filter (fun M : Matrix (Fin n) (Fin n) (Fin n) =>
    IsLatinSquare M ∧ ¬ IsEvenLatinSquare M)).card

/--
Alon–Tarsi conjecture: for every positive even integer `n`, the number of even latin squares
of order `n` and the number of odd latin squares of order `n` are different.
-/
theorem main :
    ∀ n : ℕ, 0 < n → Even n → evenLatinSquareCount n ≠ oddLatinSquareCount n := by
  sorry

end OMA.S_opg_even_vs_odd_latin_squares
