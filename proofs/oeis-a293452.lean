import OMAStatements.S_oeis_a293452

open OMA.S_oeis_a293452

/-- At width two the only nonsink fires once, sending both horizontal grains to the sink. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a293452.main) := by
  intro h
  have hrun : completes (initial 2) [1] := by
    change (1 : Fin 2).val ≠ 0 ∧ 4 ≤ initial 2 1 ∧ ∀ j, topple (initial 2) 1 j < 4
    decide
  have hformula := (h 2 (by decide) 1).mp ⟨[1], hrun, rfl⟩
  exact (by decide : 1 ≠ rectangleSum 2) hformula

open OMA.S_oeis_a293452

namespace Sandpile

private def finalHeight (n i : ℕ) : ℤ := if 2*i = n then 2 else 3

/-- The residual `r i` is the number of firings still owed at site `i`. -/
private structure Balance {n : ℕ} (c : Heights n) (r : ℕ → ℕ) : Prop where
  left : r 0 = 0
  right : r n = 0
  sink : ∀ j : Fin n, j.val = 0 → c j = 0
  interior : ∀ j : Fin n, 0 < j.val → (c j : ℤ) = finalHeight n j.val +
    2 * r j.val - r (j.val - 1) - r (j.val + 1)

end Sandpile

open OMA.S_oeis_a293452
namespace Sandpile

end Sandpile

namespace Sandpile

end Sandpile

namespace Sandpile

end Sandpile

open OMA.S_oeis_a293452

namespace Sandpile

end Sandpile
