import Mathlib

/-!
# A000051: a(n) = 2^n + 1.

Source: https://oeis.org/A000051
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000051

def luschnyMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun j k =>
    -⌊((j.val : ℚ) - (k.val : ℚ) - 2) / (n + 1 : ℚ)⌋

theorem main : ∀ n : ℕ, (2 ^ n + 1 : ℤ) = Matrix.permanent (luschnyMatrix n) := by
  sorry

end OMA.S_oeis_a000051

