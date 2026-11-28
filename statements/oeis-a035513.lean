import Mathlib

/-!
# Residue pairs in the Wythoff array

Clark Kimberling's June 4, 2025 conjecture in OEIS A035513 concerns columns 1 and 2
of the ordinary Wythoff array. The extended columns numbered -1 and 0 in the entry
are `n-1` and `floor(n * φ)`, where rows start at `n=1`. The next two entries of the
Fibonacci recurrence give the pair below. Source: https://oeis.org/A035513.

Credit: @connoranderson
-/

namespace OMA.S_oeis_a035513

/-- The first two ordinary columns in row `r+1` of the Wythoff array. -/
noncomputable def firstTwo (r : ℕ) : ℕ × ℕ :=
  let f := ⌊((r : ℝ) + 1) * Real.goldenRatio⌋₊
  (r + f, r + 2 * f)

/-- Every pair of residues occurs among the first two entries of a positive row. -/
theorem main : ∀ m : ℕ, 2 ≤ m →
    (Set.range (fun r : ℕ => (((firstTwo r).1 : ZMod m), ((firstTwo r).2 : ZMod m)))).ncard =
      m ^ 2 := by
  sorry

end OMA.S_oeis_a035513
