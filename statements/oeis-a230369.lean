import Mathlib

/-!
# A230369: a strong divisibility sequence associated with the algebraic integer 2 + i

Source: https://oeis.org/A230369
Credit: @LordMike

Let alpha be an algebraic integer and define a sequence of integers a(n) by the condition
a(n) = max {integer d : alpha^n == 1 (mod d)}. For the present sequence we take alpha = 2 + i.
Formula: As n -> inf, lim sup log(a(n))/n = 0.

Reading used here: congruence is in the Gaussian integers `ℤ[i]`, d ranges over natural numbers,
a(n) = sSup of those d (bounded and nonempty for n ≥ 1, offset 1). The limsup is taken in `EReal`
to avoid the real-valued junk value for unbounded sequences.
-/

namespace OMA.S_oeis_a230369

/-- `a n` is the largest natural `d` with `(2 + i)^n ≡ 1 (mod d)` in `ℤ[i]`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {d : ℕ | (d : GaussianInt) ∣ (⟨2, 1⟩ : GaussianInt) ^ n - 1}

theorem main : Filter.limsup (fun n : ℕ => ((Real.log (a n) / n : ℝ) : EReal)) Filter.atTop = 0 := by
  sorry

end OMA.S_oeis_a230369
