import OMAStatements.S_oeis_a136746

-- Credit: @LordMike. Shortened from the proof by @agchua.
namespace R
open OMA.S_oeis_a136746
def T : Finset ℕ := {1, 2, 3, 5, 6, 8, 12, 13, 14, 16, 17, 19, 23, 24, 25, 27, 28}

theorem low : 17 ≤ A003003 28 := by
  have : ∀ a ∈ T, ∀ d ∈ Finset.range 10, 0 < d → a + d ∈ T → a + 2 * d ∈ T → a + 3 * d ∉ T := by
    decide
  have b : ∀ x ∈ T, x ≤ 28 := by decide
  unfold A003003
  classical
  exact (show T.card = 17 by decide) ▸ Finset.le_sup (f := Finset.card) (Finset.mem_filter.2
    ⟨Finset.mem_powerset.2 fun x h ↦ Finset.mem_Icc.2 ⟨by revert x; decide, b x h⟩,
      fun ⟨a, d, hd, h0, h1, h2, h3⟩ ↦ this a h0 d (Finset.mem_range.2 (by linarith [b _ h3])) hd h1 h2 h3⟩)
end R


open OMA.S_oeis_a136746 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a136746.main := by
  intro H
  have e : (X + 1) * (X - 1) ^ 2 = (X ^ 3 - X ^ 2 - X ^ 1 + 1 : PowerSeries ℚ) := by ring
  rw [e] at H
  have E := fun n => congrArg (coeff n) H
  have := E 0; have := E 1; have := E 2; have := E 3; have := E 4; have := E 5; have := E 6
  have := E 7; have := E 8; have := E 9; have := E 10; have := E 11; have := E 12; have := E 13
  have := E 14; have := E 15; have := E 16; have := E 17; have := E 18; have := E 19; have := E 20
  have := E 21; have := E 22; have := E 23; have := E 24; have := E 25; have := E 26; have := E 27
  simp [mul_sub, mul_add, coeff_mul_X_pow', coeff_X_pow, coeff_X] at *

  have l : (17 : ℚ) ≤ A003003 28 := mod_cast R.low
  linarith [(by exact_mod_cast ‹A003003 1 = 1› : (A003003 1 : ℚ) = 1)]
