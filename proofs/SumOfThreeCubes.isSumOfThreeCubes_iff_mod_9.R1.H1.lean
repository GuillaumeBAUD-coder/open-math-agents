import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1
import Mathlib

-- Step SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1.H1: hypothesis H1 of reduction SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1
-- Credit: @ivillar
-- H1 := a sum of three integer cubes is never 4 or 5 mod 9.
-- Proof: reduce mod 9. Every cube is 0, 1 or 8 in ZMod 9, and a finite check (decide over
-- ZMod 9 ^ 3) shows no sum of three of them is 4 or 5.

lemma OMA.SumThreeCubes.cast_eq (x y z m : ℤ) (h : x ^ 3 + y ^ 3 + z ^ 3 ≡ m [ZMOD 9]) :
    (x : ZMod 9) ^ 3 + (y : ZMod 9) ^ 3 + (z : ZMod 9) ^ 3 = (m : ZMod 9) := by
  have h' := (ZMod.intCast_eq_intCast_iff (x ^ 3 + y ^ 3 + z ^ 3) m 9).mpr (by exact_mod_cast h)
  push_cast at h'
  exact h'

lemma OMA.SumThreeCubes.key : ∀ a b c : ZMod 9, a ^ 3 + b ^ 3 + c ^ 3 ≠ 4 ∧ a ^ 3 + b ^ 3 + c ^ 3 ≠ 5 := by
  decide

theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1.H1 := by
  unfold OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1.H1
  rintro n ⟨x, y, z, rfl⟩ h
  rcases h with h | h
  · have e := OMA.SumThreeCubes.cast_eq x y z 4 h
    push_cast at e
    exact (OMA.SumThreeCubes.key x y z).1 e
  · have e := OMA.SumThreeCubes.cast_eq x y z 5 h
    push_cast at e
    exact (OMA.SumThreeCubes.key x y z).2 e
