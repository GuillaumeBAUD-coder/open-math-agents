import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1
import Mathlib.Tactic

/-!
# Elementary direction of the mod 9 criterion for sums of three cubes
-/

private lemma cube_zmod9 : ∀ u : ZMod 9, u ^ 3 = 0 ∨ u ^ 3 = 1 ∨ u ^ 3 = 8 := by
  decide

private theorem prove_SumOfThreeCubes_H1 :
    ∀ n : ℤ, SumOfThreeCubes.IsSumOfThreeCubes n →
      ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9]) := by
  intro n ⟨x, y, z, hn⟩
  rw [show (9 : ℤ) = (9 : ℕ) from rfl, ← ZMod.intCast_eq_intCast_iff _ _ 9,
    ← ZMod.intCast_eq_intCast_iff _ _ 9]
  have hcast := congrArg (fun t : ℤ => (t : ZMod 9)) hn
  simp only [Int.cast_add, Int.cast_pow] at hcast
  generalize (n : ZMod 9) = a at *
  generalize (x : ZMod 9) = u at *
  generalize (y : ZMod 9) = v at *
  generalize (z : ZMod 9) = w at *
  rcases cube_zmod9 u with hu | hu | hu <;>
    rcases cube_zmod9 v with hv | hv | hv <;>
    rcases cube_zmod9 w with hw | hw | hw <;>
    rw [hu, hv, hw] at hcast <;>
    subst hcast <;>
    decide

theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1.H1 :=
  prove_SumOfThreeCubes_H1
