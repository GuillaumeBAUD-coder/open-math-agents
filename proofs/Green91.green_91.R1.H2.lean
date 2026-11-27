import OMAReductions.R_Green91_green_91_R1
import Mathlib

-- Step Green91.green_91.R1.H2: hypothesis H2 of reduction Green91.green_91.R1
-- Credit: @ivillar

/-!
# A sublinear error is eventually at most one percent

If `f = o(n)` then `|f n| ≤ n / 100` for large `n`.
-/

namespace Green91SublinearStep

open Filter Asymptotics Topology

theorem sublinear : ∀ f : ℕ → ℝ, f =o[atTop] (fun n : ℕ ↦ (n : ℝ)) →
  ∀ᶠ n : ℕ in atTop, (99 / 100 : ℝ) * n ≤ (n : ℝ) - f n := by
  intro f hf
  filter_upwards [hf.bound (show (0 : ℝ) < 1 / 100 by norm_num)] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg n), Real.norm_eq_abs] at hn
  have h := le_abs_self (f n)
  linarith

end Green91SublinearStep

theorem OMA.solution : OMA.R_Green91_green_91_R1.H2 :=
  Green91SublinearStep.sublinear
