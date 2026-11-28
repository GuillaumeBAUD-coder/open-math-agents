import OMAStatements.S_oeis_a016744
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Ring

-- Original proof by @Genbox.
theorem OMA.solution : type_of% @OMA.S_oeis_a016744.main := by
  have hs : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 4) (Real.pi ^ 4 / 90) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
  have scale (c : ℝ) :
      HasSum (fun n : ℕ => (1 : ℝ) / (c * ((n : ℝ) + 1)) ^ 4) (Real.pi ^ 4 / (90 * c ^ 4)) := by
    simpa only [mul_pow, div_div, mul_comm] using hs.div_const (c ^ 4)
  let f (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 1)) ^ 4
  let s : ℝ := Real.pi ^ 4 / 1440
  have h : HasSum f s := by
    simpa only [show (90 : ℝ) * 2 ^ 4 = 1440 by norm_num] using scale 2
  refine ⟨h, ?_⟩
  have ho : HasSum (fun n => f (2 * n + 1)) (s / 16) := by
    convert scale 4 using 1
    · funext n
      unfold f
      congr 2
      push_cast
      ring
    · dsimp [s]
      ring
  have he := (h.summable.comp_injective (i := fun n : ℕ => 2 * n)
    (mul_right_injective₀ two_ne_zero)).hasSum
  have hu := (he.even_add_odd ho).unique h
  rw [eq_sub_of_add_eq hu] at he
  have ha := HasSum.even_add_odd (f := fun n => (-1 : ℝ) ^ n * f n)
    (by simpa [pow_mul, Function.comp_def] using he) (by simpa [pow_add, pow_mul] using ho.neg)
  convert ha using 1
  · funext n
    simp [pow_add, f, div_eq_mul_inv]
  · dsimp [s]
    ring
