import OMAStatements.S_oeis_a400218
import Mathlib

open OMA.S_oeis_a400218 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a400218.main := by
  have w (n : ℕ) : (v (n+3)).2.2 = -(v (n+2)).2.2/3 + (v (n+1)).2.2/3 + (v n).2.2 := by
    induction n with
    | zero => norm_num [v]
    | succ n ih =>
      simp [v, step] at ih ⊢
      linarith
  have h (m : ℕ) : a (m+3) = 3^m * (v (m+3)).2.2 := by
    rcases m with _ | m <;> simp [a]
  simp only [← map_ofNat (C (R := ℚ))]
  ext n
  rcases n with _ | _ | _ | _ | _ | _ | n <;> first
  | (simp [mul_add, mul_sub, ← mul_assoc, pow_succ, h, w, coeff_X, coeff_one]
     ring; done)
  | (simp [mul_add, mul_sub, ← mul_assoc, pow_succ, a, v, step, coeff_X, coeff_one]
     try norm_num)
