import OMAStatements.S_oeis_a085640
import Mathlib

open Polynomial

namespace OMA.S_oeis_a085640

noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

lemma hprim : IsPrimitiveRoot ω 3 := by
  have := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [ω] using this

lemma hω : ω ^ 2 + ω + 1 = 0 := by
  have h := hprim.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ, add_assoc, add_comm, add_left_comm] using h

lemma hω3 : ω ^ 3 = 1 := hprim.pow_eq_one

lemma hfac : (X ^ 3 - 1 : ℂ[X]) = (X - C 1) * ((X - C ω) * (X - C (ω ^ 2))) := by
  have h1 : (X - C ω) * (X - C (ω ^ 2)) = (X ^ 2 + X + 1 : ℂ[X]) := by
    have : (X - C ω) * (X - C (ω ^ 2)) = X ^ 2 - C (ω + ω ^ 2) * X + C (ω * ω ^ 2) := by
      simp only [map_add, map_mul]; ring
    rw [this]
    have e1 : ω + ω ^ 2 = -1 := by linear_combination hω
    have e2 : ω * ω ^ 2 = 1 := by linear_combination hω3
    rw [e1, e2]; simp
  rw [h1]; simp; ring

lemma hsplit : (X ^ 3 - 1 : ℂ[X]).Splits := by
  rw [hfac]
  exact (Splits.X_sub_C _).mul ((Splits.X_sub_C _).mul (Splits.X_sub_C _))

lemma hroots : (X ^ 3 - 1 : ℂ[X]).roots = {1, ω, ω ^ 2} := by
  rw [hfac, roots_mul, roots_mul, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  · simp [Multiset.cons_swap]
  · exact mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _) 
  · refine mul_ne_zero (X_sub_C_ne_zero _) (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))

noncomputable def xs (z : ℂ) (n : ℕ) : ℂ := (Chebyshev.T ℂ (n : ℤ)).eval z

lemma xs_zero (z : ℂ) : xs z 0 = 1 := by simp [xs, Chebyshev.T_zero]
lemma xs_one (z : ℂ) : xs z 1 = z := by simp [xs, Chebyshev.T_one]
lemma xs_two (z : ℂ) (n : ℕ) : xs z (n + 2) = 2 * z * xs z (n + 1) - xs z n := by
  simp only [xs]
  have := Chebyshev.T_add_two ℂ (n : ℤ)
  push_cast
  rw [this]; simp

lemma a_cast (n : ℕ) : (a n : ℂ) = xs ω n * xs (ω ^ 2) n := by
  have h := resultant_map_map (X ^ 3 - 1 : ℤ[X]) (Chebyshev.T ℤ (n : ℤ)) 3 (Chebyshev.T ℤ (n : ℤ)).natDegree (Int.castRingHom ℂ)
  have hn : (Chebyshev.T ℤ (n : ℤ)).natDegree = n := by
    rw [Chebyshev.natDegree_T]; simp
  have hd : (X ^ 3 - 1 : ℤ[X]).natDegree = 3 := by
    simpa using (natDegree_X_pow_sub_C (n := 3) (r := (1 : ℤ)))
  have hm : (X ^ 3 - 1 : ℂ[X]).natDegree = 3 := by
    simpa using (natDegree_X_pow_sub_C (n := 3) (r := (1 : ℂ)))
  have e1 : a n = resultant (X ^ 3 - 1 : ℤ[X]) (Chebyshev.T ℤ (n : ℤ)) 3 n := by
    unfold a; rw [hd, hn]
  have hmap : (X ^ 3 - 1 : ℤ[X]).map (Int.castRingHom ℂ) = (X ^ 3 - 1 : ℂ[X]) := by
    simp
  rw [hn, hmap, Chebyshev.map_T] at h
  have hdeg : (Chebyshev.T ℂ (n : ℤ)).natDegree ≤ n := by
    rw [Chebyshev.natDegree_T]; simp
  have h2 := resultant_eq_prod_eval (X ^ 3 - 1 : ℂ[X]) (Chebyshev.T ℂ (n : ℤ)) n hdeg hsplit
  rw [hm, hroots] at h2
  have hmonic : (X ^ 3 - 1 : ℂ[X]).Monic := by
    simpa using (monic_X_pow_sub_C (1 : ℂ) (n := 3) (by norm_num))
  rw [hmonic.leadingCoeff] at h2
  rw [e1]
  have h3 : ((resultant (X ^ 3 - 1 : ℤ[X]) (Chebyshev.T ℤ (n : ℤ)) 3 n : ℤ) : ℂ) =
      (X ^ 3 - 1 : ℂ[X]).resultant (Chebyshev.T ℂ ↑n) 3 n := by
    rw [h]; rfl
  rw [h3, h2]
  simp [xs, Chebyshev.T_eval_one, mul_assoc]

lemma rec4 (n : ℕ) :
    xs ω (n + 4) * xs (ω ^ 2) (n + 4) =
      4 * (xs ω (n + 3) * xs (ω ^ 2) (n + 3)) + 6 * (xs ω (n + 2) * xs (ω ^ 2) (n + 2)) +
      4 * (xs ω (n + 1) * xs (ω ^ 2) (n + 1)) - xs ω n * xs (ω ^ 2) n := by
  have ex2 : xs ω (n + 2) = 2 * ω * xs ω (n + 1) - xs ω n := xs_two ω n
  have ex3 : xs ω (n + 3) = 2 * ω * xs ω (n + 2) - xs ω (n + 1) := xs_two ω (n + 1)
  have ex4 : xs ω (n + 4) = 2 * ω * xs ω (n + 3) - xs ω (n + 2) := xs_two ω (n + 2)
  have ey2 : xs (ω ^ 2) (n + 2) = 2 * ω ^ 2 * xs (ω ^ 2) (n + 1) - xs (ω ^ 2) n := xs_two _ n
  have ey3 : xs (ω ^ 2) (n + 3) = 2 * ω ^ 2 * xs (ω ^ 2) (n + 2) - xs (ω ^ 2) (n + 1) := xs_two _ (n + 1)
  have ey4 : xs (ω ^ 2) (n + 4) = 2 * ω ^ 2 * xs (ω ^ 2) (n + 3) - xs (ω ^ 2) (n + 2) := xs_two _ (n + 2)
  rw [ex4, ey4, ex3, ey3, ex2, ey2]
  generalize xs ω n = x0
  generalize xs ω (n + 1) = x1
  generalize xs (ω ^ 2) n = y0
  generalize xs (ω ^ 2) (n + 1) = y1
  linear_combination (64 * ω^7 * x1 * y1 + ω^6 * (-32 * x0 * y1 - 64 * x1 * y1) + ω^5 * (32 * x0 * y1 - 32 * x1 * y0 - 32 * x1 * y1) + ω^4 * (16 * x0 * y0 + 8 * x0 * y1 + 32 * x1 * y0 + 32 * x1 * y1) + ω^3 * (-16 * x0 * y0 - 8 * x0 * y1 + 16 * x1 * y0 - 32 * x1 * y1) + ω^2 * (-4 * x0 * y0 + 16 * x0 * y1 - 16 * x1 * y0 + 16 * x1 * y1) + ω * (4 * x0 * y0 - 8 * x0 * y1 + 8 * x1 * y0 + 8 * x1 * y1) - 4 * x0 * y0 - 8 * x1 * y1) * hω

lemma a_rec (n : ℕ) : a (n + 4) = 4 * a (n + 3) + 6 * a (n + 2) + 4 * a (n + 1) - a n := by
  apply Int.cast_injective (α := ℂ)
  push_cast
  simp only [a_cast]
  exact rec4 n

lemma a_vals : a 1 = 1 ∧ a 2 = 7 ∧ a 3 = 37 ∧ a 4 = 193 := by
  have e1 : xs ω 1 = ω := xs_one ω
  have e2 : xs ω 2 = 2 * ω * ω - 1 := by rw [xs_two ω 0, xs_one, xs_zero]
  have f2 : xs (ω ^ 2) 2 = 2 * ω ^ 2 * ω ^ 2 - 1 := by rw [xs_two _ 0, xs_one, xs_zero]
  have e3 : xs ω 3 = 2 * ω * xs ω 2 - xs ω 1 := xs_two ω 1
  have f3 : xs (ω ^ 2) 3 = 2 * ω ^ 2 * xs (ω ^ 2) 2 - xs (ω ^ 2) 1 := xs_two _ 1
  have e4 : xs ω 4 = 2 * ω * xs ω 3 - xs ω 2 := xs_two ω 2
  have f4 : xs (ω ^ 2) 4 = 2 * ω ^ 2 * xs (ω ^ 2) 3 - xs (ω ^ 2) 2 := xs_two _ 2
  have f1 : xs (ω ^ 2) 1 = ω ^ 2 := xs_one _
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Int.cast_injective (α := ℂ) <;> push_cast <;> simp only [a_cast]
  · rw [e1, f1]; linear_combination (ω - 1) * hω
  · rw [e2, f2]; linear_combination (4*ω^4 - 4*ω^3 - 2*ω^2 + 6*ω - 6) * hω
  · rw [e3, f3, e2, f2, e1, f1]; linear_combination (16*ω^7 - 16*ω^6 - 12*ω^5 + 28*ω^4 - 28*ω^3 + 37*ω - 37) * hω
  · rw [e4, f4, e3, f3, e2, f2, e1, f1]; linear_combination (64*ω^10 - 64*ω^9 - 64*ω^8 + 128*ω^7 - 120*ω^6 - 8*ω^5 + 192*ω^4 - 184*ω^3 - 8*ω^2 + 192*ω - 192) * hω

end OMA.S_oeis_a085640

open OMA.S_oeis_a085640 in
theorem OMA.solution : type_of% @OMA.S_oeis_a085640.main := by
  obtain ⟨v1, v2, v3, v4⟩ := a_vals
  set f : PowerSeries ℚ := PowerSeries.mk (fun n => (a (n + 1) : ℚ)) with hf
  have hP : f * (1 - 4 * PowerSeries.X - 6 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4) =
      f - PowerSeries.C (4:ℚ) * (PowerSeries.X * f) - PowerSeries.C (6:ℚ) * (PowerSeries.X * (PowerSeries.X * f)) -
        PowerSeries.C (4:ℚ) * (PowerSeries.X * (PowerSeries.X * (PowerSeries.X * f))) +
        PowerSeries.X * (PowerSeries.X * (PowerSeries.X * (PowerSeries.X * f))) := by
    rw [show PowerSeries.C (4:ℚ) = 4 from map_ofNat _ 4, show PowerSeries.C (6:ℚ) = 6 from map_ofNat _ 6]
    ring
  have hR : (1 + 3 * PowerSeries.X + 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 : PowerSeries ℚ) =
      1 + PowerSeries.C (3:ℚ) * PowerSeries.X + PowerSeries.C (3:ℚ) * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 := by
    rw [show PowerSeries.C (3:ℚ) = 3 from map_ofNat _ 3]
  rw [hP, hR]
  ext n
  rcases n with _ | _ | _ | _ | n
  · simp [hf, v1, PowerSeries.coeff_one]
  · simp [hf, v1, v2, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_one, PowerSeries.coeff_X]
    norm_num
  · simp [hf, v1, v2, v3, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    norm_num
  · simp [hf, v1, v2, v3, v4, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    norm_num
  · have h := a_rec (n + 1)
    have h' : ((a (n + 1 + 4) : ℤ) : ℚ) = 4 * (a (n + 1 + 3) : ℚ) + 6 * (a (n + 1 + 2) : ℚ) + 4 * (a (n + 1 + 1) : ℚ) - (a (n + 1) : ℚ) := by
      exact_mod_cast h
    simp only [map_add, map_sub, map_mul, hf, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    simp [PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    linarith [h']
