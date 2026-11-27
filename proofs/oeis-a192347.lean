import OMAStatements.S_oeis_a192347
import Mathlib

/-!
Evaluate at a real root t of x^2 - x - 1 (t = φ or ψ). The remainder c0 + c1 x of p(n) modulo
x^2 - x - 1 takes the value p(n)(t) = c0 + c1 t, so c1 sqrt 5 = p(n)(φ) - p(n)(ψ).
With s = sqrt(t+2), the binomial theorem gives 2 p(n)(t) = (t+s)^n + (t-s)^n, and both
t + s and t - s are roots of y^2 - 2t y - 1 (as t^2 = t + 1), so
p(n+2)(t) = 2t p(n+1)(t) + p(n)(t). Eliminating t with t^2 = t + 1 gives the order 4
recurrence with characteristic polynomial y^4 - 2y^3 - 6y^2 + 2y + 1.
-/

namespace R192347
open OMA.S_oeis_a192347 Polynomial

theorem hq : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!

theorem hdeg (f : ℤ[X]) : (f %ₘ (X ^ 2 - X - 1)).natDegree ≤ 1 := by
  have h2 : (X ^ 2 - X - 1 : ℤ[X]).natDegree = 2 := by compute_degree!
  have h1 : (X ^ 2 - X - 1 : ℤ[X]) ≠ 1 := by
    intro h
    rw [h, natDegree_one] at h2
    omega
  have := natDegree_modByMonic_lt f hq h1
  omega

theorem eval_rem (t : ℝ) (ht : t ^ 2 = t + 1) (f : ℤ[X]) :
    aeval t f = ((f %ₘ (X ^ 2 - X - 1)).coeff 0 : ℝ) +
      ((f %ₘ (X ^ 2 - X - 1)).coeff 1 : ℝ) * t := by
  have hroot : aeval t (X ^ 2 - X - 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    linear_combination ht
  rw [← aeval_modByMonic_eq_self_of_root hroot]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (hdeg f)]
  simp only [map_add, map_mul, aeval_C, aeval_X, algebraMap_int_eq, eq_intCast, map_intCast,
    map_natCast, map_ofNat]
  ring

theorem closed (t s : ℝ) (hs : s ^ 2 = t + 2) (n : ℕ) :
    2 * aeval t (p n) = (t + s) ^ n + (t - s) ^ n := by
  rw [show t + s = s + t by ring, show t - s = -s + t by ring, add_pow, add_pow,
    ← Finset.sum_add_distrib, p, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rcases Nat.even_or_odd j with he | ho
  · rw [if_pos he, Even.neg_pow he]
    obtain ⟨i, rfl⟩ := he
    rw [show (i + i) / 2 = i by omega, show s ^ (i + i) = (s ^ 2) ^ i by ring, hs]
    simp only [map_mul, map_pow, map_add, aeval_C, aeval_X, algebraMap_int_eq, eq_intCast,
      Int.cast_natCast, Int.cast_ofNat, map_intCast, map_natCast, map_ofNat]
    ring
  · rw [if_neg (Nat.not_even_iff_odd.mpr ho), map_zero, mul_zero, Odd.neg_pow ho]
    ring

theorem rec2 (t : ℝ) (ht : t ^ 2 = t + 1) (ht2 : 0 ≤ t + 2) (n : ℕ) :
    aeval t (p (n + 2)) = 2 * t * aeval t (p (n + 1)) + aeval t (p n) := by
  have hs : (Real.sqrt (t + 2)) ^ 2 = t + 2 := Real.sq_sqrt ht2
  have e0 := closed t (Real.sqrt (t + 2)) hs n
  have e1 := closed t (Real.sqrt (t + 2)) hs (n + 1)
  have e2 := closed t (Real.sqrt (t + 2)) hs (n + 2)
  have hA : (t + Real.sqrt (t + 2)) ^ 2 = 2 * t * (t + Real.sqrt (t + 2)) + 1 := by
    linear_combination hs - ht
  have hB : (t - Real.sqrt (t + 2)) ^ 2 = 2 * t * (t - Real.sqrt (t + 2)) + 1 := by
    linear_combination hs - ht
  linear_combination (1 / 2 : ℝ) * e2 - t * e1 - (1 / 2 : ℝ) * e0 +
    (1 / 2 : ℝ) * (t + Real.sqrt (t + 2)) ^ n * hA + (1 / 2 : ℝ) * (t - Real.sqrt (t + 2)) ^ n * hB

theorem rec4 (t : ℝ) (ht : t ^ 2 = t + 1) (ht2 : 0 ≤ t + 2) (n : ℕ) :
    aeval t (p (n + 4)) = 2 * aeval t (p (n + 3)) + 6 * aeval t (p (n + 2)) -
      2 * aeval t (p (n + 1)) - aeval t (p n) := by
  have e0 : aeval t (p (n + 2)) = 2 * t * aeval t (p (n + 1)) + aeval t (p n) := rec2 t ht ht2 n
  have e1 : aeval t (p (n + 3)) = 2 * t * aeval t (p (n + 2)) + aeval t (p (n + 1)) :=
    rec2 t ht ht2 (n + 1)
  have e2 : aeval t (p (n + 4)) = 2 * t * aeval t (p (n + 3)) + aeval t (p (n + 2)) :=
    rec2 t ht ht2 (n + 2)
  linear_combination e2 + (2 * t - 2) * e1 - e0 + 4 * aeval t (p (n + 2)) * ht

theorem hk (k : ℕ) : (a (k + 1) : ℝ) * Real.sqrt 5 =
    aeval Real.goldenRatio (p k) - aeval Real.goldenConj (p k) := by
  have ha : a (k + 1) = (p k %ₘ (X ^ 2 - X - 1)).coeff 1 := by
    simp only [a, Nat.add_sub_cancel]
  rw [ha, eval_rem _ Real.goldenRatio_sq, eval_rem _ Real.goldenConj_sq,
    ← Real.goldenRatio_sub_goldenConj]
  ring

theorem solve : ∀ n : ℕ, 4 < n →
    a n = 2 * a (n - 1) + 6 * a (n - 2) - 2 * a (n - 3) - a (n - 4) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  have hφ2 : 0 ≤ Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have hψ2 : 0 ≤ Real.goldenConj + 2 := by linarith [Real.neg_one_lt_goldenConj]
  have rφ := rec4 _ Real.goldenRatio_sq hφ2 m
  have rψ := rec4 _ Real.goldenConj_sq hψ2 m
  have h5 : (a (m + 5) : ℝ) * Real.sqrt 5 =
      aeval Real.goldenRatio (p (m + 4)) - aeval Real.goldenConj (p (m + 4)) := hk (m + 4)
  have h4 : (a (m + 4) : ℝ) * Real.sqrt 5 =
      aeval Real.goldenRatio (p (m + 3)) - aeval Real.goldenConj (p (m + 3)) := hk (m + 3)
  have h3 : (a (m + 3) : ℝ) * Real.sqrt 5 =
      aeval Real.goldenRatio (p (m + 2)) - aeval Real.goldenConj (p (m + 2)) := hk (m + 2)
  have h2 : (a (m + 2) : ℝ) * Real.sqrt 5 =
      aeval Real.goldenRatio (p (m + 1)) - aeval Real.goldenConj (p (m + 1)) := hk (m + 1)
  have h1 : (a (m + 1) : ℝ) * Real.sqrt 5 =
      aeval Real.goldenRatio (p m) - aeval Real.goldenConj (p m) := hk m
  have key : ((a (m + 5) : ℝ) - (2 * a (m + 4) + 6 * a (m + 3) - 2 * a (m + 2) - a (m + 1))) *
      Real.sqrt 5 = 0 := by
    linear_combination h5 - 2 * h4 - 6 * h3 + 2 * h2 + h1 + rφ - rψ
  have hs5 : Real.sqrt 5 ≠ 0 := by positivity
  have key2 := (mul_eq_zero.mp key).resolve_right hs5
  have fin : (a (m + 5) : ℝ) = 2 * a (m + 4) + 6 * a (m + 3) - 2 * a (m + 2) - a (m + 1) := by
    linarith
  exact_mod_cast fin

end R192347

theorem OMA.solution : type_of% @OMA.S_oeis_a192347.main := R192347.solve
