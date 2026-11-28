import OMAStatements.S_oeis_a400218
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: z-coordinates satisfy 3z(n+3)+z(n+2)-z(n+1)-3z(n)=0 (its difference is the order-4 step, base case 0); scaling gives a(n+3)+a(n+2)-3a(n+1)-27a(n)=0 for n>=3; compare coefficients.

namespace OMA.P_oeis_a400218
open OMA.S_oeis_a400218 PowerSeries

theorem zstep (n : ℕ) : (v (n + 4)).2.2 =
    2 / 3 * ((v (n + 1)).2.2 + (v (n + 2)).2.2 + (v (n + 3)).2.2) - (v n).2.2 := by
  simp [v, step]

theorem w (n : ℕ) :
    3 * (v (n + 3)).2.2 + (v (n + 2)).2.2 - (v (n + 1)).2.2 - 3 * (v n).2.2 = 0 := by
  induction n with
  | zero => norm_num [v]
  | succ n ih =>
    have h := zstep n
    rw [show n + 1 + 3 = n + 4 by ring, show n + 1 + 2 = n + 3 by ring,
      show n + 1 + 1 = n + 2 by ring]
    linarith

theorem a_eq (m : ℕ) : a (m + 3) = 3 ^ m * (v (m + 3)).2.2 := by
  rcases m with _ | m
  · simp [a]
  · simp only [a, show ¬ (m + 1 + 3 ≤ 3) by omega, if_false, show m + 1 + 3 - 3 = m + 1 by omega]

theorem arec (m : ℕ) :
    a (m + 6) + a (m + 5) - 3 * a (m + 4) - 27 * a (m + 3) = 0 := by
  have h1 := a_eq (m + 3)
  have h2 := a_eq (m + 2)
  have h3 := a_eq (m + 1)
  have h4 := a_eq m
  rw [show m + 3 + 3 = m + 6 by ring] at h1
  rw [show m + 2 + 3 = m + 5 by ring] at h2
  rw [show m + 1 + 3 = m + 4 by ring] at h3
  rw [h1, h2, h3, h4]
  have hw := w (m + 3)
  rw [show m + 3 + 3 = m + 6 by ring, show m + 3 + 2 = m + 5 by ring,
    show m + 3 + 1 = m + 4 by ring] at hw
  rw [pow_add, pow_add, pow_add]
  linear_combination (9 * 3 ^ m) * hw

theorem cmul (n : ℕ) (f : ℚ⟦X⟧) (c : ℚ) : coeff n (C c * f) = c * coeff n f := coeff_C_mul n f c

theorem cXp (n k : ℕ) (f : ℚ⟦X⟧) :
    coeff n (X ^ k * f) = if k ≤ n then coeff (n - k) f else 0 := coeff_X_pow_mul' f k n

theorem solve : type_of% @OMA.S_oeis_a400218.main := by
  have eC : ∀ c : ℕ, (c : ℚ⟦X⟧) = C (c : ℚ) := fun c => (map_natCast C c).symm
  have eL : PowerSeries.mk a *
      (27 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 - PowerSeries.X - 1) =
      C ((27 : ℕ) : ℚ) * (X ^ 3 * PowerSeries.mk a) + C ((3 : ℕ) : ℚ) * (X ^ 2 * PowerSeries.mk a)
        - X ^ 1 * PowerSeries.mk a - PowerSeries.mk a := by
    rw [← eC, ← eC]; push_cast; ring
  have eR : (18 * PowerSeries.X ^ 5 + 26 * PowerSeries.X ^ 4 - 24 * PowerSeries.X ^ 3 -
      5 * PowerSeries.X ^ 2 + 1 : ℚ⟦X⟧) =
      C ((18 : ℕ) : ℚ) * (X ^ 5 * 1) + C ((26 : ℕ) : ℚ) * (X ^ 4 * 1)
        - C ((24 : ℕ) : ℚ) * (X ^ 3 * 1) - C ((5 : ℕ) : ℚ) * (X ^ 2 * 1) + 1 := by
    rw [← eC, ← eC, ← eC, ← eC]; push_cast; ring
  rw [eL, eR]
  ext n
  simp only [map_add, map_sub, cmul, cXp, coeff_mk, coeff_one]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · norm_num [a, v]
  · norm_num [a, v]
  · norm_num [a, v]
  · norm_num [a, v]
  · norm_num [a, v, step]
  · norm_num [a, v, step]
  · have := arec n
    simp only [show 3 ≤ n + 6 by omega, show 2 ≤ n + 6 by omega, show 1 ≤ n + 6 by omega,
      show 5 ≤ n + 6 by omega, show 4 ≤ n + 6 by omega, if_true,
      show n + 6 - 3 = n + 3 by omega, show n + 6 - 2 = n + 4 by omega,
      show n + 6 - 1 = n + 5 by omega, show n + 6 - 5 = n + 1 by omega,
      show n + 6 - 4 = n + 2 by omega, show n + 6 ≠ 0 by omega, show n + 1 ≠ 0 by omega,
      show n + 2 ≠ 0 by omega, show n + 3 ≠ 0 by omega, if_false]
    simp
    linarith

end OMA.P_oeis_a400218

theorem OMA.solution : type_of% @OMA.S_oeis_a400218.main := OMA.P_oeis_a400218.solve
