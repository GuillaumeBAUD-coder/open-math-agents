import OMAStatements.S_oeis_a119574
import Mathlib

namespace OMA.S_oeis_a119574

open PowerSeries

noncomputable def Cg : PowerSeries ℚ := PowerSeries.mk fun n => (catalan n : ℚ)
noncomputable def Bs : PowerSeries ℚ := PowerSeries.mk fun n => (n.centralBinom : ℚ)

lemma Cg_eq : Cg = 1 + X * Cg ^ 2 := by
  ext n
  rcases n with _ | n
  · simp [Cg]
  · rw [map_add, coeff_succ_X_mul, pow_two, coeff_mul, coeff_one, if_neg (by omega)]
    simp only [Cg, coeff_mk]
    rw [zero_add, catalan_succ']
    push_cast
    rfl

lemma dB : d⁄dX ℚ Bs = C (2 : ℚ) * Bs + C (4 : ℚ) * (X * d⁄dX ℚ Bs) := by
  ext n
  rcases n with _ | n
  · simp [coeff_derivative, Bs, Nat.centralBinom]
  · rw [map_add, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul, coeff_derivative, coeff_derivative]
    have h := Nat.succ_mul_centralBinom_succ (n + 1)
    have h' : (((n + 1 + 1) * (n + 1 + 1).centralBinom : ℕ) : ℚ) = ((2 * (2 * (n + 1) + 1) * (n + 1).centralBinom : ℕ) : ℚ) := by
      rw [← h]
    push_cast at h'
    have h2 := Nat.succ_mul_centralBinom_succ n
    simp only [Bs, coeff_mk]
    push_cast
    linear_combination h'

noncomputable def Ss : PowerSeries ℚ := 1 - 2 * (X * Cg)

lemma Ss_sq : Ss ^ 2 = 1 - 4 * X := by
  have h := Cg_eq
  unfold Ss
  linear_combination (-4 * X : PowerSeries ℚ) * h

lemma dB' : d⁄dX ℚ Bs = 2 * Bs + 4 * (X * d⁄dX ℚ Bs) := by
  have := dB
  simpa only [map_ofNat] using this

lemma dS : Ss * d⁄dX ℚ Ss = -2 := by
  have h := congrArg (d⁄dX ℚ) Ss_sq
  simp only [pow_two, Derivation.leibniz, smul_eq_mul, map_sub, derivative_one, derivative_X] at h
  have d4 : d⁄dX ℚ (4 : PowerSeries ℚ) = 0 := by
    have := derivative_C (R := ℚ) (r := (4 : ℚ))
    simpa only [map_ofNat] using this
  rw [d4] at h
  have hu : (C (1 / 2 : ℚ) : PowerSeries ℚ) * 2 = 1 := by
    rw [← map_ofNat (C : ℚ →+* PowerSeries ℚ) 2, ← map_mul]; norm_num
  linear_combination (C (1 / 2 : ℚ) : PowerSeries ℚ) * h - (Ss * d⁄dX ℚ Ss + 2) * hu

lemma Ss_ne : Ss ≠ 0 := by
  intro h
  have : constantCoeff Ss = 1 := by simp [Ss]
  rw [h] at this
  simp at this

lemma SB : Ss * Bs = 1 := by
  have h1 := dS
  have h2 := dB'
  have h3 := Ss_sq
  have hd : d⁄dX ℚ (Ss * Bs) = 0 := by
    have : Ss * d⁄dX ℚ (Ss * Bs) = 0 := by
      simp only [Derivation.leibniz, smul_eq_mul]
      linear_combination Bs * h1 + (d⁄dX ℚ Bs) * h3 + h2
    exact (mul_eq_zero.mp this).resolve_left Ss_ne
  apply derivative.ext
  · rw [hd, derivative_one]
  · simp [Ss, Bs]

lemma dB3 : d⁄dX ℚ Bs = 2 * Bs ^ 3 := by
  have h2 := dB'
  have h2' : Ss ^ 2 * d⁄dX ℚ Bs = 2 * Bs := by rw [Ss_sq]; linear_combination h2
  linear_combination Bs ^ 2 * h2' - (d⁄dX ℚ Bs * (1 + Ss * Bs)) * SB

lemma A_eq : PowerSeries.mk (fun n => ((2 * n).choose n : ℚ) * ((n : ℚ) + 2) ^ 2 / ((n : ℚ) + 1)) =
    3 * Bs + 2 * X * Bs ^ 3 + Cg := by
  have h1 : PowerSeries.mk (fun n => ((2 * n).choose n : ℚ) * ((n : ℚ) + 2) ^ 2 / ((n : ℚ) + 1)) =
      d⁄dX ℚ (X * Bs) + 2 * Bs + Cg := by
    ext n
    simp only [coeff_mk, map_add, coeff_derivative, coeff_succ_X_mul, Cg, Bs]
    have h : (n + 1) * catalan n = n.centralBinom := by
      obtain ⟨k, hk⟩ := Nat.succ_dvd_centralBinom n
      rw [catalan_eq_centralBinom_div, hk, Nat.mul_div_cancel_left _ (by omega)]
    have h' : ((n + 1 : ℚ)) * (catalan n : ℚ) = (n.centralBinom : ℚ) := by exact_mod_cast h
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    have e : ((2 * n).choose n : ℚ) = (n.centralBinom : ℚ) := rfl
    rw [e]
    have e2 : (coeff n) (2 * mk fun n => (n.centralBinom : ℚ)) = 2 * (n.centralBinom : ℚ) := by
      rw [← map_ofNat (C : ℚ →+* PowerSeries ℚ) 2, coeff_C_mul]; simp
    rw [e2, div_eq_iff hn]
    linear_combination (-(1:ℚ)) * h'
  have h2 : d⁄dX ℚ (X * Bs) = Bs + X * (2 * Bs ^ 3) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_X, dB3]; ring
  rw [h1, h2]; ring

end OMA.S_oeis_a119574

theorem OMA.solution : type_of% @OMA.S_oeis_a119574.main := by
  open OMA.S_oeis_a119574 PowerSeries in
  refine ⟨Ss, by simp [Ss], Ss_sq, ?_⟩
  have hA : PowerSeries.mk (OMA.S_oeis_a119574.a) = 3 * Bs + 2 * X * Bs ^ 3 + Cg := by
    rw [← A_eq]; rfl
  rw [hA]
  have r1 := SB
  have r2 := Ss_sq
  have r3 : 2 * X * Cg = 1 - Ss := by unfold Ss; ring
  have r4 := Cg_eq
  linear_combination (4 * Bs ^ 2 * Ss ^ 2 * X ^ 2 + 4 * Bs * Ss * X ^ 2 + 6 * Ss ^ 2 * X + 4 * X ^ 2 : PowerSeries ℚ) * r1 + (2 * Cg * Ss * X - Ss + 6 * X) * r2 + (-8 * Cg * X ^ 2 + 2 * Cg * X + 4 * X - 1) * r3 - (16 * X ^ 2 - 4 * X) * r4
