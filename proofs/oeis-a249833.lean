import OMAStatements.S_oeis_a249833
import Mathlib

/-!
# OEIS A249833 / A370382

With `L = log B`, the hypothesis gives `L' = 1 + L * exp L` and `exp L = B`.  Writing
`h = 1 + y * exp y` and `T n = sum_q R n q * y^q / q!`, the recursion for `R` says
`T (n+1) = d/dy (h * T n)`, and the chain rule gives `B^(n+1) = (h * T n)(L)`.
Taking constant coefficients gives the claim.
-/

open PowerSeries

namespace OMA.A249833

noncomputable def h : PowerSeries ℚ := 1 + X * exp ℚ

noncomputable def T (n : ℕ) : PowerSeries ℚ :=
  mk fun q => (OMA.S_oeis_a249833.R n q : ℚ) / (q.factorial : ℚ)

theorem T_zero : T 0 = exp ℚ := by
  ext q
  simp [T, coeff_exp, OMA.S_oeis_a249833.R]

theorem T_succ (n : ℕ) : T (n + 1) = derivative ℚ (h * T n) := by
  ext q
  rw [coeff_derivative, h, add_mul, one_mul, map_add, mul_assoc, coeff_succ_X_mul,
    mul_comm (exp ℚ) (T n), coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [T, coeff_mk, coeff_exp, OMA.S_oeis_a249833.R]
  have key : ∀ k ∈ Finset.range (q + 1),
      ((q.choose k : ℚ) * (OMA.S_oeis_a249833.R n k : ℚ)) / (q.factorial : ℚ)
        = (OMA.S_oeis_a249833.R n k : ℚ) / (k.factorial : ℚ) *
          (algebraMap ℚ ℚ) (1 / ((q - k).factorial : ℚ)) := by
    intro k hk
    have hk' : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have e := Nat.choose_mul_factorial_mul_factorial hk'
    have e' : (q.choose k : ℚ) * (k.factorial : ℚ) * ((q - k).factorial : ℚ)
        = (q.factorial : ℚ) := by exact_mod_cast e
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((q - k).factorial : ℚ) ≠ 0 := by positivity
    have h3 : (q.factorial : ℚ) ≠ 0 := by positivity
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    have h4 : (q.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk').ne'
    rw [← e']
    field_simp
  rw [← Finset.sum_congr rfl key, ← Finset.sum_div, Nat.factorial_succ]
  have h3 : (q.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem constCoeff_subst_of (L f : PowerSeries ℚ) (hL : constantCoeff L = 0) :
    constantCoeff (f.subst L) = constantCoeff f := by
  have hs : HasSubst L := HasSubst.of_constantCoeff_zero' hL
  conv_lhs => rw [eq_X_mul_shift_add_const f]
  rw [← coe_substAlgHom hs, map_add, map_mul, substAlgHom_X, coe_substAlgHom hs, subst_C]
  rw [map_add, map_mul, hL, zero_mul, zero_add]
  exact MvPowerSeries.constantCoeff_C _

theorem geom : (mk fun n => (-1 : ℚ) ^ n) * (1 + X) = 1 := by
  rw [mul_add, mul_one]
  ext n
  cases n <;> simp [coeff_succ_mul_X, pow_succ]

theorem main_aux (B : PowerSeries ℚ) (hB : constantCoeff B = 1)
    (hD : derivative ℚ B = B + B ^ 2 * logOf B) (n : ℕ) :
    (derivative ℚ)^[n + 1] B = (h * T n).subst (logOf B) := by
  have hL0 : constantCoeff (logOf B) = 0 := constantCoeff_logOf hB
  have hs : HasSubst (logOf B) := HasSubst.of_constantCoeff_zero' hL0
  have hs1 : HasSubst (B - 1) := HasSubst.of_constantCoeff_zero' (by simp [hB])
  have hB0 : B ≠ 0 := by
    intro h0
    rw [h0] at hB
    simp at hB
  have hG : (subst (B - 1) (mk fun n => (-1 : ℚ) ^ n) : PowerSeries ℚ) * B = 1 := by
    have := congrArg (substAlgHom hs1) geom
    rw [map_mul, map_add, map_one, substAlgHom_X, coe_substAlgHom hs1] at this
    have hB' : 1 + (B - 1) = B := by ring
    rwa [hB'] at this
  have hLd : derivative ℚ (logOf B) * B = derivative ℚ B := by
    have e : derivative ℚ (logOf B)
        = (subst (B - 1) (mk fun n => (-1 : ℚ) ^ n) : PowerSeries ℚ) * derivative ℚ B := by
      rw [logOf_eq, derivative_subst hs1, deriv_log]
      simp
    rw [e]
    linear_combination (derivative ℚ B) * hG
  have hL' : derivative ℚ (logOf B) = 1 + logOf B * B := by
    apply mul_right_cancel₀ hB0
    rw [hLd, hD]
    ring
  have hBi : B * B⁻¹ = 1 := PowerSeries.mul_inv_cancel B (by rw [hB]; exact one_ne_zero)
  have hE : (subst (logOf B) (exp ℚ) : PowerSeries ℚ) = B := by
    have dE : derivative ℚ (subst (logOf B) (exp ℚ) : PowerSeries ℚ)
        = (subst (logOf B) (exp ℚ) : PowerSeries ℚ) * derivative ℚ (logOf B) := by
      rw [derivative_subst hs, derivative_exp]
    have h1 : (subst (logOf B) (exp ℚ) : PowerSeries ℚ) * B⁻¹ = 1 := by
      apply derivative.ext
      · rw [Derivation.leibniz, derivative_inv', dE, ← hLd, derivative_one]
        simp only [smul_eq_mul]
        linear_combination
          (-(subst (logOf B) (exp ℚ) : PowerSeries ℚ) * derivative ℚ (logOf B) * B⁻¹) * hBi
      · rw [map_mul, constCoeff_subst_of _ _ hL0, constantCoeff_inv, hB]
        simp
    calc (subst (logOf B) (exp ℚ) : PowerSeries ℚ)
        = (subst (logOf B) (exp ℚ) : PowerSeries ℚ) * B⁻¹ * B := by
          rw [mul_assoc, mul_comm B⁻¹ B, hBi, mul_one]
      _ = B := by rw [h1, one_mul]
  have hh : (subst (logOf B) h : PowerSeries ℚ) = 1 + logOf B * B := by
    rw [h, ← coe_substAlgHom hs, map_add, map_mul, map_one, substAlgHom_X, coe_substAlgHom hs, hE]
  induction n with
  | zero =>
    rw [Function.iterate_one, T_zero, subst_mul hs, hh, hE, hD]
    ring
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, derivative_subst hs, ← T_succ, hL', ← hh,
      subst_mul hs, mul_comm]

end OMA.A249833

theorem OMA.solution : type_of% @OMA.S_oeis_a249833.main := by
  intro B hB hD n
  have key := congrArg constantCoeff (OMA.A249833.main_aux B hB hD n)
  rw [constantCoeff_iterate_derivative,
    OMA.A249833.constCoeff_subst_of _ _ (constantCoeff_logOf hB)] at key
  rw [key]
  simp [OMA.A249833.h, OMA.A249833.T]
