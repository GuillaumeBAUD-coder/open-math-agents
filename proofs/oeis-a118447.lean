import OMAStatements.S_oeis_a118447
import Mathlib
open PowerSeries

namespace OMA.S_oeis_a118447
open PowerSeries

lemma key (T S : ℚ⟦X⟧) (hS : S ^ 2 = 1 - C (4:ℚ) * X) (hTS : T * S = 1) (hT0 : constantCoeff T = 1) (k n : ℕ) :
    ((n : ℚ) + 1) * coeff (n + 1) (T ^ k) = (4 * n + 2 * k) * coeff n (T ^ k) := by
  have h1 : S * (d⁄dX ℚ) S = -2 := by
    have h := congrArg (d⁄dX ℚ) hS
    rw [Derivation.leibniz_pow] at h
    simp at h
    have h4 : (C (4:ℚ) : ℚ⟦X⟧) = 4 := map_ofNat C 4
    rw [h4] at h
    have : (2:ℚ⟦X⟧) * (S * (d⁄dX ℚ) S) = 2 * (-2) := by linear_combination h
    have h20 : (2:ℚ⟦X⟧) ≠ 0 := fun h => by
      have := congrArg constantCoeff h
      rw [map_ofNat] at this
      exact absurd this (by norm_num)
    exact mul_left_cancel₀ h20 this
  have hA : (d⁄dX ℚ) T * S + T * (d⁄dX ℚ) S = 0 := by
    have h := congrArg (d⁄dX ℚ) hTS
    rw [Derivation.leibniz] at h
    simp at h
    linear_combination h
  have h2 : (d⁄dX ℚ) T = 2 * T ^ 3 := by
    linear_combination T * hA - T ^ 3 * h1 - ((d⁄dX ℚ) T - T ^ 2 * (d⁄dX ℚ) S) * hTS
  have h3 : (1 - C (4:ℚ) * X) * (d⁄dX ℚ) (T ^ k) = C (2 * (k:ℚ)) * T ^ k := by
    rw [← hS]
    rcases k with _ | m
    · simp
    · rw [Derivation.leibniz_pow, h2]
      simp only [nsmul_eq_mul, smul_eq_mul, Nat.add_sub_cancel, map_mul, map_natCast, map_ofNat]
      push_cast
      linear_combination (2 * ((m : ℚ⟦X⟧) + 1) * T ^ (m + 1) * (T * S + 1)) * hTS
  have h5 := congrArg (coeff n) h3
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_C_mul, coeff_derivative] at h5
  rcases n with _ | n
  · simp [hT0] at h5 ⊢
    linarith
  · rw [coeff_succ_X_mul, coeff_derivative] at h5
    push_cast at h5 ⊢
    linarith

lemma uniq (p f : ℕ → ℚ) (k : ℕ) (h0 : p 0 = f 0)
    (hp : ∀ n : ℕ, ((n : ℚ) + 1) * p (n + 1) = (4 * n + 2 * k) * p n)
    (hf : ∀ n : ℕ, ((n : ℚ) + 1) * f (n + 1) = (4 * n + 2 * k) * f n) : ∀ n, p n = f n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have h1 := hp n
    have h2 := hf n
    rw [ih] at h1
    have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
    exact mul_left_cancel₀ hne (by rw [h1, h2])

lemma cb (n : ℕ) : ((n : ℚ) + 1) * (Nat.centralBinom (n + 1) : ℚ) = 2 * (2 * n + 1) * Nat.centralBinom n := by
  have := Nat.succ_mul_centralBinom_succ n
  exact_mod_cast this

end OMA.S_oeis_a118447

theorem OMA.solution : type_of% @OMA.S_oeis_a118447.main := by
  intro S G hS h0 hG n hn
  open OMA.S_oeis_a118447 in
  have hS' : S ^ 2 = 1 - C (4:ℚ) * X := by rw [hS, map_ofNat]
  have hc0 : constantCoeff S = 1 := by rwa [← coeff_zero_eq_constantCoeff_apply]
  have hS0 : S ≠ 0 := fun h => by simp [h] at hc0
  set T : ℚ⟦X⟧ := S⁻¹ with hT
  have hTS : T * S = 1 := by
    rw [mul_comm]; exact PowerSeries.mul_inv_cancel S (by rw [hc0]; norm_num)
  have hT0 : constantCoeff T = 1 := by
    rw [hT, PowerSeries.constantCoeff_inv, hc0]; norm_num
  have e1 : S^5*T = S^4 := by linear_combination S^4 * hTS
  have e2 : S^5*T^2 = S^3 := by linear_combination S^3*(T*S+1) * hTS
  have e3 : S^5*T^3 = S^2 := by linear_combination S^2*((T*S)^2+T*S+1) * hTS
  have e4 : S^5*T^4 = S := by linear_combination S*((T*S)^3+(T*S)^2+T*S+1) * hTS
  have e5 : S^5*T^5 = 1 := by linear_combination ((T*S)^4+(T*S)^3+(T*S)^2+T*S+1) * hTS
  have hEq : (8:ℚ⟦X⟧) * G = T + 2*T^2 - 4*T^3 - 2*T^4 + 3*T^5 := by
    apply mul_left_cancel₀ (pow_ne_zero 5 hS0)
    calc S^5 * (8*G) = (S-1)^2*(S+1)*(S+3) := by linear_combination hG
      _ = S^5*(T + 2*T^2 - 4*T^3 - 2*T^4 + 3*T^5) := by
        linear_combination (-1)*e1 - 2*e2 + 4*e3 + 2*e4 - 3*e5
  have hEq' : C (8:ℚ) * G = T + C (2:ℚ)*T^2 - C (4:ℚ)*T^3 - C (2:ℚ)*T^4 + C (3:ℚ)*T^5 := by
    simp only [map_ofNat]; exact hEq
  have hg : ∀ m : ℕ, 8 * coeff m G = coeff m T + 2 * coeff m (T^2) - 4 * coeff m (T^3)
      - 2 * coeff m (T^4) + 3 * coeff m (T^5) := by
    intro m
    have := congrArg (coeff m) hEq'
    simpa [coeff_C_mul] using this
  have hk : ∀ k m : ℕ, ((m : ℚ) + 1) * coeff (m + 1) (T ^ k) = (4 * m + 2 * k) * coeff m (T ^ k) :=
    fun k m => OMA.S_oeis_a118447.key T S hS' hTS hT0 k m
  have h00 : ∀ k : ℕ, coeff 0 (T ^ k) = 1 := fun k => by simp [hT0]
  have c1 : ∀ m, coeff m (T ^ 1) = (Nat.centralBinom m : ℚ) := by
    refine OMA.S_oeis_a118447.uniq _ _ 1 (by rw [h00]; simp) (hk 1) ?_
    intro m
    have := OMA.S_oeis_a118447.cb m
    push_cast; linarith
  have c2 : ∀ m, coeff m (T ^ 2) = 4 ^ m := by
    refine OMA.S_oeis_a118447.uniq _ _ 2 (by simp [h00]) (hk 2) ?_
    intro m; push_cast; ring
  have c3 : ∀ m, coeff m (T ^ 3) = (2 * m + 1) * (Nat.centralBinom m : ℚ) := by
    refine OMA.S_oeis_a118447.uniq _ _ 3 (by simp [h00]) (hk 3) ?_
    intro m
    have := OMA.S_oeis_a118447.cb m
    push_cast; linear_combination (2 * (m:ℚ) + 3) * this
  have c4 : ∀ m, coeff m (T ^ 4) = ((m : ℚ) + 1) * 4 ^ m := by
    refine OMA.S_oeis_a118447.uniq _ _ 4 (by simp [h00]) (hk 4) ?_
    intro m; push_cast; ring
  have c5 : ∀ m, coeff m (T ^ 5) = (2 * m + 1) * (2 * m + 3) / 3 * (Nat.centralBinom m : ℚ) := by
    refine OMA.S_oeis_a118447.uniq _ _ 5 (by simp [h00]) (hk 5) ?_
    intro m
    have := OMA.S_oeis_a118447.cb m
    push_cast; linear_combination ((2 * (m:ℚ) + 3) * (2 * m + 5) / 3) * this
  have hG' : ∀ m : ℕ, coeff m G = ((m:ℚ)^2 * (Nat.centralBinom m : ℚ) / 2 - m * 4 ^ m / 4) := by
    intro m
    have := hg m
    rw [pow_one] at c1
    rw [c1, c2, c3, c4, c5] at this
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have r1 := OMA.S_oeis_a118447.cb m
  have r2 := OMA.S_oeis_a118447.cb (m + 1)
  have e : m + 2 - 1 = m + 1 := rfl
  have e' : m + 2 - 2 = m := rfl
  rw [e, e', hG' (m+2), hG' (m+1), hG' m]
  have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℚ) + 1 + 1) ≠ 0 := by positivity
  have hc1 : (Nat.centralBinom (m + 1) : ℚ) = 2 * (2 * m + 1) / (m + 1) * Nat.centralBinom m := by
    field_simp; linarith
  have hc2 : (Nat.centralBinom (m + 1 + 1) : ℚ) =
      2 * (2 * ((m:ℚ) + 1) + 1) / (m + 1 + 1) * Nat.centralBinom (m + 1) := by
    push_cast at r2
    field_simp; linarith
  show _ * ((((m + 2 : ℕ) : ℚ)) ^ 2 * (Nat.centralBinom (m + 1 + 1) : ℚ) / 2 - ((m + 2 : ℕ) : ℚ) * 4 ^ (m + 2) / 4) + _ * ((((m + 1 : ℕ) : ℚ)) ^ 2 * (Nat.centralBinom (m + 1) : ℚ) / 2 - ((m + 1 : ℕ) : ℚ) * 4 ^ (m + 1) / 4) + _ * (((m : ℚ)) ^ 2 * (Nat.centralBinom m : ℚ) / 2 - (m : ℚ) * 4 ^ m / 4) = 0
  rw [hc2, hc1]
  push_cast
  field_simp
  ring
