import OMAStatements.S_oeis_a290265
import Mathlib

/-!
Proof of Mathar's recurrence for A290265, a(n) = [x^n] m - [x^(1 + n/2)] B.

With t(k) = [x^k] T: from T^2 = 1 - 2x - 3x^2, (1 - 2x - 3x^2) T' = -(1 + 3x) T, so
(i+3) t(i+3) = (2i+3) t(i+2) + 3i t(i+1). From 2(1 - 3x) B = 1 - 3x + T one gets
(1 - 2x - 3x^2) B' = 2B - 1, so (i+3) b(i+3) = (2i+6) b(i+2) + 3(i+1) b(i+1). Also
[x^k] m = -t(k+2)/2. The operator of the statement kills every solution of the recurrence of t
(shifted by 2) and, in both parities of n, every solution of the recurrence of b evaluated at
1 + floor(n/2): after expressing all terms through two consecutive values, the identities are
checked by field_simp and ring.
-/

namespace OMA.Helpers

open PowerSeries

/-- The operator of the statement. -/
def a290265L (f : ℕ → ℚ) (n : ℕ) : ℚ :=
  (94 + 109 * (n : ℚ) - (n : ℚ) ^ 2 - 16 * (n : ℚ) ^ 3) * f n + (-188 - 21 * (n : ℚ) + 158 * (n : ℚ) ^ 2 - 9 * (n : ℚ) ^ 3) * f (n - 1) +
        (59 * (n : ℚ) - 450 * (n : ℚ) ^ 2 + 139 * (n : ℚ) ^ 3) * f (n - 2) + (-2250 + 3869 * (n : ℚ) - 1806 * (n : ℚ) ^ 2 + 187 * (n : ℚ) ^ 3) * f (n - 3) +
        (-4510 + 2947 * (n : ℚ) - 152 * (n : ℚ) ^ 2 - 97 * (n : ℚ) ^ 3) * f (n - 4) + (4112 - 5779 * (n : ℚ) + 2398 * (n : ℚ) ^ 2 - 311 * (n : ℚ) ^ 3) * f (n - 5) +
        (13044 - 13083 * (n : ℚ) + 4374 * (n : ℚ) ^ 2 - 459 * (n : ℚ) ^ 3) * f (n - 6) + (32382 - 26133 * (n : ℚ) + 6498 * (n : ℚ) ^ 2 - 507 * (n : ℚ) ^ 3) * f (n - 7) +
        (30996 - 18288 * (n : ℚ) + 3429 * (n : ℚ) ^ 2 - 207 * (n : ℚ) ^ 3) * f (n - 8)

theorem a290265L_comb (f g h : ℕ → ℚ) (c d : ℚ) (hf : ∀ k, f k = c * g k + d * h k) (n : ℕ) :
    a290265L f n = c * a290265L g n + d * a290265L h n := by
  unfold a290265L
  simp only [hf]
  ring

theorem a290265_Dmul (D : Derivation ℚ ℚ⟦X⟧ ℚ⟦X⟧) (f g : ℚ⟦X⟧) :
    D (f * g) = f * D g + g * D f := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

theorem a290265_Dnum (D : Derivation ℚ ℚ⟦X⟧ ℚ⟦X⟧) (n : ℕ) [n.AtLeastTwo] :
    D (no_index (OfNat.ofNat n : ℚ⟦X⟧)) = 0 := by
  rw [← Nat.cast_ofNat]
  exact D.map_natCast n

theorem a290265_ne_zero {f : ℚ⟦X⟧} (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  intro hf
  rw [hf, map_zero] at h
  exact h rfl

/-- The ODE of `T`. -/
theorem a290265_T_ode (T : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2) :
    T * (d⁄dX ℚ) T = -(1 + 3 * X) := by
  have h := congrArg (d⁄dX ℚ) hT
  simp only [pow_two, a290265_Dmul, map_sub, Derivation.map_one_eq_zero, a290265_Dnum,
    derivative_X] at h
  have h2 : (2 : ℚ⟦X⟧) * (T * (d⁄dX ℚ) T) = 2 * (-(1 + 3 * X)) := by linear_combination h
  have hne : (2 : ℚ⟦X⟧) ≠ 0 := by
    apply a290265_ne_zero
    rw [map_ofNat]
    norm_num
  exact mul_left_cancel₀ hne h2

/-- Coefficient recurrence of `T`. -/
theorem a290265_T_rec (T : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2) (i : ℕ) :
    ((i : ℚ) + 3) * coeff (i + 3) T = (2 * (i : ℚ) + 3) * coeff (i + 2) T
      + 3 * (i : ℚ) * coeff (i + 1) T := by
  have e := a290265_T_ode T hT
  have h' : (d⁄dX ℚ) T - C 2 * (X ^ 1 * (d⁄dX ℚ) T) - C 3 * (X ^ 2 * (d⁄dX ℚ) T)
      + T + C 3 * (X ^ 1 * T) = 0 := by
    simp only [map_ofNat]
    linear_combination T * e - (d⁄dX ℚ) T * hT
  have hk := congrArg (coeff (i + 2)) h'
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', map_zero] at hk
  simp only [show 2 ≤ i + 2 by omega, show 1 ≤ i + 2 by omega, if_true,
    show i + 2 - 2 = i by omega, show i + 2 - 1 = i + 1 by omega, coeff_derivative,
    Nat.add_assoc, Nat.reduceAdd] at hk
  push_cast at hk
  linear_combination hk

/-- Coefficient recurrence of `B`. -/
theorem a290265_B_rec (T B : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hB : 2 * (1 - 3 * X) * B = 1 - 3 * X + T) (i : ℕ) :
    ((i : ℚ) + 3) * coeff (i + 3) B = (2 * (i : ℚ) + 6) * coeff (i + 2) B
      + 3 * ((i : ℚ) + 1) * coeff (i + 1) B := by
  have e := a290265_T_ode T hT
  have dB : 2 * (1 - 3 * X) * (d⁄dX ℚ) B - 6 * B = -3 + (d⁄dX ℚ) T := by
    have h := congrArg (d⁄dX ℚ) hB
    simp only [a290265_Dmul, map_sub, map_add, Derivation.map_one_eq_zero, a290265_Dnum,
      derivative_X] at h
    linear_combination h
  have hZ : 2 * (1 - 3 * X) * ((1 - 2 * X - 3 * X ^ 2) * (d⁄dX ℚ) B - (2 * B - 1)) = 0 := by
    linear_combination (1 - 2 * X - 3 * X ^ 2) * dB + (1 + 3 * X) * hB + T * e
      - (d⁄dX ℚ) T * hT
  have hne : (2 * (1 - 3 * X) : ℚ⟦X⟧) ≠ 0 := by
    apply a290265_ne_zero
    have c2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := map_ofNat _ 2
    simp [c2]
  have hode := (mul_eq_zero.mp hZ).resolve_left hne
  have h' : (d⁄dX ℚ) B - C 2 * (X ^ 1 * (d⁄dX ℚ) B) - C 3 * (X ^ 2 * (d⁄dX ℚ) B)
      - C 2 * B + 1 = 0 := by
    simp only [map_ofNat]
    linear_combination hode
  have hk := congrArg (coeff (i + 2)) h'
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', map_zero, coeff_one] at hk
  simp only [show 2 ≤ i + 2 by omega, show 1 ≤ i + 2 by omega, if_true,
    show i + 2 ≠ 0 by omega, if_false, show i + 2 - 2 = i by omega,
    show i + 2 - 1 = i + 1 by omega, coeff_derivative, Nat.add_assoc, Nat.reduceAdd] at hk
  push_cast at hk
  linear_combination hk

/-- The operator kills the shifted coefficients of `T`. -/
theorem a290265_t_part (T : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2) (p : ℕ) :
    a290265L (fun k => coeff (k + 2) T) (p + 8) = 0 := by
  have rt := a290265_T_rec T hT
  unfold a290265L
  simp only [show p + 8 - 1 + 2 = p + 9 by omega, show p + 8 - 2 + 2 = p + 8 by omega,
    show p + 8 - 3 + 2 = p + 7 by omega, show p + 8 - 4 + 2 = p + 6 by omega,
    show p + 8 - 5 + 2 = p + 5 by omega, show p + 8 - 6 + 2 = p + 4 by omega,
    show p + 8 - 7 + 2 = p + 3 by omega, show p + 8 - 8 + 2 = p + 2 by omega,
    show p + 8 + 2 = p + 10 by omega]
  have step : ∀ i : ℕ, coeff (i + 3) T = ((2 * (i : ℚ) + 3) * coeff (i + 2) T
      + 3 * (i : ℚ) * coeff (i + 1) T) / ((i : ℚ) + 3) := by
    intro i
    rw [eq_div_iff (by positivity)]
    linear_combination rt i
  rw [show p + 10 = (p + 7) + 3 by omega, step (p + 7),
    show p + 7 + 2 = (p + 6) + 3 by omega, step (p + 6),
    show p + 6 + 2 = (p + 5) + 3 by omega, step (p + 5),
    show p + 5 + 2 = (p + 4) + 3 by omega, step (p + 4),
    show p + 4 + 2 = (p + 3) + 3 by omega, step (p + 3),
    show p + 3 + 2 = (p + 2) + 3 by omega, step (p + 2),
    show p + 2 + 2 = (p + 1) + 3 by omega, step (p + 1)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  push_cast
  field_simp
  ring

/-- The operator kills `k ↦ b(1 + k/2)`. -/
theorem a290265_b_part (T B : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hB : 2 * (1 - 3 * X) * B = 1 - 3 * X + T) (p : ℕ) :
    a290265L (fun k => coeff (1 + k / 2) B) (p + 8) = 0 := by
  have rb := a290265_B_rec T B hT hB
  have step : ∀ i : ℕ, coeff (i + 3) B = ((2 * (i : ℚ) + 6) * coeff (i + 2) B
      + 3 * ((i : ℚ) + 1) * coeff (i + 1) B) / ((i : ℚ) + 3) := by
    intro i
    rw [eq_div_iff (by positivity)]
    linear_combination rb i
  unfold a290265L
  obtain ⟨q, rfl | rfl⟩ : ∃ q, p = 2 * q ∨ p = 2 * q + 1 := ⟨p / 2, by omega⟩
  · simp only [show 1 + (2 * q + 8) / 2 = q + 5 by omega,
      show 1 + (2 * q + 8 - 1) / 2 = q + 4 by omega, show 1 + (2 * q + 8 - 2) / 2 = q + 4 by omega,
      show 1 + (2 * q + 8 - 3) / 2 = q + 3 by omega, show 1 + (2 * q + 8 - 4) / 2 = q + 3 by omega,
      show 1 + (2 * q + 8 - 5) / 2 = q + 2 by omega, show 1 + (2 * q + 8 - 6) / 2 = q + 2 by omega,
      show 1 + (2 * q + 8 - 7) / 2 = q + 1 by omega, show 1 + (2 * q + 8 - 8) / 2 = q + 1 by omega]
    rw [show q + 5 = (q + 2) + 3 by omega, step (q + 2),
      show q + 2 + 2 = (q + 1) + 3 by omega, step (q + 1),
      show q + 1 + 2 = q + 3 by omega, show q + 3 = q + 3 from rfl, step q]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    push_cast
    field_simp
    ring
  · simp only [show 1 + (2 * q + 1 + 8) / 2 = q + 5 by omega,
      show 1 + (2 * q + 1 + 8 - 1) / 2 = q + 5 by omega,
      show 1 + (2 * q + 1 + 8 - 2) / 2 = q + 4 by omega,
      show 1 + (2 * q + 1 + 8 - 3) / 2 = q + 4 by omega,
      show 1 + (2 * q + 1 + 8 - 4) / 2 = q + 3 by omega,
      show 1 + (2 * q + 1 + 8 - 5) / 2 = q + 3 by omega,
      show 1 + (2 * q + 1 + 8 - 6) / 2 = q + 2 by omega,
      show 1 + (2 * q + 1 + 8 - 7) / 2 = q + 2 by omega,
      show 1 + (2 * q + 1 + 8 - 8) / 2 = q + 1 by omega]
    rw [show q + 5 = (q + 2) + 3 by omega, step (q + 2),
      show q + 2 + 2 = (q + 1) + 3 by omega, step (q + 1),
      show q + 1 + 2 = q + 3 by omega, step q]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    push_cast
    field_simp
    ring

end OMA.Helpers

open OMA.Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a290265.main := by
  intro T m B hT _hT0 hm hB a ha n hn
  show a290265L a n = 0
  have rm : ∀ k : ℕ, coeff k m = -(1 / 2) * coeff (k + 2) T := by
    intro k
    have h8 : X ^ 2 * (C 2 * m) = 1 - X - T := by
      simp only [map_ofNat]
      linear_combination hm
    have hk := congrArg (coeff (k + 2)) h8
    rw [coeff_X_pow_mul, coeff_C_mul] at hk
    simp only [map_sub, coeff_one, coeff_X, show k + 2 ≠ 0 by omega,
      show k + 2 ≠ 1 by omega, if_false] at hk
    linear_combination hk / 2
  have hcomb : ∀ k, a k = -(1 / 2) * coeff (k + 2) T + (-1) * coeff (1 + k / 2) B := by
    intro k
    rw [ha k, rm k]
    ring
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 8 := ⟨n - 8, by omega⟩
  rw [a290265L_comb a _ _ _ _ hcomb, a290265_t_part T hT p, a290265_b_part T B hT hB p]
  ring
