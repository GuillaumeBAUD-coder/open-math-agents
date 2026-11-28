import OMAStatements.S_oeis_a239425
import Mathlib


/-!
Proof of the corrected Mathar recurrence for A239425 (n ≥ 5).

With U = W - T - 1 one has U (W + T + 1) = 16 x, which turns the defining equation of G into
8 x^2 G = 6 - 4x - 8x^2 - 2T - V with V = W (T + 1), so for k ≥ 1 the coefficient g(k) is a
combination of the coefficients of T and V at k + 2. The coefficients of T satisfy
(j+1) t(j+1) = (4j-2) t(j). V satisfies V^2 = P = 8 + 8T + 16xT - 48x^2; with u = 1/(1-4x) one has
T' = -2Tu and u' = 4u^2, and expressing the first three derivatives of V through P and its
derivatives gives a third-order linear ODE for V (`a239425_V_ode`). Its coefficients give the
order-2 recurrence 2(k+2)(2k+1)(5k-3) v(k+2) = (k+1)(35k^2-21k-2) v(k+1) + 18(k-1)(2k-1)(5k+2) v(k).
The recurrence of the statement kills both coefficient sequences.
-/

namespace OMA.Helpers

open PowerSeries

theorem a239425_Dmul (D : Derivation ℚ ℚ⟦X⟧ ℚ⟦X⟧) (f g : ℚ⟦X⟧) :
    D (f * g) = f * D g + g * D f := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

theorem a239425_Dnum (D : Derivation ℚ ℚ⟦X⟧ ℚ⟦X⟧) (n : ℕ) [n.AtLeastTwo] :
    D (no_index (OfNat.ofNat n : ℚ⟦X⟧)) = 0 := by
  rw [← Nat.cast_ofNat]
  exact D.map_natCast n

theorem a239425_ne_zero {f : ℚ⟦X⟧} (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  intro hf
  rw [hf, map_zero] at h
  exact h rfl

theorem a239425_cancel2 {f g : ℚ⟦X⟧} (h : 2 * f = 2 * g) : f = g := by
  have h2 : (2 : ℚ⟦X⟧) ≠ 0 := by
    apply a239425_ne_zero
    rw [map_ofNat]
    norm_num
  exact mul_left_cancel₀ h2 h

theorem a239425_e2 (D : Derivation ℚ ℚ⟦X⟧ ℚ⟦X⟧) (hDX : D X = 1) (T : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 4 * X) : T * D T = -2 := by
  have h := congrArg D hT
  rw [pow_two, a239425_Dmul, map_sub, Derivation.map_one_eq_zero, a239425_Dmul,
    a239425_Dnum, hDX] at h
  apply a239425_cancel2
  linear_combination h

theorem a239425_chain (D : Derivation ℚ ℚ⟦X⟧ ℚ⟦X⟧) (V P P1 P2 P3 : ℚ⟦X⟧) (hP1 : D P = P1)
    (hP2 : D P1 = P2) (hP3 : D P2 = P3) (hV : V ^ 2 = P) :
    8 * P ^ 3 * D (D (D V)) = (4 * P ^ 2 * P3 - 3 * P1 * (2 * P * P2 - P1 ^ 2)) * V ∧
    4 * P ^ 2 * D (D V) = (2 * P * P2 - P1 ^ 2) * V ∧ 2 * P * D V = P1 * V := by
  have h0 : 2 * (V * D V) = P1 := by
    have h := congrArg D hV
    rw [pow_two, a239425_Dmul, hP1] at h
    linear_combination h
  have h1 : 2 * P * D V = P1 * V := by linear_combination V * h0 - 2 * D V * hV
  have d1 : 2 * P1 * D V + 2 * P * D (D V) = P2 * V + P1 * D V := by
    have h := congrArg D h1
    simp only [a239425_Dmul, a239425_Dnum, hP1, hP2] at h
    linear_combination h
  have h2 : 4 * P ^ 2 * D (D V) = (2 * P * P2 - P1 ^ 2) * V := by
    linear_combination 2 * P * d1 - P1 * h1
  have d2 : 8 * P * P1 * D (D V) + 4 * P ^ 2 * D (D (D V)) =
      2 * P * P3 * V + (2 * P * P2 - P1 ^ 2) * D V := by
    have h := congrArg D h2
    simp only [a239425_Dmul, a239425_Dnum, hP1, hP2, hP3, map_sub, pow_two] at h
    linear_combination h
  refine ⟨?_, h2, h1⟩
  linear_combination 2 * P * d2 - 4 * P1 * h2 + (2 * P * P2 - P1 ^ 2) * h1

/-- A third-order linear ODE for `V`, whose coefficients give an order-2 recurrence. -/
theorem a239425_V_ode (D : Derivation ℚ ℚ⟦X⟧ ℚ⟦X⟧) (hDX : D X = 1) (T U V : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 4 * X) (hT0 : constantCoeff T = 1) (hU : U * (1 - 4 * X) = 1)
    (hV : V ^ 2 = 8 + 8 * T + 16 * X * T - 48 * X ^ 2) :
    (-180 * X ^ 5 - 35 * X ^ 4 + 20 * X ^ 3) * D (D (D V))
      + (-342 * X ^ 4 - 14 * X ^ 3 - 22 * X ^ 2) * D (D V)
      + (36 * X ^ 3 + 2 * X ^ 2 + 16 * X) * D V + (-36 * X ^ 2) * V = 0 := by
  have e2 : T * D T = -2 := a239425_e2 D hDX T hT
  have dT : D T = -2 * T * U := by
    linear_combination (-D T) * hU + (-U * D T) * hT + (U * T) * e2
  have dU : D U = 4 * U ^ 2 := by
    have h := congrArg D hU
    simp only [a239425_Dmul, map_sub, Derivation.map_one_eq_zero, a239425_Dnum, hDX] at h
    linear_combination (-D U) * hU + U * h
  have hU2 : U * T ^ 2 = 1 := by linear_combination hU + U * hT
  have hP1 : D (8 + 8 * T + 16 * X * T - 48 * X ^ 2) = -32*T*U*X - 16*T*U + 16*T - 96*X := by
    simp only [map_add, map_sub, a239425_Dmul, a239425_Dnum, hDX, dT, pow_two]
    ring
  have hP2 : D (-32*T*U*X - 16*T*U + 16*T - 96*X) = -64*T*U^2*X - 32*T*U^2 - 64*T*U - 96 := by
    simp only [map_add, map_sub, map_neg, a239425_Dmul, a239425_Dnum, hDX, dT, dU, pow_succ,
      pow_zero, one_mul, Derivation.map_one_eq_zero]
    ring
  have hP3 : D (-64*T*U^2*X - 32*T*U^2 - 64*T*U - 96) = -384*T*U^3*X - 192*T*U^3 - 192*T*U^2 := by
    simp only [map_add, map_sub, map_neg, a239425_Dmul, a239425_Dnum, hDX, dT, dU, pow_succ,
      pow_zero, one_mul, Derivation.map_one_eq_zero]
    ring
  obtain ⟨h3, h2, h1⟩ := a239425_chain D V _ _ _ _ hP1 hP2 hP3 hV
  set P : ℚ⟦X⟧ := 8 + 8 * T + 16 * X * T - 48 * X ^ 2 with hP
  set P1 : ℚ⟦X⟧ := -32*T*U*X - 16*T*U + 16*T - 96*X with hP1d
  set P2 : ℚ⟦X⟧ := -64*T*U^2*X - 32*T*U^2 - 64*T*U - 96 with hP2d
  set P3 : ℚ⟦X⟧ := -384*T*U^3*X - 192*T*U^3 - 192*T*U^2 with hP3d
  set A3 : ℚ⟦X⟧ := -180 * X ^ 5 - 35 * X ^ 4 + 20 * X ^ 3 with hA3
  set A2 : ℚ⟦X⟧ := -342 * X ^ 4 - 14 * X ^ 3 - 22 * X ^ 2 with hA2
  set A1 : ℚ⟦X⟧ := 36 * X ^ 3 + 2 * X ^ 2 + 16 * X with hA1
  set A0 : ℚ⟦X⟧ := -36 * X ^ 2 with hA0
  set R : ℚ⟦X⟧ := A3 * (4 * P ^ 2 * P3 - 3 * P1 * (2 * P * P2 - P1 ^ 2))
    + 2 * P * A2 * (2 * P * P2 - P1 ^ 2) + 4 * P ^ 2 * A1 * P1 + 8 * P ^ 3 * A0 with hR
  have key : 8 * P ^ 3 * (A3 * D (D (D V)) + A2 * D (D V) + A1 * D V + A0 * V) = R * V := by
    rw [hR]
    linear_combination A3 * h3 + 2 * P * A2 * h2 + 4 * P ^ 2 * A1 * h1
  have hR0 : T ^ 6 * R = 0 := by
    rw [hR, hA3, hA2, hA1, hA0, hP, hP1d, hP2d, hP3d]
    linear_combination (123863040*T^7*U^2*X^8 + 209879040*T^7*U^2*X^7 + 115261440*T^7*U^2*X^6 + 12902400*T^7*U^2*X^5 - 7311360*T^7*U^2*X^4 - 1720320*T^7*U^2*X^3 + 60162048*T^7*U*X^7 + 83509248*T^7*U*X^6 + 38289408*T^7*U*X^5 + 6819840*T^7*U*X^4 + 1056768*T^7*U*X^3 + 270336*T^7*U*X^2 + 5603328*T^7*X^6 + 6758400*T^7*X^5 + 2535424*T^7*X^4 + 98304*T^7*X^3 - 221184*T^7*X^2 - 65536*T^7*X - 530841600*T^6*U^2*X^9 - 634060800*T^6*U^2*X^8 - 88473600*T^6*U^2*X^7 + 138854400*T^6*U^2*X^6 + 44236800*T^6*U^2*X^5 - 5529600*T^6*U^2*X^4 - 2457600*T^6*U^2*X^3 - 168099840*T^6*U*X^8 - 42270720*T^6*U*X^7 + 104693760*T^6*U*X^6 + 45506560*T^6*U*X^5 - 737280*T^6*U*X^4 - 368640*T^6*U*X^3 + 450560*T^6*U*X^2 + 26542080*T^6*X^7 + 59768832*T^6*X^6 + 39960576*T^6*X^5 + 10772480*T^6*X^4 + 1916928*T^6*X^3 - 131072*T^6*X + 637009920*T^5*U^2*X^10 + 442368000*T^5*U^2*X^9 - 221184000*T^5*U^2*X^8 - 182845440*T^5*U^2*X^7 + 20643840*T^5*U^2*X^6 + 24084480*T^5*U^2*X^5 - 245760*T^5*U^2*X^4 - 983040*T^5*U^2*X^3 + 201719808*T^5*U*X^9 + 73728000*T^5*U*X^8 + 75694080*T^5*U*X^7 + 119291904*T^5*U*X^6 + 32710656*T^5*U*X^5 - 7671808*T^5*U*X^4 - 2228224*T^5*U*X^3 + 180224*T^5*U*X^2 - 10616832*T^5*X^8 + 112656384*T^5*X^7 + 154877952*T^5*X^6 + 57901056*T^5*X^5 + 6057984*T^5*X^4 + 1515520*T^5*X^3 + 491520*T^5*X^2 - 65536*T^5*X - 530841600*T^4*U*X^9 - 634060800*T^4*U*X^8 - 88473600*T^4*U*X^7 + 138854400*T^4*U*X^6 + 44236800*T^4*U*X^5 - 5529600*T^4*U*X^4 - 2457600*T^4*U*X^3 - 168099840*T^4*X^8 - 42270720*T^4*X^7 + 104693760*T^4*X^6 + 45506560*T^4*X^5 - 737280*T^4*X^4 - 368640*T^4*X^3 + 450560*T^4*X^2 + 637009920*T^3*U*X^10 + 442368000*T^3*U*X^9 - 221184000*T^3*U*X^8 - 182845440*T^3*U*X^7 + 20643840*T^3*U*X^6 + 24084480*T^3*U*X^5 - 245760*T^3*U*X^4 - 983040*T^3*U*X^3 + 201719808*T^3*X^9 + 73728000*T^3*X^8 + 75694080*T^3*X^7 + 119291904*T^3*X^6 + 32710656*T^3*X^5 - 7671808*T^3*X^4 - 2228224*T^3*X^3 + 180224*T^3*X^2 - 530841600*T^2*X^9 - 634060800*T^2*X^8 - 88473600*T^2*X^7 + 138854400*T^2*X^6 + 44236800*T^2*X^5 - 5529600*T^2*X^4 - 2457600*T^2*X^3 + 637009920*T*X^10 + 442368000*T*X^9 - 221184000*T*X^8 - 182845440*T*X^7 + 20643840*T*X^6 + 24084480*T*X^5 - 245760*T*X^4 - 983040*T*X^3) * hU2 + (-61440*T^7*X^4 + 40960*T^7*X^3 + 212992*T^7*X^2 + 65536*T^7*X + 8404992*T^6*X^6 + 10690560*T^6*X^5 + 3047424*T^6*X^4 - 892928*T^6*X^3 + 73728*T^6*X^2 + 131072*T^6*X - 5308416*T^5*X^7 + 30965760*T^5*X^6 + 41656320*T^5*X^5 + 13099008*T^5*X^4 - 663552*T^5*X^3 - 409600*T^5*X^2 + 65536*T^5*X - 8847360*T^4*X^7 + 35143680*T^4*X^6 + 52469760*T^4*X^5 + 20193280*T^4*X^4 + 1024000*T^4*X^3 - 450560*T^4*X^2 + 10616832*T^3*X^8 - 16515072*T^3*X^7 + 19218432*T^3*X^6 + 47161344*T^3*X^5 + 21811200*T^3*X^4 + 2490368*T^3*X^3 - 180224*T^3*X^2 - 132710400*T^2*X^8 - 191692800*T^2*X^7 - 70041600*T^2*X^6 + 17203200*T^2*X^5 + 15360000*T^2*X^4 + 2457600*T^2*X^3 + 159252480*T*X^9 + 150405120*T*X^8 - 17694720*T*X^7 - 50135040*T*X^6 - 7372800*T*X^5 + 4177920*T*X^4 + 983040*T*X^3) * hT
  have hne : T ^ 6 * (8 * P ^ 3) ≠ 0 := by
    apply a239425_ne_zero
    have c8 : constantCoeff (8 : ℚ⟦X⟧) = 8 := map_ofNat _ 8
    have c16 : constantCoeff (16 : ℚ⟦X⟧) = 16 := map_ofNat _ 16
    have c48 : constantCoeff (48 : ℚ⟦X⟧) = 48 := map_ofNat _ 48
    simp [hP, hT0, c8, c16, c48]
  have h4 : T ^ 6 * (8 * P ^ 3) * (A3 * D (D (D V)) + A2 * D (D V) + A1 * D V + A0 * V) = 0 := by
    rw [mul_assoc, key]
    linear_combination V * hR0
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h hne
  · exact h

/-- Coefficient recurrence for `V` (order 2), at index `k = m + 3`. -/
theorem a239425_V_rec (V : ℚ⟦X⟧)
    (h : (-180 * X ^ 5 - 35 * X ^ 4 + 20 * X ^ 3) * (d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) V))
      + (-342 * X ^ 4 - 14 * X ^ 3 - 22 * X ^ 2) * (d⁄dX ℚ) ((d⁄dX ℚ) V)
      + (36 * X ^ 3 + 2 * X ^ 2 + 16 * X) * (d⁄dX ℚ) V + (-36 * X ^ 2) * V = 0) (m : ℕ) :
    2 * ((m : ℚ) + 5) * (2 * (m : ℚ) + 7) * (5 * (m : ℚ) + 12) * coeff (m + 5) V =
      ((m : ℚ) + 4) * (35 * ((m : ℚ) + 3) ^ 2 - 21 * ((m : ℚ) + 3) - 2) * coeff (m + 4) V
      + 18 * ((m : ℚ) + 2) * (2 * (m : ℚ) + 5) * (5 * (m : ℚ) + 17) * coeff (m + 3) V := by
  have h' : C 20 * (X ^ 3 * (d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) V)))
      - C 180 * (X ^ 5 * (d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) V)))
      - C 35 * (X ^ 4 * (d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) V)))
      - C 342 * (X ^ 4 * (d⁄dX ℚ) ((d⁄dX ℚ) V)) - C 14 * (X ^ 3 * (d⁄dX ℚ) ((d⁄dX ℚ) V))
      - C 22 * (X ^ 2 * (d⁄dX ℚ) ((d⁄dX ℚ) V))
      + C 36 * (X ^ 3 * (d⁄dX ℚ) V) + C 2 * (X ^ 2 * (d⁄dX ℚ) V) + C 16 * (X ^ 1 * (d⁄dX ℚ) V)
      - C 36 * (X ^ 2 * V) = 0 := by
    simp only [map_ofNat]
    linear_combination h
  have hk := congrArg (coeff (m + 5)) h'
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', map_zero] at hk
  simp only [show 5 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, show 3 ≤ m + 5 by omega,
    show 2 ≤ m + 5 by omega, show 1 ≤ m + 5 by omega, if_true, show m + 5 - 5 = m by omega,
    show m + 5 - 4 = m + 1 by omega, show m + 5 - 3 = m + 2 by omega,
    show m + 5 - 2 = m + 3 by omega, show m + 5 - 1 = m + 4 by omega, coeff_derivative,
    Nat.add_assoc, Nat.reduceAdd] at hk
  push_cast at hk
  linear_combination hk

/-- Coefficient recurrence for `T`. -/
theorem a239425_T_rec (T : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 4 * X) (hT0 : constantCoeff T = 1) (j : ℕ) :
    ((j : ℚ) + 1) * coeff (j + 1) T = (4 * (j : ℚ) - 2) * coeff j T := by
  have e2 : T * (d⁄dX ℚ) T = -2 := a239425_e2 (d⁄dX ℚ) derivative_X T hT
  have h1 : (d⁄dX ℚ) T - C 4 * (X * (d⁄dX ℚ) T) = - (C 2 * T) := by
    simp only [map_ofNat]
    linear_combination T * e2 - (d⁄dX ℚ) T * hT
  have hk := congrArg (coeff j) h1
  rw [map_sub, map_neg, coeff_C_mul, coeff_C_mul, coeff_derivative] at hk
  rcases j with _ | j
  · rw [coeff_zero_X_mul] at hk
    push_cast at hk ⊢
    linear_combination hk
  · rw [coeff_succ_X_mul, coeff_derivative] at hk
    push_cast at hk ⊢
    linear_combination hk

end OMA.Helpers

open OMA.Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a239425.main := by
  intro T W G hT hT0 hW hW0 hG _hG0 n hn
  have hT0' : constantCoeff T = 1 := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hT0
  have hW0' : constantCoeff W = 2 := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hW0
  set V : ℚ⟦X⟧ := W * (T + 1) with hVdef
  have hV : V ^ 2 = 8 + 8 * T + 16 * X * T - 48 * X ^ 2 := by
    rw [hVdef]
    linear_combination (T ^ 2 + 2 * T + 1) * hW + (2 * T + 12 * X + 6) * hT
  have hX1 : constantCoeff (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by simp
  have hU : (1 - 4 * X : ℚ⟦X⟧)⁻¹ * (1 - 4 * X) = 1 := PowerSeries.inv_mul_cancel _ hX1
  have hode := a239425_V_ode (d⁄dX ℚ) derivative_X T _ V hT hT0' hU hV
  have rv := a239425_V_rec V hode
  have rt := a239425_T_rec T hT hT0'
  -- the relation between G, T and V
  have hU : (W - T - 1) * (W + T + 1) = 16 * X := by linear_combination hW - hT
  have hUne : (W - T - 1) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h0
    rw [h0, zero_mul] at hU
    have := congrArg (coeff 1) hU
    rw [← map_ofNat (C (R := ℚ)) 16, coeff_C_mul, coeff_X] at this
    norm_num at this
  have h8 : X ^ 2 * (C 8 * G) = C 6 - C 4 * X - C 8 * X ^ 2 - C 2 * T - V := by
    have h2 : (8 * X ^ 2 * G - (6 - 4 * X - 8 * X ^ 2 - 2 * T - V)) * (W - T - 1) ^ 2 = 0 := by
      rw [hVdef]
      linear_combination 8 * hG + (-2 * T ^ 2 + T * W - 2 * T + W + 4 * X) * hW
        + (T * W - 2 * T + W - 20 * X - 2) * hT
    have h3 := (mul_eq_zero.mp h2).resolve_right hUne
    simp only [map_ofNat]
    linear_combination h3
  have rg : ∀ j : ℕ, coeff (j + 1) G = (-2 * coeff (j + 3) T - coeff (j + 3) V) / 8 := by
    intro j
    have hk := congrArg (coeff (j + 3)) h8
    rw [show j + 3 = (j + 1) + 2 by ring, coeff_X_pow_mul, coeff_C_mul] at hk
    simp only [map_sub, coeff_C, coeff_C_mul, coeff_X, coeff_X_pow] at hk
    simp only [show j + 1 + 2 ≠ 0 by omega, show j + 1 + 2 ≠ 1 by omega,
      show j + 1 + 2 ≠ 2 by omega, if_false] at hk
    rw [show j + 1 + 2 = j + 3 by ring] at hk
    linear_combination hk / 8
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  rw [show m + 5 = (m + 4) + 1 by ring, rg (m + 4), rg (m + 3), rg (m + 2), rg (m + 1), rg m]
  rw [show m + 4 + 3 = m + 7 by ring, show m + 3 + 3 = m + 6 by ring,
    show m + 2 + 3 = m + 5 by ring, show m + 1 + 3 = m + 4 by ring]
  have T7 : coeff (m + 7) T = (4 * ((m : ℚ) + 6) - 2) * coeff (m + 6) T / ((m : ℚ) + 7) := by
    have h := rt (m + 6)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have T6 : coeff (m + 6) T = (4 * ((m : ℚ) + 5) - 2) * coeff (m + 5) T / ((m : ℚ) + 6) := by
    have h := rt (m + 5)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have T5 : coeff (m + 5) T = (4 * ((m : ℚ) + 4) - 2) * coeff (m + 4) T / ((m : ℚ) + 5) := by
    have h := rt (m + 4)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have T4 : coeff (m + 4) T = (4 * ((m : ℚ) + 3) - 2) * coeff (m + 3) T / ((m : ℚ) + 4) := by
    have h := rt (m + 3)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have V7 : coeff (m + 7) V = (((m : ℚ) + 6) * (35 * ((m : ℚ) + 5) ^ 2 - 21 * ((m : ℚ) + 5) - 2)
      * coeff (m + 6) V + 18 * ((m : ℚ) + 4) * (2 * (m : ℚ) + 9) * (5 * (m : ℚ) + 27) * coeff (m + 5) V)
      / (2 * ((m : ℚ) + 7) * (2 * (m : ℚ) + 11) * (5 * (m : ℚ) + 22)) := by
    have h := rv (m + 2)
    rw [show m + 2 + 5 = m + 7 by ring, show m + 2 + 4 = m + 6 by ring,
      show m + 2 + 3 = m + 5 by ring] at h
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have V6 : coeff (m + 6) V = (((m : ℚ) + 5) * (35 * ((m : ℚ) + 4) ^ 2 - 21 * ((m : ℚ) + 4) - 2)
      * coeff (m + 5) V + 18 * ((m : ℚ) + 3) * (2 * (m : ℚ) + 7) * (5 * (m : ℚ) + 22) * coeff (m + 4) V)
      / (2 * ((m : ℚ) + 6) * (2 * (m : ℚ) + 9) * (5 * (m : ℚ) + 17)) := by
    have h := rv (m + 1)
    rw [show m + 1 + 5 = m + 6 by ring, show m + 1 + 4 = m + 5 by ring,
      show m + 1 + 3 = m + 4 by ring] at h
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have V5 : coeff (m + 5) V = (((m : ℚ) + 4) * (35 * ((m : ℚ) + 3) ^ 2 - 21 * ((m : ℚ) + 3) - 2)
      * coeff (m + 4) V + 18 * ((m : ℚ) + 2) * (2 * (m : ℚ) + 5) * (5 * (m : ℚ) + 17) * coeff (m + 3) V)
      / (2 * ((m : ℚ) + 5) * (2 * (m : ℚ) + 7) * (5 * (m : ℚ) + 12)) := by
    have h := rv m
    rw [eq_div_iff (by positivity)]
    linear_combination h
  rw [V7, V6, V5, T7, T6, T5, T4]
  push_cast
  field_simp
  ring
