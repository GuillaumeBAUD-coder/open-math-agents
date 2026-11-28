import OMAStatements.S_oeis_a273722

-- Problem: A273722: The number of valleys of width 1 (i.e., DHU configurations, where U=(0,1), H(1,0), D=(0,-1)) in all bargraphs of semiperimeter n (n>=2).
-- Upstream: formal-conjectures statements/oeis-a273722.lean:0 (declaration OMA.S_oeis_a273722.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Let H = 1/T. Then H^2*P = 1 gives a first order differential equation for H and a recurrence of
order 4 with linear coefficients for its coefficients h(m). Since 2*x*G = A*H - B with polynomials A, B,
every a(n) with n ≥ 2 is a combination of five consecutive h(m), and the left side of the recurrence is a
combination with polynomial coefficients of five instances of the recurrence of h. -/

namespace A273722Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 + (0) * S) :
    (2 - 8 * X + 4 * X ^ 2 + 2 * X ^ 4) * derivative ℚ G + (-4 + 4 * X + 4 * X ^ 3) * G = 0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hS2 : S * S = (1 - 4 * X + 2 * (X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-1 + 4 * X - 2 * X ^ 2 - X ^ 4) * G = (0 : ℚ⟦X⟧) + (-1) * S := by
    linear_combination (0 - (1) * S) * hG + (1) * ((1) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 4 * X + 2 * (X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) = -4 + 4 * X + 4 * X ^ 3 := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 + 4 * X + 4 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-1 + 4 * X - 2 * (X * X) - 1 * (X * X * X * X) : ℚ⟦X⟧) * G) = (4 - 4 * X - 4 * X ^ 3) * G + (-1 + 4 * X - 2 * X ^ 2 - X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hR : derivative ℚ ((0 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S) =
      0 + (0) * S + (-1) * derivative ℚ S := by
    simp [Derivation.leibniz]
  have hk2 : (-1 + 4 * X - 2 * (X * X) - 1 * (X * X * X * X) : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (4 - 4 * X - 4 * X ^ 3) * G + (-1 + 4 * X - 2 * X ^ 2 - X ^ 4) * derivative ℚ G =
      0 + (0) * S + (-1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 4 * X + 2 * X ^ 2 + X ^ 4) * ((2 - 8 * X + 4 * X ^ 2 + 2 * X ^ 4) * derivative ℚ G + (-4 + 4 * X + 4 * X ^ 3) * G - (0)) = 0 := by
    linear_combination (-1) ^ 2 * S * hdS - 2 * (-1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 4 * X + 2 * X ^ 2 + X ^ 4) + (-1) * (-4 + 4 * X + 4 * X ^ 3)) * hk + 2 * (-1) * (1 - 4 * X + 2 * X ^ 2 + X ^ 4) * hdk
  have hg : (1 - 4 * X + 2 * X ^ 2 + X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 + (0) * S) :
    derivative ℚ G * C 2 + derivative ℚ G * X * C (-8) +
      derivative ℚ G * X * X * C 4 + derivative ℚ G * X * X * X * X * C 2 +
      G * C (-4) + G * X * C 4 +
      G * X * X * X * C 4 =
      0 := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 + (0) * S) (m : ℕ) :
    2 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-8) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      4 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 2 * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-4) * coeff (m + 1 + 1 + 1 + 1) G + 4 * coeff (m + 1 + 1 + 1) G +
      4 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 + (0) * S) :
    8 * coeff (0 + 1 + 1 + 1 + 1) G + (-24) * coeff (0 + 1 + 1 + 1) G +
      8 * coeff (0 + 1 + 1) G + (-4) * coeff (0 + 1 + 1 + 1) G +
      4 * coeff (0 + 1 + 1) G + 4 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h


set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 + (0) * S) :
    6 * coeff (0 + 1 + 1 + 1) G + (-16) * coeff (0 + 1 + 1) G + 4 * coeff (0 + 1) G +
      (-4) * coeff (0 + 1 + 1) G + 4 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

/-- The recurrence of h, for n ≥ 4. -/
theorem hrec : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4 →
    coeff 0 S = 1 →
    G * S = 1 →
    ∀ n : ℕ, 4 ≤ n →
      (2 * (n : ℚ)) * coeff n G + (4 - 8 * (n : ℚ)) * coeff (n - 1) G +
        (-4 + 4 * (n : ℚ)) * coeff (n - 2) G + (-4 + 2 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e4]
  cases m with
  | zero =>
    have r := relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination r
  | succ m =>
    have r := rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination r

theorem ghC (T G H : ℚ⟦X⟧)
    (hG : G * (2 * X * T) = 1 - 5 * X + 6 * X ^ 2 - X ^ 3 + X ^ 4 - (1 - 3 * X + X ^ 2) * T)
    (hH : H * T = 1) :
    G * X * C 2 = H * C 1 + H * X * C (-5) + H * X * X * C 6 + H * X * X * X * C (-1) +
      H * X * X * X * X * C 1 - (C 1 + C (-3) * X + C 1 * X * X) := by
  have h : G * (2 * X) = (1 - 5 * X + 6 * X ^ 2 - X ^ 3 + X ^ 4) * H - (1 - 3 * X + X ^ 2) := by
    linear_combination H * hG - (G * (2 * X) + (1 - 3 * X + X ^ 2)) * hH
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

theorem gh (T G H : ℚ⟦X⟧)
    (hG : G * (2 * X * T) = 1 - 5 * X + 6 * X ^ 2 - X ^ 3 + X ^ 4 - (1 - 3 * X + X ^ 2) * T)
    (hH : H * T = 1) (k : ℕ) :
    2 * coeff (k + 1 + 1 + 1) G = coeff (k + 1 + 1 + 1 + 1) H + (-5) * coeff (k + 1 + 1 + 1) H +
      6 * coeff (k + 1 + 1) H + (-1) * coeff (k + 1) H + coeff k H := by
  have h := congrArg (coeff (k + 1 + 1 + 1 + 1)) (ghC T G H hG hH)
  simp only [map_add, map_sub, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C,
    Nat.add_one_ne_zero, ↓reduceIte] at h
  linear_combination h

theorem gh2 (T G H : ℚ⟦X⟧)
    (hG : G * (2 * X * T) = 1 - 5 * X + 6 * X ^ 2 - X ^ 3 + X ^ 4 - (1 - 3 * X + X ^ 2) * T)
    (hH : H * T = 1) :
    2 * coeff (0 + 1 + 1) G = coeff (0 + 1 + 1 + 1) H + (-5) * coeff (0 + 1 + 1) H +
      6 * coeff (0 + 1) H + (-1) * coeff 0 H := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (ghC T G H hG hH)
  simp only [map_add, map_sub, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C,
    Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  linear_combination h

end A273722Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a273722.main := by
  intro T G hT hT0 hG n hn
  have hc : PowerSeries.constantCoeff T ≠ 0 := by
    have h : PowerSeries.constantCoeff T = 1 := by simpa using hT0
    rw [h]
    exact one_ne_zero
  obtain ⟨H, hH⟩ : ∃ H : PowerSeries ℚ, H * T = 1 := ⟨T⁻¹, PowerSeries.inv_mul_cancel T hc⟩
  have hrec := A273722Aux.hrec T H hT hT0 hH
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 from rfl, show m + 6 - 2 = m + 4 from rfl, show m + 6 - 3 = m + 3 from rfl,
    show m + 6 - 4 = m + 2 from rfl]
  rcases m with _ | j
  · have g6 := A273722Aux.gh T G H hG hH 3
    have g5 := A273722Aux.gh T G H hG hH 2
    have g4 := A273722Aux.gh T G H hG hH 1
    have g3 := A273722Aux.gh T G H hG hH 0
    have g2 := A273722Aux.gh2 T G H hG hH
    have r7 := hrec 7 (by norm_num)
    have r6 := hrec 6 (by norm_num)
    have r5 := hrec 5 (by norm_num)
    have r4 := hrec 4 (by norm_num)
    have r3 := A273722Aux.relE1 T H hT (by linear_combination hH)
    norm_num at g6 g5 g4 g3 g2 r7 r6 r5 r4 r3 ⊢
    linear_combination (0 / 1 : ℚ) * g6 + (189 / 1 : ℚ) * g5 + (-133 / 1 : ℚ) * g4 + (28 / 1 : ℚ) * g3 + (-35 / 1 : ℚ) * g2 +
      (0 / 1 : ℚ) * r7 + (63 / 4 : ℚ) * r6 + (-77 / 2 : ℚ) * r5 + (63 / 4 : ℚ) * r4 + (-35 / 2 : ℚ) * r3
  · have g0 := A273722Aux.gh T G H hG hH (j + 4)
    have g1 := A273722Aux.gh T G H hG hH (j + 3)
    have g2 := A273722Aux.gh T G H hG hH (j + 2)
    have g3 := A273722Aux.gh T G H hG hH (j + 1)
    have g4 := A273722Aux.gh T G H hG hH j
    have r0 := hrec (j + 8) (by omega)
    have r1 := hrec (j + 7) (by omega)
    have r2 := hrec (j + 6) (by omega)
    have r3 := hrec (j + 5) (by omega)
    have r4 := hrec (j + 4) (by omega)
    rw [show j + 8 - 1 = j + 7 from rfl, show j + 8 - 2 = j + 6 from rfl, show j + 8 - 4 = j + 4 from rfl] at r0
    rw [show j + 7 - 1 = j + 6 from rfl, show j + 7 - 2 = j + 5 from rfl, show j + 7 - 4 = j + 3 from rfl] at r1
    rw [show j + 6 - 1 = j + 5 from rfl, show j + 6 - 2 = j + 4 from rfl, show j + 6 - 4 = j + 2 from rfl] at r2
    rw [show j + 5 - 1 = j + 4 from rfl, show j + 5 - 2 = j + 3 from rfl, show j + 5 - 4 = j + 1 from rfl] at r3
    rw [show j + 4 - 1 = j + 3 from rfl, show j + 4 - 2 = j + 2 from rfl, show j + 4 - 4 = j from rfl] at r4
    simp only [Nat.add_assoc, Nat.reduceAdd] at g0 g1 g2 g3 g4 ⊢
    push_cast at r0 r1 r2 r3 r4 ⊢
    linear_combination (378 + 123 * ((j : ℚ) + 7) - 199 * ((j : ℚ) + 7) ^ 2 + 52 * ((j : ℚ) + 7) ^ 3 - 4 * ((j : ℚ) + 7) ^ 4) / 2 * g0 + (1134 - 1926 * ((j : ℚ) + 7) + 1020 * ((j : ℚ) + 7) ^ 2 - 216 * ((j : ℚ) + 7) ^ 3 + 16 * ((j : ℚ) + 7) ^ 4) / 2 * g1 +
      (-1094 + 1302 * ((j : ℚ) + 7) - 578 * ((j : ℚ) + 7) ^ 2 + 112 * ((j : ℚ) + 7) ^ 3 - 8 * ((j : ℚ) + 7) ^ 4) / 2 * g2 + (80 - 52 * ((j : ℚ) + 7) + 8 * ((j : ℚ) + 7) ^ 2) / 2 * g3 +
      (-700 + 795 * ((j : ℚ) + 7) - 331 * ((j : ℚ) + 7) ^ 2 + 60 * ((j : ℚ) + 7) ^ 3 - 4 * ((j : ℚ) + 7) ^ 4) / 2 * g4 +
      (378 - 255 * ((j : ℚ) + 7) + 56 * ((j : ℚ) + 7) ^ 2 - 4 * ((j : ℚ) + 7) ^ 3) / 4 * r0 + (-1539 + 1107 * ((j : ℚ) + 7) - 260 * ((j : ℚ) + 7) ^ 2 + 20 * ((j : ℚ) + 7) ^ 3) / 4 * r1 +
      (1418 - 1126 * ((j : ℚ) + 7) + 288 * ((j : ℚ) + 7) ^ 2 - 24 * ((j : ℚ) + 7) ^ 3) / 4 * r2 + (-195 + 163 * ((j : ℚ) + 7) - 44 * ((j : ℚ) + 7) ^ 2 + 4 * ((j : ℚ) + 7) ^ 3) / 4 * r3 +
      (140 - 131 * ((j : ℚ) + 7) + 40 * ((j : ℚ) + 7) ^ 2 - 4 * ((j : ℚ) + 7) ^ 3) / 4 * r4
