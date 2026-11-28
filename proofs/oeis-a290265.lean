import OMAStatements.S_oeis_a290265

-- Problem: A290265: The number of non-palindromic Motzkin paths of length n.
-- Upstream: formal-conjectures statements/oeis-a290265.lean:0 (declaration OMA.S_oeis_a290265.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Let W = T(x^2) = sqrt(1-2x^2-3x^4) and let H be the series with coefficients A005773(1+floor(n/2)),
so that x^2 H = (1+x) (B(x^2) - 1). The g.f. G = m - H of a is linear in T and W:
(2x^2 - 6x^4) G = (2 - 6x^2) + (-1 + 3x^2) T + (-1 - x) W. Differentiating this relation and the
relations for the derivatives of the two square roots, and eliminating the derivatives, shows that
the differential operator read off the recurrence maps G to a polynomial; the recurrence is the
coefficient of a power of x in the resulting equation. -/

namespace A290265Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G T W : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hW : W ^ 2 = 1 - 2 * X ^ 2 - 3 * X ^ 4)
    (hG : (2 * X ^ 2 - 6 * X ^ 4) * G = (2 - 6 * X ^ 2) + (-1 + 3 * X ^ 2) * T + (-1 - X) * W) :
    (-16 * X ^ 3 - 9 * X ^ 4 + 139 * X ^ 5 + 187 * X ^ 6 - 97 * X ^ 7 - 311 * X ^ 8 - 459 * X ^ 9 - 507 * X ^ 10 - 207 * X ^ 11) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-49 * X ^ 2 + 104 * X ^ 3 + 801 * X ^ 4 + 438 * X ^ 5 - 1607 * X ^ 6 - 3200 * X ^ 7 - 5265 * X ^ 8 - 5670 * X ^ 9 - 2160 * X ^ 10) * derivative ℚ (derivative ℚ G) + (92 * X + 390 * X ^ 2 + 450 * X ^ 3 - 1854 * X ^ 4 - 4338 * X ^ 5 - 7702 * X ^ 6 - 14514 * X ^ 7 - 14346 * X ^ 8 - 4914 * X ^ 9) * derivative ℚ G + (94 - 60 * X - 570 * X ^ 2 - 1848 * X ^ 3 - 1362 * X ^ 4 - 3708 * X ^ 5 - 7134 * X ^ 6 - 6048 * X ^ 7 - 1836 * X ^ 8) * G =
      -40 * X ^ 3 + 1320 * X ^ 4 + 792 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d36 : derivative ℚ (36 : ℚ⟦X⟧) = 0 := dnum 36
  have d72 : derivative ℚ (72 : ℚ⟦X⟧) = 0 := dnum 72
  have ht2 : T * T = (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) := by linear_combination hT
  have hPtd : derivative ℚ (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) = (-2 - 6 * X) := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have httd : derivative ℚ (T * T) = 2 * T * derivative ℚ T := by
    simp [Derivation.leibniz]
    ring
  have hdt : 2 * T * derivative ℚ T = (-2 - 6 * X) := by rw [← httd, ht2, hPtd]
  have t1 : 2 * ((1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) * derivative ℚ T) = (-2 - 6 * X : ℚ⟦X⟧) * T := by
    linear_combination T * hdt - 2 * derivative ℚ T * hT
  have hLt2 : derivative ℚ (2 * ((1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) * derivative ℚ T)) =
      2 * (-2 - 6 * X) * derivative ℚ T + 2 * (1 - 2 * X - 3 * X ^ 2) * derivative ℚ (derivative ℚ T) := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hRt2 : derivative ℚ ((-2 - 6 * X : ℚ⟦X⟧) * T) =
      (-6) * T + (-2 - 6 * X) * derivative ℚ T := by
    simp [Derivation.leibniz, d2, d6]
    ring
  have t2 : 2 * (-2 - 6 * X) * derivative ℚ T + 2 * (1 - 2 * X - 3 * X ^ 2) * derivative ℚ (derivative ℚ T) =
      (-6) * T + (-2 - 6 * X) * derivative ℚ T := by
    rw [← hLt2, ← hRt2, t1]
  have t2p : 2 * ((-2 - 6 * X : ℚ⟦X⟧) * derivative ℚ T) + 2 * ((1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T)) = (-6 : ℚ⟦X⟧) * T + (-2 - 6 * X : ℚ⟦X⟧) * derivative ℚ T := by linear_combination t2
  have hLt3 : derivative ℚ (2 * ((-2 - 6 * X : ℚ⟦X⟧) * derivative ℚ T) + 2 * ((1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T))) =
      2 * (-6) * derivative ℚ T + 4 * (-2 - 6 * X) * derivative ℚ (derivative ℚ T) + 2 * (1 - 2 * X - 3 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ T)) := by
    simp [Derivation.leibniz, d2, d3, d6]
    ring
  have hRt3 : derivative ℚ ((-6 : ℚ⟦X⟧) * T + (-2 - 6 * X : ℚ⟦X⟧) * derivative ℚ T) =
      (0) * T + 2 * (-6) * derivative ℚ T + (-2 - 6 * X) * derivative ℚ (derivative ℚ T) := by
    simp [Derivation.leibniz, d2, d6]
    ring
  have t3 : 2 * (-6) * derivative ℚ T + 4 * (-2 - 6 * X) * derivative ℚ (derivative ℚ T) + 2 * (1 - 2 * X - 3 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ T)) =
      (0) * T + 2 * (-6) * derivative ℚ T + (-2 - 6 * X) * derivative ℚ (derivative ℚ T) := by
    rw [← hLt3, ← hRt3, t2p]
  have hw2 : W * W = (1 - 2 * (X * X) - 3 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hW
  have hPwd : derivative ℚ (1 - 2 * (X * X) - 3 * (X * X * X * X) : ℚ⟦X⟧) = (-4 * X - 12 * X ^ 3) := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hwwd : derivative ℚ (W * W) = 2 * W * derivative ℚ W := by
    simp [Derivation.leibniz]
    ring
  have hdw : 2 * W * derivative ℚ W = (-4 * X - 12 * X ^ 3) := by rw [← hwwd, hw2, hPwd]
  have w1 : 2 * ((1 - 2 * (X * X) - 3 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ W) = (-4 * X - 12 * (X * X * X) : ℚ⟦X⟧) * W := by
    linear_combination W * hdw - 2 * derivative ℚ W * hW
  have hLw2 : derivative ℚ (2 * ((1 - 2 * (X * X) - 3 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ W)) =
      2 * (-4 * X - 12 * X ^ 3) * derivative ℚ W + 2 * (1 - 2 * X ^ 2 - 3 * X ^ 4) * derivative ℚ (derivative ℚ W) := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hRw2 : derivative ℚ ((-4 * X - 12 * (X * X * X) : ℚ⟦X⟧) * W) =
      (-4 - 36 * X ^ 2) * W + (-4 * X - 12 * X ^ 3) * derivative ℚ W := by
    simp [Derivation.leibniz, d4, d12]
    ring
  have w2 : 2 * (-4 * X - 12 * X ^ 3) * derivative ℚ W + 2 * (1 - 2 * X ^ 2 - 3 * X ^ 4) * derivative ℚ (derivative ℚ W) =
      (-4 - 36 * X ^ 2) * W + (-4 * X - 12 * X ^ 3) * derivative ℚ W := by
    rw [← hLw2, ← hRw2, w1]
  have w2p : 2 * ((-4 * X - 12 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ W) + 2 * ((1 - 2 * (X * X) - 3 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) = (-4 - 36 * (X * X) : ℚ⟦X⟧) * W + (-4 * X - 12 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ W := by linear_combination w2
  have hLw3 : derivative ℚ (2 * ((-4 * X - 12 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ W) + 2 * ((1 - 2 * (X * X) - 3 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W))) =
      2 * (-4 - 36 * X ^ 2) * derivative ℚ W + 4 * (-4 * X - 12 * X ^ 3) * derivative ℚ (derivative ℚ W) + 2 * (1 - 2 * X ^ 2 - 3 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by
    simp [Derivation.leibniz, d2, d3, d4, d12]
    ring
  have hRw3 : derivative ℚ ((-4 - 36 * (X * X) : ℚ⟦X⟧) * W + (-4 * X - 12 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ W) =
      (-72 * X) * W + 2 * (-4 - 36 * X ^ 2) * derivative ℚ W + (-4 * X - 12 * X ^ 3) * derivative ℚ (derivative ℚ W) := by
    simp [Derivation.leibniz, d4, d12, d36]
    ring
  have w3 : 2 * (-4 - 36 * X ^ 2) * derivative ℚ W + 4 * (-4 * X - 12 * X ^ 3) * derivative ℚ (derivative ℚ W) + 2 * (1 - 2 * X ^ 2 - 3 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ W)) =
      (-72 * X) * W + 2 * (-4 - 36 * X ^ 2) * derivative ℚ W + (-4 * X - 12 * X ^ 3) * derivative ℚ (derivative ℚ W) := by
    rw [← hLw3, ← hRw3, w2p]
  have e0 : (2 * (X * X) - 6 * (X * X * X * X) : ℚ⟦X⟧) * G =
      (2 - 6 * (X * X) : ℚ⟦X⟧) + (-1 + 3 * (X * X) : ℚ⟦X⟧) * T + (-1 - 1 * X : ℚ⟦X⟧) * W := by linear_combination hG
  have hLe1 : derivative ℚ ((2 * (X * X) - 6 * (X * X * X * X) : ℚ⟦X⟧) * G) =
      (4 * X - 24 * X ^ 3) * G + (2 * X ^ 2 - 6 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d6]
    ring
  have hRe1 : derivative ℚ ((2 - 6 * (X * X) : ℚ⟦X⟧) + (-1 + 3 * (X * X) : ℚ⟦X⟧) * T + (-1 - 1 * X : ℚ⟦X⟧) * W) =
      (-12 * X) + (6 * X) * T + (-1 + 3 * X ^ 2) * derivative ℚ T + (-1) * W + (-1 - X) * derivative ℚ W := by
    simp [Derivation.leibniz, d2, d3, d6]
    ring
  have e1 : (4 * X - 24 * X ^ 3) * G + (2 * X ^ 2 - 6 * X ^ 4) * derivative ℚ G =
      (-12 * X) + (6 * X) * T + (-1 + 3 * X ^ 2) * derivative ℚ T + (-1) * W + (-1 - X) * derivative ℚ W := by
    rw [← hLe1, ← hRe1, e0]
  have e1p : (4 * X - 24 * (X * X * X) : ℚ⟦X⟧) * G + (2 * (X * X) - 6 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G =
      (-12 * X : ℚ⟦X⟧) + (6 * X : ℚ⟦X⟧) * T + (-1 + 3 * (X * X) : ℚ⟦X⟧) * derivative ℚ T + (-1 : ℚ⟦X⟧) * W + (-1 - 1 * X : ℚ⟦X⟧) * derivative ℚ W := by linear_combination e1
  have hLe2 : derivative ℚ ((4 * X - 24 * (X * X * X) : ℚ⟦X⟧) * G + (2 * (X * X) - 6 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (4 - 72 * X ^ 2) * G + 2 * (4 * X - 24 * X ^ 3) * derivative ℚ G + (2 * X ^ 2 - 6 * X ^ 4) * derivative ℚ (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d4, d6, d24]
    ring
  have hRe2 : derivative ℚ ((-12 * X : ℚ⟦X⟧) + (6 * X : ℚ⟦X⟧) * T + (-1 + 3 * (X * X) : ℚ⟦X⟧) * derivative ℚ T + (-1 : ℚ⟦X⟧) * W + (-1 - 1 * X : ℚ⟦X⟧) * derivative ℚ W) =
      (-12) + (6) * T + 2 * (6 * X) * derivative ℚ T + (-1 + 3 * X ^ 2) * derivative ℚ (derivative ℚ T) + (0) * W + 2 * (-1) * derivative ℚ W + (-1 - X) * derivative ℚ (derivative ℚ W) := by
    simp [Derivation.leibniz, d3, d6, d12]
    ring
  have e2 : (4 - 72 * X ^ 2) * G + 2 * (4 * X - 24 * X ^ 3) * derivative ℚ G + (2 * X ^ 2 - 6 * X ^ 4) * derivative ℚ (derivative ℚ G) =
      (-12) + (6) * T + 2 * (6 * X) * derivative ℚ T + (-1 + 3 * X ^ 2) * derivative ℚ (derivative ℚ T) + (0) * W + 2 * (-1) * derivative ℚ W + (-1 - X) * derivative ℚ (derivative ℚ W) := by
    rw [← hLe2, ← hRe2, e1p]
  have e2p : (4 - 72 * (X * X) : ℚ⟦X⟧) * G + 2 * ((4 * X - 24 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G) + (2 * (X * X) - 6 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) =
      (-12 : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * T + 2 * ((6 * X : ℚ⟦X⟧) * derivative ℚ T) + (-1 + 3 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T) + (0 : ℚ⟦X⟧) * W + 2 * ((-1 : ℚ⟦X⟧) * derivative ℚ W) + (-1 - 1 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W) := by linear_combination e2
  have hLe3 : derivative ℚ ((4 - 72 * (X * X) : ℚ⟦X⟧) * G + 2 * ((4 * X - 24 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G) + (2 * (X * X) - 6 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) =
      (-144 * X) * G + 3 * (4 - 72 * X ^ 2) * derivative ℚ G + 3 * (4 * X - 24 * X ^ 3) * derivative ℚ (derivative ℚ G) + (2 * X ^ 2 - 6 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2, d4, d6, d24, d72]
    ring
  have hRe3 : derivative ℚ ((-12 : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * T + 2 * ((6 * X : ℚ⟦X⟧) * derivative ℚ T) + (-1 + 3 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T) + (0 : ℚ⟦X⟧) * W + 2 * ((-1 : ℚ⟦X⟧) * derivative ℚ W) + (-1 - 1 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) =
      (0) + (0) * T + 3 * (6) * derivative ℚ T + 3 * (6 * X) * derivative ℚ (derivative ℚ T) + (-1 + 3 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (0) * W + 3 * (0) * derivative ℚ W + 3 * (-1) * derivative ℚ (derivative ℚ W) + (-1 - X) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by
    simp [Derivation.leibniz, d2, d3, d6, d12]
    ring
  have e3 : (-144 * X) * G + 3 * (4 - 72 * X ^ 2) * derivative ℚ G + 3 * (4 * X - 24 * X ^ 3) * derivative ℚ (derivative ℚ G) + (2 * X ^ 2 - 6 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (0) + (0) * T + 3 * (6) * derivative ℚ T + 3 * (6 * X) * derivative ℚ (derivative ℚ T) + (-1 + 3 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (0) * W + 3 * (0) * derivative ℚ W + 3 * (-1) * derivative ℚ (derivative ℚ W) + (-1 - X) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by
    rw [← hLe3, ← hRe3, e2p]
  have hfull : (4 - 24 * X - 60 * X ^ 2 + 544 * X ^ 3 + 264 * X ^ 4 - 5328 * X ^ 5 + 328 * X ^ 6 + 28896 * X ^ 7 - 5796 * X ^ 8 - 90248 * X ^ 9 + 11484 * X ^ 10 + 138048 * X ^ 11 + 26352 * X ^ 12 + 30240 * X ^ 13 - 115344 * X ^ 14 - 475200 * X ^ 15 + 35964 * X ^ 16 + 556632 * X ^ 17 + 300348 * X ^ 18 + 303264 * X ^ 19 - 227448 * X ^ 20 - 898128 * X ^ 21 - 367416 * X ^ 22 + 69984 * X ^ 23 + 236196 * X ^ 24 + 472392 * X ^ 25 + 236196 * X ^ 26 : ℚ⟦X⟧) * ((-16 * X ^ 3 - 9 * X ^ 4 + 139 * X ^ 5 + 187 * X ^ 6 - 97 * X ^ 7 - 311 * X ^ 8 - 459 * X ^ 9 - 507 * X ^ 10 - 207 * X ^ 11) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-49 * X ^ 2 + 104 * X ^ 3 + 801 * X ^ 4 + 438 * X ^ 5 - 1607 * X ^ 6 - 3200 * X ^ 7 - 5265 * X ^ 8 - 5670 * X ^ 9 - 2160 * X ^ 10) * derivative ℚ (derivative ℚ G) + (92 * X + 390 * X ^ 2 + 450 * X ^ 3 - 1854 * X ^ 4 - 4338 * X ^ 5 - 7702 * X ^ 6 - 14514 * X ^ 7 - 14346 * X ^ 8 - 4914 * X ^ 9) * derivative ℚ G + (94 - 60 * X - 570 * X ^ 2 - 1848 * X ^ 3 - 1362 * X ^ 4 - 3708 * X ^ 5 - 7134 * X ^ 6 - 6048 * X ^ 7 - 1836 * X ^ 8) * G - (-40 * X ^ 3 + 1320 * X ^ 4 + 792 * X ^ 5)) = 0 := by
    linear_combination (-32 * X + 174 * X ^ 2 + 770 * X ^ 3 - 4854 * X ^ 4 - 8858 * X ^ 5 + 59614 * X ^ 6 + 69714 * X ^ 7 - 411974 * X ^ 8 - 427850 * X ^ 9 + 1661286 * X ^ 10 + 1949962 * X ^ 11 - 3339278 * X ^ 12 - 5586370 * X ^ 13 - 595274 * X ^ 14 + 6214202 * X ^ 15 + 17809794 * X ^ 16 + 13401966 * X ^ 17 - 25813494 * X ^ 18 - 47973114 * X ^ 19 - 26094690 * X ^ 20 + 17682354 * X ^ 21 + 81663066 * X ^ 22 + 95599926 * X ^ 23 + 13303278 * X ^ 24 - 74799774 * X ^ 25 - 118843038 * X ^ 26 - 103741074 * X ^ 27 - 16546842 * X ^ 28 + 62561322 * X ^ 29 + 82839186 * X ^ 30 + 68851134 * X ^ 31 + 36256086 * X ^ 32 + 8148762 * X ^ 33) * e3 +
      (94 - 248 * X - 3666 * X ^ 2 + 9460 * X ^ 3 + 59190 * X ^ 4 - 142168 * X ^ 5 - 543746 * X ^ 6 + 1135236 * X ^ 7 + 3193838 * X ^ 8 - 5216120 * X ^ 9 - 12399354 * X ^ 10 + 12942212 * X ^ 11 + 30266478 * X ^ 12 - 8839576 * X ^ 13 - 34257226 * X ^ 14 - 37774764 * X ^ 15 - 34805934 * X ^ 16 + 90402264 * X ^ 17 + 168967242 * X ^ 18 + 451548 * X ^ 19 - 141815070 * X ^ 20 - 190113480 * X ^ 21 - 179711622 * X ^ 22 + 81073548 * X ^ 23 + 295246458 * X ^ 24 + 218040984 * X ^ 25 + 90945666 * X ^ 26 - 58497876 * X ^ 27 - 181857798 * X ^ 28 - 146598984 * X ^ 29 - 75464622 * X ^ 30 - 41806692 * X ^ 31 - 12754584 * X ^ 32) * e2 +
      (-376 + 2304 * X + 7212 * X ^ 2 - 63228 * X ^ 3 - 43504 * X ^ 4 + 755688 * X ^ 5 - 27084 * X ^ 6 - 5150836 * X ^ 7 + 1565208 * X ^ 8 + 21864816 * X ^ 9 - 7652404 * X ^ 10 - 58084668 * X ^ 11 + 11996800 * X ^ 12 + 83727800 * X ^ 13 + 23671668 * X ^ 14 + 3431148 * X ^ 15 - 115749576 * X ^ 16 - 270649440 * X ^ 17 + 80971812 * X ^ 18 + 430971948 * X ^ 19 + 265904208 * X ^ 20 + 55932120 * X ^ 21 - 353476548 * X ^ 22 - 713515068 * X ^ 23 - 311772888 * X ^ 24 + 209847024 * X ^ 25 + 396485604 * X ^ 26 + 461133324 * X ^ 27 + 268948512 * X ^ 28 + 19368072 * X ^ 29 - 19131876 * X ^ 30 + 2125764 * X ^ 31) * e1 +
      (564 - 3744 * X - 6480 * X ^ 2 + 88720 * X ^ 3 - 40548 * X ^ 4 - 860928 * X ^ 5 + 1090024 * X ^ 6 + 4396128 * X ^ 7 - 7975692 * X ^ 8 - 12135584 * X ^ 9 + 30394368 * X ^ 10 + 14649264 * X ^ 11 - 66303620 * X ^ 12 + 802560 * X ^ 13 + 66992856 * X ^ 14 + 12921408 * X ^ 15 + 84184380 * X ^ 16 - 80618976 * X ^ 17 - 412188048 * X ^ 18 - 113344272 * X ^ 19 + 322801524 * X ^ 20 + 490323456 * X ^ 21 + 638318232 * X ^ 22 + 160193376 * X ^ 23 - 606717540 * X ^ 24 - 757296864 * X ^ 25 - 614949408 * X ^ 26 - 347995440 * X ^ 27 + 4960116 * X ^ 28 + 90699264 * X ^ 29 + 21257640 * X ^ 30) * e0 +
      (16 * X - 55 * X ^ 2 - 495 * X ^ 3 + 1533 * X ^ 4 + 7165 * X ^ 5 - 18159 * X ^ 6 - 62967 * X ^ 7 + 114997 * X ^ 8 + 359589 * X ^ 9 - 384435 * X ^ 10 - 1306859 * X ^ 11 + 394545 * X ^ 12 + 2586641 * X ^ 13 + 1645637 * X ^ 14 - 435459 * X ^ 15 - 5731815 * X ^ 16 - 10149687 * X ^ 17 + 2126619 * X ^ 18 + 17893683 * X ^ 19 + 16494327 * X ^ 20 + 5868855 * X ^ 21 - 18752877 * X ^ 22 - 41175621 * X ^ 23 - 22766913 * X ^ 24 + 11739087 * X ^ 25 + 34553871 * X ^ 26 + 43995879 * X ^ 27 + 21662235 * X ^ 28 - 11580165 * X ^ 29 - 24413481 * X ^ 30 - 24151041 * X ^ 31 - 15411789 * X ^ 32 - 4074381 * X ^ 33) * t3 +
      (-47 + 78 * X + 1680 * X ^ 2 - 1922 * X ^ 3 - 26824 * X ^ 4 + 17466 * X ^ 5 + 245404 * X ^ 6 - 53470 * X ^ 7 - 1377552 * X ^ 8 - 198626 * X ^ 9 + 4692872 * X ^ 10 + 2065662 * X ^ 11 - 8550768 * X ^ 12 - 5814118 * X ^ 13 + 3187140 * X ^ 14 + 2706834 * X ^ 15 + 15805458 * X ^ 16 + 16120890 * X ^ 17 - 21384000 * X ^ 18 - 18528534 * X ^ 19 + 1917432 * X ^ 20 - 24813378 * X ^ 21 - 11039004 * X ^ 22 + 20439702 * X ^ 23 + 12089736 * X ^ 24 + 48132954 * X ^ 25 + 66047400 * X ^ 26 + 6189210 * X ^ 27 - 34852032 * X ^ 28 - 54285714 * X ^ 29 - 62591940 * X ^ 30 - 33657930 * X ^ 31 - 5845851 * X ^ 32) * t2 +
      (141 - 657 * X - 3069 * X ^ 2 + 15013 * X ^ 3 + 33873 * X ^ 4 - 147489 * X ^ 5 - 263753 * X ^ 6 + 786669 * X ^ 7 + 1524537 * X ^ 8 - 2268485 * X ^ 9 - 6037497 * X ^ 10 + 2256921 * X ^ 11 + 14170333 * X ^ 12 + 5975643 * X ^ 13 - 12028485 * X ^ 14 - 19601199 * X ^ 15 - 24340041 * X ^ 16 + 8307117 * X ^ 17 + 66554649 * X ^ 18 + 35935407 * X ^ 19 - 25770717 * X ^ 20 - 36053667 * X ^ 21 - 65017323 * X ^ 22 - 28087641 * X ^ 23 + 54024003 * X ^ 24 + 31271913 * X ^ 25 + 7818525 * X ^ 26 + 9992403 * X ^ 27 - 12498705 * X ^ 28 + 59049 * X ^ 29 + 16120377 * X ^ 30 + 5845851 * X ^ 31) * t1 +
      (16 * X - 71 * X ^ 2 - 440 * X ^ 3 + 1900 * X ^ 4 + 6024 * X ^ 5 - 21791 * X ^ 6 - 53936 * X ^ 7 + 133248 * X ^ 8 + 330112 * X ^ 9 - 415595 * X ^ 10 - 1307208 * X ^ 11 + 263212 * X ^ 12 + 2838744 * X ^ 13 + 2370461 * X ^ 14 - 1053600 * X ^ 15 - 6481440 * X ^ 16 - 9196848 * X ^ 17 + 354267 * X ^ 18 + 15338808 * X ^ 19 + 18298116 * X ^ 20 + 7293240 * X ^ 21 - 12013677 * X ^ 22 - 28028592 * X ^ 23 - 23584608 * X ^ 24 - 3429216 * X ^ 25 + 13611159 * X ^ 26 + 20347848 * X ^ 27 + 16612452 * X ^ 28 + 7400808 * X ^ 29 + 1358127 * X ^ 30) * w3 +
      (-47 + 125 * X + 1698 * X ^ 2 - 4228 * X ^ 3 - 26141 * X ^ 4 + 56817 * X ^ 5 + 234572 * X ^ 6 - 395912 * X ^ 7 - 1371039 * X ^ 8 + 1438793 * X ^ 9 + 5287270 * X ^ 10 - 1601628 * X ^ 11 - 12035237 * X ^ 12 - 7122211 * X ^ 13 + 7735368 * X ^ 14 + 26605968 * X ^ 15 + 33716475 * X ^ 16 - 12276153 * X ^ 17 - 74471346 * X ^ 18 - 72024444 * X ^ 19 - 11479887 * X ^ 20 + 74728899 * X ^ 21 + 135902124 * X ^ 22 + 96587640 * X ^ 23 - 7643565 * X ^ 24 - 84835917 * X ^ 25 - 108899478 * X ^ 26 - 83377188 * X ^ 27 - 35370351 * X ^ 28 - 6200145 * X ^ 29) * w2 +
      (94 - 810 * X - 654 * X ^ 2 + 20042 * X ^ 3 - 14556 * X ^ 4 - 218364 * X ^ 5 + 236636 * X ^ 6 + 1389420 * X ^ 7 - 1422342 * X ^ 8 - 5709790 * X ^ 9 + 3660486 * X ^ 10 + 15023310 * X ^ 11 + 1260904 * X ^ 12 - 18452328 * X ^ 13 - 29793432 * X ^ 14 - 24352056 * X ^ 15 + 45639666 * X ^ 16 + 112581306 * X ^ 17 + 62854110 * X ^ 18 - 50960826 * X ^ 19 - 161701596 * X ^ 20 - 204770268 * X ^ 21 - 89045892 * X ^ 22 + 92924172 * X ^ 23 + 195749622 * X ^ 24 + 204585102 * X ^ 25 + 140103594 * X ^ 26 + 53970786 * X ^ 27 + 8503056 * X ^ 28) * w1
  have hM0 : (4 - 24 * X - 60 * X ^ 2 + 544 * X ^ 3 + 264 * X ^ 4 - 5328 * X ^ 5 + 328 * X ^ 6 + 28896 * X ^ 7 - 5796 * X ^ 8 - 90248 * X ^ 9 + 11484 * X ^ 10 + 138048 * X ^ 11 + 26352 * X ^ 12 + 30240 * X ^ 13 - 115344 * X ^ 14 - 475200 * X ^ 15 + 35964 * X ^ 16 + 556632 * X ^ 17 + 300348 * X ^ 18 + 303264 * X ^ 19 - 227448 * X ^ 20 - 898128 * X ^ 21 - 367416 * X ^ 22 + 69984 * X ^ 23 + 236196 * X ^ 24 + 472392 * X ^ 25 + 236196 * X ^ 26 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
    simp [kc] at h'
  have h := (mul_eq_zero.mp hfull).resolve_left hM0
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G T W : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hW : W ^ 2 = 1 - 2 * X ^ 2 - 3 * X ^ 4)
    (hG : (2 * X ^ 2 - 6 * X ^ 4) * G = (2 - 6 * X ^ 2) + (-1 + 3 * X ^ 2) * T + (-1 - X) * W) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C (-16) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-9) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 139 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C 187 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C (-97) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * C (-311) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * X * C (-459) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * X * X * C (-507) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * X * X * X * C (-207) + derivative ℚ (derivative ℚ G) * X * X * C (-49) +
      derivative ℚ (derivative ℚ G) * X * X * X * C 104 + derivative ℚ (derivative ℚ G) * X * X * X * X * C 801 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 438 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-1607) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-3200) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C (-5265) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * X * C (-5670) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * X * X * C (-2160) +
      derivative ℚ G * X * C 92 + derivative ℚ G * X * X * C 390 +
      derivative ℚ G * X * X * X * C 450 + derivative ℚ G * X * X * X * X * C (-1854) +
      derivative ℚ G * X * X * X * X * X * C (-4338) + derivative ℚ G * X * X * X * X * X * X * C (-7702) +
      derivative ℚ G * X * X * X * X * X * X * X * C (-14514) + derivative ℚ G * X * X * X * X * X * X * X * X * C (-14346) +
      derivative ℚ G * X * X * X * X * X * X * X * X * X * C (-4914) + G * C 94 +
      G * X * C (-60) + G * X * X * C (-570) +
      G * X * X * X * C (-1848) + G * X * X * X * X * C (-1362) +
      G * X * X * X * X * X * C (-3708) + G * X * X * X * X * X * X * C (-7134) +
      G * X * X * X * X * X * X * X * C (-6048) + G * X * X * X * X * X * X * X * X * C (-1836) =
      C (-40) * X * X * X + C 1320 * X * X * X * X +
      C 792 * X * X * X * X * X := by
  have h := key G T W hT hW hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G T W : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hW : W ^ 2 = 1 - 2 * X ^ 2 - 3 * X ^ 4)
    (hG : (2 * X ^ 2 - 6 * X ^ 4) * G = (2 - 6 * X ^ 2) + (-1 + 3 * X ^ 2) * T + (-1 - X) * W) (m : ℕ) :
    (-16) * ((m : ℚ) + 11) * ((m : ℚ) + 10) * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-9) * ((m : ℚ) + 10) * ((m : ℚ) + 9) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      139 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 187 * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-97) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-311) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-459) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-507) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-207) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + (-49) * ((m : ℚ) + 11) * ((m : ℚ) + 10) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      104 * ((m : ℚ) + 10) * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 801 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      438 * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1607) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-3200) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-5265) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-5670) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-2160) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      92 * ((m : ℚ) + 11) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 390 * ((m : ℚ) + 10) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      450 * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1854) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-4338) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-7702) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-14514) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-14346) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-4914) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 94 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-60) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-570) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1848) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1362) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-3708) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-7134) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-6048) * coeff (m + 1 + 1 + 1 + 1) G + (-1836) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G T W hT hW hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G T W : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hW : W ^ 2 = 1 - 2 * X ^ 2 - 3 * X ^ 4)
    (hG : (2 * X ^ 2 - 6 * X ^ 4) * G = (2 - 6 * X ^ 2) + (-1 + 3 * X ^ 2) * T + (-1 - X) * W) :
    (-5376) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1890) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      16680 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 11220 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-2328) * coeff (0 + 1 + 1 + 1 + 1) G + (-1866) * coeff (0 + 1 + 1 + 1) G +
      (-2744) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 4368 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      24030 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 8760 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-19284) * coeff (0 + 1 + 1 + 1 + 1) G + (-19200) * coeff (0 + 1 + 1 + 1) G +
      (-10530) * coeff (0 + 1 + 1) G + 736 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      2730 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 2700 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-9270) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-17352) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-23106) * coeff (0 + 1 + 1 + 1) G + (-29028) * coeff (0 + 1 + 1) G +
      (-14346) * coeff (0 + 1) G + 94 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-60) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-570) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1848) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-1362) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-3708) * coeff (0 + 1 + 1 + 1) G + (-7134) * coeff (0 + 1 + 1) G +
      (-6048) * coeff (0 + 1) G + (-1836) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G T W hT hW hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G T W : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hW : W ^ 2 = 1 - 2 * X ^ 2 - 3 * X ^ 4)
    (hG : (2 * X ^ 2 - 6 * X ^ 4) * G = (2 - 6 * X ^ 2) + (-1 + 3 * X ^ 2) * T + (-1 - X) * W) :
    (-8064) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3024) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      29190 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 22440 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-5820) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-7464) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2754) * coeff (0 + 1 + 1 + 1) G + (-3528) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      5824 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 33642 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      13140 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-32140) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-38400) * coeff (0 + 1 + 1 + 1 + 1) G + (-31590) * coeff (0 + 1 + 1 + 1) G +
      (-11340) * coeff (0 + 1 + 1) G + 828 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      3120 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 3150 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-11124) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-21690) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-30808) * coeff (0 + 1 + 1 + 1 + 1) G + (-43542) * coeff (0 + 1 + 1 + 1) G +
      (-28692) * coeff (0 + 1 + 1) G + (-4914) * coeff (0 + 1) G +
      94 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-60) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-570) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1848) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1362) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-3708) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-7134) * coeff (0 + 1 + 1 + 1) G + (-6048) * coeff (0 + 1 + 1) G +
      (-1836) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G T W hT hW hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE2 (G T W : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hW : W ^ 2 = 1 - 2 * X ^ 2 - 3 * X ^ 4)
    (hG : (2 * X ^ 2 - 6 * X ^ 4) * G = (2 - 6 * X ^ 2) + (-1 + 3 * X ^ 2) * T + (-1 - X) * W) :
    (-11520) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-4536) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      46704 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 39270 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-11640) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-18660) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-11016) * coeff (0 + 1 + 1 + 1 + 1) G + (-3042) * coeff (0 + 1 + 1 + 1) G +
      (-4410) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 7488 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      44856 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 18396 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-48210) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-64000) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-63180) * coeff (0 + 1 + 1 + 1 + 1) G + (-34020) * coeff (0 + 1 + 1 + 1) G +
      (-4320) * coeff (0 + 1 + 1) G + 920 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      3510 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 3600 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-12978) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-26028) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-38510) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-58056) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-43038) * coeff (0 + 1 + 1 + 1) G + (-9828) * coeff (0 + 1 + 1) G +
      94 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-60) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-570) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1848) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1362) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3708) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-7134) * coeff (0 + 1 + 1 + 1 + 1) G + (-6048) * coeff (0 + 1 + 1 + 1) G +
      (-1836) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G T W hT hW hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem gen : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
    W ^ 2 = 1 - 2 * X ^ 2 - 3 * X ^ 4 →
    (2 * X ^ 2 - 6 * X ^ 4) * G = (2 - 6 * X ^ 2) + (-1 + 3 * X ^ 2) * T + (-1 - X) * W →
    ∀ n : ℕ, 8 ≤ n →
      (94 + 109 * (n : ℚ) - (n : ℚ) ^ 2 - 16 * (n : ℚ) ^ 3) * coeff n G + (-188 - 21 * (n : ℚ) + 158 * (n : ℚ) ^ 2 - 9 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (59 * (n : ℚ) - 450 * (n : ℚ) ^ 2 + 139 * (n : ℚ) ^ 3) * coeff (n - 2) G + (-2250 + 3869 * (n : ℚ) - 1806 * (n : ℚ) ^ 2 + 187 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-4510 + 2947 * (n : ℚ) - 152 * (n : ℚ) ^ 2 - 97 * (n : ℚ) ^ 3) * coeff (n - 4) G + (4112 - 5779 * (n : ℚ) + 2398 * (n : ℚ) ^ 2 - 311 * (n : ℚ) ^ 3) * coeff (n - 5) G +
        (13044 - 13083 * (n : ℚ) + 4374 * (n : ℚ) ^ 2 - 459 * (n : ℚ) ^ 3) * coeff (n - 6) G + (32382 - 26133 * (n : ℚ) + 6498 * (n : ℚ) ^ 2 - 507 * (n : ℚ) ^ 3) * coeff (n - 7) G +
        (30996 - 18288 * (n : ℚ) + 3429 * (n : ℚ) ^ 2 - 207 * (n : ℚ) ^ 3) * coeff (n - 8) G = 0 := by
  intro T W G hT hW hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 8, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m + 1 := rfl
  have e8 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 8 = m := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  cases m with
  | zero =>
    have r := A290265Aux.relE0 G T W hT hW hG
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A290265Aux.relE1 G T W hT hW hG
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A290265Aux.relE2 G T W hT hW hG
        push_cast
        linear_combination r
      | succ m =>
        have r := A290265Aux.rel G T W hT hW hG m
        push_cast
        linear_combination r

theorem key_coeff (B : ℚ⟦X⟧) (hb0 : coeff 0 B = 1) (k : ℕ) :
    (if 2 ≤ k + 1 then coeff (1 + (k + 1 - 2) / 2) B else 0) =
      (if 2 ∣ k + 1 then coeff ((k + 1) / 2) B else 0) +
        ((if 2 ∣ k then coeff (k / 2) B else 0) - (if k = 0 then 1 else 0)) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rcases j with _ | i
    · simp [hb0]
    · have h1 : ¬ (2 ∣ 2 * (i + 1) + 1) := by omega
      have h2 : 2 ∣ 2 * (i + 1) := ⟨i + 1, rfl⟩
      have h3 : 2 ≤ 2 * (i + 1) + 1 := by omega
      have h4 : 2 * (i + 1) ≠ 0 := by omega
      have h5 : 1 + (2 * (i + 1) + 1 - 2) / 2 = i + 1 := by omega
      have h6 : 2 * (i + 1) / 2 = i + 1 := by omega
      rw [if_pos h3, if_neg h1, if_pos h2, if_neg h4, h5, h6]
      ring
  · have h1 : 2 ∣ 2 * j + 1 + 1 := ⟨j + 1, by ring⟩
    have h2 : ¬ (2 ∣ 2 * j + 1) := by omega
    have h3 : 2 ≤ 2 * j + 1 + 1 := by omega
    have h4 : 2 * j + 1 ≠ 0 := by omega
    have h5 : 1 + (2 * j + 1 + 1 - 2) / 2 = j + 1 := by omega
    have h6 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [if_pos h3, if_pos h1, if_neg h2, if_neg h4, h5, h6]
    ring

set_option maxHeartbeats 4000000 in
theorem wrap (T m B : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2) (hT0 : coeff 0 T = 1)
    (hm : 2 * X ^ 2 * m = 1 - X - T) (hB : 2 * (1 - 3 * X) * B = 1 - 3 * X + T) :
    ∃ W G : ℚ⟦X⟧, W ^ 2 = 1 - 2 * X ^ 2 - 3 * X ^ 4 ∧
      (2 * X ^ 2 - 6 * X ^ 4) * G = (2 - 6 * X ^ 2) + (-1 + 3 * X ^ 2) * T + (-1 - X) * W ∧
      ∀ n, coeff n G = coeff n m - coeff (1 + n / 2) B := by
  have hsq : HasSubst (X ^ 2 : ℚ⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  have hW := congrArg (substAlgHom hsq) hT
  simp only [map_pow, map_sub, map_mul, map_one, map_ofNat, substAlgHom_X] at hW
  have hB2 := congrArg (substAlgHom hsq) hB
  simp only [map_add, map_sub, map_mul, map_one, map_ofNat, substAlgHom_X] at hB2
  rw [coe_substAlgHom hsq] at hW hB2
  have hT0c : constantCoeff T = 1 := by simpa using hT0
  have hb0c : constantCoeff B = 1 := by
    have h := congrArg constantCoeff hB
    have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
    simp only [map_mul, map_sub, map_add, map_one, constantCoeff_X, mul_zero, sub_zero, k2,
      hT0c] at h
    linarith
  have hb0 : coeff 0 B = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    exact hb0c
  have hsubc : ∀ n : ℕ, coeff n (B.subst (X ^ 2 : ℚ⟦X⟧)) =
      if 2 ∣ n then coeff (n / 2) B else 0 := by
    intro n
    rw [coeff_subst_X_pow (two_ne_zero)]
    simp
  have hH : X ^ 2 * (PowerSeries.mk fun n => coeff (1 + n / 2) B) =
      (1 + X) * (B.subst (X ^ 2 : ℚ⟦X⟧) - 1) := by
    ext n
    rcases n with _ | k
    · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, map_mul,
        map_pow, constantCoeff_X, map_add, map_sub, map_one, constantCoeff_X,
        ← coeff_zero_eq_constantCoeff_apply (B.subst (X ^ 2 : ℚ⟦X⟧)), hsubc 0]
      simp [hb0]
    · have h := key_coeff B hb0 k
      simp only [coeff_X_pow_mul', add_mul, one_mul, map_add, coeff_succ_X_mul, map_sub,
        coeff_one, hsubc, coeff_mk, Nat.add_one_ne_zero, ↓reduceIte]
      linarith
  refine ⟨T.subst (X ^ 2 : ℚ⟦X⟧), m - PowerSeries.mk fun n => coeff (1 + n / 2) B, ?_, ?_, ?_⟩
  · linear_combination hW
  · linear_combination (1 - 3 * X ^ 2) * hm - 2 * (1 - 3 * X ^ 2) * hH - (1 + X) * hB2
  · intro n
    rw [map_sub, coeff_mk]

end A290265Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a290265.main := by
  intro T m B hT hT0 hm hB a ha n hn
  obtain ⟨W, G, hW, hG, hc⟩ := A290265Aux.wrap T m B hT hT0 hm hB
  have key := A290265Aux.gen T W G hT hW hG n hn
  have ha' : ∀ k, PowerSeries.coeff k G = a k := fun k => by rw [hc, ha]
  simp only [ha'] at key
  exact key
