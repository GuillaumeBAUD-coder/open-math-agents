import OMAStatements.S_oeis_a138413

-- Problem: A138413: A bisection of A000957.
-- Upstream: formal-conjectures statements/oeis-a138413.lean:0 (declaration OMA.S_oeis_a138413.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Let G(x) = F(x) + F(-x), whose coefficients are 2 a(n) at x^(2n) and 0 at odd powers. With
W = S(-x) = sqrt(1+4x), G is linear in S and W:
(64 - 16 x^2) G = (32 - 32 x^2) + (-16 + 8x) S + (-16 - 8x) W. Differentiating this relation and the
relations 2 (1-4x) DS = -4 S, 2 (1+4x) DW = 4 W for the derivatives of the square roots, and
eliminating the derivatives, shows that the differential operator read off the recurrence (rewritten
for the index m = 2n) maps G to a polynomial; the recurrence is the coefficient of a power of x in
the resulting equation. -/

namespace A138413Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G T W : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 4 * X)
    (hW : W ^ 2 = 1 + 4 * X)
    (hG : (64 - 16 * X ^ 2) * G = (32 - 32 * X ^ 2) + (-16 + 8 * X) * T + (-16 - 8 * X) * W) :
    (56 * X ^ 3 - 910 * X ^ 5 + 224 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-96 * X ^ 2 - 1212 * X ^ 4 + 1632 * X ^ 6) * derivative ℚ (derivative ℚ G) + (492 * X ^ 3 + 2376 * X ^ 5) * derivative ℚ G + (-144 * X ^ 2 + 384 * X ^ 4) * G =
      768 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have ht2 : T * T = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hT
  have hPtd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = (-4) := by
    simp [Derivation.leibniz, d4]
  have httd : derivative ℚ (T * T) = 2 * T * derivative ℚ T := by
    simp [Derivation.leibniz]
    ring
  have hdt : 2 * T * derivative ℚ T = (-4) := by rw [← httd, ht2, hPtd]
  have t1 : 2 * ((1 - 4 * X : ℚ⟦X⟧) * derivative ℚ T) = (-4 : ℚ⟦X⟧) * T := by
    linear_combination T * hdt - 2 * derivative ℚ T * hT
  have hLt2 : derivative ℚ (2 * ((1 - 4 * X : ℚ⟦X⟧) * derivative ℚ T)) =
      2 * (-4) * derivative ℚ T + 2 * (1 - 4 * X) * derivative ℚ (derivative ℚ T) := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hRt2 : derivative ℚ ((-4 : ℚ⟦X⟧) * T) =
      (0) * T + (-4) * derivative ℚ T := by
    simp [Derivation.leibniz, d4]
  have t2 : 2 * (-4) * derivative ℚ T + 2 * (1 - 4 * X) * derivative ℚ (derivative ℚ T) =
      (0) * T + (-4) * derivative ℚ T := by
    rw [← hLt2, ← hRt2, t1]
  have t2p : 2 * ((-4 : ℚ⟦X⟧) * derivative ℚ T) + 2 * ((1 - 4 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T)) = (0 : ℚ⟦X⟧) * T + (-4 : ℚ⟦X⟧) * derivative ℚ T := by linear_combination t2
  have hLt3 : derivative ℚ (2 * ((-4 : ℚ⟦X⟧) * derivative ℚ T) + 2 * ((1 - 4 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T))) =
      2 * (0) * derivative ℚ T + 4 * (-4) * derivative ℚ (derivative ℚ T) + 2 * (1 - 4 * X) * derivative ℚ (derivative ℚ (derivative ℚ T)) := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hRt3 : derivative ℚ ((0 : ℚ⟦X⟧) * T + (-4 : ℚ⟦X⟧) * derivative ℚ T) =
      (0) * T + 2 * (0) * derivative ℚ T + (-4) * derivative ℚ (derivative ℚ T) := by
    simp [Derivation.leibniz, d4]
  have t3 : 2 * (0) * derivative ℚ T + 4 * (-4) * derivative ℚ (derivative ℚ T) + 2 * (1 - 4 * X) * derivative ℚ (derivative ℚ (derivative ℚ T)) =
      (0) * T + 2 * (0) * derivative ℚ T + (-4) * derivative ℚ (derivative ℚ T) := by
    rw [← hLt3, ← hRt3, t2p]
  have hw2 : W * W = (1 + 4 * X : ℚ⟦X⟧) := by linear_combination hW
  have hPwd : derivative ℚ (1 + 4 * X : ℚ⟦X⟧) = (4) := by
    simp [Derivation.leibniz, d4]
  have hwwd : derivative ℚ (W * W) = 2 * W * derivative ℚ W := by
    simp [Derivation.leibniz]
    ring
  have hdw : 2 * W * derivative ℚ W = (4) := by rw [← hwwd, hw2, hPwd]
  have w1 : 2 * ((1 + 4 * X : ℚ⟦X⟧) * derivative ℚ W) = (4 : ℚ⟦X⟧) * W := by
    linear_combination W * hdw - 2 * derivative ℚ W * hW
  have hLw2 : derivative ℚ (2 * ((1 + 4 * X : ℚ⟦X⟧) * derivative ℚ W)) =
      2 * (4) * derivative ℚ W + 2 * (1 + 4 * X) * derivative ℚ (derivative ℚ W) := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hRw2 : derivative ℚ ((4 : ℚ⟦X⟧) * W) =
      (0) * W + (4) * derivative ℚ W := by
    simp [Derivation.leibniz, d4]
  have w2 : 2 * (4) * derivative ℚ W + 2 * (1 + 4 * X) * derivative ℚ (derivative ℚ W) =
      (0) * W + (4) * derivative ℚ W := by
    rw [← hLw2, ← hRw2, w1]
  have w2p : 2 * ((4 : ℚ⟦X⟧) * derivative ℚ W) + 2 * ((1 + 4 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) = (0 : ℚ⟦X⟧) * W + (4 : ℚ⟦X⟧) * derivative ℚ W := by linear_combination w2
  have hLw3 : derivative ℚ (2 * ((4 : ℚ⟦X⟧) * derivative ℚ W) + 2 * ((1 + 4 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W))) =
      2 * (0) * derivative ℚ W + 4 * (4) * derivative ℚ (derivative ℚ W) + 2 * (1 + 4 * X) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hRw3 : derivative ℚ ((0 : ℚ⟦X⟧) * W + (4 : ℚ⟦X⟧) * derivative ℚ W) =
      (0) * W + 2 * (0) * derivative ℚ W + (4) * derivative ℚ (derivative ℚ W) := by
    simp [Derivation.leibniz, d4]
  have w3 : 2 * (0) * derivative ℚ W + 4 * (4) * derivative ℚ (derivative ℚ W) + 2 * (1 + 4 * X) * derivative ℚ (derivative ℚ (derivative ℚ W)) =
      (0) * W + 2 * (0) * derivative ℚ W + (4) * derivative ℚ (derivative ℚ W) := by
    rw [← hLw3, ← hRw3, w2p]
  have e0 : (64 - 16 * (X * X) : ℚ⟦X⟧) * G =
      (32 - 32 * (X * X) : ℚ⟦X⟧) + (-16 + 8 * X : ℚ⟦X⟧) * T + (-16 - 8 * X : ℚ⟦X⟧) * W := by linear_combination hG
  have hLe1 : derivative ℚ ((64 - 16 * (X * X) : ℚ⟦X⟧) * G) =
      (-32 * X) * G + (64 - 16 * X ^ 2) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d64]
    ring
  have hRe1 : derivative ℚ ((32 - 32 * (X * X) : ℚ⟦X⟧) + (-16 + 8 * X : ℚ⟦X⟧) * T + (-16 - 8 * X : ℚ⟦X⟧) * W) =
      (-64 * X) + (8) * T + (-16 + 8 * X) * derivative ℚ T + (-8) * W + (-16 - 8 * X) * derivative ℚ W := by
    simp [Derivation.leibniz, d8, d16, d32]
    ring
  have e1 : (-32 * X) * G + (64 - 16 * X ^ 2) * derivative ℚ G =
      (-64 * X) + (8) * T + (-16 + 8 * X) * derivative ℚ T + (-8) * W + (-16 - 8 * X) * derivative ℚ W := by
    rw [← hLe1, ← hRe1, e0]
  have e1p : (-32 * X : ℚ⟦X⟧) * G + (64 - 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ G =
      (-64 * X : ℚ⟦X⟧) + (8 : ℚ⟦X⟧) * T + (-16 + 8 * X : ℚ⟦X⟧) * derivative ℚ T + (-8 : ℚ⟦X⟧) * W + (-16 - 8 * X : ℚ⟦X⟧) * derivative ℚ W := by linear_combination e1
  have hLe2 : derivative ℚ ((-32 * X : ℚ⟦X⟧) * G + (64 - 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (-32) * G + 2 * (-32 * X) * derivative ℚ G + (64 - 16 * X ^ 2) * derivative ℚ (derivative ℚ G) := by
    simp [Derivation.leibniz, d16, d32, d64]
    ring
  have hRe2 : derivative ℚ ((-64 * X : ℚ⟦X⟧) + (8 : ℚ⟦X⟧) * T + (-16 + 8 * X : ℚ⟦X⟧) * derivative ℚ T + (-8 : ℚ⟦X⟧) * W + (-16 - 8 * X : ℚ⟦X⟧) * derivative ℚ W) =
      (-64) + (0) * T + 2 * (8) * derivative ℚ T + (-16 + 8 * X) * derivative ℚ (derivative ℚ T) + (0) * W + 2 * (-8) * derivative ℚ W + (-16 - 8 * X) * derivative ℚ (derivative ℚ W) := by
    simp [Derivation.leibniz, d8, d16, d64]
    ring
  have e2 : (-32) * G + 2 * (-32 * X) * derivative ℚ G + (64 - 16 * X ^ 2) * derivative ℚ (derivative ℚ G) =
      (-64) + (0) * T + 2 * (8) * derivative ℚ T + (-16 + 8 * X) * derivative ℚ (derivative ℚ T) + (0) * W + 2 * (-8) * derivative ℚ W + (-16 - 8 * X) * derivative ℚ (derivative ℚ W) := by
    rw [← hLe2, ← hRe2, e1p]
  have e2p : (-32 : ℚ⟦X⟧) * G + 2 * ((-32 * X : ℚ⟦X⟧) * derivative ℚ G) + (64 - 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) =
      (-64 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * T + 2 * ((8 : ℚ⟦X⟧) * derivative ℚ T) + (-16 + 8 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T) + (0 : ℚ⟦X⟧) * W + 2 * ((-8 : ℚ⟦X⟧) * derivative ℚ W) + (-16 - 8 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W) := by linear_combination e2
  have hLe3 : derivative ℚ ((-32 : ℚ⟦X⟧) * G + 2 * ((-32 * X : ℚ⟦X⟧) * derivative ℚ G) + (64 - 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) =
      (0) * G + 3 * (-32) * derivative ℚ G + 3 * (-32 * X) * derivative ℚ (derivative ℚ G) + (64 - 16 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2, d16, d32, d64]
    ring
  have hRe3 : derivative ℚ ((-64 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * T + 2 * ((8 : ℚ⟦X⟧) * derivative ℚ T) + (-16 + 8 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T) + (0 : ℚ⟦X⟧) * W + 2 * ((-8 : ℚ⟦X⟧) * derivative ℚ W) + (-16 - 8 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) =
      (0) + (0) * T + 3 * (0) * derivative ℚ T + 3 * (8) * derivative ℚ (derivative ℚ T) + (-16 + 8 * X) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (0) * W + 3 * (0) * derivative ℚ W + 3 * (-8) * derivative ℚ (derivative ℚ W) + (-16 - 8 * X) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by
    simp [Derivation.leibniz, d2, d8, d16, d64]
    ring
  have e3 : (0) * G + 3 * (-32) * derivative ℚ G + 3 * (-32 * X) * derivative ℚ (derivative ℚ G) + (64 - 16 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (0) + (0) * T + 3 * (0) * derivative ℚ T + 3 * (8) * derivative ℚ (derivative ℚ T) + (-16 + 8 * X) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (0) * W + 3 * (0) * derivative ℚ W + 3 * (-8) * derivative ℚ (derivative ℚ W) + (-16 - 8 * X) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by
    rw [← hLe3, ← hRe3, e2p]
  have hfull : (2048 - 100352 * X ^ 2 + 1671936 * X ^ 4 - 9998464 * X ^ 6 + 8984584 * X ^ 8 - 3244416 * X ^ 10 + 530432 * X ^ 12 - 32768 * X ^ 14 : ℚ⟦X⟧) * ((56 * X ^ 3 - 910 * X ^ 5 + 224 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-96 * X ^ 2 - 1212 * X ^ 4 + 1632 * X ^ 6) * derivative ℚ (derivative ℚ G) + (492 * X ^ 3 + 2376 * X ^ 5) * derivative ℚ G + (-144 * X ^ 2 + 384 * X ^ 4) * G - (768 * X ^ 4)) = 0 := by
    linear_combination (1792 * X ^ 3 - 116480 * X ^ 5 + 2867872 * X ^ 7 - 32155760 * X ^ 9 + 147840007 * X ^ 11 - 128623040 * X ^ 13 + 45885952 * X ^ 15 - 7454720 * X ^ 17 + 458752 * X ^ 19) * e3 +
      (-3072 * X ^ 2 + 113664 * X ^ 4 - 701568 * X ^ 6 - 15097152 * X ^ 8 + 166495476 * X ^ 10 - 156855888 * X ^ 12 + 57603840 * X ^ 14 - 9498624 * X ^ 16 + 589824 * X ^ 18) * e2 +
      (15360 * X ^ 3 - 752640 * X ^ 5 + 12539520 * X ^ 7 - 74988480 * X ^ 9 + 67384380 * X ^ 11 - 24333120 * X ^ 13 + 3978240 * X ^ 15 - 245760 * X ^ 17) * e1 +
      (-6144 * X ^ 2 + 301056 * X ^ 4 - 5015808 * X ^ 6 + 29995392 * X ^ 8 - 26953752 * X ^ 10 + 9733248 * X ^ 12 - 1591296 * X ^ 14 + 98304 * X ^ 16) * e0 +
      (-14336 * X ^ 3 - 50176 * X ^ 4 + 731136 * X ^ 5 + 2458624 * X ^ 6 - 13108480 * X ^ 7 - 40962432 * X ^ 8 + 93396352 * X ^ 9 + 244962368 * X ^ 10 - 202870584 * X ^ 11 - 220122308 * X ^ 12 + 148495088 * X ^ 13 + 79488192 * X ^ 14 - 49134848 * X ^ 15 - 12995584 * X ^ 16 + 7655424 * X ^ 17 + 802816 * X ^ 18 - 458752 * X ^ 19) * t3 +
      (24576 * X ^ 2 + 21504 * X ^ 3 - 1124352 * X ^ 4 - 1053696 * X ^ 5 + 16149504 * X ^ 6 + 17555328 * X ^ 7 - 54776064 * X ^ 8 - 104983872 * X ^ 9 - 282125088 * X ^ 10 + 94338132 * X ^ 11 + 311465784 * X ^ 12 - 34066368 * X ^ 13 - 120167040 * X ^ 14 + 5569536 * X ^ 15 + 20293632 * X ^ 16 - 344064 * X ^ 17 - 1277952 * X ^ 18) * t2 +
      (24576 * X ^ 2 + 18432 * X ^ 3 - 1204224 * X ^ 4 - 903168 * X ^ 5 + 20063232 * X ^ 6 + 15047424 * X ^ 7 - 119981568 * X ^ 8 - 89986176 * X ^ 9 + 107815008 * X ^ 10 + 80861256 * X ^ 11 - 38932992 * X ^ 12 - 29199744 * X ^ 13 + 6365184 * X ^ 14 + 4773888 * X ^ 15 - 393216 * X ^ 16 - 294912 * X ^ 17) * t1 +
      (-14336 * X ^ 3 + 50176 * X ^ 4 + 731136 * X ^ 5 - 2458624 * X ^ 6 - 13108480 * X ^ 7 + 40962432 * X ^ 8 + 93396352 * X ^ 9 - 244962368 * X ^ 10 - 202870584 * X ^ 11 + 220122308 * X ^ 12 + 148495088 * X ^ 13 - 79488192 * X ^ 14 - 49134848 * X ^ 15 + 12995584 * X ^ 16 + 7655424 * X ^ 17 - 802816 * X ^ 18 - 458752 * X ^ 19) * w3 +
      (24576 * X ^ 2 - 21504 * X ^ 3 - 1124352 * X ^ 4 + 1053696 * X ^ 5 + 16149504 * X ^ 6 - 17555328 * X ^ 7 - 54776064 * X ^ 8 + 104983872 * X ^ 9 - 282125088 * X ^ 10 - 94338132 * X ^ 11 + 311465784 * X ^ 12 + 34066368 * X ^ 13 - 120167040 * X ^ 14 - 5569536 * X ^ 15 + 20293632 * X ^ 16 + 344064 * X ^ 17 - 1277952 * X ^ 18) * w2 +
      (-24576 * X ^ 2 + 18432 * X ^ 3 + 1204224 * X ^ 4 - 903168 * X ^ 5 - 20063232 * X ^ 6 + 15047424 * X ^ 7 + 119981568 * X ^ 8 - 89986176 * X ^ 9 - 107815008 * X ^ 10 + 80861256 * X ^ 11 + 38932992 * X ^ 12 - 29199744 * X ^ 13 - 6365184 * X ^ 14 + 4773888 * X ^ 15 + 393216 * X ^ 16 - 294912 * X ^ 17) * w1
  have hM0 : (2048 - 100352 * X ^ 2 + 1671936 * X ^ 4 - 9998464 * X ^ 6 + 8984584 * X ^ 8 - 3244416 * X ^ 10 + 530432 * X ^ 12 - 32768 * X ^ 14 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (2048 : ℚ⟦X⟧) = 2048 := cnum 2048
    simp [kc] at h'
  have h := (mul_eq_zero.mp hfull).resolve_left hM0
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G T W : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 4 * X)
    (hW : W ^ 2 = 1 + 4 * X)
    (hG : (64 - 16 * X ^ 2) * G = (32 - 32 * X ^ 2) + (-16 + 8 * X) * T + (-16 - 8 * X) * W) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 56 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-910) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C 224 + derivative ℚ (derivative ℚ G) * X * X * C (-96) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-1212) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 1632 +
      derivative ℚ G * X * X * X * C 492 + derivative ℚ G * X * X * X * X * X * C 2376 +
      G * X * X * C (-144) + G * X * X * X * X * C 384 =
      C 768 * X * X * X * X := by
  have h := key G T W hT hW hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G T W : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 4 * X)
    (hW : W ^ 2 = 1 + 4 * X)
    (hG : (64 - 16 * X ^ 2) * G = (32 - 32 * X ^ 2) + (-16 + 8 * X) * T + (-16 - 8 * X) * W) (m : ℕ) :
    56 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-910) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      224 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + (-96) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1212) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 1632 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      492 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 2376 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-144) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 384 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G T W hT hW hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G T W : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 4 * X)
    (hW : W ^ 2 = 1 + 4 * X)
    (hG : (64 - 16 * X ^ 2) * G = (32 - 32 * X ^ 2) + (-16 + 8 * X) * T + (-16 - 8 * X) * W) :
    3360 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-5460) * coeff (0 + 1 + 1 + 1) G +
      (-1920) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-7272) * coeff (0 + 1 + 1 + 1) G +
      1476 * coeff (0 + 1 + 1 + 1) G + 2376 * coeff (0 + 1) G +
      (-144) * coeff (0 + 1 + 1 + 1) G + 384 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G T W hT hW hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G T W : ℚ⟦X⟧)
    (hT : T ^ 2 = 1 - 4 * X)
    (hW : W ^ 2 = 1 + 4 * X)
    (hG : (64 - 16 * X ^ 2) * G = (32 - 32 * X ^ 2) + (-16 + 8 * X) * T + (-16 - 8 * X) * W) :
    6720 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-21840) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2880) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-14544) * coeff (0 + 1 + 1 + 1 + 1) G +
      3264 * coeff (0 + 1 + 1) G + 1968 * coeff (0 + 1 + 1 + 1 + 1) G +
      4752 * coeff (0 + 1 + 1) G + (-144) * coeff (0 + 1 + 1 + 1 + 1) G +
      384 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G T W hT hW hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem gen : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    W ^ 2 = 1 + 4 * X →
    (64 - 16 * X ^ 2) * G = (32 - 32 * X ^ 2) + (-16 + 8 * X) * T + (-16 - 8 * X) * W →
    ∀ n : ℕ, 5 ≤ n →
      (208 * (n : ℚ) - 264 * (n : ℚ) ^ 2 + 56 * (n : ℚ) ^ 3) * coeff n G + (13440 - 17108 * (n : ℚ) + 6978 * (n : ℚ) ^ 2 - 910 * (n : ℚ) ^ 3) * coeff (n - 2) G +
        (-3360 + 4264 * (n : ℚ) - 1728 * (n : ℚ) ^ 2 + 224 * (n : ℚ) ^ 3) * coeff (n - 4) G = 0 := by
  intro T W G hT hW hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  rw [e2, e4]
  cases m with
  | zero =>
    have r := A138413Aux.relE0 G T W hT hW hG
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A138413Aux.relE1 G T W hT hW hG
      push_cast
      linear_combination r
    | succ m =>
      have r := A138413Aux.rel G T W hT hW hG m
      push_cast
      linear_combination r

end A138413Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a138413.main := by
  intro S F hS _ hF n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have e1' : k + 3 - 1 = k + 2 := rfl
  have e2' : k + 3 - 2 = k + 1 := rfl
  rw [e1', e2']
  have hW : (PowerSeries.rescale (-1 : ℚ) S) ^ 2 = 1 + 4 * PowerSeries.X := by
    have h := congrArg (PowerSeries.rescale (-1 : ℚ)) hS
    simp only [map_pow, map_sub, map_one, map_mul, map_ofNat, PowerSeries.rescale_neg_one_X] at h
    linear_combination h
  have hF2 : PowerSeries.rescale (-1 : ℚ) F * (3 - PowerSeries.rescale (-1 : ℚ) S) =
      1 - PowerSeries.rescale (-1 : ℚ) S := by
    have h := congrArg (PowerSeries.rescale (-1 : ℚ)) hF
    simp only [map_sub, map_one, map_mul, map_ofNat] at h
    exact h
  have hFl : (8 + 4 * PowerSeries.X) * F = (2 + 4 * PowerSeries.X) + (-2) * S := by
    linear_combination (3 + S) * hF + (F - 1) * hS
  have hF2l : (8 - 4 * PowerSeries.X) * PowerSeries.rescale (-1 : ℚ) F =
      (2 - 4 * PowerSeries.X) + (-2) * PowerSeries.rescale (-1 : ℚ) S := by
    linear_combination (3 + PowerSeries.rescale (-1 : ℚ) S) * hF2 +
      (PowerSeries.rescale (-1 : ℚ) F - 1) * hW
  have hG : (64 - 16 * PowerSeries.X ^ 2) * (F + PowerSeries.rescale (-1 : ℚ) F) =
      (32 - 32 * PowerSeries.X ^ 2) + (-16 + 8 * PowerSeries.X) * S +
        (-16 - 8 * PowerSeries.X) * PowerSeries.rescale (-1 : ℚ) S := by
    linear_combination (8 - 4 * PowerSeries.X) * hFl + (8 + 4 * PowerSeries.X) * hF2l
  have c0 : ∀ j : ℕ, PowerSeries.coeff (2 * j) (F + PowerSeries.rescale (-1 : ℚ) F) =
      2 * PowerSeries.coeff (2 * j) F := by
    intro j
    rw [map_add, PowerSeries.coeff_rescale, pow_mul, neg_one_sq, one_pow]
    ring
  have key := A138413Aux.gen S (PowerSeries.rescale (-1 : ℚ) S) (F + PowerSeries.rescale (-1 : ℚ) F)
    hS hW hG (2 * (k + 3)) (by omega)
  have e1 : 2 * (k + 3) - 2 = 2 * (k + 2) := by omega
  have e2 : 2 * (k + 3) - 4 = 2 * (k + 1) := by omega
  rw [e1, e2, c0, c0, c0] at key
  push_cast at key ⊢
  linear_combination (1 / 16 : ℚ) * key
