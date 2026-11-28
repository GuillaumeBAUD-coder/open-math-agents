import OMAStatements.S_oeis_a168452

namespace OMA.P168452

open PowerSeries OMA.S_oeis_a168452

lemma cat_rec (k : ℕ) :
    ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) = 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
  have h1 := congrArg (Nat.cast : ℕ → ℤ) (succ_mul_catalan_eq_centralBinom (k + 1))
  have h2 := congrArg (Nat.cast : ℕ → ℤ) (Nat.succ_mul_centralBinom_succ k)
  have h3 := congrArg (Nat.cast : ℕ → ℤ) (succ_mul_catalan_eq_centralBinom k)
  push_cast at h1 h2 h3
  have key : ((k : ℤ) + 1)
      * (((k : ℤ) + 2) * (catalan (k + 1) : ℤ) - 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ)) = 0 := by
    linear_combination ((k : ℤ) + 1) * h1 + h2 - 2 * (2 * (k : ℤ) + 1) * h3
  have hne : ((k : ℤ) + 1) ≠ 0 := by positivity
  have h4 := (mul_eq_zero.mp key).resolve_left hne
  linarith

lemma c_rec (k : ℕ) :
    ((k : ℤ) + 2) * ((k : ℤ) + 3) * c (k + 1)
      = 4 * (2 * (k : ℤ) + 1) * (2 * (k : ℤ) + 3) * c k := by
  have h1 := cat_rec k
  have h2 := cat_rec (k + 1)
  push_cast at h2
  unfold c
  linear_combination (((k : ℤ) + 3) * (catalan (k + 1 + 1) : ℤ)) * h1
    + (2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ)) * h2

/-- The operator `x * d/dx`. -/
noncomputable def th (H : ℤ⟦X⟧) : ℤ⟦X⟧ := X * d⁄dX ℤ H

lemma cth (H : ℤ⟦X⟧) (k : ℕ) : coeff k (th H) = (k : ℤ) * coeff k H := by
  unfold th
  cases k with
  | zero => simp
  | succ j =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

lemma th_add (A B : ℤ⟦X⟧) : th (A + B) = th A + th B := by
  unfold th
  rw [map_add]
  ring

lemma th_mul (A B : ℤ⟦X⟧) : th (A * B) = th A * B + A * th B := by
  unfold th
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- The generating function of A005568. -/
noncomputable def F0 : ℤ⟦X⟧ := PowerSeries.mk c

/-- `F1 = th F0`. -/
noncomputable def F1 : ℤ⟦X⟧ := th F0

/-- `F2 = th F1`. -/
noncomputable def F2 : ℤ⟦X⟧ := th F1

/-- `F3 = th F2`. -/
noncomputable def F3 : ℤ⟦X⟧ := th F2

/-- `F4 = th F3`. -/
noncomputable def F4 : ℤ⟦X⟧ := th F3

/-- `F5 = th F4`. -/
noncomputable def F5 : ℤ⟦X⟧ := th F4

lemma cF0 (k : ℕ) : coeff k F0 = c k := by
  unfold F0
  rw [coeff_mk]

lemma cF1 (k : ℕ) : coeff k F1 = (k : ℤ) * c k := by
  unfold F1
  rw [cth, cF0]

lemma cF2 (k : ℕ) : coeff k F2 = (k : ℤ) ^ 2 * c k := by
  unfold F2
  rw [cth, cF1]
  ring

lemma cF3 (k : ℕ) : coeff k F3 = (k : ℤ) ^ 3 * c k := by
  unfold F3
  rw [cth, cF2]
  ring

lemma cF4 (k : ℕ) : coeff k F4 = (k : ℤ) ^ 4 * c k := by
  unfold F4
  rw [cth, cF3]
  ring

lemma cF5 (k : ℕ) : coeff k F5 = (k : ℤ) ^ 5 * c k := by
  unfold F5
  rw [cth, cF4]
  ring

lemma thF0 : th F0 = F1 := rfl

lemma thF1 : th F1 = F2 := rfl

lemma thF2 : th F2 = F3 := rfl

lemma thF3 : th F3 = F4 := rfl

lemma thF4 : th F4 = F5 := rfl

lemma c_zero : c 0 = 1 := by
  simp [c]

lemma EC0 : F2 + C (3 : ℤ) * F1 + C (2 : ℤ) * F0
    = C (2 : ℤ) + X * (C (12 : ℤ) * F0 + C (32 : ℤ) * F1 + C (16 : ℤ) * F2) := by
  ext j
  cases j with
  | zero =>
    simp only [map_add, coeff_C_mul, coeff_zero_X_mul, cF0, cF1, cF2, cF3, cF4, cF5,
      coeff_C, c_zero]
    simp
  | succ i =>
    simp only [map_add, coeff_C_mul, coeff_succ_X_mul, cF0, cF1, cF2, cF3, cF4, cF5,
      coeff_C, Nat.add_one_ne_zero, if_false]
    have h := c_rec i
    push_cast
    linear_combination (((i : ℤ) + 1) ^ 0) * h

lemma E0 : F2 + 3 * F1 + 2 * F0
    = 2 + X * (12 * F0 + 32 * F1 + 16 * F2) := by
  have h := EC0
  simp only [map_ofNat] at h
  exact h

lemma EC1 : F3 + C (3 : ℤ) * F2 + C (2 : ℤ) * F1
    = X * (C (12 : ℤ) * F0 + C (44 : ℤ) * F1 + C (48 : ℤ) * F2 + C (16 : ℤ) * F3) := by
  ext j
  cases j with
  | zero =>
    simp only [map_add, coeff_C_mul, coeff_zero_X_mul, cF0, cF1, cF2, cF3, cF4, cF5,
      coeff_C, c_zero]
    simp
  | succ i =>
    simp only [map_add, coeff_C_mul, coeff_succ_X_mul, cF0, cF1, cF2, cF3, cF4, cF5,
      coeff_C, Nat.add_one_ne_zero, if_false]
    have h := c_rec i
    push_cast
    linear_combination (((i : ℤ) + 1) ^ 1) * h

lemma E1 : F3 + 3 * F2 + 2 * F1
    = X * (12 * F0 + 44 * F1 + 48 * F2 + 16 * F3) := by
  have h := EC1
  simp only [map_ofNat] at h
  exact h

lemma EC2 : F4 + C (3 : ℤ) * F3 + C (2 : ℤ) * F2
    = X * (C (12 : ℤ) * F0 + C (56 : ℤ) * F1 + C (92 : ℤ) * F2 + C (64 : ℤ) * F3 + C (16 : ℤ)
        * F4) := by
  ext j
  cases j with
  | zero =>
    simp only [map_add, coeff_C_mul, coeff_zero_X_mul, cF0, cF1, cF2, cF3, cF4, cF5,
      coeff_C, c_zero]
    simp
  | succ i =>
    simp only [map_add, coeff_C_mul, coeff_succ_X_mul, cF0, cF1, cF2, cF3, cF4, cF5,
      coeff_C, Nat.add_one_ne_zero, if_false]
    have h := c_rec i
    push_cast
    linear_combination (((i : ℤ) + 1) ^ 2) * h

lemma E2 : F4 + 3 * F3 + 2 * F2
    = X * (12 * F0 + 56 * F1 + 92 * F2 + 64 * F3 + 16 * F4) := by
  have h := EC2
  simp only [map_ofNat] at h
  exact h

lemma EC3 : F5 + C (3 : ℤ) * F4 + C (2 : ℤ) * F3
    = X * (C (12 : ℤ) * F0 + C (68 : ℤ) * F1 + C (148 : ℤ) * F2 + C (156 : ℤ) * F3 + C (80 : ℤ)
        * F4 + C (16 : ℤ) * F5) := by
  ext j
  cases j with
  | zero =>
    simp only [map_add, coeff_C_mul, coeff_zero_X_mul, cF0, cF1, cF2, cF3, cF4, cF5,
      coeff_C, c_zero]
    simp
  | succ i =>
    simp only [map_add, coeff_C_mul, coeff_succ_X_mul, cF0, cF1, cF2, cF3, cF4, cF5,
      coeff_C, Nat.add_one_ne_zero, if_false]
    have h := c_rec i
    push_cast
    linear_combination (((i : ℤ) + 1) ^ 3) * h

lemma E3 : F5 + 3 * F4 + 2 * F3
    = X * (12 * F0 + 68 * F1 + 148 * F2 + 156 * F3 + 80 * F4 + 16 * F5) := by
  have h := EC3
  simp only [map_ofNat] at h
  exact h

/-- The generating function of the self-convolution. -/
noncomputable def T0 : ℤ⟦X⟧ := F0 * F0

/-- `T1 = th T0`. -/
noncomputable def T1 : ℤ⟦X⟧ := th T0

/-- `T2 = th T1`. -/
noncomputable def T2 : ℤ⟦X⟧ := th T1

/-- `T3 = th T2`. -/
noncomputable def T3 : ℤ⟦X⟧ := th T2

/-- `T4 = th T3`. -/
noncomputable def T4 : ℤ⟦X⟧ := th T3

/-- `T5 = th T4`. -/
noncomputable def T5 : ℤ⟦X⟧ := th T4

lemma cT0 (k : ℕ) : coeff k T0 = a k := by
  unfold T0 F0 a
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk] <;> rfl

lemma cT1 (k : ℕ) : coeff k T1 = (k : ℤ) * a k := by
  unfold T1
  rw [cth, cT0]

lemma cT2 (k : ℕ) : coeff k T2 = (k : ℤ) ^ 2 * a k := by
  unfold T2
  rw [cth, cT1]
  ring

lemma cT3 (k : ℕ) : coeff k T3 = (k : ℤ) ^ 3 * a k := by
  unfold T3
  rw [cth, cT2]
  ring

lemma cT4 (k : ℕ) : coeff k T4 = (k : ℤ) ^ 4 * a k := by
  unfold T4
  rw [cth, cT3]
  ring

lemma cT5 (k : ℕ) : coeff k T5 = (k : ℤ) ^ 5 * a k := by
  unfold T5
  rw [cth, cT4]
  ring

lemma hT1 : T1 = F1 * F0 + F0 * F1 := by
  unfold T1
  unfold T0
  simp only [th_add, th_mul, thF0, thF1, thF2, thF3, thF4] <;> ring

lemma hT2 : T2 = F2 * F0 + F1 * F1 + F1 * F1 + F0 * F2 := by
  unfold T2
  rw [hT1]
  simp only [th_add, th_mul, thF0, thF1, thF2, thF3, thF4] <;> ring

lemma hT3 : T3 = F3 * F0 + F2 * F1 + F2 * F1 + F1 * F2 + F2 * F1 + F1 * F2 + F1 * F2 + F0 * F3 := by
  unfold T3
  rw [hT2]
  simp only [th_add, th_mul, thF0, thF1, thF2, thF3, thF4] <;> ring

lemma hT4 : T4 = F4 * F0 + F3 * F1 + F3 * F1 + F2 * F2 + F3 * F1 + F2 * F2 + F2 * F2 + F1 * F3
    + F3 * F1 + F2 * F2 + F2 * F2 + F1 * F3 + F2 * F2 + F1 * F3 + F1 * F3 + F0 * F4 := by
  unfold T4
  rw [hT3]
  simp only [th_add, th_mul, thF0, thF1, thF2, thF3, thF4] <;> ring

lemma hT5 : T5 = F5 * F0 + F4 * F1 + F4 * F1 + F3 * F2 + F4 * F1 + F3 * F2 + F3 * F2 + F2 * F3
    + F4 * F1 + F3 * F2 + F3 * F2 + F2 * F3 + F3 * F2 + F2 * F3 + F2 * F3 + F1 * F4 + F4 * F1
    + F3 * F2 + F3 * F2 + F2 * F3 + F3 * F2 + F2 * F3 + F2 * F3 + F1 * F4 + F3 * F2 + F2 * F3
    + F2 * F3 + F1 * F4 + F2 * F3 + F1 * F4 + F1 * F4 + F0 * F5 := by
  unfold T5
  rw [hT4]
  simp only [th_add, th_mul, thF0, thF1, thF2, thF3, thF4] <;> ring

lemma Zne : (1 - 16 * X : ℤ⟦X⟧) ≠ 0 := by
  intro h
  have h2 := congrArg constantCoeff h
  simp at h2

set_option maxHeartbeats 1600000 in
lemma ode_ring :
    ((72) * X ^ 0 + (-4032) * X ^ 1 + (61728) * X ^ 2 + (-207360) * X ^ 3 + (-1474560) * X ^ 4) * T0
      + ((222) * X ^ 0 + (-11304) * X ^ 1 + (168192) * X ^ 2 + (-463872) * X ^ 3 + (-4276224)
          * X ^ 4) * T1
      + ((255) * X ^ 0 + (-11980) * X ^ 1 + (167424) * X ^ 2 + (-359424) * X ^ 3 + (-4751360)
          * X ^ 4) * T2
      + ((135) * X ^ 0 + (-6004) * X ^ 1 + (78528) * X ^ 2 + (-113664) * X ^ 3 + (-2539520)
          * X ^ 4) * T3
      + ((33) * X ^ 0 + (-1424) * X ^ 1 + (17664) * X ^ 2 + (-12288) * X ^ 3 + (-655360)
          * X ^ 4) * T4
      + ((3) * X ^ 0 + (-128) * X ^ 1 + (1536) * X ^ 2 + (-65536) * X ^ 4) * T5
      = ((72) * X ^ 0 + (-1152) * X ^ 1) := by
  have hZ : (1 - 16 * X : ℤ⟦X⟧) ^ 5 * ((((72) * X ^ 0 + (-4032) * X ^ 1 + (61728) * X ^ 2
      + (-207360) * X ^ 3 + (-1474560) * X ^ 4) * T0
      + ((222) * X ^ 0 + (-11304) * X ^ 1 + (168192) * X ^ 2 + (-463872) * X ^ 3 + (-4276224)
          * X ^ 4) * T1
      + ((255) * X ^ 0 + (-11980) * X ^ 1 + (167424) * X ^ 2 + (-359424) * X ^ 3 + (-4751360)
          * X ^ 4) * T2
      + ((135) * X ^ 0 + (-6004) * X ^ 1 + (78528) * X ^ 2 + (-113664) * X ^ 3 + (-2539520)
          * X ^ 4) * T3
      + ((33) * X ^ 0 + (-1424) * X ^ 1 + (17664) * X ^ 2 + (-12288) * X ^ 3 + (-655360)
          * X ^ 4) * T4
      + ((3) * X ^ 0 + (-128) * X ^ 1 + (1536) * X ^ 2 + (-65536) * X ^ 4) * T5)
      - ((72) * X ^ 0 + (-1152) * X ^ 1)) = 0 := by
    rw [hT1, hT2, hT3, hT4, hT5]
    unfold T0
    linear_combination (-3623878656*F0*X^7 + 1962934272*F0*X^6 - 438829056*F0*X^5
        + 53084160*F0*X^4 - 3778560*F0*X^3 + 158976*F0*X^2 - 3672*F0*X + 36*F0
        - 9663676416*F1*X^7 + 4529848320*F1*X^6 - 905969664*F1*X^5 + 100270080*F1*X^4
        - 6635520*F1*X^3 + 262656*F1*X^2 - 5760*F1*X + 54*F1 - 4831838208*F2*X^7
        + 2113929216*F2*X^6 - 396361728*F2*X^5 + 41287680*F2*X^4 - 2580480*F2*X^3 + 96768*F2*X^2
        - 2016*F2*X + 18*F2 + 603979776*X^6 - 226492416*X^5 + 35389440*X^4 - 2949120*X^3
        + 138240*X^2 - 3456*X + 36) * E0
      + (-77309411328*F0*X^8 + 13421772800*F0*X^7 + 2952790016*F0*X^6 - 1168113664*F0*X^5
          + 159907840*F0*X^4 - 11804672*F0*X^3 + 501760*F0*X^2 - 11616*F0*X + 114*F0
          - 171798691840*F1*X^8 + 39191576576*F1*X^7 + 2315255808*F1*X^6 - 1734344704*F1*X^5
          + 254935040*F1*X^4 - 19046400*F1*X^3 + 802304*F1*X^2 - 18208*F1*X + 174*F1
          - 85899345920*F2*X^8 + 21474836480*F2*X^7 - 587202560*F2*X^5 + 91750400*F2*X^4
          - 6881280*F2*X^3 + 286720*F2*X^2 - 6400*F2*X + 60*F2) * E1
      + (-42949672960*F0*X^8 + 10200547328*F0*X^7 + 503316480*F0*X^6 - 438304768*F0*X^5
          + 66191360*F0*X^4 - 5038080*F0*X^3 + 215552*F0*X^2 - 4960*F0*X + 48*F0
          - 42949672960*F1*X^8 + 10737418240*F1*X^7 - 293601280*F1*X^5 + 45875200*F1*X^4
          - 3440640*F1*X^3 + 143360*F1*X^2 - 3200*F1*X + 30*F1) * E2
      + (-8589934592*F0*X^8 + 2147483648*F0*X^7 - 58720256*F0*X^5 + 9175040*F0*X^4
          - 688128*F0*X^3 + 28672*F0*X^2 - 640*F0*X + 6*F0) * E3
  have h := (mul_eq_zero.mp hZ).resolve_left (pow_ne_zero _ Zne)
  exact sub_eq_zero.mp h

lemma ode :
    C (72 : ℤ) * T0
      + C (-4032 : ℤ) * (X * T0)
      + C (61728 : ℤ) * (X * (X * T0))
      + C (-207360 : ℤ) * (X * (X * (X * T0)))
      + C (-1474560 : ℤ) * (X * (X * (X * (X * T0))))
      + C (222 : ℤ) * T1
      + C (-11304 : ℤ) * (X * T1)
      + C (168192 : ℤ) * (X * (X * T1))
      + C (-463872 : ℤ) * (X * (X * (X * T1)))
      + C (-4276224 : ℤ) * (X * (X * (X * (X * T1))))
      + C (255 : ℤ) * T2
      + C (-11980 : ℤ) * (X * T2)
      + C (167424 : ℤ) * (X * (X * T2))
      + C (-359424 : ℤ) * (X * (X * (X * T2)))
      + C (-4751360 : ℤ) * (X * (X * (X * (X * T2))))
      + C (135 : ℤ) * T3
      + C (-6004 : ℤ) * (X * T3)
      + C (78528 : ℤ) * (X * (X * T3))
      + C (-113664 : ℤ) * (X * (X * (X * T3)))
      + C (-2539520 : ℤ) * (X * (X * (X * (X * T3))))
      + C (33 : ℤ) * T4
      + C (-1424 : ℤ) * (X * T4)
      + C (17664 : ℤ) * (X * (X * T4))
      + C (-12288 : ℤ) * (X * (X * (X * T4)))
      + C (-655360 : ℤ) * (X * (X * (X * (X * T4))))
      + C (3 : ℤ) * T5
      + C (-128 : ℤ) * (X * T5)
      + C (1536 : ℤ) * (X * (X * T5))
      + C (-65536 : ℤ) * (X * (X * (X * (X * T5))))
      = C (72 : ℤ) * X ^ 0 + C (-1152 : ℤ) * X ^ 1 := by
  simp only [map_neg, map_ofNat, map_one]
  linear_combination ode_ring

lemma rec_raw (m : ℕ) :
    coeff (m + 4) (C (72 : ℤ) * T0
      + C (-4032 : ℤ) * (X * T0)
      + C (61728 : ℤ) * (X * (X * T0))
      + C (-207360 : ℤ) * (X * (X * (X * T0)))
      + C (-1474560 : ℤ) * (X * (X * (X * (X * T0))))
      + C (222 : ℤ) * T1
      + C (-11304 : ℤ) * (X * T1)
      + C (168192 : ℤ) * (X * (X * T1))
      + C (-463872 : ℤ) * (X * (X * (X * T1)))
      + C (-4276224 : ℤ) * (X * (X * (X * (X * T1))))
      + C (255 : ℤ) * T2
      + C (-11980 : ℤ) * (X * T2)
      + C (167424 : ℤ) * (X * (X * T2))
      + C (-359424 : ℤ) * (X * (X * (X * T2)))
      + C (-4751360 : ℤ) * (X * (X * (X * (X * T2))))
      + C (135 : ℤ) * T3
      + C (-6004 : ℤ) * (X * T3)
      + C (78528 : ℤ) * (X * (X * T3))
      + C (-113664 : ℤ) * (X * (X * (X * T3)))
      + C (-2539520 : ℤ) * (X * (X * (X * (X * T3))))
      + C (33 : ℤ) * T4
      + C (-1424 : ℤ) * (X * T4)
      + C (17664 : ℤ) * (X * (X * T4))
      + C (-12288 : ℤ) * (X * (X * (X * T4)))
      + C (-655360 : ℤ) * (X * (X * (X * (X * T4))))
      + C (3 : ℤ) * T5
      + C (-128 : ℤ) * (X * T5)
      + C (1536 : ℤ) * (X * (X * T5))
      + C (-65536 : ℤ) * (X * (X * (X * (X * T5))))) = 0 := by
  rw [ode]
  simp only [map_add, coeff_C_mul, coeff_X_pow]
  simp

lemma rec (m : ℕ) :
    3 * (((m : ℤ) + 4) + 4) * (((m : ℤ) + 4) + 3) * (((m : ℤ) + 4) + 2) * (((m : ℤ) + 4)
        + 1) ^ 2 * a (m + 4)
      - 4 * ((m : ℤ) + 4) * (((m : ℤ) + 4) + 1) * (32 * ((m : ℤ) + 4) ^ 3 + 164 * ((m : ℤ)
          + 4) ^ 2 + 233 * ((m : ℤ) + 4) + 75) * a (m + 3)
      + 96 * (16 * ((m : ℤ) + 4) ^ 5 + 24 * ((m : ℤ) + 4) ^ 4 - 14 * ((m : ℤ) + 4) ^ 3 - 28
          * ((m : ℤ) + 4) ^ 2 - 16 * ((m : ℤ) + 4) + 3) * a (m + 2)
      + 1536 * (-8 * ((m : ℤ) + 4) ^ 4 + 22 * ((m : ℤ) + 4) ^ 3 - 32 * ((m : ℤ) + 4) + 15)
          * a (m + 1)
      - 16384 * (2 * ((m : ℤ) + 4) - 5) * (((m : ℤ) + 4) - 1) * (((m : ℤ) + 4) - 2) * (((m : ℤ)
          + 4) - 3) * (2 * ((m : ℤ) + 4) - 3) * a m = 0 := by
  have h := rec_raw m
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, cT0, cT1, cT2, cT3, cT4, cT5] at h
  push_cast at h
  linear_combination h

end OMA.P168452

open OMA.S_oeis_a168452 OMA.P168452 in
theorem OMA.solution : type_of% @OMA.S_oeis_a168452.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e2 : m + 4 - 2 = m + 2 := by omega
  have e3 : m + 4 - 3 = m + 1 := by omega
  have e4 : m + 4 - 4 = m := by omega
  rw [e1, e2, e3, e4]
  have h := rec m
  push_cast
  linear_combination h
