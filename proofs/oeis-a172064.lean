import OMAStatements.S_oeis_a172064

-- Problem: A172064: Expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=7.
-- Upstream: formal-conjectures statements/oeis-a172064.lean:0 (declaration OMA.S_oeis_a172064.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A172064Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-128 * X ^ 7 + 512 * X ^ 8 + (384 * X ^ 7) * S) = 128 - 896 * X + 1792 * X ^ 2 - 896 * X ^ 3 + (-128 + 640 * X - 768 * X ^ 2 + 128 * X ^ 3) * S) :
    (8589934592 * X - 81604378624 * X ^ 2 + 231928233984 * X ^ 3 - 120259084288 * X ^ 4 - 214748364800 * X ^ 5 + 25769803776 * X ^ 6 + 34359738368 * X ^ 7) * derivative ℚ G + (60129542144 - 532575944704 * X + 1357209665536 * X ^ 2 - 463856467968 * X ^ 3 - 1211180777472 * X ^ 4 + 17179869184 * X ^ 5 + 154618822656 * X ^ 6) * G = 60129542144 + 17179869184 * X := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d32768 : derivative ℚ (32768 : ℚ⟦X⟧) = 0 := dnum 32768
  have d65536 : derivative ℚ (65536 : ℚ⟦X⟧) = 0 := dnum 65536
  have d131072 : derivative ℚ (131072 : ℚ⟦X⟧) = 0 := dnum 131072
  have d196608 : derivative ℚ (196608 : ℚ⟦X⟧) = 0 := dnum 196608
  have d262144 : derivative ℚ (262144 : ℚ⟦X⟧) = 0 := dnum 262144
  have d458752 : derivative ℚ (458752 : ℚ⟦X⟧) = 0 := dnum 458752
  have d589824 : derivative ℚ (589824 : ℚ⟦X⟧) = 0 := dnum 589824
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-131072 * X ^ 14 + 458752 * X ^ 15 + 262144 * X ^ 16) * G = (32768 * X ^ 7 - 262144 * X ^ 8 + 589824 * X ^ 9 - 196608 * X ^ 10 - 262144 * X ^ 11 : ℚ⟦X⟧) + (-32768 * X ^ 7 + 196608 * X ^ 8 - 262144 * X ^ 9 - 65536 * X ^ 10 + 65536 * X ^ 11) * S := by
    linear_combination (-128 * X ^ 7 + 512 * X ^ 8 - (384 * X ^ 7) * S) * hG + (384 * X ^ 7) * ((384 * X ^ 7) * G - (-128 + 640 * X - 768 * X ^ 2 + 128 * X ^ 3)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-131072 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 458752 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 262144 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-1835008 * X ^ 13 + 6881280 * X ^ 14 + 4194304 * X ^ 15) * G + (-131072 * X ^ 14 + 458752 * X ^ 15 + 262144 * X ^ 16) * derivative ℚ G := by
    simp [Derivation.leibniz, d131072, d262144, d458752]
    ring
  have hR : derivative ℚ ((32768 * (X * X * X * X * X * X * X) - 262144 * (X * X * X * X * X * X * X * X) + 589824 * (X * X * X * X * X * X * X * X * X) - 196608 * (X * X * X * X * X * X * X * X * X * X) - 262144 * (X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-32768 * (X * X * X * X * X * X * X) + 196608 * (X * X * X * X * X * X * X * X) - 262144 * (X * X * X * X * X * X * X * X * X) - 65536 * (X * X * X * X * X * X * X * X * X * X) + 65536 * (X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      229376 * X ^ 6 - 2097152 * X ^ 7 + 5308416 * X ^ 8 - 1966080 * X ^ 9 - 2883584 * X ^ 10 + (-229376 * X ^ 6 + 1572864 * X ^ 7 - 2359296 * X ^ 8 - 655360 * X ^ 9 + 720896 * X ^ 10) * S + (-32768 * X ^ 7 + 196608 * X ^ 8 - 262144 * X ^ 9 - 65536 * X ^ 10 + 65536 * X ^ 11) * derivative ℚ S := by
    simp [Derivation.leibniz, d32768, d65536, d196608, d262144, d589824]
    ring
  have hk2 : (-131072 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 458752 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 262144 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (32768 * (X * X * X * X * X * X * X) - 262144 * (X * X * X * X * X * X * X * X) + 589824 * (X * X * X * X * X * X * X * X * X) - 196608 * (X * X * X * X * X * X * X * X * X * X) - 262144 * (X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-32768 * (X * X * X * X * X * X * X) + 196608 * (X * X * X * X * X * X * X * X) - 262144 * (X * X * X * X * X * X * X * X * X) - 65536 * (X * X * X * X * X * X * X * X * X * X) + 65536 * (X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-1835008 * X ^ 13 + 6881280 * X ^ 14 + 4194304 * X ^ 15) * G + (-131072 * X ^ 14 + 458752 * X ^ 15 + 262144 * X ^ 16) * derivative ℚ G =
      229376 * X ^ 6 - 2097152 * X ^ 7 + 5308416 * X ^ 8 - 1966080 * X ^ 9 - 2883584 * X ^ 10 + (-229376 * X ^ 6 + 1572864 * X ^ 7 - 2359296 * X ^ 8 - 655360 * X ^ 9 + 720896 * X ^ 10) * S + (-32768 * X ^ 7 + 196608 * X ^ 8 - 262144 * X ^ 9 - 65536 * X ^ 10 + 65536 * X ^ 11) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 20 * ((1 - 4 * X) * ((8589934592 * X - 81604378624 * X ^ 2 + 231928233984 * X ^ 3 - 120259084288 * X ^ 4 - 214748364800 * X ^ 5 + 25769803776 * X ^ 6 + 34359738368 * X ^ 7) * derivative ℚ G + (60129542144 - 532575944704 * X + 1357209665536 * X ^ 2 - 463856467968 * X ^ 3 - 1211180777472 * X ^ 4 + 17179869184 * X ^ 5 + 154618822656 * X ^ 6) * G - (60129542144 + 17179869184 * X))) = 0 := by
    linear_combination (-32768 * X ^ 7 + 196608 * X ^ 8 - 262144 * X ^ 9 - 65536 * X ^ 10 + 65536 * X ^ 11) ^ 2 * S * hdS - 2 * (-32768 * X ^ 7 + 196608 * X ^ 8 - 262144 * X ^ 9 - 65536 * X ^ 10 + 65536 * X ^ 11) ^ 2 * derivative ℚ S * hS -
      (2 * (-229376 * X ^ 6 + 1572864 * X ^ 7 - 2359296 * X ^ 8 - 655360 * X ^ 9 + 720896 * X ^ 10) * (1 - 4 * X) + (-32768 * X ^ 7 + 196608 * X ^ 8 - 262144 * X ^ 9 - 65536 * X ^ 10 + 65536 * X ^ 11) * (-4)) * hk + 2 * (-32768 * X ^ 7 + 196608 * X ^ 8 - 262144 * X ^ 9 - 65536 * X ^ 10 + 65536 * X ^ 11) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 20 ≠ 0 := pow_ne_zero 20 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-128 * X ^ 7 + 512 * X ^ 8 + (384 * X ^ 7) * S) = 128 - 896 * X + 1792 * X ^ 2 - 896 * X ^ 3 + (-128 + 640 * X - 768 * X ^ 2 + 128 * X ^ 3) * S) :
    (6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (82 * X ^ 2 - 338 * X ^ 3 - 230 * X ^ 4) * derivative ℚ (derivative ℚ G) + (224 * X - 1502 * X ^ 2 - 1236 * X ^ 3) * derivative ℚ G + (-1792 * X - 1800 * X ^ 2) * G =
      0 := by
  have h := key S G hS hG
  have d8589934592 : derivative ℚ (8589934592 : ℚ⟦X⟧) = 0 := dnum 8589934592
  have d17179869184 : derivative ℚ (17179869184 : ℚ⟦X⟧) = 0 := dnum 17179869184
  have d25769803776 : derivative ℚ (25769803776 : ℚ⟦X⟧) = 0 := dnum 25769803776
  have d34359738368 : derivative ℚ (34359738368 : ℚ⟦X⟧) = 0 := dnum 34359738368
  have d60129542144 : derivative ℚ (60129542144 : ℚ⟦X⟧) = 0 := dnum 60129542144
  have d81604378624 : derivative ℚ (81604378624 : ℚ⟦X⟧) = 0 := dnum 81604378624
  have d85899345920 : derivative ℚ (85899345920 : ℚ⟦X⟧) = 0 := dnum 85899345920
  have d120259084288 : derivative ℚ (120259084288 : ℚ⟦X⟧) = 0 := dnum 120259084288
  have d154618822656 : derivative ℚ (154618822656 : ℚ⟦X⟧) = 0 := dnum 154618822656
  have d163208757248 : derivative ℚ (163208757248 : ℚ⟦X⟧) = 0 := dnum 163208757248
  have d214748364800 : derivative ℚ (214748364800 : ℚ⟦X⟧) = 0 := dnum 214748364800
  have d231928233984 : derivative ℚ (231928233984 : ℚ⟦X⟧) = 0 := dnum 231928233984
  have d240518168576 : derivative ℚ (240518168576 : ℚ⟦X⟧) = 0 := dnum 240518168576
  have d463856467968 : derivative ℚ (463856467968 : ℚ⟦X⟧) = 0 := dnum 463856467968
  have d481036337152 : derivative ℚ (481036337152 : ℚ⟦X⟧) = 0 := dnum 481036337152
  have d532575944704 : derivative ℚ (532575944704 : ℚ⟦X⟧) = 0 := dnum 532575944704
  have d695784701952 : derivative ℚ (695784701952 : ℚ⟦X⟧) = 0 := dnum 695784701952
  have d927712935936 : derivative ℚ (927712935936 : ℚ⟦X⟧) = 0 := dnum 927712935936
  have d1073741824000 : derivative ℚ (1073741824000 : ℚ⟦X⟧) = 0 := dnum 1073741824000
  have d1211180777472 : derivative ℚ (1211180777472 : ℚ⟦X⟧) = 0 := dnum 1211180777472
  have d1357209665536 : derivative ℚ (1357209665536 : ℚ⟦X⟧) = 0 := dnum 1357209665536
  have d1391569403904 : derivative ℚ (1391569403904 : ℚ⟦X⟧) = 0 := dnum 1391569403904
  have d2714419331072 : derivative ℚ (2714419331072 : ℚ⟦X⟧) = 0 := dnum 2714419331072
  have d4844723109888 : derivative ℚ (4844723109888 : ℚ⟦X⟧) = 0 := dnum 4844723109888
  have hL : derivative ℚ ((8589934592 * X - 81604378624 * (X * X) + 231928233984 * (X * X * X) - 120259084288 * (X * X * X * X) - 214748364800 * (X * X * X * X * X) + 25769803776 * (X * X * X * X * X * X) + 34359738368 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (60129542144 - 532575944704 * X + 1357209665536 * (X * X) - 463856467968 * (X * X * X) - 1211180777472 * (X * X * X * X) + 17179869184 * (X * X * X * X * X) + 154618822656 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (8589934592 - 163208757248 * X + 695784701952 * X ^ 2 - 481036337152 * X ^ 3 - 1073741824000 * X ^ 4 + 154618822656 * X ^ 5 + 240518168576 * X ^ 6) * derivative ℚ G + (8589934592 * X - 81604378624 * X ^ 2 + 231928233984 * X ^ 3 - 120259084288 * X ^ 4 - 214748364800 * X ^ 5 + 25769803776 * X ^ 6 + 34359738368 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-532575944704 + 2714419331072 * X - 1391569403904 * X ^ 2 - 4844723109888 * X ^ 3 + 85899345920 * X ^ 4 + 927712935936 * X ^ 5) * G + (60129542144 - 532575944704 * X + 1357209665536 * X ^ 2 - 463856467968 * X ^ 3 - 1211180777472 * X ^ 4 + 17179869184 * X ^ 5 + 154618822656 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d8589934592, d17179869184, d25769803776, d34359738368, d60129542144, d81604378624, d120259084288, d154618822656, d214748364800, d231928233984, d463856467968, d532575944704, d1211180777472, d1357209665536]
    ring
  have hRd : derivative ℚ (60129542144 + 17179869184 * X : ℚ⟦X⟧) = 17179869184 := by
    simp [Derivation.leibniz, d17179869184, d60129542144]
  have h2 : (8589934592 * X - 81604378624 * (X * X) + 231928233984 * (X * X * X) - 120259084288 * (X * X * X * X) - 214748364800 * (X * X * X * X * X) + 25769803776 * (X * X * X * X * X * X) + 34359738368 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (60129542144 - 532575944704 * X + 1357209665536 * (X * X) - 463856467968 * (X * X * X) - 1211180777472 * (X * X * X * X) + 17179869184 * (X * X * X * X * X) + 154618822656 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (60129542144 + 17179869184 * X : ℚ⟦X⟧) := by linear_combination h
  have hd : (8589934592 - 163208757248 * X + 695784701952 * X ^ 2 - 481036337152 * X ^ 3 - 1073741824000 * X ^ 4 + 154618822656 * X ^ 5 + 240518168576 * X ^ 6) * derivative ℚ G + (8589934592 * X - 81604378624 * X ^ 2 + 231928233984 * X ^ 3 - 120259084288 * X ^ 4 - 214748364800 * X ^ 5 + 25769803776 * X ^ 6 + 34359738368 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-532575944704 + 2714419331072 * X - 1391569403904 * X ^ 2 - 4844723109888 * X ^ 3 + 85899345920 * X ^ 4 + 927712935936 * X ^ 5) * G + (60129542144 - 532575944704 * X + 1357209665536 * X ^ 2 - 463856467968 * X ^ 3 - 1211180777472 * X ^ 4 + 17179869184 * X ^ 5 + 154618822656 * X ^ 6) * derivative ℚ G = 17179869184 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((8589934592 - 163208757248 * X + 695784701952 * (X * X) - 481036337152 * (X * X * X) - 1073741824000 * (X * X * X * X) + 154618822656 * (X * X * X * X * X) + 240518168576 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (8589934592 * X - 81604378624 * (X * X) + 231928233984 * (X * X * X) - 120259084288 * (X * X * X * X) - 214748364800 * (X * X * X * X * X) + 25769803776 * (X * X * X * X * X * X) + 34359738368 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-532575944704 + 2714419331072 * X - 1391569403904 * (X * X) - 4844723109888 * (X * X * X) + 85899345920 * (X * X * X * X) + 927712935936 * (X * X * X * X * X) : ℚ⟦X⟧) * G + (60129542144 - 532575944704 * X + 1357209665536 * (X * X) - 463856467968 * (X * X * X) - 1211180777472 * (X * X * X * X) + 17179869184 * (X * X * X * X * X) + 154618822656 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (-1228360646656 + 6820408066048 * X - 4226247819264 * X ^ 2 - 13984413515776 * X ^ 3 + 944892805120 * X ^ 4 + 3298534883328 * X ^ 5) * derivative ℚ G + (77309411328 - 858993459200 * X + 2748779069440 * X ^ 2 - 1425929142272 * X ^ 3 - 3358664425472 * X ^ 4 + 326417514496 * X ^ 5 + 635655159808 * X ^ 6) * derivative ℚ (derivative ℚ G) + (8589934592 * X - 81604378624 * X ^ 2 + 231928233984 * X ^ 3 - 120259084288 * X ^ 4 - 214748364800 * X ^ 5 + 25769803776 * X ^ 6 + 34359738368 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2714419331072 - 2783138807808 * X - 14534169329664 * X ^ 2 + 343597383680 * X ^ 3 + 4638564679680 * X ^ 4) * G := by
    simp [Derivation.leibniz, d8589934592, d17179869184, d25769803776, d34359738368, d60129542144, d81604378624, d85899345920, d120259084288, d154618822656, d163208757248, d214748364800, d231928233984, d240518168576, d463856467968, d481036337152, d532575944704, d695784701952, d927712935936, d1073741824000, d1211180777472, d1357209665536, d1391569403904, d2714419331072, d4844723109888]
    ring
  have hRd2 : derivative ℚ (17179869184 : ℚ⟦X⟧) = 0 := by
    simp [d17179869184]
  have hdp : (8589934592 - 163208757248 * X + 695784701952 * (X * X) - 481036337152 * (X * X * X) - 1073741824000 * (X * X * X * X) + 154618822656 * (X * X * X * X * X) + 240518168576 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (8589934592 * X - 81604378624 * (X * X) + 231928233984 * (X * X * X) - 120259084288 * (X * X * X * X) - 214748364800 * (X * X * X * X * X) + 25769803776 * (X * X * X * X * X * X) + 34359738368 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-532575944704 + 2714419331072 * X - 1391569403904 * (X * X) - 4844723109888 * (X * X * X) + 85899345920 * (X * X * X * X) + 927712935936 * (X * X * X * X * X) : ℚ⟦X⟧) * G + (60129542144 - 532575944704 * X + 1357209665536 * (X * X) - 463856467968 * (X * X * X) - 1211180777472 * (X * X * X * X) + 17179869184 * (X * X * X * X * X) + 154618822656 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (17179869184 : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (-1228360646656 + 6820408066048 * X - 4226247819264 * X ^ 2 - 13984413515776 * X ^ 3 + 944892805120 * X ^ 4 + 3298534883328 * X ^ 5) * derivative ℚ G + (77309411328 - 858993459200 * X + 2748779069440 * X ^ 2 - 1425929142272 * X ^ 3 - 3358664425472 * X ^ 4 + 326417514496 * X ^ 5 + 635655159808 * X ^ 6) * derivative ℚ (derivative ℚ G) + (8589934592 * X - 81604378624 * X ^ 2 + 231928233984 * X ^ 3 - 120259084288 * X ^ 4 - 214748364800 * X ^ 5 + 25769803776 * X ^ 6 + 34359738368 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2714419331072 - 2783138807808 * X - 14534169329664 * X ^ 2 + 343597383680 * X ^ 3 + 4638564679680 * X ^ 4) * G = 0 := by
    rw [← hL2, hdp, hRd2]
  have hfull : (4294967296 - 51539607552 * X + 223338299392 * X ^ 2 - 395136991232 * X ^ 3 + 154618822656 * X ^ 4 + 240518168576 * X ^ 5 - 120259084288 * X ^ 6 - 34359738368 * X ^ 7 + 17179869184 * X ^ 8) * ((6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (82 * X ^ 2 - 338 * X ^ 3 - 230 * X ^ 4) * derivative ℚ (derivative ℚ G) + (224 * X - 1502 * X ^ 2 - 1236 * X ^ 3) * derivative ℚ G + (-1792 * X - 1800 * X ^ 2) * G - (0)) = 0 := by
    linear_combination (3 * X ^ 2 - 18 * X ^ 3 + 24 * X ^ 4 + 6 * X ^ 5 - 6 * X ^ 6) * hd2 + (14 * X - 66 * X ^ 2 + 64 * X ^ 3 + 10 * X ^ 4 - 4 * X ^ 5) * hd + (-4 * X + 20 * X ^ 2 - 24 * X ^ 3 + 4 * X ^ 4) * h
  have hg : (4294967296 - 51539607552 * X + 223338299392 * X ^ 2 - 395136991232 * X ^ 3 + 154618822656 * X ^ 4 + 240518168576 * X ^ 5 - 120259084288 * X ^ 6 - 34359738368 * X ^ 7 + 17179869184 * X ^ 8 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (4294967296 : ℚ⟦X⟧) = 4294967296 := cnum 4294967296
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-128 * X ^ 7 + 512 * X ^ 8 + (384 * X ^ 7) * S) = 128 - 896 * X + 1792 * X ^ 2 - 896 * X ^ 3 + (-128 + 640 * X - 768 * X ^ 2 + 128 * X ^ 3) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 6 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-21) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-12) + derivative ℚ (derivative ℚ G) * X * X * C 82 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-338) + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-230) +
      derivative ℚ G * X * C 224 + derivative ℚ G * X * X * C (-1502) +
      derivative ℚ G * X * X * X * C (-1236) + G * X * C (-1792) +
      G * X * X * C (-1800) =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-128 * X ^ 7 + 512 * X ^ 8 + (384 * X ^ 7) * S) = 128 - 896 * X + 1792 * X ^ 2 - 896 * X ^ 3 + (-128 + 640 * X - 768 * X ^ 2 + 128 * X ^ 3) * S) (m : ℕ) :
    6 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-21) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-12) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 82 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-338) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-230) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      224 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-1502) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-1236) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-1792) * coeff (m + 1 + 1 + 1 + 1) G +
      (-1800) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-128 * X ^ 7 + 512 * X ^ 8 + (384 * X ^ 7) * S) = 128 - 896 * X + 1792 * X ^ 2 - 896 * X ^ 3 + (-128 + 640 * X - 768 * X ^ 2 + 128 * X ^ 3) * S) :
    164 * coeff (0 + 1 + 1) G + 448 * coeff (0 + 1 + 1) G +
      (-1502) * coeff (0 + 1) G + (-1792) * coeff (0 + 1) G +
      (-1800) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-128 * X ^ 7 + 512 * X ^ 8 + (384 * X ^ 7) * S) = 128 - 896 * X + 1792 * X ^ 2 - 896 * X ^ 3 + (-128 + 640 * X - 768 * X ^ 2 + 128 * X ^ 3) * S) :
    36 * coeff (0 + 1 + 1 + 1) G + 492 * coeff (0 + 1 + 1 + 1) G +
      (-676) * coeff (0 + 1 + 1) G + 672 * coeff (0 + 1 + 1 + 1) G +
      (-3004) * coeff (0 + 1 + 1) G + (-1236) * coeff (0 + 1) G +
      (-1792) * coeff (0 + 1 + 1) G + (-1800) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-128 * X ^ 7 + 512 * X ^ 8 + (384 * X ^ 7) * S) = 128 - 896 * X + 1792 * X ^ 2 - 896 * X ^ 3 + (-128 + 640 * X - 768 * X ^ 2 + 128 * X ^ 3) * S) :
    144 * coeff (0 + 1 + 1 + 1 + 1) G + (-126) * coeff (0 + 1 + 1 + 1) G +
      984 * coeff (0 + 1 + 1 + 1 + 1) G + (-2028) * coeff (0 + 1 + 1 + 1) G +
      (-460) * coeff (0 + 1 + 1) G + 896 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-4506) * coeff (0 + 1 + 1 + 1) G + (-2472) * coeff (0 + 1 + 1) G +
      (-1792) * coeff (0 + 1 + 1 + 1) G + (-1800) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A172064Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a172064.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A172064Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (128 * PowerSeries.X ^ 7) * hG - ((-2) + (12) * S + (-30) * S ^ 2 + (40) * S ^ 3 + (-30) * S ^ 4 + (12) * S ^ 5 + (-2) * S ^ 6 + (-4 * PowerSeries.X) * c + (20 * PowerSeries.X) * c * S + (-40 * PowerSeries.X) * c * S ^ 2 + (40 * PowerSeries.X) * c * S ^ 3 + (-20 * PowerSeries.X) * c * S ^ 4 + (4 * PowerSeries.X) * c * S ^ 5 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (32 * PowerSeries.X ^ 2) * c ^ 2 * S + (-48 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (32 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (48 * PowerSeries.X ^ 3) * c ^ 3 * S + (-48 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (64 * PowerSeries.X ^ 4) * c ^ 4 * S + (-32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (64 * PowerSeries.X ^ 5) * c ^ 5 * S + (-128 * PowerSeries.X ^ 6) * c ^ 6) * hc - ((-126 + 392 * PowerSeries.X - 224 * PowerSeries.X ^ 2) + (114 - 184 * PowerSeries.X + 32 * PowerSeries.X ^ 2) * S + (-84 + 56 * PowerSeries.X) * S ^ 2 + (44 - 8 * PowerSeries.X) * S ^ 3 + (-14) * S ^ 4 + (2) * S ^ 5) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A172064Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (128 * PowerSeries.X ^ 7) * hG - ((-2) + (12) * S + (-30) * S ^ 2 + (40) * S ^ 3 + (-30) * S ^ 4 + (12) * S ^ 5 + (-2) * S ^ 6 + (-4 * PowerSeries.X) * c + (20 * PowerSeries.X) * c * S + (-40 * PowerSeries.X) * c * S ^ 2 + (40 * PowerSeries.X) * c * S ^ 3 + (-20 * PowerSeries.X) * c * S ^ 4 + (4 * PowerSeries.X) * c * S ^ 5 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (32 * PowerSeries.X ^ 2) * c ^ 2 * S + (-48 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (32 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (48 * PowerSeries.X ^ 3) * c ^ 3 * S + (-48 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (64 * PowerSeries.X ^ 4) * c ^ 4 * S + (-32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (64 * PowerSeries.X ^ 5) * c ^ 5 * S + (-128 * PowerSeries.X ^ 6) * c ^ 6) * hc - ((-126 + 392 * PowerSeries.X - 224 * PowerSeries.X ^ 2) + (114 - 184 * PowerSeries.X + 32 * PowerSeries.X ^ 2) * S + (-84 + 56 * PowerSeries.X) * S ^ 2 + (44 - 8 * PowerSeries.X) * S ^ 3 + (-14) * S ^ 4 + (2) * S ^ 5) * hS)
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A172064Aux.relE2 (S) G (by linear_combination hS)
            (by linear_combination (128 * PowerSeries.X ^ 7) * hG - ((-2) + (12) * S + (-30) * S ^ 2 + (40) * S ^ 3 + (-30) * S ^ 4 + (12) * S ^ 5 + (-2) * S ^ 6 + (-4 * PowerSeries.X) * c + (20 * PowerSeries.X) * c * S + (-40 * PowerSeries.X) * c * S ^ 2 + (40 * PowerSeries.X) * c * S ^ 3 + (-20 * PowerSeries.X) * c * S ^ 4 + (4 * PowerSeries.X) * c * S ^ 5 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (32 * PowerSeries.X ^ 2) * c ^ 2 * S + (-48 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (32 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (48 * PowerSeries.X ^ 3) * c ^ 3 * S + (-48 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (64 * PowerSeries.X ^ 4) * c ^ 4 * S + (-32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (64 * PowerSeries.X ^ 5) * c ^ 5 * S + (-128 * PowerSeries.X ^ 6) * c ^ 6) * hc - ((-126 + 392 * PowerSeries.X - 224 * PowerSeries.X ^ 2) + (114 - 184 * PowerSeries.X + 32 * PowerSeries.X ^ 2) * S + (-84 + 56 * PowerSeries.X) * S ^ 2 + (44 - 8 * PowerSeries.X) * S ^ 3 + (-14) * S ^ 4 + (2) * S ^ 5) * hS)
        push_cast
        linear_combination r
      | succ m =>
        have r := A172064Aux.rel (S) G (by linear_combination hS)
            (by linear_combination (128 * PowerSeries.X ^ 7) * hG - ((-2) + (12) * S + (-30) * S ^ 2 + (40) * S ^ 3 + (-30) * S ^ 4 + (12) * S ^ 5 + (-2) * S ^ 6 + (-4 * PowerSeries.X) * c + (20 * PowerSeries.X) * c * S + (-40 * PowerSeries.X) * c * S ^ 2 + (40 * PowerSeries.X) * c * S ^ 3 + (-20 * PowerSeries.X) * c * S ^ 4 + (4 * PowerSeries.X) * c * S ^ 5 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (32 * PowerSeries.X ^ 2) * c ^ 2 * S + (-48 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (32 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (48 * PowerSeries.X ^ 3) * c ^ 3 * S + (-48 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (64 * PowerSeries.X ^ 4) * c ^ 4 * S + (-32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (64 * PowerSeries.X ^ 5) * c ^ 5 * S + (-128 * PowerSeries.X ^ 6) * c ^ 6) * hc - ((-126 + 392 * PowerSeries.X - 224 * PowerSeries.X ^ 2) + (114 - 184 * PowerSeries.X + 32 * PowerSeries.X ^ 2) * S + (-84 + 56 * PowerSeries.X) * S ^ 2 + (44 - 8 * PowerSeries.X) * S ^ 3 + (-14) * S ^ 4 + (2) * S ^ 5) * hS) m
        push_cast
        linear_combination r
