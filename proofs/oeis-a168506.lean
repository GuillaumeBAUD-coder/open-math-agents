import OMAStatements.S_oeis_a168506

-- Problem: A168506: Number of rooted plane trees of total weight n whose nodes are themselves planted plane trees whose roots are distinguished as either red or blue, the weight of each such node being equal to the size of the corresponding planted tree.
-- Upstream: formal-conjectures statements/oeis-a168506.lean:0 (declaration OMA.S_oeis_a168506.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A168506Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * G + (1 + 2 * X : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    (X ^ 3 - 12 * X ^ 4 + 32 * X ^ 5 + 64 * X ^ 6 - 256 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-4 * X ^ 2 + 34 * X ^ 3 - 64 * X ^ 4 + 32 * X ^ 5 - 256 * X ^ 6) * derivative ℚ (derivative ℚ G) + (68 * X ^ 3 - 272 * X ^ 4 - 48 * X ^ 5) * derivative ℚ G + (-32 * X ^ 2 + 200 * X ^ 3 + 48 * X ^ 4) * G =
      -16 * X ^ 2 + 100 * X ^ 3 + 24 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have hp0 : (4 * (X * X * X) : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * G + (1 + 2 * X : ℚ⟦X⟧) * G * G + (-2 : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((4 * (X * X * X) : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * G + (1 + 2 * X : ℚ⟦X⟧) * G * G + (-2 : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (12 * X ^ 2 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G + (2 + 4 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hd1 : (12 * X ^ 2 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G + (2 + 4 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (12 * (X * X) : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G + (2 + 4 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G * G + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((12 * (X * X) : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G + (2 + 4 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G * G + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (24 * X : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 + 4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2, d4, d6, d12]
    ring
  have hd2 : (24 * X : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 + 4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (24 * X : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((24 * X : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G))) =
      (24 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (6 + 12 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-12 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (2 + 4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-36 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2, d4, d6, d8, d12, d24]
    ring
  have hd3 : (24 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (6 + 12 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-12 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (2 + 4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-36 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((-2 * X : ℚ⟦X⟧) + (2 + 4 * X : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((X ^ 3 - 12 * X ^ 4 + 32 * X ^ 5 + 64 * X ^ 6 - 256 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-4 * X ^ 2 + 34 * X ^ 3 - 64 * X ^ 4 + 32 * X ^ 5 - 256 * X ^ 6) * derivative ℚ (derivative ℚ G) + (68 * X ^ 3 - 272 * X ^ 4 - 48 * X ^ 5) * derivative ℚ G + (-32 * X ^ 2 + 200 * X ^ 3 + 48 * X ^ 4) * G - (-16 * X ^ 2 + 100 * X ^ 3 + 24 * X ^ 4)) = 0 := by
    linear_combination ((-224 * X ^ 4 + 3968 * X ^ 5 - 29184 * X ^ 6 + 85248 * X ^ 7 + 47616 * X ^ 8 - 580608 * X ^ 9 + 147456 * X ^ 10 + 1327104 * X ^ 11 + 5308416 * X ^ 12 : ℚ⟦X⟧) + (256 * X ^ 3 - 1088 * X ^ 4 - 14208 * X ^ 5 + 199168 * X ^ 6 - 860160 * X ^ 7 + 12288 * X ^ 8 + 5898240 * X ^ 9 - 8552448 * X ^ 10 - 21233664 * X ^ 11 : ℚ⟦X⟧) * G + (-128 * X ^ 2 - 1152 * X ^ 3 + 1600 * X ^ 4 + 34944 * X ^ 5 - 298496 * X ^ 6 + 2522112 * X ^ 7 - 12288 * X ^ 8 - 13565952 * X ^ 9 + 45711360 * X ^ 10 + 21233664 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 + (1536 * X ^ 2 + 6144 * X ^ 3 + 25856 * X ^ 4 - 486400 * X ^ 5 - 317440 * X ^ 6 - 3102720 * X ^ 7 - 9437184 * X ^ 8 + 15335424 * X ^ 9 - 74317824 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (-11136 * X ^ 2 - 39552 * X ^ 3 + 107264 * X ^ 4 + 2703104 * X ^ 5 + 1055744 * X ^ 6 + 4094976 * X ^ 7 + 28311552 * X ^ 8 - 7667712 * X ^ 9 + 37158912 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 + (57088 * X ^ 2 + 94976 * X ^ 3 - 1459456 * X ^ 4 - 6897152 * X ^ 5 + 24576 * X ^ 6 - 11722752 * X ^ 7 - 28311552 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 + (-199936 * X ^ 2 + 149248 * X ^ 3 + 5099264 * X ^ 4 + 9390592 * X ^ 5 - 1843200 * X ^ 6 + 18358272 * X ^ 7 + 9437184 * X ^ 8 : ℚ⟦X⟧) * G ^ 6 + (471040 * X ^ 2 - 1331200 * X ^ 3 - 8949760 * X ^ 4 - 7110656 * X ^ 5 + 1572864 * X ^ 6 - 12386304 * X ^ 7 : ℚ⟦X⟧) * G ^ 7 + (-744448 * X ^ 2 + 3251200 * X ^ 3 + 8829952 * X ^ 4 + 3067904 * X ^ 5 - 393216 * X ^ 6 + 3096576 * X ^ 7 : ℚ⟦X⟧) * G ^ 8 + (778240 * X ^ 2 - 4198400 * X ^ 3 - 4935680 * X ^ 4 - 860160 * X ^ 5 : ℚ⟦X⟧) * G ^ 9 + (-516096 * X ^ 2 + 3092480 * X ^ 3 + 1527808 * X ^ 4 + 172032 * X ^ 5 : ℚ⟦X⟧) * G ^ 10 + (196608 * X ^ 2 - 1228800 * X ^ 3 - 294912 * X ^ 4 : ℚ⟦X⟧) * G ^ 11 + (-32768 * X ^ 2 + 204800 * X ^ 3 + 49152 * X ^ 4 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((224 * X ^ 5 - 2912 * X ^ 6 + 13888 * X ^ 7 - 25344 * X ^ 8 - 24064 * X ^ 9 + 193536 * X ^ 10 - 49152 * X ^ 11 - 442368 * X ^ 12 - 1769472 * X ^ 13 : ℚ⟦X⟧) + (-208 * X ^ 5 + 2240 * X ^ 6 - 5120 * X ^ 7 - 13440 * X ^ 8 + 44544 * X ^ 9 + 40960 * X ^ 10 - 73728 * X ^ 11 - 294912 * X ^ 12 : ℚ⟦X⟧) * (derivative ℚ G) + (48 * X ^ 5 - 480 * X ^ 6 + 576 * X ^ 7 + 3840 * X ^ 8 - 12288 * X ^ 10 - 49152 * X ^ 11 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-368 * X ^ 4 + 1728 * X ^ 5 + 12736 * X ^ 6 - 102144 * X ^ 7 + 205824 * X ^ 8 + 77824 * X ^ 9 - 1818624 * X ^ 10 + 3440640 * X ^ 11 + 7077888 * X ^ 12 : ℚ⟦X⟧) * G + (432 * X ^ 4 - 1728 * X ^ 5 - 20928 * X ^ 6 + 107904 * X ^ 7 + 40704 * X ^ 8 - 740352 * X ^ 9 + 319488 * X ^ 10 + 1622016 * X ^ 11 + 589824 * X ^ 12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-96 * X ^ 4 + 288 * X ^ 5 + 5760 * X ^ 6 - 16128 * X ^ 7 - 70656 * X ^ 8 + 98304 * X ^ 9 + 344064 * X ^ 10 + 196608 * X ^ 11 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (256 * X ^ 3 + 656 * X ^ 4 - 9984 * X ^ 5 - 39232 * X ^ 6 + 340992 * X ^ 7 - 108544 * X ^ 8 - 1171456 * X ^ 9 + 1572864 * X ^ 10 - 15826944 * X ^ 11 - 7077888 * X ^ 12 : ℚ⟦X⟧) * G ^ 2 + (-288 * X ^ 3 - 3120 * X ^ 4 + 43680 * X ^ 5 - 17856 * X ^ 6 - 635520 * X ^ 7 + 781824 * X ^ 8 + 2764800 * X ^ 9 - 4448256 * X ^ 10 - 4423680 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (48 * X ^ 3 + 960 * X ^ 4 - 10272 * X ^ 5 - 21120 * X ^ 6 + 225024 * X ^ 7 + 218112 * X ^ 8 - 1277952 * X ^ 9 - 1523712 * X ^ 10 - 196608 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-64 * X ^ 2 - 1536 * X ^ 3 + 1536 * X ^ 4 + 17152 * X ^ 5 + 207104 * X ^ 6 - 1278464 * X ^ 7 - 743424 * X ^ 8 + 11231232 * X ^ 9 + 491520 * X ^ 10 + 24772608 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (64 * X ^ 2 + 3520 * X ^ 3 - 7648 * X ^ 4 - 211264 * X ^ 5 + 627584 * X ^ 6 + 1475328 * X ^ 7 - 4617216 * X ^ 8 - 2482176 * X ^ 9 + 13778944 * X ^ 10 + 2949120 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-768 * X ^ 3 - 1344 * X ^ 4 + 78336 * X ^ 5 - 110592 * X ^ 6 - 1130496 * X ^ 7 + 884736 * X ^ 8 + 5505024 * X ^ 9 + 2359296 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (576 * X ^ 2 + 3520 * X ^ 3 + 15712 * X ^ 4 - 101568 * X ^ 5 - 644480 * X ^ 6 + 3738880 * X ^ 7 - 2384896 * X ^ 8 - 28225536 * X ^ 9 - 245760 * X ^ 10 - 12386304 * X ^ 11 : ℚ⟦X⟧) * G ^ 4 + (-960 * X ^ 2 - 14688 * X ^ 3 + 123936 * X ^ 4 + 344064 * X ^ 5 - 2404992 * X ^ 6 - 1147392 * X ^ 7 + 10874880 * X ^ 8 - 6266880 * X ^ 9 - 16220160 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (5328 * X ^ 3 - 25632 * X ^ 4 - 246528 * X ^ 5 + 1059840 * X ^ 6 + 2396160 * X ^ 7 - 6930432 * X ^ 8 - 10616832 * X ^ 9 - 1179648 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (-2240 * X ^ 2 - 8192 * X ^ 3 - 123712 * X ^ 4 + 656256 * X ^ 5 + 1101312 * X ^ 6 - 6793216 * X ^ 7 + 14868480 * X ^ 8 + 27131904 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 + (5952 * X ^ 2 + 17280 * X ^ 3 - 438144 * X ^ 4 + 183936 * X ^ 5 + 4421376 * X ^ 6 - 814080 * X ^ 7 - 13811712 * X ^ 8 + 16957440 * X ^ 9 + 6488064 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-20448 * X ^ 3 + 167040 * X ^ 4 + 248832 * X ^ 5 - 3373056 * X ^ 6 - 958464 * X ^ 7 + 17694720 * X ^ 8 + 9437184 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (4928 * X ^ 2 + 41344 * X ^ 3 + 273856 * X ^ 4 - 2005120 * X ^ 5 - 1169920 * X ^ 6 + 7387136 * X ^ 7 - 24223744 * X ^ 8 - 9043968 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 + (-20160 * X ^ 2 + 55104 * X ^ 3 + 694848 * X ^ 4 - 1357440 * X ^ 5 - 4978176 * X ^ 6 + 2236416 * X ^ 7 + 9461760 * X ^ 8 - 14450688 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (47136 * X ^ 3 - 475008 * X ^ 4 + 433152 * X ^ 5 + 5769216 * X ^ 6 - 5873664 * X ^ 7 - 22413312 * X ^ 8 - 3145728 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (-6656 * X ^ 2 - 148736 * X ^ 3 - 99328 * X ^ 4 + 3326976 * X ^ 5 + 786432 * X ^ 6 - 4390912 * X ^ 7 + 16515072 * X ^ 8 : ℚ⟦X⟧) * G ^ 7 + (41088 * X ^ 2 - 233856 * X ^ 3 - 404352 * X ^ 4 + 1751808 * X ^ 5 + 4518912 * X ^ 6 - 2015232 * X ^ 7 - 2703360 * X ^ 8 + 4128768 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-66816 * X ^ 3 + 746496 * X ^ 4 - 1474560 * X ^ 5 - 6045696 * X ^ 6 + 13565952 * X ^ 7 + 14155776 * X ^ 8 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (5504 * X ^ 2 + 304832 * X ^ 3 - 592640 * X ^ 4 - 3163392 * X ^ 5 - 319488 * X ^ 6 + 1097728 * X ^ 7 - 4128768 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 + (-51840 * X ^ 2 + 379008 * X ^ 3 - 251136 * X ^ 4 - 820224 * X ^ 5 - 3944448 * X ^ 6 + 1032192 * X ^ 7 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (57024 * X ^ 3 - 670464 * X ^ 4 + 1658880 * X ^ 5 + 4091904 * X ^ 6 - 13713408 * X ^ 7 - 3538944 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (-2560 * X ^ 2 - 369920 * X ^ 3 + 1177600 * X ^ 4 + 1689600 * X ^ 5 + 81920 * X ^ 6 : ℚ⟦X⟧) * G ^ 9 + (39680 * X ^ 2 - 323584 * X ^ 3 + 506368 * X ^ 4 - 43008 * X ^ 5 + 2678784 * X ^ 6 - 229376 * X ^ 7 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-26880 * X ^ 3 + 322560 * X ^ 4 - 860160 * X ^ 5 - 1720320 * X ^ 6 + 6881280 * X ^ 7 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (512 * X ^ 2 + 265472 * X ^ 3 - 1001472 * X ^ 4 - 473088 * X ^ 5 - 16384 * X ^ 6 : ℚ⟦X⟧) * G ^ 10 + (-16896 * X ^ 2 + 143616 * X ^ 3 - 270336 * X ^ 4 + 135168 * X ^ 5 - 1081344 * X ^ 6 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (5376 * X ^ 3 - 64512 * X ^ 4 + 172032 * X ^ 5 + 344064 * X ^ 6 - 1376256 * X ^ 7 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (-104448 * X ^ 3 + 417792 * X ^ 4 + 73728 * X ^ 5 : ℚ⟦X⟧) * G ^ 11 + (3072 * X ^ 2 - 26112 * X ^ 3 + 49152 * X ^ 4 - 24576 * X ^ 5 + 196608 * X ^ 6 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (17408 * X ^ 3 - 69632 * X ^ 4 - 12288 * X ^ 5 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((-112 * X ^ 6 + 1120 * X ^ 7 - 2560 * X ^ 8 - 2560 * X ^ 9 + 8192 * X ^ 10 : ℚ⟦X⟧) + (48 * X ^ 6 - 480 * X ^ 7 + 384 * X ^ 8 + 6144 * X ^ 9 - 6144 * X ^ 10 - 24576 * X ^ 11 : ℚ⟦X⟧) * (derivative ℚ G) + (400 * X ^ 5 - 3008 * X ^ 6 - 256 * X ^ 7 + 27648 * X ^ 8 - 65536 * X ^ 10 : ℚ⟦X⟧) * G + (-144 * X ^ 5 + 864 * X ^ 6 + 5184 * X ^ 7 - 29952 * X ^ 8 - 36864 * X ^ 9 + 184320 * X ^ 10 + 147456 * X ^ 11 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-528 * X ^ 4 + 1392 * X ^ 5 + 21696 * X ^ 6 - 57600 * X ^ 7 - 113664 * X ^ 8 + 122880 * X ^ 9 + 196608 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (144 * X ^ 4 + 432 * X ^ 5 - 16704 * X ^ 6 + 24192 * X ^ 7 + 235008 * X ^ 8 - 221184 * X ^ 9 - 1105920 * X ^ 10 - 294912 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (304 * X ^ 3 + 2528 * X ^ 4 - 31488 * X ^ 5 - 12800 * X ^ 6 + 308224 * X ^ 7 + 188416 * X ^ 8 - 573440 * X ^ 9 - 262144 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (-48 * X ^ 3 - 1536 * X ^ 4 + 12000 * X ^ 5 + 60288 * X ^ 6 - 372480 * X ^ 7 - 549888 * X ^ 8 + 2310144 * X ^ 9 + 2703360 * X ^ 10 + 196608 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-64 * X ^ 2 - 2800 * X ^ 3 + 7600 * X ^ 4 + 120832 * X ^ 5 - 239360 * X ^ 6 - 766464 * X ^ 7 + 61440 * X ^ 8 + 1105920 * X ^ 9 + 131072 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 + (720 * X ^ 3 + 3600 * X ^ 4 - 92160 * X ^ 5 + 69120 * X ^ 6 + 1474560 * X ^ 7 - 737280 * X ^ 8 - 7372800 * X ^ 9 - 2949120 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (768 * X ^ 2 + 8976 * X ^ 3 - 81600 * X ^ 4 - 139008 * X ^ 5 + 860160 * X ^ 6 + 1167360 * X ^ 7 - 737280 * X ^ 8 - 983040 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 + (-4464 * X ^ 3 + 16416 * X ^ 4 + 258048 * X ^ 5 - 940032 * X ^ 6 - 2617344 * X ^ 7 + 6488064 * X ^ 8 + 11206656 * X ^ 9 + 1179648 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-3968 * X ^ 2 - 5488 * X ^ 3 + 236608 * X ^ 4 - 182016 * X ^ 5 - 1441792 * X ^ 6 - 1306624 * X ^ 7 + 1163264 * X ^ 8 + 327680 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 + (15120 * X ^ 3 - 116928 * X ^ 4 - 258048 * X ^ 5 + 2644992 * X ^ 6 + 1290240 * X ^ 7 - 14450688 * X ^ 8 - 8257536 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (11520 * X ^ 2 - 39552 * X ^ 3 - 310272 * X ^ 4 + 669696 * X ^ 5 + 1622016 * X ^ 6 + 1179648 * X ^ 7 - 786432 * X ^ 8 : ℚ⟦X⟧) * G ^ 7 + (-30816 * X ^ 3 + 305280 * X ^ 4 - 221184 * X ^ 5 - 3926016 * X ^ 6 + 3465216 * X ^ 7 + 15925248 * X ^ 8 + 2359296 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-20544 * X ^ 2 + 123552 * X ^ 3 + 125184 * X ^ 4 - 701952 * X ^ 5 - 1658880 * X ^ 6 - 786432 * X ^ 7 + 196608 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 + (38880 * X ^ 3 - 432000 * X ^ 4 + 829440 * X ^ 5 + 3594240 * X ^ 6 - 7741440 * X ^ 7 - 8847360 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (23040 * X ^ 2 - 171520 * X ^ 3 + 148480 * X ^ 4 + 266240 * X ^ 5 + 1556480 * X ^ 6 + 327680 * X ^ 7 : ℚ⟦X⟧) * G ^ 9 + (-29760 * X ^ 3 + 349440 * X ^ 4 - 860160 * X ^ 5 - 2150400 * X ^ 6 + 7127040 * X ^ 7 + 1966080 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-15872 * X ^ 2 + 130048 * X ^ 3 - 209920 * X ^ 4 + 36864 * X ^ 5 - 1032192 * X ^ 6 - 65536 * X ^ 7 : ℚ⟦X⟧) * G ^ 10 + (12672 * X ^ 3 - 152064 * X ^ 4 + 405504 * X ^ 5 + 811008 * X ^ 6 - 3244032 * X ^ 7 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (6144 * X ^ 2 - 52224 * X ^ 3 + 98304 * X ^ 4 - 49152 * X ^ 5 + 393216 * X ^ 6 : ℚ⟦X⟧) * G ^ 11 + (-2304 * X ^ 3 + 27648 * X ^ 4 - 73728 * X ^ 5 - 147456 * X ^ 6 + 589824 * X ^ 7 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-1024 * X ^ 2 + 8704 * X ^ 3 - 16384 * X ^ 4 + 8192 * X ^ 5 - 65536 * X ^ 6 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((16 * X ^ 7 - 192 * X ^ 8 + 512 * X ^ 9 + 1024 * X ^ 10 - 4096 * X ^ 11 : ℚ⟦X⟧) + (-64 * X ^ 6 + 640 * X ^ 7 - 512 * X ^ 8 - 8192 * X ^ 9 + 8192 * X ^ 10 + 32768 * X ^ 11 : ℚ⟦X⟧) * G + (96 * X ^ 5 - 576 * X ^ 6 - 3456 * X ^ 7 + 19968 * X ^ 8 + 24576 * X ^ 9 - 122880 * X ^ 10 - 98304 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 + (-64 * X ^ 4 - 192 * X ^ 5 + 7424 * X ^ 6 - 10752 * X ^ 7 - 104448 * X ^ 8 + 98304 * X ^ 9 + 491520 * X ^ 10 + 131072 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (16 * X ^ 3 + 512 * X ^ 4 - 4000 * X ^ 5 - 20096 * X ^ 6 + 124160 * X ^ 7 + 183296 * X ^ 8 - 770048 * X ^ 9 - 901120 * X ^ 10 - 65536 * X ^ 11 : ℚ⟦X⟧) * G ^ 4 + (-192 * X ^ 3 - 960 * X ^ 4 + 24576 * X ^ 5 - 18432 * X ^ 6 - 393216 * X ^ 7 + 196608 * X ^ 8 + 1966080 * X ^ 9 + 786432 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 + (992 * X ^ 3 - 3648 * X ^ 4 - 57344 * X ^ 5 + 208896 * X ^ 6 + 581632 * X ^ 7 - 1441792 * X ^ 8 - 2490368 * X ^ 9 - 262144 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 + (-2880 * X ^ 3 + 22272 * X ^ 4 + 49152 * X ^ 5 - 503808 * X ^ 6 - 245760 * X ^ 7 + 2752512 * X ^ 8 + 1572864 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 + (5136 * X ^ 3 - 50880 * X ^ 4 + 36864 * X ^ 5 + 654336 * X ^ 6 - 577536 * X ^ 7 - 2654208 * X ^ 8 - 393216 * X ^ 9 : ℚ⟦X⟧) * G ^ 8 + (-5760 * X ^ 3 + 64000 * X ^ 4 - 122880 * X ^ 5 - 532480 * X ^ 6 + 1146880 * X ^ 7 + 1310720 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 + (3968 * X ^ 3 - 46592 * X ^ 4 + 114688 * X ^ 5 + 286720 * X ^ 6 - 950272 * X ^ 7 - 262144 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 + (-1536 * X ^ 3 + 18432 * X ^ 4 - 49152 * X ^ 5 - 98304 * X ^ 6 + 393216 * X ^ 7 : ℚ⟦X⟧) * G ^ 11 + (256 * X ^ 3 - 3072 * X ^ 4 + 8192 * X ^ 5 + 16384 * X ^ 6 - 65536 * X ^ 7 : ℚ⟦X⟧) * G ^ 12) * hd3
  have hres : ((-8388608 * X + 33554432 * X ^ 2 : ℚ⟦X⟧) + (8388608 + 16777216 * X - 67108864 * X ^ 2 : ℚ⟦X⟧) * G + (-25165824 : ℚ⟦X⟧) * G ^ 2 + (16777216 : ℚ⟦X⟧) * G ^ 3) * ((-2 * X : ℚ⟦X⟧) + (2 + 4 * X : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3) = (16777216 * X ^ 2 - 134217728 * X ^ 3 + 1073741824 * X ^ 5 : ℚ⟦X⟧) := by
    linear_combination (-((-16777216 + 268435456 * X ^ 2 : ℚ⟦X⟧) + (67108864 : ℚ⟦X⟧) * G + (-67108864 : ℚ⟦X⟧) * G ^ 2)) * hP
  have hd0 : (16777216 - 134217728 * X + 1073741824 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (16777216 : ℚ⟦X⟧) = 16777216 := cnum 16777216
    simp [kc] at h'
  have hdisc : (16777216 * X ^ 2 - 134217728 * X ^ 3 + 1073741824 * X ^ 5 : ℚ⟦X⟧) ≠ 0 := by
    have e : (16777216 * X ^ 2 - 134217728 * X ^ 3 + 1073741824 * X ^ 5 : ℚ⟦X⟧) = X ^ 2 * (16777216 - 134217728 * X + 1073741824 * X ^ 3 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 2 X_ne_zero) hd0
  have hPG : (-2 * X : ℚ⟦X⟧) + (2 + 4 * X : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hres
    exact hdisc hres.symm
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * G + (1 + 2 * X : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 1 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-12) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 32 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C 64 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C (-256) + derivative ℚ (derivative ℚ G) * X * X * C (-4) +
      derivative ℚ (derivative ℚ G) * X * X * X * C 34 + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-64) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 32 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-256) +
      derivative ℚ G * X * X * X * C 68 + derivative ℚ G * X * X * X * X * C (-272) +
      derivative ℚ G * X * X * X * X * X * C (-48) + G * X * X * C (-32) +
      G * X * X * X * C 200 + G * X * X * X * X * C 48 =
      C (-16) * X * X + C 100 * X * X * X +
      C 24 * X * X * X * X := by
  have h := key G hP
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * G + (1 + 2 * X : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) (m : ℕ) :
    1 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-12) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      32 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 64 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-256) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      34 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-64) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      32 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-256) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      68 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-272) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-48) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-32) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      200 * coeff (m + 1 + 1 + 1 + 1) G + 48 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * G + (1 + 2 * X : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    60 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-288) * coeff (0 + 1 + 1 + 1 + 1) G +
      192 * coeff (0 + 1 + 1 + 1) G + (-80) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      408 * coeff (0 + 1 + 1 + 1 + 1) G + (-384) * coeff (0 + 1 + 1 + 1) G +
      64 * coeff (0 + 1 + 1) G + 204 * coeff (0 + 1 + 1 + 1) G +
      (-544) * coeff (0 + 1 + 1) G + (-48) * coeff (0 + 1) G +
      (-32) * coeff (0 + 1 + 1 + 1) G + 200 * coeff (0 + 1 + 1) G +
      48 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * G + (1 + 2 * X : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    120 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-720) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      768 * coeff (0 + 1 + 1 + 1 + 1) G + 384 * coeff (0 + 1 + 1 + 1) G +
      (-120) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 680 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-768) * coeff (0 + 1 + 1 + 1 + 1) G + 192 * coeff (0 + 1 + 1 + 1) G +
      (-512) * coeff (0 + 1 + 1) G + 272 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-816) * coeff (0 + 1 + 1 + 1) G + (-96) * coeff (0 + 1 + 1) G +
      (-32) * coeff (0 + 1 + 1 + 1 + 1) G + 200 * coeff (0 + 1 + 1 + 1) G +
      48 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A168506Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a168506.main := by
  intro T W G hT _ hW _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  rw [e1, e2, e3, e4]
  have hn : ((2)) * ((8)) = (16 : PowerSeries ℚ) := by
    linear_combination (0 : PowerSeries ℚ) * hT
  have hnu0 : (16 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (16 : PowerSeries ℚ) = 16 := A168506Aux.cnum 16
    simp [kc] at h'
  have hnu : (16 : PowerSeries ℚ) ≠ 0 := by
    have e : (16 : PowerSeries ℚ) = PowerSeries.X ^ 0 * (16 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 0 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((2) : PowerSeries ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((2)) ^ 4 * ((4 * PowerSeries.X ^ 3 : PowerSeries ℚ) + (-2 * PowerSeries.X : PowerSeries ℚ) * G + (1 + 2 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-2 : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((16) * PowerSeries.X ^ 2) * hT +
      ((-1) + (1) * W ^ 2 + (4) * PowerSeries.X + (4) * PowerSeries.X * T) * hW +
      ((1) + (1) * W + (-1) * W ^ 2 + (-1) * W ^ 3 + (2) * G + (4) * G * W + (2) * G * W ^ 2 + (-12) * G ^ 2 + (-4) * G ^ 2 * W + (8) * G ^ 3 + (-8) * PowerSeries.X + (-8) * PowerSeries.X * W + (16) * PowerSeries.X * G) * hG
  have hP : (4 * PowerSeries.X ^ 3 : PowerSeries ℚ) + (-2 * PowerSeries.X : PowerSeries ℚ) * G + (1 + 2 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-2 : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  cases m with
  | zero =>
    have r := A168506Aux.relE0 G hP
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A168506Aux.relE1 G hP
      push_cast
      linear_combination r
    | succ m =>
      have r := A168506Aux.rel G hP m
      push_cast
      linear_combination r
