import OMAStatements.S_oeis_a071684

-- Problem: A071684: Number of plane trees with n edges and having an odd number of leaves.
-- Upstream: formal-conjectures statements/oeis-a071684.lean:0 (declaration OMA.S_oeis_a071684.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A071684Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * G + (-1 + 2 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (8 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (10 * X ^ 3 + 10 * X ^ 4 - 160 * X ^ 5 + 40 * X ^ 6 - 800 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (3 * X ^ 2 - 24 * X ^ 3 - 360 * X ^ 4 + 24 * X ^ 5 - 4368 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-54 * X + 120 * X ^ 3 + 24 * X ^ 4 - 3552 * X ^ 5) * derivative ℚ G + (108 * X - 12 * X ^ 2) * G =
      -54 * X + 6 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have hp0 : (1 * X : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * G + (-1 + 2 * X + 4 * (X * X) : ℚ⟦X⟧) * G * G + (8 * (X * X) : ℚ⟦X⟧) * G * G * G + (4 * (X * X) : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * X : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * G + (-1 + 2 * X + 4 * (X * X) : ℚ⟦X⟧) * G * G + (8 * (X * X) : ℚ⟦X⟧) * G * G * G + (4 * (X * X) : ℚ⟦X⟧) * G * G * G * G) =
      (1 : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G + (-2 + 4 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 8 * X : ℚ⟦X⟧) * G ^ 2 + (24 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (16 * X : ℚ⟦X⟧) * G ^ 3 + (16 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (8 * X : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d4, d8]
    ring
  have hd1 : (1 : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G + (-2 + 4 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 8 * X : ℚ⟦X⟧) * G ^ 2 + (24 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (16 * X : ℚ⟦X⟧) * G ^ 3 + (16 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (8 * X : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (1 : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G + (-2 + 4 * X + 8 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 8 * X : ℚ⟦X⟧) * G * G + (24 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (16 * X : ℚ⟦X⟧) * G * G * G + (16 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (8 * X : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G + (-2 + 4 * X + 8 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 8 * X : ℚ⟦X⟧) * G * G + (24 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (16 * X : ℚ⟦X⟧) * G * G * G + (16 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (8 * X : ℚ⟦X⟧) * G * G * G * G) =
      (-1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 + 4 * X + 8 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 + 4 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 + 32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (48 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (8 : ℚ⟦X⟧) * G ^ 2 + (24 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (96 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (48 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (16 : ℚ⟦X⟧) * G ^ 3 + (16 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (64 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d4, d8, d16, d24]
    ring
  have hd2 : (-1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 + 4 * X + 8 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 + 4 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 + 32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (48 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (8 : ℚ⟦X⟧) * G ^ 2 + (24 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (96 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (48 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (16 : ℚ⟦X⟧) * G ^ 3 + (16 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (64 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (-1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 + 4 * X + 8 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-2 + 4 * X + 8 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 + 32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (48 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G * G + (24 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (96 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (48 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (16 : ℚ⟦X⟧) * G * G * G + (16 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (64 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((-1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 + 4 * X + 8 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-2 + 4 * X + 8 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 + 32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (48 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G * G + (24 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (96 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (48 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (16 : ℚ⟦X⟧) * G * G * G + (16 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (64 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G * G * G * G) =
      (-1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (6 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 + 12 * X + 24 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (12 + 48 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (48 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-2 + 4 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 + 48 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (48 : ℚ⟦X⟧) * G * (derivative ℚ G) + (144 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (288 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (96 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (24 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (144 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (144 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (144 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (288 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (16 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (96 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (96 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d4, d8, d16, d24, d32, d48, d64, d96]
    ring
  have hd3 : (-1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (6 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 + 12 * X + 24 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (12 + 48 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (48 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-2 + 4 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 + 48 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (48 : ℚ⟦X⟧) * G * (derivative ℚ G) + (144 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (288 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (96 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (24 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (144 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (144 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (144 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (288 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (16 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (96 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (96 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((-1 + 2 * X : ℚ⟦X⟧) + (-2 + 4 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G + (24 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (16 * X ^ 2 : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((10 * X ^ 3 + 10 * X ^ 4 - 160 * X ^ 5 + 40 * X ^ 6 - 800 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (3 * X ^ 2 - 24 * X ^ 3 - 360 * X ^ 4 + 24 * X ^ 5 - 4368 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-54 * X + 120 * X ^ 3 + 24 * X ^ 4 - 3552 * X ^ 5) * derivative ℚ G + (108 * X - 12 * X ^ 2) * G - (-54 * X + 6 * X ^ 2)) = 0 := by
    linear_combination ((108 * X - 1080 * X ^ 2 + 3984 * X ^ 3 - 4128 * X ^ 4 - 3648 * X ^ 5 + 14208 * X ^ 6 + 38400 * X ^ 7 - 161280 * X ^ 8 + 132096 * X ^ 9 + 153600 * X ^ 10 : ℚ⟦X⟧) + (864 * X - 9072 * X ^ 2 + 31392 * X ^ 3 + 192 * X ^ 4 - 133632 * X ^ 5 + 280320 * X ^ 6 + 24576 * X ^ 7 - 872448 * X ^ 8 + 675840 * X ^ 9 + 1732608 * X ^ 10 : ℚ⟦X⟧) * G + (2592 * X - 29712 * X ^ 2 + 88032 * X ^ 3 + 214464 * X ^ 4 - 883968 * X ^ 5 + 957696 * X ^ 6 + 144384 * X ^ 7 - 2543616 * X ^ 8 + 2519040 * X ^ 9 + 6426624 * X ^ 10 + 393216 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 + (3456 * X - 47808 * X ^ 2 + 96384 * X ^ 3 + 1085952 * X ^ 4 - 2472960 * X ^ 5 - 1357824 * X ^ 6 + 4048896 * X ^ 7 - 3010560 * X ^ 8 + 5799936 * X ^ 9 + 11452416 * X ^ 10 + 1572864 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (1728 * X - 40224 * X ^ 2 + 5952 * X ^ 3 + 2487552 * X ^ 4 - 2939136 * X ^ 5 - 16166400 * X ^ 6 + 17077248 * X ^ 7 + 15962112 * X ^ 8 + 1155072 * X ^ 9 + 10788864 * X ^ 10 - 7077888 * X ^ 11 - 3145728 * X ^ 12 : ℚ⟦X⟧) * G ^ 4 + (-19584 * X ^ 2 - 50688 * X ^ 3 + 3176448 * X ^ 4 - 4608 * X ^ 5 - 44805120 * X ^ 6 + 25583616 * X ^ 7 + 96448512 * X ^ 8 - 14303232 * X ^ 9 - 21135360 * X ^ 10 - 47579136 * X ^ 11 - 44826624 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 + (-6528 * X ^ 2 - 16896 * X ^ 3 + 2463744 * X ^ 4 + 3396096 * X ^ 5 - 64164864 * X ^ 6 - 2826240 * X ^ 7 + 247418880 * X ^ 8 + 15974400 * X ^ 9 - 144211968 * X ^ 10 - 129368064 * X ^ 11 - 180092928 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 + (1204224 * X ^ 4 + 2912256 * X ^ 5 - 53256192 * X ^ 6 - 57507840 * X ^ 7 + 372080640 * X ^ 8 + 158662656 * X ^ 9 - 335806464 * X ^ 10 - 254017536 * X ^ 11 - 335020032 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 + (301056 * X ^ 4 + 728064 * X ^ 5 - 27138048 * X ^ 6 - 74096640 * X ^ 7 + 346939392 * X ^ 8 + 347848704 * X ^ 9 - 434601984 * X ^ 10 - 387317760 * X ^ 11 - 325582848 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 + (-9216000 * X ^ 6 - 39813120 * X ^ 7 + 199557120 * X ^ 8 + 410910720 * X ^ 9 - 354877440 * X ^ 10 - 414842880 * X ^ 11 - 161218560 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 + (-1843200 * X ^ 6 - 7962624 * X ^ 7 + 70189056 * X ^ 8 + 287637504 * X ^ 9 - 192086016 * X ^ 10 - 281935872 * X ^ 11 - 32243712 * X ^ 12 : ℚ⟦X⟧) * G ^ 10 + (16515072 * X ^ 8 + 112066560 * X ^ 9 - 66060288 * X ^ 10 - 108527616 * X ^ 11 : ℚ⟦X⟧) * G ^ 11 + (2752512 * X ^ 8 + 18677760 * X ^ 9 - 11010048 * X ^ 10 - 18087936 * X ^ 11 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((-54 * X + 438 * X ^ 2 - 1140 * X ^ 3 + 576 * X ^ 4 - 672 * X ^ 5 + 5856 * X ^ 6 - 14400 * X ^ 7 - 38400 * X ^ 8 + 161280 * X ^ 9 - 132096 * X ^ 10 - 153600 * X ^ 11 : ℚ⟦X⟧) + (-6 * X ^ 2 - 24 * X ^ 3 + 1296 * X ^ 4 - 5040 * X ^ 5 + 3168 * X ^ 6 - 5376 * X ^ 7 - 3840 * X ^ 8 + 200448 * X ^ 9 - 442368 * X ^ 10 + 110592 * X ^ 11 + 307200 * X ^ 12 : ℚ⟦X⟧) * (derivative ℚ G) + (120 * X ^ 3 - 840 * X ^ 4 - 480 * X ^ 5 + 17280 * X ^ 6 - 54720 * X ^ 7 + 96000 * X ^ 8 - 161280 * X ^ 9 + 138240 * X ^ 10 + 15360 * X ^ 11 + 337920 * X ^ 12 - 614400 * X ^ 13 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-432 * X + 3516 * X ^ 2 - 6984 * X ^ 3 - 7440 * X ^ 4 + 1920 * X ^ 5 + 95040 * X ^ 6 - 201600 * X ^ 7 - 189696 * X ^ 8 + 1004544 * X ^ 9 - 522240 * X ^ 10 - 1732608 * X ^ 11 : ℚ⟦X⟧) * G + (-36 * X ^ 2 - 384 * X ^ 3 + 9264 * X ^ 4 - 24192 * X ^ 5 - 46848 * X ^ 6 + 100608 * X ^ 7 - 404736 * X ^ 8 + 2823168 * X ^ 9 - 4297728 * X ^ 10 - 1228800 * X ^ 11 + 4521984 * X ^ 12 + 1228800 * X ^ 13 : ℚ⟦X⟧) * G * (derivative ℚ G) + (480 * X ^ 3 - 3360 * X ^ 4 - 7680 * X ^ 5 + 97920 * X ^ 6 - 134400 * X ^ 7 - 295680 * X ^ 8 + 645120 * X ^ 9 - 1259520 * X ^ 10 + 2027520 * X ^ 11 + 5591040 * X ^ 12 - 8355840 * X ^ 13 - 4915200 * X ^ 14 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-1296 * X + 10572 * X ^ 2 - 7512 * X ^ 3 - 86544 * X ^ 4 - 3648 * X ^ 5 + 692544 * X ^ 6 - 1211520 * X ^ 7 + 59136 * X ^ 8 + 2565120 * X ^ 9 - 1333248 * X ^ 10 - 5898240 * X ^ 11 + 221184 * X ^ 12 : ℚ⟦X⟧) * G ^ 2 + (-72 * X ^ 2 - 1008 * X ^ 3 + 22128 * X ^ 4 - 26784 * X ^ 5 - 312384 * X ^ 6 + 425472 * X ^ 7 - 2241792 * X ^ 8 + 14965248 * X ^ 9 - 15074304 * X ^ 10 - 19636224 * X ^ 11 + 22093824 * X ^ 12 + 12189696 * X ^ 13 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (480 * X ^ 3 - 3360 * X ^ 4 - 30720 * X ^ 5 + 213120 * X ^ 6 + 326400 * X ^ 7 - 3383040 * X ^ 8 + 3502080 * X ^ 9 + 675840 * X ^ 10 - 3563520 * X ^ 11 + 51793920 * X ^ 12 - 43499520 * X ^ 13 - 78151680 * X ^ 14 - 9830400 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-1728 * X + 14112 * X ^ 2 + 33696 * X ^ 3 - 316800 * X ^ 4 - 128256 * X ^ 5 + 2566656 * X ^ 6 - 3632640 * X ^ 7 + 1714176 * X ^ 8 + 5130240 * X ^ 9 - 9547776 * X ^ 10 - 6782976 * X ^ 11 + 5357568 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 + (-48 * X ^ 2 - 672 * X ^ 3 + 21792 * X ^ 4 + 33984 * X ^ 5 - 590208 * X ^ 6 - 12288 * X ^ 7 - 6271488 * X ^ 8 + 45204480 * X ^ 9 - 15108096 * X ^ 10 - 111648768 * X ^ 11 + 53329920 * X ^ 12 + 23691264 * X ^ 13 - 11599872 * X ^ 14 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-46080 * X ^ 5 + 230400 * X ^ 6 + 1413120 * X ^ 7 - 7649280 * X ^ 8 - 4608000 * X ^ 9 + 41717760 * X ^ 10 - 43868160 * X ^ 11 + 170803200 * X ^ 12 - 38830080 * X ^ 13 - 532807680 * X ^ 14 - 157286400 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (-864 * X + 7056 * X ^ 2 + 103728 * X ^ 3 - 554880 * X ^ 4 - 571968 * X ^ 5 + 5537280 * X ^ 6 - 6183168 * X ^ 7 + 2503680 * X ^ 8 + 17111040 * X ^ 9 - 51007488 * X ^ 10 + 528384 * X ^ 11 + 37380096 * X ^ 12 - 196608 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 + (10560 * X ^ 4 + 77760 * X ^ 5 - 126720 * X ^ 6 - 2545920 * X ^ 7 - 13777920 * X ^ 8 + 88473600 * X ^ 9 + 63928320 * X ^ 10 - 378839040 * X ^ 11 + 51363840 * X ^ 12 - 101990400 * X ^ 13 - 173998080 * X ^ 14 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-23040 * X ^ 5 + 115200 * X ^ 6 + 1935360 * X ^ 7 - 7511040 * X ^ 8 - 32532480 * X ^ 9 + 119900160 * X ^ 10 - 15667200 * X ^ 11 + 130498560 * X ^ 12 + 314818560 * X ^ 13 - 1906606080 * X ^ 14 - 1091174400 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (104256 * X ^ 3 - 475776 * X ^ 4 - 1211520 * X ^ 5 + 7414272 * X ^ 6 - 6288384 * X ^ 7 - 4755456 * X ^ 8 + 58398720 * X ^ 9 - 149016576 * X ^ 10 - 16785408 * X ^ 11 + 134873088 * X ^ 12 + 1179648 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 + (4224 * X ^ 4 + 31104 * X ^ 5 + 841728 * X ^ 6 - 5222400 * X ^ 7 - 26477568 * X ^ 8 + 114395136 * X ^ 9 + 294776832 * X ^ 10 - 834625536 * X ^ 11 - 165150720 * X ^ 12 - 550600704 * X ^ 13 - 1039466496 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (1474560 * X ^ 7 - 4423680 * X ^ 8 - 48660480 * X ^ 9 + 131235840 * X ^ 10 + 267632640 * X ^ 11 - 354631680 * X ^ 12 + 896532480 * X ^ 13 - 3801415680 * X ^ 14 - 4187750400 * X ^ 15 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (34752 * X ^ 3 - 158592 * X ^ 4 - 1407360 * X ^ 5 + 6320640 * X ^ 6 - 4174848 * X ^ 7 - 21282816 * X ^ 8 + 132900864 * X ^ 9 - 253931520 * X ^ 10 - 141680640 * X ^ 11 + 314966016 * X ^ 12 - 19660800 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 + (892416 * X ^ 6 - 4204032 * X ^ 7 - 39029760 * X ^ 8 + 97069056 * X ^ 9 + 593166336 * X ^ 10 - 1159667712 * X ^ 11 - 948928512 * X ^ 12 - 1000538112 * X ^ 13 - 3378708480 * X ^ 14 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (491520 * X ^ 7 - 1474560 * X ^ 8 - 36864000 * X ^ 9 + 64389120 * X ^ 10 + 564019200 * X ^ 11 - 758169600 * X ^ 12 + 463994880 * X ^ 13 - 4157276160 * X ^ 14 - 9653452800 * X ^ 15 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (-860160 * X ^ 5 + 3299328 * X ^ 6 - 2445312 * X ^ 7 - 33841152 * X ^ 8 + 195035136 * X ^ 9 - 239370240 * X ^ 10 - 428408832 * X ^ 11 + 533594112 * X ^ 12 - 150994944 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 + (254976 * X ^ 6 - 1201152 * X ^ 7 - 36956160 * X ^ 8 + 53538816 * X ^ 9 + 708280320 * X ^ 10 - 911130624 * X ^ 11 - 2288320512 * X ^ 12 - 694026240 * X ^ 13 - 6660685824 * X ^ 14 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-17694720 * X ^ 9 + 17694720 * X ^ 10 + 489553920 * X ^ 11 - 465960960 * X ^ 12 - 1179648000 * X ^ 13 - 2146959360 * X ^ 14 - 13683916800 * X ^ 15 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (-215040 * X ^ 5 + 824832 * X ^ 6 - 1440768 * X ^ 7 - 29657088 * X ^ 8 + 187699200 * X ^ 9 - 67215360 * X ^ 10 - 747061248 * X ^ 11 + 675151872 * X ^ 12 - 405209088 * X ^ 13 : ℚ⟦X⟧) * G ^ 8 + (-19353600 * X ^ 8 + 19353600 * X ^ 9 + 537108480 * X ^ 10 - 258048000 * X ^ 11 - 3134914560 * X ^ 12 + 206438400 * X ^ 13 - 8216248320 * X ^ 14 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (-4423680 * X ^ 9 + 4423680 * X ^ 10 + 225607680 * X ^ 11 - 13271040 * X ^ 12 - 1946419200 * X ^ 13 - 123863040 * X ^ 14 - 11678515200 * X ^ 15 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (-552960 * X ^ 7 - 14131200 * X ^ 8 + 118579200 * X ^ 9 + 108625920 * X ^ 10 - 815923200 * X ^ 11 + 616366080 * X ^ 12 - 556400640 * X ^ 13 : ℚ⟦X⟧) * G ^ 9 + (-4300800 * X ^ 8 + 4300800 * X ^ 9 + 267141120 * X ^ 10 + 139100160 * X ^ 11 - 2498887680 * X ^ 12 + 615383040 * X ^ 13 - 6208880640 * X ^ 14 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (68812800 * X ^ 11 + 68812800 * X ^ 12 - 1101004800 * X ^ 13 + 275251200 * X ^ 14 - 5505024000 * X ^ 15 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (-110592 * X ^ 7 - 2826240 * X ^ 8 + 49668096 * X ^ 9 + 135266304 * X ^ 10 - 552468480 * X ^ 11 + 378470400 * X ^ 12 - 422707200 * X ^ 13 : ℚ⟦X⟧) * G ^ 10 + (88670208 * X ^ 10 + 117866496 * X ^ 11 - 1081344000 * X ^ 12 + 341704704 * X ^ 13 - 2629828608 * X ^ 14 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (13762560 * X ^ 11 + 13762560 * X ^ 12 - 220200960 * X ^ 13 + 55050240 * X ^ 14 - 1101004800 * X ^ 15 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (14155776 * X ^ 9 + 61931520 * X ^ 10 - 212336640 * X ^ 11 + 139198464 * X ^ 12 - 169869312 * X ^ 13 : ℚ⟦X⟧) * G ^ 11 + (16121856 * X ^ 10 + 21430272 * X ^ 11 - 196608000 * X ^ 12 + 62128128 * X ^ 13 - 478150656 * X ^ 14 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (2359296 * X ^ 9 + 10321920 * X ^ 10 - 35389440 * X ^ 11 + 23199744 * X ^ 12 - 28311552 * X ^ 13 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((3 * X ^ 2 + 12 * X ^ 3 - 396 * X ^ 4 + 1632 * X ^ 5 - 6144 * X ^ 6 + 28416 * X ^ 7 - 72000 * X ^ 8 + 80640 * X ^ 9 - 31488 * X ^ 10 : ℚ⟦X⟧) + (-60 * X ^ 3 + 420 * X ^ 4 + 240 * X ^ 5 - 8640 * X ^ 6 + 28320 * X ^ 7 - 50880 * X ^ 8 + 65280 * X ^ 9 - 161280 * X ^ 11 + 153600 * X ^ 12 : ℚ⟦X⟧) * (derivative ℚ G) + (24 * X ^ 2 + 96 * X ^ 3 - 2784 * X ^ 4 + 10560 * X ^ 5 - 43872 * X ^ 6 + 240384 * X ^ 7 - 549120 * X ^ 8 + 250368 * X ^ 9 + 471552 * X ^ 10 - 350208 * X ^ 11 : ℚ⟦X⟧) * G + (-360 * X ^ 3 + 2520 * X ^ 4 + 4320 * X ^ 5 - 66240 * X ^ 6 + 135360 * X ^ 7 + 11520 * X ^ 8 - 391680 * X ^ 9 + 1474560 * X ^ 10 - 2903040 * X ^ 11 + 829440 * X ^ 12 + 1843200 * X ^ 13 : ℚ⟦X⟧) * G * (derivative ℚ G) + (72 * X ^ 2 + 288 * X ^ 3 - 6048 * X ^ 4 + 16704 * X ^ 5 - 110304 * X ^ 6 + 831744 * X ^ 7 - 1410048 * X ^ 8 - 2128896 * X ^ 9 + 5746176 * X ^ 10 - 1290240 * X ^ 11 - 1179648 * X ^ 12 : ℚ⟦X⟧) * G ^ 2 + (-720 * X ^ 3 + 5040 * X ^ 4 + 23040 * X ^ 5 - 204480 * X ^ 6 + 51840 * X ^ 7 + 1745280 * X ^ 8 - 3916800 * X ^ 9 + 6958080 * X ^ 10 - 8939520 * X ^ 11 - 12625920 * X ^ 12 + 23592960 * X ^ 13 + 7372800 * X ^ 14 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (96 * X ^ 2 + 384 * X ^ 3 - 384 * X ^ 4 - 27648 * X ^ 5 - 131328 * X ^ 6 + 1649664 * X ^ 7 - 597504 * X ^ 8 - 15227904 * X ^ 9 + 21000192 * X ^ 10 + 9695232 * X ^ 11 - 10985472 * X ^ 12 - 688128 * X ^ 13 : ℚ⟦X⟧) * G ^ 3 + (-480 * X ^ 3 + 3360 * X ^ 4 + 53760 * X ^ 5 - 328320 * X ^ 6 - 764160 * X ^ 7 + 6401280 * X ^ 8 - 7004160 * X ^ 9 - 675840 * X ^ 10 + 10567680 * X ^ 11 - 100085760 * X ^ 12 + 93634560 * X ^ 13 + 107642880 * X ^ 14 + 9830400 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (48 * X ^ 2 + 192 * X ^ 3 + 15168 * X ^ 4 - 113664 * X ^ 5 - 227712 * X ^ 6 + 2508288 * X ^ 7 + 4416768 * X ^ 8 - 42462720 * X ^ 9 + 27841536 * X ^ 10 + 81512448 * X ^ 11 - 36986880 * X ^ 12 - 8454144 * X ^ 13 + 1769472 * X ^ 14 : ℚ⟦X⟧) * G ^ 4 + (57600 * X ^ 5 - 288000 * X ^ 6 - 1843200 * X ^ 7 + 9792000 * X ^ 8 + 6681600 * X ^ 9 - 57369600 * X ^ 10 + 73267200 * X ^ 11 - 249753600 * X ^ 12 + 90316800 * X ^ 13 + 619315200 * X ^ 14 + 147456000 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (18432 * X ^ 4 - 119808 * X ^ 5 - 658944 * X ^ 6 + 3465216 * X ^ 7 + 12367872 * X ^ 8 - 67092480 * X ^ 9 - 22468608 * X ^ 10 + 259448832 * X ^ 11 - 32956416 * X ^ 12 - 45711360 * X ^ 13 + 21233664 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 + (23040 * X ^ 5 - 115200 * X ^ 6 - 2027520 * X ^ 7 + 7787520 * X ^ 8 + 33638400 * X ^ 9 - 126167040 * X ^ 10 + 39260160 * X ^ 11 - 172523520 * X ^ 12 - 288276480 * X ^ 13 + 1856471040 * X ^ 14 + 914227200 * X ^ 15 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (6144 * X ^ 4 - 39936 * X ^ 5 - 993792 * X ^ 6 + 3563520 * X ^ 7 + 19433472 * X ^ 8 - 67436544 * X ^ 9 - 139388928 * X ^ 10 + 461512704 * X ^ 11 + 134307840 * X ^ 12 - 143622144 * X ^ 13 + 109707264 * X ^ 14 : ℚ⟦X⟧) * G ^ 6 + (-1290240 * X ^ 7 + 3870720 * X ^ 8 + 41287680 * X ^ 9 - 113541120 * X ^ 10 - 203857920 * X ^ 11 + 270950400 * X ^ 12 - 784465920 * X ^ 13 + 3148185600 * X ^ 14 + 3096576000 * X ^ 15 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-663552 * X ^ 6 + 2064384 * X ^ 7 + 21381120 * X ^ 8 - 44531712 * X ^ 9 - 244334592 * X ^ 10 + 496041984 * X ^ 11 + 522584064 * X ^ 12 - 291373056 * X ^ 13 + 318504960 * X ^ 14 : ℚ⟦X⟧) * G ^ 7 + (-368640 * X ^ 7 + 1105920 * X ^ 8 + 26542080 * X ^ 9 - 47185920 * X ^ 10 - 391495680 * X ^ 11 + 540426240 * X ^ 12 - 436469760 * X ^ 13 + 2987458560 * X ^ 14 + 6311116800 * X ^ 15 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-165888 * X ^ 6 + 516096 * X ^ 7 + 15667200 * X ^ 8 - 18505728 * X ^ 9 - 251596800 * X ^ 10 + 303316992 * X ^ 11 + 906264576 * X ^ 12 - 399605760 * X ^ 13 + 568000512 * X ^ 14 : ℚ⟦X⟧) * G ^ 8 + (11059200 * X ^ 9 - 11059200 * X ^ 10 - 298598400 * X ^ 11 + 298598400 * X ^ 12 + 619315200 * X ^ 13 + 1371340800 * X ^ 14 + 7962624000 * X ^ 15 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (6881280 * X ^ 8 - 4915200 * X ^ 9 - 168099840 * X ^ 10 + 58982400 * X ^ 11 + 949616640 * X ^ 12 - 373555200 * X ^ 13 + 637009920 * X ^ 14 : ℚ⟦X⟧) * G ^ 9 + (2457600 * X ^ 9 - 2457600 * X ^ 10 - 120422400 * X ^ 11 + 12288000 * X ^ 12 + 1002700800 * X ^ 13 + 88473600 * X ^ 14 + 6094848000 * X ^ 15 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (1376256 * X ^ 8 - 983040 * X ^ 9 - 74711040 * X ^ 10 - 48758784 * X ^ 11 + 622460928 * X ^ 12 - 230424576 * X ^ 13 + 438829056 * X ^ 14 : ℚ⟦X⟧) * G ^ 10 + (-32440320 * X ^ 11 - 32440320 * X ^ 12 + 519045120 * X ^ 13 - 129761280 * X ^ 14 + 2595225600 * X ^ 15 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (-22413312 * X ^ 10 - 33030144 * X ^ 11 + 235929600 * X ^ 12 - 84934656 * X ^ 13 + 169869312 * X ^ 14 : ℚ⟦X⟧) * G ^ 11 + (-5898240 * X ^ 11 - 5898240 * X ^ 12 + 94371840 * X ^ 13 - 23592960 * X ^ 14 + 471859200 * X ^ 15 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-3735552 * X ^ 10 - 5505024 * X ^ 11 + 39321600 * X ^ 12 - 14155776 * X ^ 13 + 28311552 * X ^ 14 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((10 * X ^ 3 - 70 * X ^ 4 + 1240 * X ^ 6 - 5120 * X ^ 7 + 12640 * X ^ 8 - 23040 * X ^ 9 + 26240 * X ^ 10 - 12800 * X ^ 11 : ℚ⟦X⟧) + (80 * X ^ 3 - 560 * X ^ 4 - 320 * X ^ 5 + 11520 * X ^ 6 - 37760 * X ^ 7 + 67840 * X ^ 8 - 87040 * X ^ 9 + 215040 * X ^ 11 - 204800 * X ^ 12 : ℚ⟦X⟧) * G + (240 * X ^ 3 - 1680 * X ^ 4 - 2880 * X ^ 5 + 44160 * X ^ 6 - 90240 * X ^ 7 - 7680 * X ^ 8 + 261120 * X ^ 9 - 983040 * X ^ 10 + 1935360 * X ^ 11 - 552960 * X ^ 12 - 1228800 * X ^ 13 : ℚ⟦X⟧) * G ^ 2 + (320 * X ^ 3 - 2240 * X ^ 4 - 10240 * X ^ 5 + 90880 * X ^ 6 - 23040 * X ^ 7 - 775680 * X ^ 8 + 1740800 * X ^ 9 - 3092480 * X ^ 10 + 3973120 * X ^ 11 + 5611520 * X ^ 12 - 10485760 * X ^ 13 - 3276800 * X ^ 14 : ℚ⟦X⟧) * G ^ 3 + (160 * X ^ 3 - 1120 * X ^ 4 - 17920 * X ^ 5 + 109440 * X ^ 6 + 254720 * X ^ 7 - 2133760 * X ^ 8 + 2334720 * X ^ 9 + 225280 * X ^ 10 - 3522560 * X ^ 11 + 33361920 * X ^ 12 - 31211520 * X ^ 13 - 35880960 * X ^ 14 - 3276800 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 + (-15360 * X ^ 5 + 76800 * X ^ 6 + 491520 * X ^ 7 - 2611200 * X ^ 8 - 1781760 * X ^ 9 + 15298560 * X ^ 10 - 19537920 * X ^ 11 + 66600960 * X ^ 12 - 24084480 * X ^ 13 - 165150720 * X ^ 14 - 39321600 * X ^ 15 : ℚ⟦X⟧) * G ^ 5 + (-5120 * X ^ 5 + 25600 * X ^ 6 + 450560 * X ^ 7 - 1730560 * X ^ 8 - 7475200 * X ^ 9 + 28037120 * X ^ 10 - 8724480 * X ^ 11 + 38338560 * X ^ 12 + 64061440 * X ^ 13 - 412549120 * X ^ 14 - 203161600 * X ^ 15 : ℚ⟦X⟧) * G ^ 6 + (245760 * X ^ 7 - 737280 * X ^ 8 - 7864320 * X ^ 9 + 21626880 * X ^ 10 + 38830080 * X ^ 11 - 51609600 * X ^ 12 + 149422080 * X ^ 13 - 599654400 * X ^ 14 - 589824000 * X ^ 15 : ℚ⟦X⟧) * G ^ 7 + (61440 * X ^ 7 - 184320 * X ^ 8 - 4423680 * X ^ 9 + 7864320 * X ^ 10 + 65249280 * X ^ 11 - 90071040 * X ^ 12 + 72744960 * X ^ 13 - 497909760 * X ^ 14 - 1051852800 * X ^ 15 : ℚ⟦X⟧) * G ^ 8 + (-1638400 * X ^ 9 + 1638400 * X ^ 10 + 44236800 * X ^ 11 - 44236800 * X ^ 12 - 91750400 * X ^ 13 - 203161600 * X ^ 14 - 1179648000 * X ^ 15 : ℚ⟦X⟧) * G ^ 9 + (-327680 * X ^ 9 + 327680 * X ^ 10 + 16056320 * X ^ 11 - 1638400 * X ^ 12 - 133693440 * X ^ 13 - 11796480 * X ^ 14 - 812646400 * X ^ 15 : ℚ⟦X⟧) * G ^ 10 + (3932160 * X ^ 11 + 3932160 * X ^ 12 - 62914560 * X ^ 13 + 15728640 * X ^ 14 - 314572800 * X ^ 15 : ℚ⟦X⟧) * G ^ 11 + (655360 * X ^ 11 + 655360 * X ^ 12 - 10485760 * X ^ 13 + 2621440 * X ^ 14 - 52428800 * X ^ 15 : ℚ⟦X⟧) * G ^ 12) * hd3
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have hPG : (-1 + 2 * X : ℚ⟦X⟧) + (-2 + 4 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G + (24 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (16 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * G + (-1 + 2 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (8 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 10 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C 10 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-160) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C 40 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C (-800) + derivative ℚ (derivative ℚ G) * X * X * C 3 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-24) + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-360) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 24 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-4368) +
      derivative ℚ G * X * C (-54) + derivative ℚ G * X * X * X * C 120 +
      derivative ℚ G * X * X * X * X * C 24 + derivative ℚ G * X * X * X * X * X * C (-3552) +
      G * X * C 108 + G * X * X * C (-12) =
      C (-54) * X + C 6 * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * G + (-1 + 2 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (8 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    10 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 10 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-160) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 40 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-800) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 3 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-24) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-360) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      24 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-4368) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-54) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 120 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      24 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-3552) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      108 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-12) * coeff (m + 1 + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * G + (-1 + 2 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (8 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    240 * coeff (0 + 1 + 1 + 1 + 1) G + 60 * coeff (0 + 1 + 1 + 1) G +
      36 * coeff (0 + 1 + 1 + 1 + 1) G + (-144) * coeff (0 + 1 + 1 + 1) G +
      (-720) * coeff (0 + 1 + 1) G + (-216) * coeff (0 + 1 + 1 + 1 + 1) G +
      240 * coeff (0 + 1 + 1) G + 24 * coeff (0 + 1) G +
      108 * coeff (0 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * G + (-1 + 2 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (8 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    600 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 240 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-960) * coeff (0 + 1 + 1 + 1) G + 60 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-288) * coeff (0 + 1 + 1 + 1 + 1) G + (-2160) * coeff (0 + 1 + 1 + 1) G +
      48 * coeff (0 + 1 + 1) G + (-270) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      360 * coeff (0 + 1 + 1 + 1) G + 48 * coeff (0 + 1 + 1) G +
      (-3552) * coeff (0 + 1) G + 108 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-12) * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE2 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 2 * X : ℚ⟦X⟧) * G + (-1 + 2 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (8 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    1200 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 600 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-3840) * coeff (0 + 1 + 1 + 1 + 1) G + 240 * coeff (0 + 1 + 1 + 1) G +
      90 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-480) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-4320) * coeff (0 + 1 + 1 + 1 + 1) G + 144 * coeff (0 + 1 + 1 + 1) G +
      (-8736) * coeff (0 + 1 + 1) G + (-324) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      480 * coeff (0 + 1 + 1 + 1 + 1) G + 72 * coeff (0 + 1 + 1 + 1) G +
      (-7104) * coeff (0 + 1 + 1) G + 108 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-12) * coeff (0 + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A071684Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a071684.main := by
  intro T W G hT _ hW _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  have hn : ((4) * PowerSeries.X) * ((64) * PowerSeries.X ^ 3) = (256 * PowerSeries.X ^ 4 : PowerSeries ℚ) := by
    linear_combination (0 : PowerSeries ℚ) * hT
  have hnu0 : (256 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (256 : PowerSeries ℚ) = 256 := A071684Aux.cnum 256
    simp [kc] at h'
  have hnu : (256 * PowerSeries.X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    have e : (256 * PowerSeries.X ^ 4 : PowerSeries ℚ) = PowerSeries.X ^ 4 * (256 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 4 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((4) * PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((4) * PowerSeries.X) ^ 4 * ((PowerSeries.X : PowerSeries ℚ) + (-1 + 2 * PowerSeries.X : PowerSeries ℚ) * G + (-1 + 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (8 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3 + (4 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((12) * PowerSeries.X ^ 2 + (-16) * PowerSeries.X ^ 2 * T * W + (4) * PowerSeries.X ^ 2 * T ^ 2 + (16) * PowerSeries.X ^ 3 + (64) * PowerSeries.X ^ 4) * hT +
      ((-12) * PowerSeries.X ^ 2 + (4) * PowerSeries.X ^ 2 * W ^ 2 + (-16) * PowerSeries.X ^ 2 * T * W + (24) * PowerSeries.X ^ 2 * T ^ 2 + (32) * PowerSeries.X ^ 3 + (-16) * PowerSeries.X ^ 4) * hW +
      ((-16) * PowerSeries.X ^ 2 * W + (4) * PowerSeries.X ^ 2 * W ^ 3 + (16) * PowerSeries.X ^ 2 * T + (-12) * PowerSeries.X ^ 2 * T * W ^ 2 + (12) * PowerSeries.X ^ 2 * T ^ 2 * W + (-4) * PowerSeries.X ^ 2 * T ^ 3 + (-32) * PowerSeries.X ^ 3 + (32) * PowerSeries.X ^ 3 * W + (8) * PowerSeries.X ^ 3 * W ^ 2 + (-32) * PowerSeries.X ^ 3 * T + (-16) * PowerSeries.X ^ 3 * T * W + (8) * PowerSeries.X ^ 3 * T ^ 2 + (-64) * PowerSeries.X ^ 3 * G + (16) * PowerSeries.X ^ 3 * G * W ^ 2 + (-32) * PowerSeries.X ^ 3 * G * T * W + (16) * PowerSeries.X ^ 3 * G * T ^ 2 + (64) * PowerSeries.X ^ 4 + (-16) * PowerSeries.X ^ 4 * W + (16) * PowerSeries.X ^ 4 * T + (128) * PowerSeries.X ^ 4 * G + (64) * PowerSeries.X ^ 4 * G * W + (-64) * PowerSeries.X ^ 4 * G * T + (64) * PowerSeries.X ^ 4 * G ^ 2 * W + (-64) * PowerSeries.X ^ 4 * G ^ 2 * T + (-32) * PowerSeries.X ^ 5 + (64) * PowerSeries.X ^ 5 * G + (384) * PowerSeries.X ^ 5 * G ^ 2 + (256) * PowerSeries.X ^ 5 * G ^ 3) * hG
  have hP : (PowerSeries.X : PowerSeries ℚ) + (-1 + 2 * PowerSeries.X : PowerSeries ℚ) * G + (-1 + 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (8 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3 + (4 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A071684Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A071684Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A071684Aux.relE2 G hP h0c
        push_cast
        linear_combination r
      | succ m =>
        have r := A071684Aux.rel G hP h0c m
        push_cast
        linear_combination r
