import OMAStatements.S_oeis_a172066

-- Problem: A172066: Expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=9.
-- Upstream: formal-conjectures statements/oeis-a172066.lean:0 (declaration OMA.S_oeis_a172066.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A172066Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-512 * X ^ 9 + 2048 * X ^ 10 + (1536 * X ^ 9) * S) = 512 - 4608 * X + 13824 * X ^ 2 - 15360 * X ^ 3 + 4608 * X ^ 4 + (-512 + 3584 * X - 7680 * X ^ 2 + 5120 * X ^ 3 - 512 * X ^ 4) * S) :
    (2199023255552 * X - 25288767438848 * X ^ 2 + 98956046499840 * X ^ 3 - 133040906960896 * X ^ 4 - 21990232555520 * X ^ 5 + 102254581383168 * X ^ 6 + 15393162788864 * X ^ 7 - 8796093022208 * X ^ 8) * derivative ℚ G + (19791209299968 - 213305255788544 * X + 765260092932096 * X ^ 2 - 884007348731904 * X ^ 3 - 292470092988416 * X ^ 4 + 639915767365632 * X ^ 5 + 131941395333120 * X ^ 6 - 48378511622144 * X ^ 7) * G = 19791209299968 + 6597069766656 * X := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d524288 : derivative ℚ (524288 : ℚ⟦X⟧) = 0 := dnum 524288
  have d1048576 : derivative ℚ (1048576 : ℚ⟦X⟧) = 0 := dnum 1048576
  have d1572864 : derivative ℚ (1572864 : ℚ⟦X⟧) = 0 := dnum 1572864
  have d2097152 : derivative ℚ (2097152 : ℚ⟦X⟧) = 0 := dnum 2097152
  have d3670016 : derivative ℚ (3670016 : ℚ⟦X⟧) = 0 := dnum 3670016
  have d4194304 : derivative ℚ (4194304 : ℚ⟦X⟧) = 0 := dnum 4194304
  have d5242880 : derivative ℚ (5242880 : ℚ⟦X⟧) = 0 := dnum 5242880
  have d6291456 : derivative ℚ (6291456 : ℚ⟦X⟧) = 0 := dnum 6291456
  have d7340032 : derivative ℚ (7340032 : ℚ⟦X⟧) = 0 := dnum 7340032
  have d9961472 : derivative ℚ (9961472 : ℚ⟦X⟧) = 0 := dnum 9961472
  have d17301504 : derivative ℚ (17301504 : ℚ⟦X⟧) = 0 := dnum 17301504
  have d18874368 : derivative ℚ (18874368 : ℚ⟦X⟧) = 0 := dnum 18874368
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-2097152 * X ^ 18 + 7340032 * X ^ 19 + 4194304 * X ^ 20) * G = (524288 * X ^ 9 - 5242880 * X ^ 10 + 17301504 * X ^ 11 - 18874368 * X ^ 12 - 1572864 * X ^ 13 + 6291456 * X ^ 14 : ℚ⟦X⟧) + (-524288 * X ^ 9 + 4194304 * X ^ 10 - 9961472 * X ^ 11 + 5242880 * X ^ 12 + 3670016 * X ^ 13 - 1048576 * X ^ 14) * S := by
    linear_combination (-512 * X ^ 9 + 2048 * X ^ 10 - (1536 * X ^ 9) * S) * hG + (1536 * X ^ 9) * ((1536 * X ^ 9) * G - (-512 + 3584 * X - 7680 * X ^ 2 + 5120 * X ^ 3 - 512 * X ^ 4)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-2097152 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 7340032 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 4194304 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-37748736 * X ^ 17 + 139460608 * X ^ 18 + 83886080 * X ^ 19) * G + (-2097152 * X ^ 18 + 7340032 * X ^ 19 + 4194304 * X ^ 20) * derivative ℚ G := by
    simp [Derivation.leibniz, d2097152, d4194304, d7340032]
    ring
  have hR : derivative ℚ ((524288 * (X * X * X * X * X * X * X * X * X) - 5242880 * (X * X * X * X * X * X * X * X * X * X) + 17301504 * (X * X * X * X * X * X * X * X * X * X * X) - 18874368 * (X * X * X * X * X * X * X * X * X * X * X * X) - 1572864 * (X * X * X * X * X * X * X * X * X * X * X * X * X) + 6291456 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-524288 * (X * X * X * X * X * X * X * X * X) + 4194304 * (X * X * X * X * X * X * X * X * X * X) - 9961472 * (X * X * X * X * X * X * X * X * X * X * X) + 5242880 * (X * X * X * X * X * X * X * X * X * X * X * X) + 3670016 * (X * X * X * X * X * X * X * X * X * X * X * X * X) - 1048576 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      4718592 * X ^ 8 - 52428800 * X ^ 9 + 190316544 * X ^ 10 - 226492416 * X ^ 11 - 20447232 * X ^ 12 + 88080384 * X ^ 13 + (-4718592 * X ^ 8 + 41943040 * X ^ 9 - 109576192 * X ^ 10 + 62914560 * X ^ 11 + 47710208 * X ^ 12 - 14680064 * X ^ 13) * S + (-524288 * X ^ 9 + 4194304 * X ^ 10 - 9961472 * X ^ 11 + 5242880 * X ^ 12 + 3670016 * X ^ 13 - 1048576 * X ^ 14) * derivative ℚ S := by
    simp [Derivation.leibniz, d524288, d1048576, d1572864, d3670016, d4194304, d5242880, d6291456, d9961472, d17301504, d18874368]
    ring
  have hk2 : (-2097152 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 7340032 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 4194304 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (524288 * (X * X * X * X * X * X * X * X * X) - 5242880 * (X * X * X * X * X * X * X * X * X * X) + 17301504 * (X * X * X * X * X * X * X * X * X * X * X) - 18874368 * (X * X * X * X * X * X * X * X * X * X * X * X) - 1572864 * (X * X * X * X * X * X * X * X * X * X * X * X * X) + 6291456 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-524288 * (X * X * X * X * X * X * X * X * X) + 4194304 * (X * X * X * X * X * X * X * X * X * X) - 9961472 * (X * X * X * X * X * X * X * X * X * X * X) + 5242880 * (X * X * X * X * X * X * X * X * X * X * X * X) + 3670016 * (X * X * X * X * X * X * X * X * X * X * X * X * X) - 1048576 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-37748736 * X ^ 17 + 139460608 * X ^ 18 + 83886080 * X ^ 19) * G + (-2097152 * X ^ 18 + 7340032 * X ^ 19 + 4194304 * X ^ 20) * derivative ℚ G =
      4718592 * X ^ 8 - 52428800 * X ^ 9 + 190316544 * X ^ 10 - 226492416 * X ^ 11 - 20447232 * X ^ 12 + 88080384 * X ^ 13 + (-4718592 * X ^ 8 + 41943040 * X ^ 9 - 109576192 * X ^ 10 + 62914560 * X ^ 11 + 47710208 * X ^ 12 - 14680064 * X ^ 13) * S + (-524288 * X ^ 9 + 4194304 * X ^ 10 - 9961472 * X ^ 11 + 5242880 * X ^ 12 + 3670016 * X ^ 13 - 1048576 * X ^ 14) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 26 * ((1 - 4 * X) * ((2199023255552 * X - 25288767438848 * X ^ 2 + 98956046499840 * X ^ 3 - 133040906960896 * X ^ 4 - 21990232555520 * X ^ 5 + 102254581383168 * X ^ 6 + 15393162788864 * X ^ 7 - 8796093022208 * X ^ 8) * derivative ℚ G + (19791209299968 - 213305255788544 * X + 765260092932096 * X ^ 2 - 884007348731904 * X ^ 3 - 292470092988416 * X ^ 4 + 639915767365632 * X ^ 5 + 131941395333120 * X ^ 6 - 48378511622144 * X ^ 7) * G - (19791209299968 + 6597069766656 * X))) = 0 := by
    linear_combination (-524288 * X ^ 9 + 4194304 * X ^ 10 - 9961472 * X ^ 11 + 5242880 * X ^ 12 + 3670016 * X ^ 13 - 1048576 * X ^ 14) ^ 2 * S * hdS - 2 * (-524288 * X ^ 9 + 4194304 * X ^ 10 - 9961472 * X ^ 11 + 5242880 * X ^ 12 + 3670016 * X ^ 13 - 1048576 * X ^ 14) ^ 2 * derivative ℚ S * hS -
      (2 * (-4718592 * X ^ 8 + 41943040 * X ^ 9 - 109576192 * X ^ 10 + 62914560 * X ^ 11 + 47710208 * X ^ 12 - 14680064 * X ^ 13) * (1 - 4 * X) + (-524288 * X ^ 9 + 4194304 * X ^ 10 - 9961472 * X ^ 11 + 5242880 * X ^ 12 + 3670016 * X ^ 13 - 1048576 * X ^ 14) * (-4)) * hk + 2 * (-524288 * X ^ 9 + 4194304 * X ^ 10 - 9961472 * X ^ 11 + 5242880 * X ^ 12 + 3670016 * X ^ 13 - 1048576 * X ^ 14) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 26 ≠ 0 := pow_ne_zero 26 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-512 * X ^ 9 + 2048 * X ^ 10 + (1536 * X ^ 9) * S) = 512 - 4608 * X + 13824 * X ^ 2 - 15360 * X ^ 3 + 4608 * X ^ 4 + (-512 + 3584 * X - 7680 * X ^ 2 + 5120 * X ^ 3 - 512 * X ^ 4) * S) :
    (2 * X ^ 3 - 7 * X ^ 4 - 4 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (34 * X ^ 2 - 136 * X ^ 3 - 90 * X ^ 4) * derivative ℚ (derivative ℚ G) + (120 * X - 758 * X ^ 2 - 582 * X ^ 3) * derivative ℚ G + (-1200 * X - 1056 * X ^ 2) * G =
      0 := by
  have h := key S G hS hG
  have d2199023255552 : derivative ℚ (2199023255552 : ℚ⟦X⟧) = 0 := dnum 2199023255552
  have d6597069766656 : derivative ℚ (6597069766656 : ℚ⟦X⟧) = 0 := dnum 6597069766656
  have d8796093022208 : derivative ℚ (8796093022208 : ℚ⟦X⟧) = 0 := dnum 8796093022208
  have d15393162788864 : derivative ℚ (15393162788864 : ℚ⟦X⟧) = 0 := dnum 15393162788864
  have d19791209299968 : derivative ℚ (19791209299968 : ℚ⟦X⟧) = 0 := dnum 19791209299968
  have d21990232555520 : derivative ℚ (21990232555520 : ℚ⟦X⟧) = 0 := dnum 21990232555520
  have d25288767438848 : derivative ℚ (25288767438848 : ℚ⟦X⟧) = 0 := dnum 25288767438848
  have d48378511622144 : derivative ℚ (48378511622144 : ℚ⟦X⟧) = 0 := dnum 48378511622144
  have d50577534877696 : derivative ℚ (50577534877696 : ℚ⟦X⟧) = 0 := dnum 50577534877696
  have d70368744177664 : derivative ℚ (70368744177664 : ℚ⟦X⟧) = 0 := dnum 70368744177664
  have d98956046499840 : derivative ℚ (98956046499840 : ℚ⟦X⟧) = 0 := dnum 98956046499840
  have d102254581383168 : derivative ℚ (102254581383168 : ℚ⟦X⟧) = 0 := dnum 102254581383168
  have d107752139522048 : derivative ℚ (107752139522048 : ℚ⟦X⟧) = 0 := dnum 107752139522048
  have d109951162777600 : derivative ℚ (109951162777600 : ℚ⟦X⟧) = 0 := dnum 109951162777600
  have d131941395333120 : derivative ℚ (131941395333120 : ℚ⟦X⟧) = 0 := dnum 131941395333120
  have d133040906960896 : derivative ℚ (133040906960896 : ℚ⟦X⟧) = 0 := dnum 133040906960896
  have d213305255788544 : derivative ℚ (213305255788544 : ℚ⟦X⟧) = 0 := dnum 213305255788544
  have d292470092988416 : derivative ℚ (292470092988416 : ℚ⟦X⟧) = 0 := dnum 292470092988416
  have d296868139499520 : derivative ℚ (296868139499520 : ℚ⟦X⟧) = 0 := dnum 296868139499520
  have d338649581355008 : derivative ℚ (338649581355008 : ℚ⟦X⟧) = 0 := dnum 338649581355008
  have d532163627843584 : derivative ℚ (532163627843584 : ℚ⟦X⟧) = 0 := dnum 532163627843584
  have d613527488299008 : derivative ℚ (613527488299008 : ℚ⟦X⟧) = 0 := dnum 613527488299008
  have d639915767365632 : derivative ℚ (639915767365632 : ℚ⟦X⟧) = 0 := dnum 639915767365632
  have d765260092932096 : derivative ℚ (765260092932096 : ℚ⟦X⟧) = 0 := dnum 765260092932096
  have d791648371998720 : derivative ℚ (791648371998720 : ℚ⟦X⟧) = 0 := dnum 791648371998720
  have d884007348731904 : derivative ℚ (884007348731904 : ℚ⟦X⟧) = 0 := dnum 884007348731904
  have d1169880371953664 : derivative ℚ (1169880371953664 : ℚ⟦X⟧) = 0 := dnum 1169880371953664
  have d1530520185864192 : derivative ℚ (1530520185864192 : ℚ⟦X⟧) = 0 := dnum 1530520185864192
  have d2652022046195712 : derivative ℚ (2652022046195712 : ℚ⟦X⟧) = 0 := dnum 2652022046195712
  have d3199578836828160 : derivative ℚ (3199578836828160 : ℚ⟦X⟧) = 0 := dnum 3199578836828160
  have hL : derivative ℚ ((2199023255552 * X - 25288767438848 * (X * X) + 98956046499840 * (X * X * X) - 133040906960896 * (X * X * X * X) - 21990232555520 * (X * X * X * X * X) + 102254581383168 * (X * X * X * X * X * X) + 15393162788864 * (X * X * X * X * X * X * X) - 8796093022208 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (19791209299968 - 213305255788544 * X + 765260092932096 * (X * X) - 884007348731904 * (X * X * X) - 292470092988416 * (X * X * X * X) + 639915767365632 * (X * X * X * X * X) + 131941395333120 * (X * X * X * X * X * X) - 48378511622144 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (2199023255552 - 50577534877696 * X + 296868139499520 * X ^ 2 - 532163627843584 * X ^ 3 - 109951162777600 * X ^ 4 + 613527488299008 * X ^ 5 + 107752139522048 * X ^ 6 - 70368744177664 * X ^ 7) * derivative ℚ G + (2199023255552 * X - 25288767438848 * X ^ 2 + 98956046499840 * X ^ 3 - 133040906960896 * X ^ 4 - 21990232555520 * X ^ 5 + 102254581383168 * X ^ 6 + 15393162788864 * X ^ 7 - 8796093022208 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-213305255788544 + 1530520185864192 * X - 2652022046195712 * X ^ 2 - 1169880371953664 * X ^ 3 + 3199578836828160 * X ^ 4 + 791648371998720 * X ^ 5 - 338649581355008 * X ^ 6) * G + (19791209299968 - 213305255788544 * X + 765260092932096 * X ^ 2 - 884007348731904 * X ^ 3 - 292470092988416 * X ^ 4 + 639915767365632 * X ^ 5 + 131941395333120 * X ^ 6 - 48378511622144 * X ^ 7) * derivative ℚ G := by
    simp [Derivation.leibniz, d2199023255552, d8796093022208, d15393162788864, d19791209299968, d21990232555520, d25288767438848, d48378511622144, d98956046499840, d102254581383168, d131941395333120, d133040906960896, d213305255788544, d292470092988416, d639915767365632, d765260092932096, d884007348731904]
    ring
  have hRd : derivative ℚ (19791209299968 + 6597069766656 * X : ℚ⟦X⟧) = 6597069766656 := by
    simp [Derivation.leibniz, d6597069766656, d19791209299968]
  have h2 : (2199023255552 * X - 25288767438848 * (X * X) + 98956046499840 * (X * X * X) - 133040906960896 * (X * X * X * X) - 21990232555520 * (X * X * X * X * X) + 102254581383168 * (X * X * X * X * X * X) + 15393162788864 * (X * X * X * X * X * X * X) - 8796093022208 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (19791209299968 - 213305255788544 * X + 765260092932096 * (X * X) - 884007348731904 * (X * X * X) - 292470092988416 * (X * X * X * X) + 639915767365632 * (X * X * X * X * X) + 131941395333120 * (X * X * X * X * X * X) - 48378511622144 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (19791209299968 + 6597069766656 * X : ℚ⟦X⟧) := by linear_combination h
  have hd : (2199023255552 - 50577534877696 * X + 296868139499520 * X ^ 2 - 532163627843584 * X ^ 3 - 109951162777600 * X ^ 4 + 613527488299008 * X ^ 5 + 107752139522048 * X ^ 6 - 70368744177664 * X ^ 7) * derivative ℚ G + (2199023255552 * X - 25288767438848 * X ^ 2 + 98956046499840 * X ^ 3 - 133040906960896 * X ^ 4 - 21990232555520 * X ^ 5 + 102254581383168 * X ^ 6 + 15393162788864 * X ^ 7 - 8796093022208 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-213305255788544 + 1530520185864192 * X - 2652022046195712 * X ^ 2 - 1169880371953664 * X ^ 3 + 3199578836828160 * X ^ 4 + 791648371998720 * X ^ 5 - 338649581355008 * X ^ 6) * G + (19791209299968 - 213305255788544 * X + 765260092932096 * X ^ 2 - 884007348731904 * X ^ 3 - 292470092988416 * X ^ 4 + 639915767365632 * X ^ 5 + 131941395333120 * X ^ 6 - 48378511622144 * X ^ 7) * derivative ℚ G = 6597069766656 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((2199023255552 - 50577534877696 * X + 296868139499520 * (X * X) - 532163627843584 * (X * X * X) - 109951162777600 * (X * X * X * X) + 613527488299008 * (X * X * X * X * X) + 107752139522048 * (X * X * X * X * X * X) - 70368744177664 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (2199023255552 * X - 25288767438848 * (X * X) + 98956046499840 * (X * X * X) - 133040906960896 * (X * X * X * X) - 21990232555520 * (X * X * X * X * X) + 102254581383168 * (X * X * X * X * X * X) + 15393162788864 * (X * X * X * X * X * X * X) - 8796093022208 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-213305255788544 + 1530520185864192 * X - 2652022046195712 * (X * X) - 1169880371953664 * (X * X * X) + 3199578836828160 * (X * X * X * X) + 791648371998720 * (X * X * X * X * X) - 338649581355008 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (19791209299968 - 213305255788544 * X + 765260092932096 * (X * X) - 884007348731904 * (X * X * X) - 292470092988416 * (X * X * X * X) + 639915767365632 * (X * X * X * X * X) + 131941395333120 * (X * X * X * X * X * X) - 48378511622144 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (-477188046454784 + 3654776650727424 * X - 6900534975922176 * X ^ 2 - 2779565395017728 * X ^ 3 + 9466795115151360 * X ^ 4 + 2229809581129728 * X ^ 5 - 1169880371953664 * X ^ 6) * derivative ℚ G + (24189255811072 - 314460325543936 * X + 1358996371931136 * X ^ 2 - 1948334604419072 * X ^ 3 - 512372418543616 * X ^ 4 + 1866970743963648 * X ^ 5 + 347445674377216 * X ^ 6 - 189115999977472 * X ^ 7) * derivative ℚ (derivative ℚ G) + (2199023255552 * X - 25288767438848 * X ^ 2 + 98956046499840 * X ^ 3 - 133040906960896 * X ^ 4 - 21990232555520 * X ^ 5 + 102254581383168 * X ^ 6 + 15393162788864 * X ^ 7 - 8796093022208 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (1530520185864192 - 5304044092391424 * X - 3509641115860992 * X ^ 2 + 12798315347312640 * X ^ 3 + 3958241859993600 * X ^ 4 - 2031897488130048 * X ^ 5) * G := by
    simp [Derivation.leibniz, d2199023255552, d8796093022208, d15393162788864, d19791209299968, d21990232555520, d25288767438848, d48378511622144, d50577534877696, d70368744177664, d98956046499840, d102254581383168, d107752139522048, d109951162777600, d131941395333120, d133040906960896, d213305255788544, d292470092988416, d296868139499520, d338649581355008, d532163627843584, d613527488299008, d639915767365632, d765260092932096, d791648371998720, d884007348731904, d1169880371953664, d1530520185864192, d2652022046195712, d3199578836828160]
    ring
  have hRd2 : derivative ℚ (6597069766656 : ℚ⟦X⟧) = 0 := by
    simp [d6597069766656]
  have hdp : (2199023255552 - 50577534877696 * X + 296868139499520 * (X * X) - 532163627843584 * (X * X * X) - 109951162777600 * (X * X * X * X) + 613527488299008 * (X * X * X * X * X) + 107752139522048 * (X * X * X * X * X * X) - 70368744177664 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (2199023255552 * X - 25288767438848 * (X * X) + 98956046499840 * (X * X * X) - 133040906960896 * (X * X * X * X) - 21990232555520 * (X * X * X * X * X) + 102254581383168 * (X * X * X * X * X * X) + 15393162788864 * (X * X * X * X * X * X * X) - 8796093022208 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-213305255788544 + 1530520185864192 * X - 2652022046195712 * (X * X) - 1169880371953664 * (X * X * X) + 3199578836828160 * (X * X * X * X) + 791648371998720 * (X * X * X * X * X) - 338649581355008 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (19791209299968 - 213305255788544 * X + 765260092932096 * (X * X) - 884007348731904 * (X * X * X) - 292470092988416 * (X * X * X * X) + 639915767365632 * (X * X * X * X * X) + 131941395333120 * (X * X * X * X * X * X) - 48378511622144 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (6597069766656 : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (-477188046454784 + 3654776650727424 * X - 6900534975922176 * X ^ 2 - 2779565395017728 * X ^ 3 + 9466795115151360 * X ^ 4 + 2229809581129728 * X ^ 5 - 1169880371953664 * X ^ 6) * derivative ℚ G + (24189255811072 - 314460325543936 * X + 1358996371931136 * X ^ 2 - 1948334604419072 * X ^ 3 - 512372418543616 * X ^ 4 + 1866970743963648 * X ^ 5 + 347445674377216 * X ^ 6 - 189115999977472 * X ^ 7) * derivative ℚ (derivative ℚ G) + (2199023255552 * X - 25288767438848 * X ^ 2 + 98956046499840 * X ^ 3 - 133040906960896 * X ^ 4 - 21990232555520 * X ^ 5 + 102254581383168 * X ^ 6 + 15393162788864 * X ^ 7 - 8796093022208 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (1530520185864192 - 5304044092391424 * X - 3509641115860992 * X ^ 2 + 12798315347312640 * X ^ 3 + 3958241859993600 * X ^ 4 - 2031897488130048 * X ^ 5) * G = 0 := by
    rw [← hL2, hdp, hRd2]
  have hfull : (1099511627776 - 17592186044416 * X + 112150186033152 * X ^ 2 - 356241767399424 * X ^ 3 + 557452395282432 * X ^ 4 - 290271069732864 * X ^ 5 - 217703302299648 * X ^ 6 + 237494511599616 * X ^ 7 + 9895604649984 * X ^ 8 - 30786325577728 * X ^ 9 + 4398046511104 * X ^ 10) * ((2 * X ^ 3 - 7 * X ^ 4 - 4 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (34 * X ^ 2 - 136 * X ^ 3 - 90 * X ^ 4) * derivative ℚ (derivative ℚ G) + (120 * X - 758 * X ^ 2 - 582 * X ^ 3) * derivative ℚ G + (-1200 * X - 1056 * X ^ 2) * G - (0)) = 0 := by
    linear_combination (X ^ 2 - 8 * X ^ 3 + 19 * X ^ 4 - 10 * X ^ 5 - 7 * X ^ 6 + 2 * X ^ 7) * hd2 + (6 * X - 40 * X ^ 2 + 76 * X ^ 3 - 30 * X ^ 4 - 14 * X ^ 5 + 2 * X ^ 6) * hd + (-2 * X + 14 * X ^ 2 - 30 * X ^ 3 + 20 * X ^ 4 - 2 * X ^ 5) * h
  have hg : (1099511627776 - 17592186044416 * X + 112150186033152 * X ^ 2 - 356241767399424 * X ^ 3 + 557452395282432 * X ^ 4 - 290271069732864 * X ^ 5 - 217703302299648 * X ^ 6 + 237494511599616 * X ^ 7 + 9895604649984 * X ^ 8 - 30786325577728 * X ^ 9 + 4398046511104 * X ^ 10 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (1099511627776 : ℚ⟦X⟧) = 1099511627776 := cnum 1099511627776
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-512 * X ^ 9 + 2048 * X ^ 10 + (1536 * X ^ 9) * S) = 512 - 4608 * X + 13824 * X ^ 2 - 15360 * X ^ 3 + 4608 * X ^ 4 + (-512 + 3584 * X - 7680 * X ^ 2 + 5120 * X ^ 3 - 512 * X ^ 4) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 2 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-7) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-4) + derivative ℚ (derivative ℚ G) * X * X * C 34 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-136) + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-90) +
      derivative ℚ G * X * C 120 + derivative ℚ G * X * X * C (-758) +
      derivative ℚ G * X * X * X * C (-582) + G * X * C (-1200) +
      G * X * X * C (-1056) =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-512 * X ^ 9 + 2048 * X ^ 10 + (1536 * X ^ 9) * S) = 512 - 4608 * X + 13824 * X ^ 2 - 15360 * X ^ 3 + 4608 * X ^ 4 + (-512 + 3584 * X - 7680 * X ^ 2 + 5120 * X ^ 3 - 512 * X ^ 4) * S) (m : ℕ) :
    2 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-7) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 34 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-136) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-90) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      120 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-758) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-582) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-1200) * coeff (m + 1 + 1 + 1 + 1) G +
      (-1056) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-512 * X ^ 9 + 2048 * X ^ 10 + (1536 * X ^ 9) * S) = 512 - 4608 * X + 13824 * X ^ 2 - 15360 * X ^ 3 + 4608 * X ^ 4 + (-512 + 3584 * X - 7680 * X ^ 2 + 5120 * X ^ 3 - 512 * X ^ 4) * S) :
    68 * coeff (0 + 1 + 1) G + 240 * coeff (0 + 1 + 1) G +
      (-758) * coeff (0 + 1) G + (-1200) * coeff (0 + 1) G +
      (-1056) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-512 * X ^ 9 + 2048 * X ^ 10 + (1536 * X ^ 9) * S) = 512 - 4608 * X + 13824 * X ^ 2 - 15360 * X ^ 3 + 4608 * X ^ 4 + (-512 + 3584 * X - 7680 * X ^ 2 + 5120 * X ^ 3 - 512 * X ^ 4) * S) :
    12 * coeff (0 + 1 + 1 + 1) G + 204 * coeff (0 + 1 + 1 + 1) G +
      (-272) * coeff (0 + 1 + 1) G + 360 * coeff (0 + 1 + 1 + 1) G +
      (-1516) * coeff (0 + 1 + 1) G + (-582) * coeff (0 + 1) G +
      (-1200) * coeff (0 + 1 + 1) G + (-1056) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-512 * X ^ 9 + 2048 * X ^ 10 + (1536 * X ^ 9) * S) = 512 - 4608 * X + 13824 * X ^ 2 - 15360 * X ^ 3 + 4608 * X ^ 4 + (-512 + 3584 * X - 7680 * X ^ 2 + 5120 * X ^ 3 - 512 * X ^ 4) * S) :
    48 * coeff (0 + 1 + 1 + 1 + 1) G + (-42) * coeff (0 + 1 + 1 + 1) G +
      408 * coeff (0 + 1 + 1 + 1 + 1) G + (-816) * coeff (0 + 1 + 1 + 1) G +
      (-180) * coeff (0 + 1 + 1) G + 480 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2274) * coeff (0 + 1 + 1 + 1) G + (-1164) * coeff (0 + 1 + 1) G +
      (-1200) * coeff (0 + 1 + 1 + 1) G + (-1056) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A172066Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a172066.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A172066Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (512 * PowerSeries.X ^ 9) * hG - ((-2) + (16) * S + (-56) * S ^ 2 + (112) * S ^ 3 + (-140) * S ^ 4 + (112) * S ^ 5 + (-56) * S ^ 6 + (16) * S ^ 7 + (-2) * S ^ 8 + (-4 * PowerSeries.X) * c + (28 * PowerSeries.X) * c * S + (-84 * PowerSeries.X) * c * S ^ 2 + (140 * PowerSeries.X) * c * S ^ 3 + (-140 * PowerSeries.X) * c * S ^ 4 + (84 * PowerSeries.X) * c * S ^ 5 + (-28 * PowerSeries.X) * c * S ^ 6 + (4 * PowerSeries.X) * c * S ^ 7 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (48 * PowerSeries.X ^ 2) * c ^ 2 * S + (-120 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (160 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-120 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (48 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 6 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (80 * PowerSeries.X ^ 3) * c ^ 3 * S + (-160 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (160 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-80 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 5 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (128 * PowerSeries.X ^ 4) * c ^ 4 * S + (-192 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (128 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 4 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (192 * PowerSeries.X ^ 5) * c ^ 5 * S + (-192 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 3 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (256 * PowerSeries.X ^ 6) * c ^ 6 * S + (-128 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 2 + (-256 * PowerSeries.X ^ 7) * c ^ 7 + (256 * PowerSeries.X ^ 7) * c ^ 7 * S + (-512 * PowerSeries.X ^ 8) * c ^ 8) * hc - ((-510 + 2568 * PowerSeries.X - 3552 * PowerSeries.X ^ 2 + 1152 * PowerSeries.X ^ 3) + (494 - 1608 * PowerSeries.X + 1248 * PowerSeries.X ^ 2 - 128 * PowerSeries.X ^ 3) * S + (-438 + 816 * PowerSeries.X - 288 * PowerSeries.X ^ 2) * S ^ 2 + (326 - 304 * PowerSeries.X + 32 * PowerSeries.X ^ 2) * S ^ 3 + (-186 + 72 * PowerSeries.X) * S ^ 4 + (74 - 8 * PowerSeries.X) * S ^ 5 + (-18) * S ^ 6 + (2) * S ^ 7) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A172066Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (512 * PowerSeries.X ^ 9) * hG - ((-2) + (16) * S + (-56) * S ^ 2 + (112) * S ^ 3 + (-140) * S ^ 4 + (112) * S ^ 5 + (-56) * S ^ 6 + (16) * S ^ 7 + (-2) * S ^ 8 + (-4 * PowerSeries.X) * c + (28 * PowerSeries.X) * c * S + (-84 * PowerSeries.X) * c * S ^ 2 + (140 * PowerSeries.X) * c * S ^ 3 + (-140 * PowerSeries.X) * c * S ^ 4 + (84 * PowerSeries.X) * c * S ^ 5 + (-28 * PowerSeries.X) * c * S ^ 6 + (4 * PowerSeries.X) * c * S ^ 7 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (48 * PowerSeries.X ^ 2) * c ^ 2 * S + (-120 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (160 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-120 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (48 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 6 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (80 * PowerSeries.X ^ 3) * c ^ 3 * S + (-160 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (160 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-80 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 5 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (128 * PowerSeries.X ^ 4) * c ^ 4 * S + (-192 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (128 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 4 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (192 * PowerSeries.X ^ 5) * c ^ 5 * S + (-192 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 3 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (256 * PowerSeries.X ^ 6) * c ^ 6 * S + (-128 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 2 + (-256 * PowerSeries.X ^ 7) * c ^ 7 + (256 * PowerSeries.X ^ 7) * c ^ 7 * S + (-512 * PowerSeries.X ^ 8) * c ^ 8) * hc - ((-510 + 2568 * PowerSeries.X - 3552 * PowerSeries.X ^ 2 + 1152 * PowerSeries.X ^ 3) + (494 - 1608 * PowerSeries.X + 1248 * PowerSeries.X ^ 2 - 128 * PowerSeries.X ^ 3) * S + (-438 + 816 * PowerSeries.X - 288 * PowerSeries.X ^ 2) * S ^ 2 + (326 - 304 * PowerSeries.X + 32 * PowerSeries.X ^ 2) * S ^ 3 + (-186 + 72 * PowerSeries.X) * S ^ 4 + (74 - 8 * PowerSeries.X) * S ^ 5 + (-18) * S ^ 6 + (2) * S ^ 7) * hS)
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A172066Aux.relE2 (S) G (by linear_combination hS)
            (by linear_combination (512 * PowerSeries.X ^ 9) * hG - ((-2) + (16) * S + (-56) * S ^ 2 + (112) * S ^ 3 + (-140) * S ^ 4 + (112) * S ^ 5 + (-56) * S ^ 6 + (16) * S ^ 7 + (-2) * S ^ 8 + (-4 * PowerSeries.X) * c + (28 * PowerSeries.X) * c * S + (-84 * PowerSeries.X) * c * S ^ 2 + (140 * PowerSeries.X) * c * S ^ 3 + (-140 * PowerSeries.X) * c * S ^ 4 + (84 * PowerSeries.X) * c * S ^ 5 + (-28 * PowerSeries.X) * c * S ^ 6 + (4 * PowerSeries.X) * c * S ^ 7 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (48 * PowerSeries.X ^ 2) * c ^ 2 * S + (-120 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (160 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-120 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (48 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 6 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (80 * PowerSeries.X ^ 3) * c ^ 3 * S + (-160 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (160 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-80 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 5 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (128 * PowerSeries.X ^ 4) * c ^ 4 * S + (-192 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (128 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 4 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (192 * PowerSeries.X ^ 5) * c ^ 5 * S + (-192 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 3 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (256 * PowerSeries.X ^ 6) * c ^ 6 * S + (-128 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 2 + (-256 * PowerSeries.X ^ 7) * c ^ 7 + (256 * PowerSeries.X ^ 7) * c ^ 7 * S + (-512 * PowerSeries.X ^ 8) * c ^ 8) * hc - ((-510 + 2568 * PowerSeries.X - 3552 * PowerSeries.X ^ 2 + 1152 * PowerSeries.X ^ 3) + (494 - 1608 * PowerSeries.X + 1248 * PowerSeries.X ^ 2 - 128 * PowerSeries.X ^ 3) * S + (-438 + 816 * PowerSeries.X - 288 * PowerSeries.X ^ 2) * S ^ 2 + (326 - 304 * PowerSeries.X + 32 * PowerSeries.X ^ 2) * S ^ 3 + (-186 + 72 * PowerSeries.X) * S ^ 4 + (74 - 8 * PowerSeries.X) * S ^ 5 + (-18) * S ^ 6 + (2) * S ^ 7) * hS)
        push_cast
        linear_combination r
      | succ m =>
        have r := A172066Aux.rel (S) G (by linear_combination hS)
            (by linear_combination (512 * PowerSeries.X ^ 9) * hG - ((-2) + (16) * S + (-56) * S ^ 2 + (112) * S ^ 3 + (-140) * S ^ 4 + (112) * S ^ 5 + (-56) * S ^ 6 + (16) * S ^ 7 + (-2) * S ^ 8 + (-4 * PowerSeries.X) * c + (28 * PowerSeries.X) * c * S + (-84 * PowerSeries.X) * c * S ^ 2 + (140 * PowerSeries.X) * c * S ^ 3 + (-140 * PowerSeries.X) * c * S ^ 4 + (84 * PowerSeries.X) * c * S ^ 5 + (-28 * PowerSeries.X) * c * S ^ 6 + (4 * PowerSeries.X) * c * S ^ 7 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (48 * PowerSeries.X ^ 2) * c ^ 2 * S + (-120 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (160 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-120 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (48 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 6 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (80 * PowerSeries.X ^ 3) * c ^ 3 * S + (-160 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (160 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-80 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 5 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (128 * PowerSeries.X ^ 4) * c ^ 4 * S + (-192 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (128 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 4 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (192 * PowerSeries.X ^ 5) * c ^ 5 * S + (-192 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 3 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (256 * PowerSeries.X ^ 6) * c ^ 6 * S + (-128 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 2 + (-256 * PowerSeries.X ^ 7) * c ^ 7 + (256 * PowerSeries.X ^ 7) * c ^ 7 * S + (-512 * PowerSeries.X ^ 8) * c ^ 8) * hc - ((-510 + 2568 * PowerSeries.X - 3552 * PowerSeries.X ^ 2 + 1152 * PowerSeries.X ^ 3) + (494 - 1608 * PowerSeries.X + 1248 * PowerSeries.X ^ 2 - 128 * PowerSeries.X ^ 3) * S + (-438 + 816 * PowerSeries.X - 288 * PowerSeries.X ^ 2) * S ^ 2 + (326 - 304 * PowerSeries.X + 32 * PowerSeries.X ^ 2) * S ^ 3 + (-186 + 72 * PowerSeries.X) * S ^ 4 + (74 - 8 * PowerSeries.X) * S ^ 5 + (-18) * S ^ 6 + (2) * S ^ 7) * hS) m
        push_cast
        linear_combination r
