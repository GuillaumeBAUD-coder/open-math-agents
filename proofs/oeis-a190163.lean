import OMAStatements.S_oeis_a190163

namespace OMA.S_oeis_a190163

open PowerSeries


lemma ne_zero_of_cc {f : ℚ⟦X⟧} (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  intro h0; apply h; rw [h0]; simp

lemma ode (T G : ℚ⟦X⟧) (hT : T = 1 + X * T + X ^ 2 * T * (T - 1))
    (hG : G * ((1 - X) * (1 - X ^ 2 * T ^ 2)) = X ^ 5 * T ^ 2 * (T - 1) ^ 2) :
    (-7*X^4 + 11*X^3 - 35*X^2 + 44*X - 28) * G + (2*X^7 - 13*X^6 + 14*X^5 + 6*X^4 - 17*X^3 + 46*X^2 - 20*X) * (d⁄dX ℚ G) + (X^8 - 7*X^7 + 13*X^6 - 5*X^5 + 7*X^4 - 13*X^3 + 4*X^2) * (d⁄dX ℚ (d⁄dX ℚ G)) = 0 := by
  have hQ : X ^ 2 * T ^ 2 - (1 - X + X ^ 2) * T + 1 = 0 := by linear_combination (-1) * hT
  have hD : ((1 - X) * (1 - X ^ 2 * T ^ 2) : ℚ⟦X⟧) ≠ 0 := by
    apply ne_zero_of_cc; simp
  have hden : ((X^5 - 3*X^4 + X^3 - X^2 + 3*X - 1) : ℚ⟦X⟧) ≠ 0 := by
    apply ne_zero_of_cc; simp
  have hE : ((2 * X ^ 2 * T + X - X ^ 2 - 1) : ℚ⟦X⟧) ≠ 0 := by
    apply ne_zero_of_cc; simp
  have hX : (X : ℚ⟦X⟧) ≠ 0 := PowerSeries.X_ne_zero
  have hH : G * (X^5 - 3*X^4 + X^3 - X^2 + 3*X - 1) = (-X^5 + X^3 + 2*X^2 - X) + (2*X^5 + X^3 - 3*X^2 + X) * T := by
    have h1 : ((1 - X) * (1 - X ^ 2 * T ^ 2)) * (X ^ 6 * (G * (X^5 - 3*X^4 + X^3 - X^2 + 3*X - 1) - ((-X^5 + X^3 + 2*X^2 - X) + (2*X^5 + X^3 - 3*X^2 + X) * T))) = 0 := by
      linear_combination (X ^ 6 * (X^5 - 3*X^4 + X^3 - X^2 + 3*X - 1)) * hG + (T^2*X^14 - 3*T^2*X^13 + T^2*X^12 - T^2*X^11 + 3*T^2*X^10 - T^2*X^9 - T*X^14 + 2*T*X^13 + T*X^12 - T*X^11 - 2*T*X^10 + T*X^9 - X^12 + X^11 + X^10 + X^9 - 3*X^8 + X^7) * hQ
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hD
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (pow_ne_zero _ hX)
    exact sub_eq_zero.1 h
  -- derivatives
  have r1 := congrArg (d⁄dX ℚ) hH
  have r2 := congrArg (d⁄dX ℚ) r1
  have hT1 := congrArg (d⁄dX ℚ) hQ
  have hT2 := congrArg (d⁄dX ℚ) hT1
  have d2 : (d⁄dX ℚ) (2 : ℚ⟦X⟧) = 0 := by simpa using (d⁄dX ℚ).map_natCast 2
  have d3 : (d⁄dX ℚ) (3 : ℚ⟦X⟧) = 0 := by simpa using (d⁄dX ℚ).map_natCast 3
  have d4 : (d⁄dX ℚ) (4 : ℚ⟦X⟧) = 0 := by simpa using (d⁄dX ℚ).map_natCast 4
  have d5 : (d⁄dX ℚ) (5 : ℚ⟦X⟧) = 0 := by simpa using (d⁄dX ℚ).map_natCast 5
  simp [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add, smul_eq_mul, nsmul_eq_mul,
    d2, d3, d4, d5] at r1 r2 hT1 hT2
  set T1 := d⁄dX ℚ T with hT1d
  set T2 := d⁄dX ℚ T1 with hT2d
  set G1 := d⁄dX ℚ G with hG1d
  set G2 := d⁄dX ℚ G1 with hG2d
  have key : ((X^5 - 3*X^4 + X^3 - X^2 + 3*X - 1) ^ 3 * (2 * X ^ 2 * T + X - X ^ 2 - 1) ^ 3 * X ^ 6) *
      ((-7*X^4 + 11*X^3 - 35*X^2 + 44*X - 28) * G + (2*X^7 - 13*X^6 + 14*X^5 + 6*X^4 - 17*X^3 + 46*X^2 - 20*X) * G1 + (X^8 - 7*X^7 + 13*X^6 - 5*X^5 + 7*X^4 - 13*X^3 + 4*X^2) * G2) = 0 := by
    linear_combination (8*T^3*X^30 - 104*T^3*X^29 + 528*T^3*X^28 - 1344*T^3*X^27 + 1992*T^3*X^26 - 2616*T^3*X^25 + 4280*T^3*X^24 - 5384*T^3*X^23 + 4680*T^3*X^22 - 4856*T^3*X^21 + 5240*T^3*X^20 - 3624*T^3*X^19 + 2208*T^3*X^18 - 1776*T^3*X^17 + 1032*T^3*X^16 - 296*T^3*X^15 + 32*T^3*X^14 - 12*T^2*X^30 + 168*T^2*X^29 - 960*T^2*X^28 + 2964*T^2*X^27 - 5796*T^2*X^26 + 8928*T^2*X^25 - 13332*T^2*X^24 + 18420*T^2*X^23 - 21516*T^2*X^22 + 22380*T^2*X^21 - 22164*T^2*X^20 + 20580*T^2*X^19 - 16608*T^2*X^18 + 11412*T^2*X^17 - 7524*T^2*X^16 + 4656*T^2*X^15 - 2040*T^2*X^14 + 492*T^2*X^13 - 48*T^2*X^12 + 6*T*X^30 - 90*T*X^29 + 570*T*X^28 - 2046*T*X^27 + 4860*T*X^26 - 8844*T*X^25 + 14028*T*X^24 - 20340*T*X^23 + 26634*T*X^22 - 31158*T*X^21 + 33030*T*X^20 - 32562*T*X^19 + 29676*T*X^18 - 24300*T*X^17 + 17772*T*X^16 - 11796*T*X^15 + 7110*T*X^14 - 3594*T*X^13 + 1290*T*X^12 - 270*T*X^11 + 24*T*X^10 - X^30 + 16*X^29 - 111*X^28 + 451*X^27 - 1246*X^26 + 2625*X^25 - 4622*X^24 + 7202*X^23 - 10167*X^22 + 13022*X^21 - 15137*X^20 + 16125*X^19 - 15878*X^18 + 14423*X^17 - 11958*X^16 + 8978*X^15 - 6113*X^14 + 3750*X^13 - 1999*X^12 + 859*X^11 - 264*X^10 + 49*X^9 - 4*X^8) * r2 + (-64*T^3*X^29 + 792*T^3*X^28 - 3856*T^3*X^27 + 9496*T^3*X^26 - 13784*T^3*X^25 + 17768*T^3*X^24 - 28088*T^3*X^23 + 34456*T^3*X^22 - 29400*T^3*X^21 + 29464*T^3*X^20 - 30888*T^3*X^19 + 20920*T^3*X^18 - 12328*T^3*X^17 + 9584*T^3*X^16 - 5432*T^3*X^15 + 1520*T^3*X^14 - 160*T^3*X^13 + 96*T^2*X^29 - 1284*T^2*X^28 + 7068*T^2*X^27 - 21216*T^2*X^26 + 40704*T^2*X^25 - 61572*T^2*X^24 + 89460*T^2*X^23 - 120468*T^2*X^22 + 137916*T^2*X^21 - 139980*T^2*X^20 + 134628*T^2*X^19 - 121908*T^2*X^18 + 96204*T^2*X^17 - 64248*T^2*X^16 + 41016*T^2*X^15 - 24804*T^2*X^14 + 10668*T^2*X^13 - 2520*T^2*X^12 + 240*T^2*X^11 - 48*T*X^29 + 690*T*X^28 - 4224*T*X^27 + 14784*T*X^26 - 34494*T*X^25 + 61746*T*X^24 - 95868*T*X^23 + 135750*T*X^22 - 173922*T*X^21 + 199182*T*X^20 - 206262*T*X^19 + 198258*T*X^18 - 176370*T*X^17 + 141180*T*X^16 - 100734*T*X^15 + 65034*T*X^14 - 38244*T*X^13 + 18996*T*X^12 - 6714*T*X^11 + 1380*T*X^10 - 120*T*X^9 + 8*X^29 - 123*X^28 + 827*X^27 - 3283*X^26 + 8917*X^25 - 18504*X^24 + 32018*X^23 - 48894*X^22 + 67590*X^21 - 84809*X^20 + 96561*X^19 - 100617*X^18 + 96815*X^17 - 85968*X^16 + 69714*X^15 - 51158*X^14 + 34002*X^13 - 20379*X^12 + 10659*X^11 - 4515*X^10 + 1369*X^9 - 250*X^8 + 20*X^7) * r1 + (160*T^3*X^28 - 1880*T^3*X^27 + 8768*T^3*X^26 - 20792*T^3*X^25 + 28360*T^3*X^24 - 31032*T^3*X^23 + 41512*T^3*X^22 - 45608*T^3*X^21 + 31976*T^3*X^20 - 24680*T^3*X^19 + 20344*T^3*X^18 - 8232*T^3*X^17 + 2584*T^3*X^16 - 992*T^3*X^15 - 1480*T^3*X^14 + 1216*T^3*X^13 - 224*T^3*X^12 - 240*T^2*X^28 + 3060*T^2*X^27 - 16212*T^2*X^26 + 47160*T^2*X^25 - 86880*T^2*X^24 + 120276*T^2*X^23 - 151356*T^2*X^22 + 177228*T^2*X^21 - 178644*T^2*X^20 + 153396*T^2*X^19 - 115500*T^2*X^18 + 79884*T^2*X^17 - 46740*T^2*X^16 + 17712*T^2*X^15 - 3144*T^2*X^14 - 2556*T^2*X^13 + 4380*T^2*X^12 - 2160*T^2*X^11 + 336*T^2*X^10 + 120*T*X^28 - 1650*T*X^27 + 9756*T*X^26 - 33216*T*X^25 + 75126*T*X^24 - 127158*T*X^23 + 179256*T*X^22 - 224430*T*X^21 + 253614*T*X^20 - 254634*T*X^19 + 223770*T*X^18 - 174390*T*X^17 + 121062*T*X^16 - 72168*T*X^15 + 33798*T*X^14 - 9150*T*X^13 - 1896*T*X^12 + 4548*T*X^11 - 3438*T*X^10 + 1248*T*X^9 - 168*T*X^8 - 20*X^28 + 295*X^27 - 1921*X^26 + 7437*X^25 - 19683*X^24 + 39250*X^23 - 63590*X^22 + 88474*X^21 - 109550*X^20 + 122113*X^19 - 122003*X^18 + 108799*X^17 - 86537*X^16 + 61270*X^15 - 37838*X^14 + 19186*X^13 - 6842*X^12 + 451*X^11 + 1647*X^10 - 1539*X^9 + 809*X^8 - 236*X^7 + 28*X^6) * hH + (8*T^2*X^33 - 104*T^2*X^32 + 532*T^2*X^31 - 1408*T^2*X^30 + 2416*T^2*X^29 - 4132*T^2*X^28 + 7556*T^2*X^27 - 10352*T^2*X^26 + 11740*T^2*X^25 - 15276*T^2*X^24 + 17796*T^2*X^23 - 15764*T^2*X^22 + 14452*T^2*X^21 - 13876*T^2*X^20 + 10192*T^2*X^19 - 6308*T^2*X^18 + 4316*T^2*X^17 - 2584*T^2*X^16 + 976*T^2*X^15 - 196*T^2*X^14 + 16*T^2*X^13 - 8*T*X^33 + 112*T*X^32 - 644*T*X^31 + 2044*T*X^30 - 4356*T*X^29 + 7956*T*X^28 - 14104*T*X^27 + 22040*T*X^26 - 29648*T*X^25 + 37368*T*X^24 - 44812*T*X^23 + 48836*T*X^22 - 48012*T*X^21 + 44092*T*X^20 - 38520*T*X^19 + 30376*T*X^18 - 20816*T*X^17 + 13208*T*X^16 - 7876*T*X^15 + 3756*T*X^14 - 1188*T*X^13 + 212*T*X^12 - 16*T*X^11 + 2*X^33 - 30*X^32 + 191*X^31 - 700*X^30 + 1761*X^29 - 3589*X^28 + 6604*X^27 - 11025*X^26 + 16448*X^25 - 22264*X^24 + 27957*X^23 - 32754*X^22 + 35415*X^21 - 35235*X^20 + 32656*X^19 - 28247*X^18 + 22428*X^17 - 16100*X^16 + 10475*X^15 - 6210*X^14 + 3205*X^13 - 1289*X^12 + 354*X^11 - 57*X^10 + 4*X^9) * hT2 + (-8*T^2*X^32 + 64*T^2*X^31 - 180*T^2*X^30 + 412*T^2*X^29 - 2044*T^2*X^28 + 7628*T^2*X^27 - 16452*T^2*X^26 + 24836*T^2*X^25 - 34880*T^2*X^24 + 50528*T^2*X^23 - 61680*T^2*X^22 + 60000*T^2*X^21 - 58408*T^2*X^20 + 57808*T^2*X^19 - 45068*T^2*X^18 + 29028*T^2*X^17 - 20084*T^2*X^16 + 12596*T^2*X^15 - 5100*T^2*X^14 + 1100*T^2*X^13 - 96*T^2*X^12 - 8*T*T1*X^33 + 104*T*T1*X^32 - 532*T*T1*X^31 + 1408*T*T1*X^30 - 2416*T*T1*X^29 + 4132*T*T1*X^28 - 7556*T*T1*X^27 + 10352*T*T1*X^26 - 11740*T*T1*X^25 + 15276*T*T1*X^24 - 17796*T*T1*X^23 + 15764*T*T1*X^22 - 14452*T*T1*X^21 + 13876*T*T1*X^20 - 10192*T*T1*X^19 + 6308*T*T1*X^18 - 4316*T*T1*X^17 + 2584*T*T1*X^16 - 976*T*T1*X^15 + 196*T*T1*X^14 - 16*T*T1*X^13 + 8*T*X^32 - 68*T*X^31 + 192*T*X^30 - 286*T*X^29 + 1400*T*X^28 - 7468*T*X^27 + 21642*T*X^26 - 41006*T*X^25 + 63436*T*X^24 - 94022*T*X^23 + 127710*T*X^22 - 148034*T*X^21 + 154410*T*X^20 - 153226*T*X^19 + 139894*T*X^18 - 112932*T*X^17 + 80834*T*X^16 - 53242*T*X^15 + 32172*T*X^14 - 15724*T*X^13 + 5222*T*X^12 - 992*T*X^11 + 80*T*X^10 + 4*T1*X^33 - 56*T1*X^32 + 322*T1*X^31 - 1022*T1*X^30 + 2178*T1*X^29 - 3978*T1*X^28 + 7052*T1*X^27 - 11020*T1*X^26 + 14824*T1*X^25 - 18684*T1*X^24 + 22406*T1*X^23 - 24418*T1*X^22 + 24006*T1*X^21 - 22046*T1*X^20 + 19260*T1*X^19 - 15188*T1*X^18 + 10408*T1*X^17 - 6604*T1*X^16 + 3938*T1*X^15 - 1878*T1*X^14 + 594*T1*X^13 - 106*T1*X^12 + 8*T1*X^11 - 4*X^32 + 46*X^31 - 210*X^30 + 511*X^29 - 981*X^28 + 2711*X^27 - 7981*X^26 + 17298*X^25 - 29126*X^24 + 44232*X^23 - 63000*X^22 + 80365*X^21 - 91031*X^20 + 94521*X^19 - 91995*X^18 + 82246*X^17 - 65562*X^16 + 47264*X^15 - 31472*X^14 + 18635*X^13 - 9169*X^12 + 3511*X^11 - 957*X^10 + 160*X^9 - 12*X^8) * hT1 + (80*T^2*X^30 - 592*T^2*X^29 + 1336*T^2*X^28 - 208*T^2*X^27 - 3808*T^2*X^26 + 8472*T^2*X^25 - 10032*T^2*X^24 + 3120*T^2*X^23 + 11040*T^2*X^22 - 23152*T^2*X^21 + 35120*T^2*X^20 - 53792*T^2*X^19 + 65376*T^2*X^18 - 57024*T^2*X^17 + 43112*T^2*X^16 - 34432*T^2*X^15 + 23408*T^2*X^14 - 10168*T^2*X^13 + 2368*T^2*X^12 - 224*T^2*X^11 - 80*T*X^30 + 672*T*X^29 - 2008*T*X^28 + 2136*T*X^27 + 2264*T*X^26 - 12072*T*X^25 + 22312*T*X^24 - 21624*T*X^23 + 2112*T*X^22 + 31072*T*X^21 - 69312*T*X^20 + 112064*T*X^19 - 154288*T*X^18 + 176192*T*X^17 - 165512*T*X^16 + 134568*T*X^15 - 100952*T*X^14 + 68008*T*X^13 - 35944*T*X^12 + 12760*T*X^11 - 2592*T*X^10 + 224*T*X^9 + 4*X^31 - 32*X^30 + 86*X^29 - 86*X^28 + 172*X^27 - 1392*X^26 + 5422*X^25 - 11846*X^24 + 15908*X^23 - 11384*X^22 - 4082*X^21 + 28194*X^20 - 57860*X^19 + 89440*X^18 - 115270*X^17 + 126070*X^16 - 118700*X^15 + 98592*X^14 - 73518*X^13 + 48438*X^12 - 26724*X^11 + 11400*X^10 - 3390*X^9 + 606*X^8 - 48*X^7) * hQ
  rcases mul_eq_zero.1 key with h | h
  · exfalso
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact hden (pow_eq_zero_iff (by norm_num) |>.1 h)
      · exact hE (pow_eq_zero_iff (by norm_num) |>.1 h)
    · exact hX (pow_eq_zero_iff (by norm_num) |>.1 h)
  · exact h

lemma cxk (F : ℚ⟦X⟧) (N k : ℕ) (h : k ≤ N) : coeff N (X ^ k * F) = coeff (N - k) F := by
  rw [coeff_X_pow_mul', if_pos h]

lemma cd (F : ℚ⟦X⟧) (m : ℕ) : coeff m (d⁄dX ℚ F) = coeff (m + 1) F * ((m : ℚ) + 1) :=
  coeff_derivative F m

lemma recur (G : ℚ⟦X⟧)
    (hode : (-7*X^4 + 11*X^3 - 35*X^2 + 44*X - 28) * G + (2*X^7 - 13*X^6 + 14*X^5 + 6*X^4 - 17*X^3 + 46*X^2 - 20*X) * (d⁄dX ℚ G) + (X^8 - 7*X^7 + 13*X^6 - 5*X^5 + 7*X^4 - 13*X^3 + 4*X^2) * (d⁄dX ℚ (d⁄dX ℚ G)) = 0)
    (n : ℕ) (hn : 6 ≤ n) :
    (28 + 24 * (n : ℚ) - 4 * (n : ℚ) ^ 2) * coeff n G + (28 - 85 * (n : ℚ) + 13 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-41 + 52 * (n : ℚ) - 7 * (n : ℚ) ^ 2) * coeff (n - 2) G + (67 - 41 * (n : ℚ) + 5 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-197 + 103 * (n : ℚ) - 13 * (n : ℚ) ^ 2) * coeff (n - 4) G + (145 - 64 * (n : ℚ) + 7 * (n : ℚ) ^ 2) * coeff (n - 5) G +
        (-30 + 11 * (n : ℚ) - (n : ℚ) ^ 2) * coeff (n - 6) G = 0 := by
  have ode' : C (-28 : ℚ) * (X ^ 0 * G) + C (44 : ℚ) * (X ^ 1 * G) + C (-35 : ℚ) * (X ^ 2 * G) + C (11 : ℚ) * (X ^ 3 * G) + C (-7 : ℚ) * (X ^ 4 * G) + C (-20 : ℚ) * (X ^ 1 * (d⁄dX ℚ G)) + C (46 : ℚ) * (X ^ 2 * (d⁄dX ℚ G)) + C (-17 : ℚ) * (X ^ 3 * (d⁄dX ℚ G)) + C (6 : ℚ) * (X ^ 4 * (d⁄dX ℚ G)) + C (14 : ℚ) * (X ^ 5 * (d⁄dX ℚ G)) + C (-13 : ℚ) * (X ^ 6 * (d⁄dX ℚ G)) + C (2 : ℚ) * (X ^ 7 * (d⁄dX ℚ G)) + C (4 : ℚ) * (X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ G))) + C (-13 : ℚ) * (X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ G))) + C (7 : ℚ) * (X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ G))) + C (-5 : ℚ) * (X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ G))) + C (13 : ℚ) * (X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ G))) + C (-7 : ℚ) * (X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ G))) + C (1 : ℚ) * (X ^ 8 * (d⁄dX ℚ (d⁄dX ℚ G))) = 0 := by
    simp only [map_neg, map_ofNat, map_one]
    linear_combination hode
  have hc := congrArg (coeff n) ode'
  rcases (by omega : n = 6 ∨ n = 7 ∨ 8 ≤ n) with h | h | h8
  · subst h
    simp [coeff_C_mul, coeff_X_pow_mul', cd] at hc
    norm_num at hc ⊢
    linear_combination (-1) * hc
  · subst h
    simp [coeff_C_mul, coeff_X_pow_mul', cd] at hc
    norm_num at hc ⊢
    linear_combination (-1) * hc
  · obtain ⟨j, h⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
    subst h
    have c0 : ∀ F : ℚ⟦X⟧, coeff (j + 8) (X ^ 0 * F) = coeff (j + 8 - 0) F := fun F => cxk F _ _ (by omega)
    have c1 : ∀ F : ℚ⟦X⟧, coeff (j + 8) (X ^ 1 * F) = coeff (j + 8 - 1) F := fun F => cxk F _ _ (by omega)
    have c2 : ∀ F : ℚ⟦X⟧, coeff (j + 8) (X ^ 2 * F) = coeff (j + 8 - 2) F := fun F => cxk F _ _ (by omega)
    have c3 : ∀ F : ℚ⟦X⟧, coeff (j + 8) (X ^ 3 * F) = coeff (j + 8 - 3) F := fun F => cxk F _ _ (by omega)
    have c4 : ∀ F : ℚ⟦X⟧, coeff (j + 8) (X ^ 4 * F) = coeff (j + 8 - 4) F := fun F => cxk F _ _ (by omega)
    have c5 : ∀ F : ℚ⟦X⟧, coeff (j + 8) (X ^ 5 * F) = coeff (j + 8 - 5) F := fun F => cxk F _ _ (by omega)
    have c6 : ∀ F : ℚ⟦X⟧, coeff (j + 8) (X ^ 6 * F) = coeff (j + 8 - 6) F := fun F => cxk F _ _ (by omega)
    have c7 : ∀ F : ℚ⟦X⟧, coeff (j + 8) (X ^ 7 * F) = coeff (j + 8 - 7) F := fun F => cxk F _ _ (by omega)
    have c8 : ∀ F : ℚ⟦X⟧, coeff (j + 8) (X ^ 8 * F) = coeff (j + 8 - 8) F := fun F => cxk F _ _ (by omega)
    have e0 : j + 8 - 0 = j + 8 := by omega
    have e1 : j + 8 - 1 = j + 7 := by omega
    have e2 : j + 8 - 2 = j + 6 := by omega
    have e3 : j + 8 - 3 = j + 5 := by omega
    have e4 : j + 8 - 4 = j + 4 := by omega
    have e5 : j + 8 - 5 = j + 3 := by omega
    have e6 : j + 8 - 6 = j + 2 := by omega
    have e7 : j + 8 - 7 = j + 1 := by omega
    have e8 : j + 8 - 8 = j + 0 := by omega
    simp only [map_add, coeff_C_mul, c0, c1, c2, c3, c4, c5, c6, c7, c8, cd, e0, e1, e2, e3, e4, e5, e6, e7, e8] at hc ⊢
    push_cast at hc ⊢
    simp only [add_assoc, Nat.reduceAdd, map_zero] at hc
    linear_combination (-1) * hc

end OMA.S_oeis_a190163

open PowerSeries OMA.S_oeis_a190163 in
theorem OMA.solution : type_of% @OMA.S_oeis_a190163.main := by
  intro T G hT hG n hn
  exact recur G (ode T G hT hG) n hn
