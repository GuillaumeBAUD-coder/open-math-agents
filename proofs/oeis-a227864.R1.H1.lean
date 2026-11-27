import OMAReductions.R_oeis_a227864_R1

/-!
# Proof of oeis-a227864.R1.H1

Certifies that every odd prime `p` with `3 <= p <= 2000` has a base `b >= 2` such that the base-`b`
digital reversal of `p^2` is prime, via an explicit table of 302 verified `(p, b)` base witnesses
and sound reflection for trial-division primality and base-`b` reversal.
-/

-- Proof of step oeis-a227864.R1.H1
-- Credit: @mvanhorn

section Cert

open OMA.S_oeis_a227864

private def noDivFrom (n d fuel : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if d * d > n then true
    else if n % d = 0 then false
    else noDivFrom n (d + 2) fuel'

private lemma noDivFrom_sound : ∀ (fuel n d : ℕ),
    Odd d → 3 ≤ d → noDivFrom n d fuel = true →
    ∀ k : ℕ, d ≤ k → Odd k → k * k ≤ n → ¬ (k ∣ n) := by
  intro fuel
  induction fuel with
  | zero => intro n d _ _ h; simp [noDivFrom] at h
  | succ fuel' ih =>
    intro n d hodd hd h k hdk hkodd hksq hkdvd
    unfold noDivFrom at h
    split_ifs at h with hgt hmod
    · have : d * d ≤ k * k := Nat.mul_le_mul hdk hdk
      omega
    · by_cases heq : k = d
      · subst heq
        exact hmod (Nat.mod_eq_zero_of_dvd hkdvd)
      · have hd2 : d + 2 ≤ k := by
          rcases hodd with ⟨a, rfl⟩
          rcases hkodd with ⟨b, rfl⟩
          omega
        have hodd2 : Odd (d + 2) := by rcases hodd with ⟨a, rfl⟩; exact ⟨a + 1, by omega⟩
        exact ih n (d + 2) hodd2 (by omega) h k hd2 hkodd hksq hkdvd

private def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else noDivFrom n 3 (n / 2 + 1)

private lemma isPrimeFast_sound (n : ℕ) (h : isPrimeFast n = true) : n.Prime := by
  unfold isPrimeFast at h
  split_ifs at h with hlt heq2 heven
  · subst heq2; decide
  · rw [Nat.prime_def_lt']
    refine ⟨by omega, fun m hm hmlt hmdvd => ?_⟩
    by_cases hmeven : m % 2 = 0
    · have h2dvd : 2 ∣ n := dvd_trans (Nat.dvd_of_mod_eq_zero hmeven) hmdvd
      exact heven (Nat.mod_eq_zero_of_dvd h2dvd)
    · have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
      by_cases hmsq : m * m ≤ n
      · exact noDivFrom_sound (n / 2 + 1) n 3 ⟨1, rfl⟩ le_rfl h m (by omega) hmodd hmsq hmdvd
      · rcases hmdvd with ⟨q, hq⟩
        have hq2 : 2 ≤ q := by
          by_contra hqlt
          have : q = 0 ∨ q = 1 := by omega
          rcases this with rfl | rfl <;> omega
        have hqsq : q * q ≤ n := by nlinarith
        have hqdvd : q ∣ n := ⟨m, by rw [hq, mul_comm]⟩
        by_cases hqeven : q % 2 = 0
        · exact heven (Nat.mod_eq_zero_of_dvd (dvd_trans (Nat.dvd_of_mod_eq_zero hqeven) hqdvd))
        · have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
          exact noDivFrom_sound (n / 2 + 1) n 3 ⟨1, rfl⟩ le_rfl h q (by omega) hqodd hqsq hqdvd

private def witnessTable : List (ℕ × ℕ) := [
  (3, 6), (5, 2), (7, 3), (11, 2), (13, 2), (17, 3), (19, 3), (23, 3), (29, 2), (31, 4),
  (37, 2), (41, 3), (43, 4), (47, 6), (53, 23), (59, 63), (61, 4), (67, 11), (71, 21), (73, 9),
  (79, 81), (83, 85), (89, 10), (97, 23), (101, 105), (103, 105), (107, 109), (109, 30), (113, 115), (127, 129),
  (131, 133), (137, 139), (139, 141), (149, 151), (151, 153), (157, 244), (163, 165), (167, 191), (173, 225), (179, 215),
  (181, 183), (191, 299), (193, 195), (197, 199), (199, 225), (211, 213), (223, 325), (227, 339), (229, 231), (233, 235),
  (239, 241), (241, 363), (251, 293), (257, 259), (263, 265), (269, 389), (271, 273), (277, 417), (281, 329), (283, 568),
  (293, 295), (307, 504), (311, 403), (313, 315), (317, 385), (331, 423), (337, 1183), (347, 349), (349, 525), (353, 704),
  (359, 361), (367, 736), (373, 375), (379, 381), (383, 573), (389, 391), (397, 792), (401, 403), (409, 615), (419, 440),
  (421, 840), (431, 833), (433, 599), (439, 931), (443, 629), (449, 1152), (457, 687), (461, 552), (463, 672), (467, 506),
  (479, 511), (487, 489), (491, 735), (499, 664), (503, 1008), (509, 680), (521, 585), (523, 525), (541, 1355), (547, 1781),
  (557, 1251), (563, 1128), (569, 1520), (571, 715), (577, 814), (587, 855), (593, 1184), (599, 897), (601, 688), (607, 1919),
  (613, 1224), (617, 721), (619, 744), (631, 1264), (641, 768), (643, 749), (647, 1296), (653, 872), (659, 705), (661, 993),
  (673, 1011), (677, 679), (683, 792), (691, 920), (701, 2457), (709, 885), (719, 1795), (727, 847), (733, 1464), (739, 1517),
  (743, 848), (751, 1504), (757, 797), (761, 1520), (769, 1155), (773, 1544), (787, 1034), (797, 2221), (809, 1296), (811, 1015),
  (821, 984), (823, 1417), (827, 1357), (829, 920), (839, 1680), (853, 1491), (857, 1177), (859, 1032), (863, 1786), (877, 1317),
  (881, 1440), (883, 1224), (887, 889), (907, 1208), (911, 1120), (919, 2160), (929, 931), (937, 1008), (941, 1128), (947, 1032),
  (953, 1904), (967, 1104), (971, 973), (977, 1952), (983, 1473), (991, 1395), (997, 1497), (1009, 1120), (1013, 1352), (1019, 1527),
  (1021, 1241), (1031, 1648), (1033, 1551), (1039, 1248), (1049, 2096), (1051, 1841), (1061, 2360), (1063, 1121), (1069, 2136), (1087, 2176),
  (1091, 1365), (1093, 2184), (1097, 2192), (1103, 1311), (1109, 1385), (1117, 1333), (1123, 1496), (1129, 1695), (1151, 2304), (1153, 1157),
  (1163, 1992), (1171, 1173), (1181, 1521), (1187, 2376), (1193, 1288), (1201, 2400), (1213, 2111), (1217, 1653), (1223, 1872), (1229, 1231),
  (1231, 1312), (1237, 1365), (1249, 1875), (1259, 1480), (1277, 2059), (1279, 1283), (1283, 1285), (1289, 1505), (1291, 1615), (1297, 1299),
  (1301, 1400), (1303, 1305), (1307, 1595), (1319, 1977), (1321, 1358), (1327, 1411), (1361, 1632), (1367, 1369), (1373, 1832), (1381, 1383),
  (1399, 1401), (1409, 1743), (1423, 1425), (1427, 1736), (1429, 1496), (1433, 1855), (1439, 1535), (1447, 2023), (1451, 1583), (1453, 2351),
  (1459, 1916), (1471, 2011), (1481, 1520), (1483, 1729), (1487, 2229), (1489, 1491), (1493, 2093), (1499, 1893), (1511, 2160), (1523, 2283),
  (1531, 2127), (1543, 1679), (1549, 2232), (1553, 2037), (1559, 1599), (1567, 1569), (1571, 1965), (1579, 1581), (1583, 2016), (1597, 2261),
  (1601, 1603), (1607, 2005), (1609, 1680), (1613, 2152), (1619, 1621), (1621, 1623), (1627, 2168), (1637, 1639), (1657, 1659), (1663, 1960),
  (1667, 2363), (1669, 1673), (1693, 2147), (1697, 1801), (1699, 2264), (1709, 2440), (1721, 2064), (1723, 1934), (1733, 2480), (1741, 1855),
  (1747, 1843), (1753, 1759), (1759, 2071), (1777, 1991), (1783, 2055), (1787, 1789), (1789, 2369), (1801, 1803), (1811, 2479), (1823, 1827),
  (1831, 1833), (1847, 2288), (1861, 1960), (1867, 2488), (1871, 2326), (1873, 1875), (1877, 1879), (1879, 2256), (1889, 2065), (1901, 1903),
  (1907, 1911), (1913, 2241), (1931, 1933), (1933, 2111), (1949, 1994), (1951, 2496), (1973, 2397), (1979, 2365), (1987, 2317), (1993, 1997),
  (1997, 2076), (1999, 200)
]

private def lookupBase (p : ℕ) : ℕ :=
  match witnessTable.find? (fun x => x.1 == p) with
  | some (_, b) => b
  | none => 0

private def checkOdd (p : ℕ) : Bool :=
  if isPrimeFast p then
    let b := lookupBase p
    decide (2 ≤ b) && isPrimeFast (reversal b (p ^ 2))
  else true

private def checkRange (lo : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => checkOdd (lo + k) && checkRange lo k

private lemma checkRange_sound (lo : ℕ) : ∀ (len : ℕ), checkRange lo len = true →
    ∀ p : ℕ, lo ≤ p → p < lo + len → checkOdd p = true := by
  intro len
  induction len with
  | zero => intro _ p h1 h2; omega
  | succ k ih =>
    intro h p h1 h2
    simp only [checkRange, Bool.and_eq_true] at h
    by_cases heq : p = lo + k
    · subst heq; exact h.1
    · exact ih h.2 p h1 (by omega)

private lemma isPrimeFast_complete (p : ℕ) (hp : p.Prime) : isPrimeFast p = true := by
  unfold isPrimeFast
  have hp2 : 2 ≤ p := hp.two_le
  split_ifs with hlt heq2 heven
  · omega
  · rfl
  · exfalso
    have h2 : 2 ∣ p := Nat.dvd_of_mod_eq_zero heven
    have := (hp.eq_one_or_self_of_dvd 2 h2).resolve_left (by omega)
    exact heq2 this.symm
  · have hnodiv : ∀ (fuel d : ℕ), 3 ≤ d → d ≤ p + 2 → d + 2 * fuel > p + 2 →
        noDivFrom p d fuel = true := by
      intro fuel
      induction fuel with
      | zero =>
        intro d _ hle hgt
        omega
      | succ fuel' ih =>
        intro d hd hle hgt
        unfold noDivFrom
        split_ifs with hdsq hdmod
        · rfl
        · exfalso
          have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hdmod
          rcases hp.eq_one_or_self_of_dvd d hdvd with h1 | hself
          · omega
          · subst hself
            nlinarith
        · exact ih (d + 2) (by omega) (by nlinarith) (by omega)
    exact hnodiv (p / 2 + 1) 3 le_rfl (by omega) (by omega)

private lemma c0 : checkRange 3 200 = true := by decide +kernel
private lemma c1 : checkRange 203 200 = true := by decide +kernel
private lemma c2 : checkRange 403 200 = true := by decide +kernel
private lemma c3 : checkRange 603 200 = true := by decide +kernel
private lemma c4 : checkRange 803 200 = true := by decide +kernel
private lemma c5 : checkRange 1003 200 = true := by decide +kernel
private lemma c6 : checkRange 1203 200 = true := by decide +kernel
private lemma c7 : checkRange 1403 200 = true := by decide +kernel
private lemma c8 : checkRange 1603 200 = true := by decide +kernel
private lemma c9 : checkRange 1803 198 = true := by decide +kernel

private lemma checkOdd_all (p : ℕ) (hp3 : 3 ≤ p) (hp2000 : p ≤ 2000) : checkOdd p = true := by
  by_cases h0 : p < 203
  · exact checkRange_sound 3 200 c0 p hp3 h0
  by_cases h1 : p < 403
  · exact checkRange_sound 203 200 c1 p (by omega) h1
  by_cases h2 : p < 603
  · exact checkRange_sound 403 200 c2 p (by omega) h2
  by_cases h3 : p < 803
  · exact checkRange_sound 603 200 c3 p (by omega) h3
  by_cases h4 : p < 1003
  · exact checkRange_sound 803 200 c4 p (by omega) h4
  by_cases h5 : p < 1203
  · exact checkRange_sound 1003 200 c5 p (by omega) h5
  by_cases h6 : p < 1403
  · exact checkRange_sound 1203 200 c6 p (by omega) h6
  by_cases h7 : p < 1603
  · exact checkRange_sound 1403 200 c7 p (by omega) h7
  by_cases h8 : p < 1803
  · exact checkRange_sound 1603 200 c8 p (by omega) h8
  exact checkRange_sound 1803 198 c9 p (by omega) (by omega)

end Cert

theorem OMA.solution : OMA.R_oeis_a227864_R1.H1 := by
  intro p hp3 hp2000 hp
  have hc := checkOdd_all p hp3 hp2000
  unfold checkOdd at hc
  rw [isPrimeFast_complete p hp] at hc
  simp only [ite_true, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨lookupBase p, hc.1, isPrimeFast_sound _ hc.2⟩
