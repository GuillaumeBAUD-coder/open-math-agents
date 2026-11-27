import OMAReductions.R_OeisA182126_conjecture3_R1

/-! Credit: Hanan Beer (@hananzlt).
Finite check of the first 61 terms; reduction by @jagong-cmu.
Prime enumeration and primality checks are verified by the Lean kernel.
-/

namespace OMA.PrimeResidues
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_0 : Nat.nth Nat.Prime 0 = 2 := (2).nth_count (by decide : Nat.Prime 2)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_1 : Nat.nth Nat.Prime 1 = 3 := (3).nth_count (by decide : Nat.Prime 3)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_2 : Nat.nth Nat.Prime 2 = 5 := (5).nth_count (by decide : Nat.Prime 5)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_3 : Nat.nth Nat.Prime 3 = 7 := (7).nth_count (by decide : Nat.Prime 7)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_4 : Nat.nth Nat.Prime 4 = 11 := (11).nth_count (by decide : Nat.Prime 11)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_5 : Nat.nth Nat.Prime 5 = 13 := (13).nth_count (by decide : Nat.Prime 13)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_6 : Nat.nth Nat.Prime 6 = 17 := (17).nth_count (by decide : Nat.Prime 17)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_7 : Nat.nth Nat.Prime 7 = 19 := (19).nth_count (by decide : Nat.Prime 19)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_8 : Nat.nth Nat.Prime 8 = 23 := (23).nth_count (by decide : Nat.Prime 23)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_9 : Nat.nth Nat.Prime 9 = 29 := (29).nth_count (by decide : Nat.Prime 29)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_10 : Nat.nth Nat.Prime 10 = 31 := (31).nth_count (by decide : Nat.Prime 31)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_11 : Nat.nth Nat.Prime 11 = 37 := (37).nth_count (by decide : Nat.Prime 37)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_12 : Nat.nth Nat.Prime 12 = 41 := (41).nth_count (by decide : Nat.Prime 41)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_13 : Nat.nth Nat.Prime 13 = 43 := (43).nth_count (by decide : Nat.Prime 43)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_14 : Nat.nth Nat.Prime 14 = 47 := (47).nth_count (by decide : Nat.Prime 47)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_15 : Nat.nth Nat.Prime 15 = 53 := (53).nth_count (by decide : Nat.Prime 53)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_16 : Nat.nth Nat.Prime 16 = 59 := (59).nth_count (by decide : Nat.Prime 59)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_17 : Nat.nth Nat.Prime 17 = 61 := (61).nth_count (by decide : Nat.Prime 61)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_18 : Nat.nth Nat.Prime 18 = 67 := (67).nth_count (by decide : Nat.Prime 67)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_19 : Nat.nth Nat.Prime 19 = 71 := (71).nth_count (by decide : Nat.Prime 71)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_20 : Nat.nth Nat.Prime 20 = 73 := (73).nth_count (by decide : Nat.Prime 73)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_21 : Nat.nth Nat.Prime 21 = 79 := (79).nth_count (by decide : Nat.Prime 79)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_22 : Nat.nth Nat.Prime 22 = 83 := (83).nth_count (by decide : Nat.Prime 83)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_23 : Nat.nth Nat.Prime 23 = 89 := (89).nth_count (by decide : Nat.Prime 89)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_24 : Nat.nth Nat.Prime 24 = 97 := (97).nth_count (by decide : Nat.Prime 97)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_25 : Nat.nth Nat.Prime 25 = 101 := (101).nth_count (by decide : Nat.Prime 101)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_26 : Nat.nth Nat.Prime 26 = 103 := (103).nth_count (by decide : Nat.Prime 103)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_27 : Nat.nth Nat.Prime 27 = 107 := (107).nth_count (by decide : Nat.Prime 107)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_28 : Nat.nth Nat.Prime 28 = 109 := (109).nth_count (by decide : Nat.Prime 109)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_29 : Nat.nth Nat.Prime 29 = 113 := (113).nth_count (by decide : Nat.Prime 113)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_30 : Nat.nth Nat.Prime 30 = 127 := (127).nth_count (by decide : Nat.Prime 127)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_31 : Nat.nth Nat.Prime 31 = 131 := (131).nth_count (by decide : Nat.Prime 131)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_32 : Nat.nth Nat.Prime 32 = 137 := (137).nth_count (by decide : Nat.Prime 137)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_33 : Nat.nth Nat.Prime 33 = 139 := (139).nth_count (by decide : Nat.Prime 139)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_34 : Nat.nth Nat.Prime 34 = 149 := (149).nth_count (by decide : Nat.Prime 149)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_35 : Nat.nth Nat.Prime 35 = 151 := (151).nth_count (by decide : Nat.Prime 151)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_36 : Nat.nth Nat.Prime 36 = 157 := (157).nth_count (by decide : Nat.Prime 157)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_37 : Nat.nth Nat.Prime 37 = 163 := (163).nth_count (by decide : Nat.Prime 163)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_38 : Nat.nth Nat.Prime 38 = 167 := (167).nth_count (by decide : Nat.Prime 167)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_39 : Nat.nth Nat.Prime 39 = 173 := (173).nth_count (by decide : Nat.Prime 173)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_40 : Nat.nth Nat.Prime 40 = 179 := (179).nth_count (by decide : Nat.Prime 179)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_41 : Nat.nth Nat.Prime 41 = 181 := (181).nth_count (by decide : Nat.Prime 181)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_42 : Nat.nth Nat.Prime 42 = 191 := (191).nth_count (by decide : Nat.Prime 191)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_43 : Nat.nth Nat.Prime 43 = 193 := (193).nth_count (by decide : Nat.Prime 193)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_44 : Nat.nth Nat.Prime 44 = 197 := (197).nth_count (by decide : Nat.Prime 197)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_45 : Nat.nth Nat.Prime 45 = 199 := (199).nth_count (by decide : Nat.Prime 199)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_46 : Nat.nth Nat.Prime 46 = 211 := (211).nth_count (by decide : Nat.Prime 211)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_47 : Nat.nth Nat.Prime 47 = 223 := (223).nth_count (by decide : Nat.Prime 223)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_48 : Nat.nth Nat.Prime 48 = 227 := (227).nth_count (by decide : Nat.Prime 227)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_49 : Nat.nth Nat.Prime 49 = 229 := (229).nth_count (by decide : Nat.Prime 229)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_50 : Nat.nth Nat.Prime 50 = 233 := (233).nth_count (by decide : Nat.Prime 233)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_51 : Nat.nth Nat.Prime 51 = 239 := (239).nth_count (by decide : Nat.Prime 239)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_52 : Nat.nth Nat.Prime 52 = 241 := (241).nth_count (by decide : Nat.Prime 241)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_53 : Nat.nth Nat.Prime 53 = 251 := (251).nth_count (by decide : Nat.Prime 251)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_54 : Nat.nth Nat.Prime 54 = 257 := (257).nth_count (by decide : Nat.Prime 257)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_55 : Nat.nth Nat.Prime 55 = 263 := (263).nth_count (by decide : Nat.Prime 263)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_56 : Nat.nth Nat.Prime 56 = 269 := (269).nth_count (by decide : Nat.Prime 269)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_57 : Nat.nth Nat.Prime 57 = 271 := (271).nth_count (by decide : Nat.Prime 271)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_58 : Nat.nth Nat.Prime 58 = 277 := (277).nth_count (by decide : Nat.Prime 277)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_59 : Nat.nth Nat.Prime 59 = 281 := (281).nth_count (by decide : Nat.Prime 281)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_60 : Nat.nth Nat.Prime 60 = 283 := (283).nth_count (by decide : Nat.Prime 283)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_61 : Nat.nth Nat.Prime 61 = 293 := (293).nth_count (by decide : Nat.Prime 293)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma prime_62 : Nat.nth Nat.Prime 62 = 307 := (307).nth_count (by decide : Nat.Prime 307)

end OMA.PrimeResidues

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := by
  intro n hn h61 hp
  interval_cases n <;> norm_num [OeisA182126.a, OeisA182126.prime, OMA.PrimeResidues.prime_0, OMA.PrimeResidues.prime_1, OMA.PrimeResidues.prime_2, OMA.PrimeResidues.prime_3, OMA.PrimeResidues.prime_4, OMA.PrimeResidues.prime_5, OMA.PrimeResidues.prime_6, OMA.PrimeResidues.prime_7, OMA.PrimeResidues.prime_8, OMA.PrimeResidues.prime_9, OMA.PrimeResidues.prime_10, OMA.PrimeResidues.prime_11, OMA.PrimeResidues.prime_12, OMA.PrimeResidues.prime_13, OMA.PrimeResidues.prime_14, OMA.PrimeResidues.prime_15, OMA.PrimeResidues.prime_16, OMA.PrimeResidues.prime_17, OMA.PrimeResidues.prime_18, OMA.PrimeResidues.prime_19, OMA.PrimeResidues.prime_20, OMA.PrimeResidues.prime_21, OMA.PrimeResidues.prime_22, OMA.PrimeResidues.prime_23, OMA.PrimeResidues.prime_24, OMA.PrimeResidues.prime_25, OMA.PrimeResidues.prime_26, OMA.PrimeResidues.prime_27, OMA.PrimeResidues.prime_28, OMA.PrimeResidues.prime_29, OMA.PrimeResidues.prime_30, OMA.PrimeResidues.prime_31, OMA.PrimeResidues.prime_32, OMA.PrimeResidues.prime_33, OMA.PrimeResidues.prime_34, OMA.PrimeResidues.prime_35, OMA.PrimeResidues.prime_36, OMA.PrimeResidues.prime_37, OMA.PrimeResidues.prime_38, OMA.PrimeResidues.prime_39, OMA.PrimeResidues.prime_40, OMA.PrimeResidues.prime_41, OMA.PrimeResidues.prime_42, OMA.PrimeResidues.prime_43, OMA.PrimeResidues.prime_44, OMA.PrimeResidues.prime_45, OMA.PrimeResidues.prime_46, OMA.PrimeResidues.prime_47, OMA.PrimeResidues.prime_48, OMA.PrimeResidues.prime_49, OMA.PrimeResidues.prime_50, OMA.PrimeResidues.prime_51, OMA.PrimeResidues.prime_52, OMA.PrimeResidues.prime_53, OMA.PrimeResidues.prime_54, OMA.PrimeResidues.prime_55, OMA.PrimeResidues.prime_56, OMA.PrimeResidues.prime_57, OMA.PrimeResidues.prime_58, OMA.PrimeResidues.prime_59, OMA.PrimeResidues.prime_60, OMA.PrimeResidues.prime_61, OMA.PrimeResidues.prime_62] at *
