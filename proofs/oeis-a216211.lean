import OMAStatements.S_oeis_a216211

open scoped BigOperators
open Matrix

namespace OMA.S_oeis_a216211_proof

open OMA.S_oeis_a216211

private def Tmat : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![1,1,1,1,1,1,1,1,0,0,0,0],
  ![1,1,0,1,1,1,0,1,0,0,0,0],
  ![0,0,1,1,0,0,1,1,0,0,0,0],
  ![1,1,0,1,0,0,0,1,1,1,0,0],
  ![0,0,0,0,1,1,1,1,0,0,0,0],
  ![0,0,0,0,1,1,0,1,0,0,0,0],
  ![0,0,1,1,1,0,1,1,0,0,0,0],
  ![1,1,0,1,0,0,0,1,1,1,1,1],
  ![1,0,0,0,0,0,0,0,1,1,0,0],
  ![1,0,0,0,0,0,0,0,1,1,0,1],
  ![1,1,0,0,0,0,0,0,0,0,1,1],
  ![1,1,0,0,0,0,0,0,0,1,1,1]
]
private def P1 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![1,1,1,1,1,1,1,1,0,0,0,0],
  ![1,1,0,1,1,1,0,1,0,0,0,0],
  ![0,0,1,1,0,0,1,1,0,0,0,0],
  ![1,1,0,1,0,0,0,1,1,1,0,0],
  ![0,0,0,0,1,1,1,1,0,0,0,0],
  ![0,0,0,0,1,1,0,1,0,0,0,0],
  ![0,0,1,1,1,0,1,1,0,0,0,0],
  ![1,1,0,1,0,0,0,1,1,1,1,1],
  ![1,0,0,0,0,0,0,0,1,1,0,0],
  ![1,0,0,0,0,0,0,0,1,1,0,1],
  ![1,1,0,0,0,0,0,0,0,0,1,1],
  ![1,1,0,0,0,0,0,0,0,1,1,1]
]
private def P2 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![4,4,3,6,5,4,4,8,2,2,1,1],
  ![4,4,1,4,4,4,2,6,2,2,1,1],
  ![2,2,2,4,1,0,2,4,2,2,1,1],
  ![6,4,1,4,2,2,1,4,4,4,1,2],
  ![1,1,1,2,3,2,2,4,1,1,1,1],
  ![1,1,0,1,2,2,1,3,1,1,1,1],
  ![2,2,2,4,2,1,3,5,2,2,1,1],
  ![8,6,1,4,2,2,1,4,4,5,3,4],
  ![3,1,1,1,1,1,1,1,2,2,0,1],
  ![4,2,1,1,1,1,1,1,2,3,1,2],
  ![4,4,1,2,2,2,1,2,0,1,2,2],
  ![5,4,1,2,2,2,1,2,1,2,2,3]
]
private def P3 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![28,24,11,29,21,17,16,38,18,19,10,12],
  ![24,20,7,21,18,16,11,29,14,15,8,10],
  ![18,14,6,16,7,5,7,17,12,13,6,8],
  ![29,21,8,20,15,14,10,24,16,18,7,11],
  ![12,10,4,11,9,7,7,16,8,9,6,7],
  ![10,8,2,7,7,6,4,11,6,7,5,6],
  ![19,15,7,18,10,7,9,21,13,14,7,9],
  ![38,29,10,24,19,18,12,28,17,21,11,16],
  ![11,7,5,8,7,6,6,10,6,7,2,4],
  ![16,11,6,10,9,8,7,12,7,9,4,7],
  ![17,16,6,14,13,12,8,18,5,7,6,7],
  ![21,18,7,15,14,13,9,19,7,10,7,9]
]
private def P4 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![178,141,55,146,106,90,76,184,104,116,60,79],
  ![141,112,42,112,89,78,60,146,79,89,47,62],
  ![104,79,31,78,51,44,38,90,58,66,31,44],
  ![146,112,47,112,89,79,62,141,78,89,42,60],
  ![79,62,23,60,45,38,32,76,44,51,29,38],
  ![60,47,16,42,35,31,23,55,31,37,22,29],
  ![116,89,35,89,60,51,45,106,66,75,37,51],
  ![184,146,60,141,116,104,79,178,90,106,55,76],
  ![55,42,22,47,37,31,29,60,31,35,16,23],
  ![76,60,29,62,51,44,38,79,38,45,23,32],
  ![90,78,31,79,66,58,44,104,44,51,31,38],
  ![106,89,37,89,75,66,51,116,51,60,35,45]
]
private def P5 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![1008,788,309,780,591,515,415,976,550,629,323,439],
  ![788,620,243,613,480,420,332,780,426,488,255,344],
  ![550,426,173,420,316,278,224,515,292,336,165,231],
  ![780,613,255,620,488,426,344,788,420,480,243,332],
  ![439,344,134,332,256,224,179,415,231,269,143,194],
  ![323,255,99,243,196,173,134,309,165,194,106,143],
  ![629,488,196,480,361,316,256,591,336,387,194,269],
  ![976,780,323,788,629,550,439,1008,515,591,309,415],
  ![309,243,106,255,194,165,143,323,173,196,99,134],
  ![415,332,143,344,269,231,194,439,224,256,134,179],
  ![515,420,165,426,336,292,231,550,278,316,173,224],
  ![591,480,194,488,387,336,269,629,316,361,196,256]
]
private def P6 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![5493,4314,1732,4276,3317,2902,2323,5382,2935,3374,1738,2367],
  ![4314,3400,1363,3376,2640,2308,1843,4276,2307,2651,1379,1867],
  ![2935,2307,947,2308,1794,1570,1263,2902,1563,1794,911,1247],
  ![4276,3376,1379,3400,2651,2307,1867,4314,2308,2640,1363,1843],
  ![2367,1867,752,1843,1442,1263,1008,2323,1247,1441,752,1021],
  ![1738,1379,556,1363,1081,947,752,1732,911,1054,558,752],
  ![3374,2651,1081,2640,2050,1794,1442,3317,1794,2063,1054,1441],
  ![5382,4276,1738,4314,3374,2935,2367,5493,2902,3317,1732,2323],
  ![1732,1363,558,1379,1054,911,752,1738,947,1081,556,752],
  ![2323,1843,752,1867,1441,1247,1021,2367,1263,1442,752,1008],
  ![2902,2308,911,2307,1794,1563,1247,2935,1570,1794,947,1263],
  ![3317,2640,1054,2651,2063,1794,1441,3374,1794,2050,1081,1442]
]
private def P7 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![29879,23570,9548,23520,18349,16026,12865,29739,15967,18334,9487,12861],
  ![23570,18612,7520,18572,14505,12662,10160,23520,12610,14477,7522,10173],
  ![15967,12610,5145,12662,9869,8606,6939,16026,8567,9814,5060,6854],
  ![23520,18572,7522,18612,14477,12610,10173,23570,12662,14505,7520,10160],
  ![12861,10173,4127,10160,7947,6939,5569,12865,6854,7875,4096,5537],
  ![9487,7522,3046,7520,5897,5145,4127,9548,5060,5812,3042,4096],
  ![18334,14477,5897,14505,11311,9869,7947,18349,9814,11255,5812,7875],
  ![29739,23520,9487,23570,18334,15967,12861,29879,16026,18349,9548,12865],
  ![9548,7520,3042,7522,5812,5060,4096,9487,5145,5897,3046,4127],
  ![12865,10160,4096,10173,7875,6854,5537,12861,6939,7947,4127,5569],
  ![16026,12662,5060,12610,9814,8567,6854,15967,8606,9869,5145,6939],
  ![18349,14505,5812,14477,11255,9814,7875,18334,9869,11311,5897,7947]
]
private def P8 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![163357,129056,52292,129121,100689,87824,70641,163496,87560,100421,52087,70421],
  ![129056,101969,41250,101954,79509,69349,55755,129121,69179,79352,41215,55692],
  ![87560,69179,28051,69349,53991,47052,37920,87824,47069,53923,27940,37754],
  ![129121,101954,41215,101969,79352,69179,55692,129056,69349,79509,41250,55755],
  ![70421,55692,22557,55755,43489,37920,30504,70641,37754,43291,22498,30373],
  ![52087,41215,16660,41250,32178,28051,22557,52292,27940,32036,16686,22498],
  ![100421,79352,32178,79509,61938,53991,43489,100689,53923,61798,32036,43291],
  ![163496,129121,52087,129056,100421,87560,70421,163357,87824,100689,52292,70641],
  ![52292,41250,16686,41215,32036,27940,22498,52087,28051,32178,16660,22557],
  ![70641,55755,22498,55692,43291,37754,30373,70421,37920,43489,22557,30504],
  ![87824,69349,27940,69179,53923,47069,37754,87560,47052,53991,28051,37920],
  ![100689,79509,32036,79352,61798,53923,43291,100421,53991,61938,32178,43489]
]
private def P9 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![895519,707538,286290,707963,551567,480926,386979,896476,480598,551019,286004,386425],
  ![707538,559007,226061,559105,435638,379883,305570,707963,379606,435298,226028,305380],
  ![480598,379606,153531,379883,295702,257782,207522,480926,258165,295919,153518,207441],
  ![707963,559105,226028,559007,435298,379606,305380,707538,379883,435638,226061,305570],
  ![386425,305380,123482,305570,238026,207522,166971,386979,207441,237814,123512,166803],
  ![286004,226028,91304,226061,176088,153531,123482,286290,153518,176016,91476,123512],
  ![551019,435298,176088,435638,339191,295702,238026,551567,295919,339210,176016,237814],
  ![896476,707963,286004,707538,551019,480598,386425,895519,480926,551567,286290,386979],
  ![286290,226061,91476,226028,176016,153518,123512,286004,153531,176088,91304,123482],
  ![386979,305570,123512,305380,237814,207441,166803,386425,207522,238026,123482,166971],
  ![480926,379883,153518,379606,295919,258165,207441,480598,257782,295702,153531,207522],
  ![551567,435638,176016,435298,339210,295919,237814,551019,295702,339191,176088,238026]
]
private def P10 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![4911542,3879925,1568788,3880765,3022529,2635550,2120355,4913258,2636056,3022481,1568905,2119924],
  ![3879925,3065021,1239169,3065244,2387636,2082066,1674807,3880765,2081972,2387352,1239371,1674669],
  ![2636056,2081972,841651,2082066,1621210,1413688,1137353,2635550,1414893,1622334,841885,1137804],
  ![3880765,3065244,1239371,3065021,2387352,2081972,1674669,3879925,2082066,2387636,1239169,1674807],
  ![2119924,1674669,676878,1674807,1304324,1137353,914904,2120355,1137804,1304607,677294,915108],
  ![1568905,1239371,500790,1239169,965133,841651,676878,1568788,841885,965397,501278,677294],
  ![3022481,2387352,965133,2387636,1859236,1621210,1304324,3022529,1622334,1860148,965397,1304607],
  ![4913258,3880765,1568905,3879925,3022481,2636056,2119924,4911542,2635550,3022529,1568788,2120355],
  ![1568788,1239169,501278,1239371,965397,841885,677294,1568905,841651,965133,500790,676878],
  ![2120355,1674807,677294,1674669,1304607,1137804,915108,2119924,1137353,1304324,676878,914904],
  ![2635550,2082066,841885,2081972,1622334,1414893,1137804,2636056,1413688,1621210,841651,1137353],
  ![3022529,2387636,965397,2387352,1860148,1622334,1304607,3022481,1621210,1859236,965133,1304324]
]
private def P11 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![26932856,21274319,8600685,21274633,16569901,14449546,11623214,26932712,14452560,16572484,8602087,11624568],
  ![21274319,16804995,6793901,16804931,13089455,11414648,9181537,21274633,11415333,13090002,6794805,9182157],
  ![14452560,11415333,4615060,11414648,8890279,7752926,6236270,14449546,7754843,8892647,4615239,6237573],
  ![21274633,16804931,6794805,16804995,13090002,11415333,9182157,21274319,11414648,13089455,6793901,9181537],
  ![11624568,9182157,3711706,9181537,7151174,6236270,5016030,11623214,6237573,7152681,3712757,5017364],
  ![8602087,6794805,2746573,6793901,5291938,4615060,3711706,8600685,4615239,5292533,2747360,3712757],
  ![16572484,13090002,5291938,13089455,10194603,8890279,7151174,16569901,8892647,10197254,5292533,7152681],
  ![26932712,21274633,8602087,21274319,16572484,14452560,11624568,26932856,14449546,16569901,8600685,11623214],
  ![8600685,6793901,2747360,6794805,5292533,4615239,3712757,8602087,4615060,5291938,2746573,3711706],
  ![11623214,9181537,3712757,9182157,7152681,6237573,5017364,11624568,6236270,7151174,3711706,5016030],
  ![14449546,11414648,4615239,11415333,8892647,7754843,6237573,14452560,7752926,8890279,4615060,6236270],
  ![16569901,13089455,5292533,13090002,10197254,8892647,7152681,16572484,8890279,10194603,5291938,7151174]
]
private def P12 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of ![
  ![147666219,116641175,47156755,116638419,90849836,79226622,63726656,147657866,79232389,90856957,47159367,63731851],
  ![116641175,92135840,37249757,92134316,71764954,62583417,50339212,116638419,62584899,71767056,37251595,50341597],
  ![79232389,62584899,25303890,62583417,48747368,42511098,34194169,79226622,42511684,48749257,25302358,34195005],
  ![116638419,92134316,37251595,92135840,71767056,62584899,50341597,116641175,62583417,71764954,37249757,50339212],
  ![63731851,50341597,20352304,50339212,39210199,34194169,27503478,63726656,34195005,39212369,20353335,27506016],
  ![47159367,37251595,15060366,37249757,29015596,25303890,20352304,47156755,25302358,29015115,15060802,20353335],
  ![90856957,71767056,29015596,71764954,55898542,48747368,39210199,90849836,48749257,55901938,29015115,39212369],
  ![147657866,116638419,47159367,116641175,90856957,79232389,63731851,147666219,79226622,90849836,47156755,63726656],
  ![47156755,37249757,15060802,37251595,29015115,25302358,20353335,47159367,25303890,29015596,15060366,20352304],
  ![63726656,50339212,20353335,50341597,39212369,34195005,27506016,63731851,34194169,39210199,20352304,27503478],
  ![79226622,62583417,25302358,62584899,48749257,42511684,34195005,79232389,42511098,48747368,25303890,34194169],
  ![90849836,71764954,29015115,71767056,55901938,48749257,39212369,90856957,48747368,55898542,29015596,39210199]
]

private def matEqBool (A B : Matrix (Fin 12) (Fin 12) ℤ) : Bool :=
  (List.finRange 12).all fun i => (List.finRange 12).all fun j => A i j == B i j

private lemma matEq_of_bool {A B : Matrix (Fin 12) (Fin 12) ℤ}
    (h : matEqBool A B = true) : A = B := by
  ext i j
  simp only [matEqBool, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h i j

private lemma sum_fin12 (f : Fin 12 → ℤ) :
    ∑ k : Fin 12, f k = ((List.finRange 12).map f).sum := by
  simp [Fin.sum_univ_succ, List.finRange_succ]

private def matMulBool (A B C : Matrix (Fin 12) (Fin 12) ℤ) : Bool :=
  (List.finRange 12).all fun i => (List.finRange 12).all fun j =>
    C i j == ((List.finRange 12).map fun k => A i k * B k j).sum

private lemma matMul_of_bool {A B C : Matrix (Fin 12) (Fin 12) ℤ}
    (h : matMulBool A B C = true) : C = A * B := by
  ext i j
  simp only [matMulBool, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  rw [h i j, Matrix.mul_apply, sum_fin12]

private lemma p1_eq : P1 = Tmat := matEq_of_bool (by decide)
private lemma p2_eq : P2 = P1 * Tmat := matMul_of_bool (by decide)
private lemma p3_eq : P3 = P2 * Tmat := matMul_of_bool (by decide)
private lemma p4_eq : P4 = P3 * Tmat := matMul_of_bool (by decide)
private lemma p5_eq : P5 = P4 * Tmat := matMul_of_bool (by decide)
private lemma p6_eq : P6 = P5 * Tmat := matMul_of_bool (by decide)
private lemma p7_eq : P7 = P6 * Tmat := matMul_of_bool (by decide)
private lemma p8_eq : P8 = P7 * Tmat := matMul_of_bool (by decide)
private lemma p9_eq : P9 = P8 * Tmat := matMul_of_bool (by decide)
private lemma p10_eq : P10 = P9 * Tmat := matMul_of_bool (by decide)
private lemma p11_eq : P11 = P10 * Tmat := matMul_of_bool (by decide)
private lemma p12_eq : P12 = P11 * Tmat := matMul_of_bool (by decide)

private lemma tpow_1 : Tmat ^ 1 = P1 := by rw [pow_one, p1_eq]
private lemma tpow_2 : Tmat ^ 2 = P2 := by rw [pow_succ, tpow_1, p2_eq]
private lemma tpow_3 : Tmat ^ 3 = P3 := by rw [pow_succ, tpow_2, p3_eq]
private lemma tpow_4 : Tmat ^ 4 = P4 := by rw [pow_succ, tpow_3, p4_eq]
private lemma tpow_5 : Tmat ^ 5 = P5 := by rw [pow_succ, tpow_4, p5_eq]
private lemma tpow_6 : Tmat ^ 6 = P6 := by rw [pow_succ, tpow_5, p6_eq]
private lemma tpow_7 : Tmat ^ 7 = P7 := by rw [pow_succ, tpow_6, p7_eq]
private lemma tpow_8 : Tmat ^ 8 = P8 := by rw [pow_succ, tpow_7, p8_eq]
private lemma tpow_9 : Tmat ^ 9 = P9 := by rw [pow_succ, tpow_8, p9_eq]
private lemma tpow_10 : Tmat ^ 10 = P10 := by rw [pow_succ, tpow_9, p10_eq]
private lemma tpow_11 : Tmat ^ 11 = P11 := by rw [pow_succ, tpow_10, p11_eq]
private lemma tpow_12 : Tmat ^ 12 = P12 := by rw [pow_succ, tpow_11, p12_eq]

private lemma p_char :
    P12 - 12 • P11 + 54 • P10 - 124 • P9 + 133 • P8 +
      16 • P7 - 175 • P6 + 94 • P5 + 69 • P4 - 40 • P3 -
      12 • P2 + 4 • P1 + 1 = 0 := by
  refine matEq_of_bool (by decide)

private lemma Tmat_char :
    Tmat ^ 12 - 12 • Tmat ^ 11 + 54 • Tmat ^ 10 - 124 • Tmat ^ 9 + 133 • Tmat ^ 8 +
      16 • Tmat ^ 7 - 175 • Tmat ^ 6 + 94 • Tmat ^ 5 + 69 • Tmat ^ 4 - 40 • Tmat ^ 3 -
      12 • Tmat ^ 2 + 4 • Tmat ^ 1 + 1 = 0 := by
  rw [tpow_12, tpow_11, tpow_10, tpow_9, tpow_8, tpow_7, tpow_6, tpow_5, tpow_4, tpow_3, tpow_2,
    tpow_1]
  exact p_char

private lemma Tmat_zero_one (s t : Fin 12) : Tmat s t = 0 ∨ Tmat s t = 1 := by
  fin_cases s <;> fin_cases t <;> decide

private def stateOp : Fin 12 → Fin 4 := ![0, 1, 0, 2, 0, 1, 0, 3, 2, 3, 3, 3]

private def statePair : Fin 12 → Option (Fin 4 × Fin 4) :=
  ![none, none, some (1, 2), none, some (2, 3), some (2, 3),
    some (1, 3), none, some (0, 1), some (0, 1), some (1, 2), some (0, 2)]

private def topMask (s : Fin 12) (c : Fin 4) : Bool :=
  (c == stateOp s) ||
    match statePair s with
    | none => false
    | some (a, b) => (c == a) || (c == b)

private def connH (h : Fin 3 → Bool) (u v : Fin 4) : Bool :=
  (List.finRange 3).all fun c => !(min u.val v.val ≤ c.val && c.val < max u.val v.val) || h c

private def noCycle (s : Fin 12) (h : Fin 3 → Bool) : Bool :=
  match statePair s with
  | none => true
  | some (a, b) => !connH h a b

private def connRow (s : Fin 12) (h : Fin 3 → Bool) (u v : Fin 4) : Bool :=
  connH h u v ||
    match statePair s with
    | none => false
    | some (a, b) => (connH h u a && connH h v b) || (connH h u b && connH h v a)

private def colDeg (top : Fin 4 → Bool) (h : Fin 3 → Bool) (bot : Fin 4 → Bool) (c : Fin 4) : ℕ :=
  (if top c then 1 else 0) + (if bot c then 1 else 0) +
    (if h0 : 0 < c.val then (if h ⟨c.val - 1, by omega⟩ then 1 else 0) else 0) +
    (if h3 : c.val < 3 then (if h ⟨c.val, h3⟩ then 1 else 0) else 0)

private def degOK (s : Fin 12) (h : Fin 3 → Bool) (bot : Fin 4 → Bool) : Bool :=
  (List.finRange 4).all fun c => let d := colDeg (topMask s) h bot c; d == 0 || d == 2

private def validTrans (s : Fin 12) (h : Fin 3 → Bool) (bot : Fin 4 → Bool) (sp : Fin 12) : Bool :=
  degOK s h bot && noCycle s h &&
    ((List.finRange 4).all fun c => bot c == topMask sp c) &&
    connRow s h (stateOp s) (stateOp sp) &&
    match statePair sp with
    | none => true
    | some (a', b') => connRow s h a' b'

private def hBits (k : Fin 8) : Fin 3 → Bool := fun c => k.val.testBit c.val
private def vBits (k : Fin 16) : Fin 4 → Bool := fun c => k.val.testBit c.val

private lemma hBits_surj (h : Fin 3 → Bool) : ∃ hk : Fin 8, hBits hk = h := by
  have hc : ∀ b0 b1 b2 : Bool,
      ((List.finRange 8).any fun k =>
        (hBits k 0 == b0) && (hBits k 1 == b1) && (hBits k 2 == b2)) = true := by decide
  have hmem := hc (h 0) (h 1) (h 2)
  rw [List.any_eq_true] at hmem
  rcases hmem with ⟨hk, _, hmatch⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
  refine ⟨hk, funext fun ⟨c, hc'⟩ => ?_⟩
  match c, hc' with
  | 0, _ => exact hmatch.1.1
  | 1, _ => exact hmatch.1.2
  | 2, _ => exact hmatch.2

private lemma vBits_surj (v : Fin 4 → Bool) : ∃ vk : Fin 16, vBits vk = v := by
  have hc : ∀ b0 b1 b2 b3 : Bool,
      ((List.finRange 16).any fun k =>
        (vBits k 0 == b0) && (vBits k 1 == b1) && (vBits k 2 == b2) && (vBits k 3 == b3)) = true := by
    decide
  have hmem := hc (v 0) (v 1) (v 2) (v 3)
  rw [List.any_eq_true] at hmem
  rcases hmem with ⟨vk, _, hmatch⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
  refine ⟨vk, funext fun ⟨c, hc'⟩ => ?_⟩
  match c, hc' with
  | 0, _ => exact hmatch.1.1.1
  | 1, _ => exact hmatch.1.1.2
  | 2, _ => exact hmatch.1.2
  | 3, _ => exact hmatch.2

private def nextState (s : Fin 12) (h : Fin 3 → Bool) (bot : Fin 4 → Bool) : Fin 12 :=
  ((List.finRange 12).find? (fun sp => validTrans s h bot sp)).getD 0

private def findTransHK (s sp : Fin 12) : Fin 8 :=
  (((List.finRange 8).find? fun hk =>
    (List.finRange 16).any fun vk => validTrans s (hBits hk) (vBits vk) sp)).getD 0

private def transH (s sp : Fin 12) : Fin 3 → Bool := hBits (findTransHK s sp)

private lemma check_all_valid :
    ((List.finRange 12).all fun s =>
      (List.finRange 8).all fun hk =>
        (List.finRange 16).all fun vk =>
          let h := hBits hk; let bot := vBits vk
          !(degOK s h bot && noCycle s h) ||
            (validTrans s h bot (nextState s h bot) &&
              (List.finRange 12).all fun sp => !validTrans s h bot sp || (sp == nextState s h bot))) = true := by
  decide

private lemma check_Tmat_hits :
    ((List.finRange 12).all fun s =>
      (List.finRange 12).all fun sp =>
        let hits := (List.finRange 8).flatMap fun hk =>
          (List.finRange 16).filterMap fun vk =>
            if validTrans s (hBits hk) (vBits vk) sp then some (hk, vk) else none
        (Tmat s sp == (hits.length : ℤ)) &&
          (!(Tmat s sp == 1) || validTrans s (transH s sp) (topMask sp) sp) &&
          ((List.finRange 8).all fun hk => (List.finRange 16).all fun vk =>
            !validTrans s (hBits hk) (vBits vk) sp || (hk == findTransHK s sp))) = true := by
  decide

private lemma nextState_of_degOK_noCycle {s : Fin 12} {h : Fin 3 → Bool} {bot : Fin 4 → Bool}
    (hdeg : degOK s h bot = true) (hnc : noCycle s h = true) :
    validTrans s h bot (nextState s h bot) = true := by
  rcases hBits_surj h with ⟨hk, rfl⟩
  rcases vBits_surj bot with ⟨vk, rfl⟩
  have hc := check_all_valid
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
  have hrow := hc s hk vk
  simp only [hdeg, hnc, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hrow
  exact hrow.1

private lemma eq_nextState_of_validTrans {s sp : Fin 12} {h : Fin 3 → Bool} {bot : Fin 4 → Bool}
    (hv : validTrans s h bot sp = true) : sp = nextState s h bot := by
  rcases hBits_surj h with ⟨hk, rfl⟩
  rcases vBits_surj bot with ⟨vk, rfl⟩
  have hdeg : degOK s (hBits hk) (vBits vk) = true := by
    simp only [validTrans, Bool.and_eq_true] at hv
    exact hv.1.1.1.1
  have hnc : noCycle s (hBits hk) = true := by
    simp only [validTrans, Bool.and_eq_true] at hv
    exact hv.1.1.1.2
  have hc := check_all_valid
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
  have hrow := hc s hk vk
  simp only [hdeg, hnc, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at hrow
  rcases hrow.2 sp with hbad | heq
  · exact absurd hv (Bool.eq_false_iff.mp hbad)
  · exact heq

private lemma validTrans_topMask_eq {s sp : Fin 12} {h : Fin 3 → Bool} {bot : Fin 4 → Bool}
    (hv : validTrans s h bot sp = true) : bot = topMask sp := by
  simp only [validTrans, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq] at hv
  exact funext hv.1.1.2

private lemma validTrans_Tmat {s sp : Fin 12} {h : Fin 3 → Bool} {bot : Fin 4 → Bool}
    (hv : validTrans s h bot sp = true) : Tmat s sp = 1 := by
  rcases hBits_surj h with ⟨hk, rfl⟩
  rcases vBits_surj bot with ⟨vk, rfl⟩
  have hc := check_Tmat_hits
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc
  rcases hc s sp with ⟨⟨hlen, _⟩, _⟩
  have hmem : (hk, vk) ∈ (List.finRange 8).flatMap fun hk' =>
      (List.finRange 16).filterMap fun vk' =>
        if validTrans s (hBits hk') (vBits vk') sp then some (hk', vk') else none := by
    rw [List.mem_flatMap]
    refine ⟨hk, List.mem_finRange hk, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨vk, List.mem_finRange vk, by simp [hv]⟩
  have hpos : 0 < ((List.finRange 8).flatMap fun hk' =>
      (List.finRange 16).filterMap fun vk' =>
        if validTrans s (hBits hk') (vBits vk') sp then some (hk', vk') else none).length :=
    List.length_pos_of_mem hmem
  rcases Tmat_zero_one s sp with h0 | h1
  · exfalso
    rw [h0] at hlen
    omega
  · exact h1

private lemma validTrans_transH_spec {s sp : Fin 12} (ht : Tmat s sp = 1) :
    validTrans s (transH s sp) (topMask sp) sp = true := by
  have hc := check_Tmat_hits
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true] at hc
  have hvt := (hc s sp).1.2
  simp [ht] at hvt
  exact hvt

private lemma validTrans_eq_transH {s sp : Fin 12} {h : Fin 3 → Bool} {bot : Fin 4 → Bool}
    (hv : validTrans s h bot sp = true) : h = transH s sp ∧ bot = topMask sp := by
  refine ⟨?_, validTrans_topMask_eq hv⟩
  rcases hBits_surj h with ⟨hk, rfl⟩
  rcases vBits_surj bot with ⟨vk, rfl⟩
  have hc := check_Tmat_hits
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hc
  rcases hc s sp with ⟨_, huniq⟩
  rcases huniq hk vk with hbad | heq
  · exact absurd hv (Bool.eq_false_iff.mp hbad)
  · rw [transH, heq]

private lemma topMask_eq_zero_iff (s : Fin 12) :
    (∀ c : Fin 4, topMask s c = decide (c.val = 0)) ↔ s = 0 := by
  have hdec : ((List.finRange 4).all fun c => topMask s c == decide (c.val = 0)) = true ↔ s = 0 := by
    fin_cases s <;> decide
  rw [← hdec, List.all_eq_true]
  simp [List.mem_finRange]

private lemma statePair_ne_none_ne_zero {s : Fin 12} {a b : Fin 4}
    (h : statePair s = some (a, b)) : s ≠ 0 := by
  rintro rfl
  simp [statePair] at h

private lemma statePair_lt {s : Fin 12} {a b : Fin 4} (h : statePair s = some (a, b)) :
    a.val < b.val := by
  fin_cases s <;> simp [statePair] at h <;> rcases h with ⟨rfl, rfl⟩ <;> decide

private lemma statePair_topMask {s : Fin 12} {a b : Fin 4} (h : statePair s = some (a, b)) :
    topMask s a = true ∧ topMask s b = true := by
  simp [topMask, h]

private lemma stateOp_topMask (s : Fin 12) : topMask s (stateOp s) = true := by
  simp [topMask]

private def walkH (u v : Fin 4) : List (Fin 4) :=
  if h : u.val ≤ v.val then
    (List.finRange (v.val - u.val + 1)).map fun i => ⟨u.val + i.val, by have := i.isLt; have := v.isLt; omega⟩
  else
    (List.finRange (u.val - v.val + 1)).map fun i => ⟨u.val - i.val, by have := u.isLt; omega⟩

private lemma walkH_head (u v : Fin 4) : (walkH u v).head? = some u := by
  fin_cases u <;> fin_cases v <;> decide

private lemma walkH_getLast (u v : Fin 4) : (walkH u v).getLast? = some v := by
  fin_cases u <;> fin_cases v <;> decide

private lemma walkH_nodup (u v : Fin 4) : (walkH u v).Nodup := by
  fin_cases u <;> fin_cases v <;> decide

private lemma walkH_nonempty (u v : Fin 4) : walkH u v ≠ [] := by
  fin_cases u <;> fin_cases v <;> decide

private lemma walkH_len_ge_two {u v : Fin 4} (hne : u ≠ v) : 2 ≤ (walkH u v).length := by
  fin_cases u <;> fin_cases v <;> simp_all <;> decide

private def adjInList (w : List Site) (u v : Site) : Bool :=
  (List.zip w w.tail).any fun p => (p.1 == u && p.2 == v) || (p.1 == v && p.2 == u)

private lemma adjInList_symm (w : List Site) (u v : Site) : adjInList w u v = adjInList w v u := by
  simp only [adjInList, Bool.or_comm]

private lemma adjInList_mem {w : List Site} {u v : Site} (h : adjInList w u v = true) :
    u ∈ w ∧ v ∈ w := by
  simp only [adjInList, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨x, y⟩, hzip, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ⟨(List.of_mem_zip hzip).1, List.mem_of_mem_tail (List.of_mem_zip hzip).2⟩
  · exact ⟨List.mem_of_mem_tail (List.of_mem_zip hzip).2, (List.of_mem_zip hzip).1⟩

private lemma adjacent_symm {u v : Site} (h : adjacent u v) : adjacent v u := by
  simpa [adjacent, Nat.dist_comm, add_comm] using h

private lemma adjInList_adjacent {w : List Site} (hc : w.IsChain adjacent) {u v : Site}
    (h : adjInList w u v = true) : adjacent u v := by
  induction w with
  | nil => simp [adjInList] at h
  | cons a t ih =>
    cases t with
    | nil => simp [adjInList] at h
    | cons b t' =>
      rw [List.isChain_cons_cons] at hc
      simp only [adjInList, List.tail_cons, List.zip_cons_cons, List.any_cons, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq] at h
      rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hrest
      · exact hc.1
      · exact adjacent_symm hc.1
      · exact ih hc.2 hrest

private lemma adjInList_append {l₁ l₂ : List Site} (hl₁ : l₁ ≠ []) (hl₂ : l₂ ≠ []) (u v : Site) :
    adjInList (l₁ ++ l₂) u v =
      (adjInList l₁ u v || adjInList l₂ u v ||
        ((l₁.getLast? == some u && l₂.head? == some v) ||
         (l₁.getLast? == some v && l₂.head? == some u))) := by
  induction l₁ with
  | nil => exact absurd rfl hl₁
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases l₂ with
      | nil => exact absurd rfl hl₂
      | cons y ys =>
        simp [adjInList, Bool.or_comm, Bool.or_assoc]
    | cons z zs =>
      have ih' := ih (List.cons_ne_nil z zs)
      simp only [List.cons_append, adjInList, List.tail_cons, List.zip_cons_cons,
        List.any_cons, List.getLast?_cons_cons] at ih' ⊢
      rw [ih']
      simp [Bool.or_assoc]

private lemma adjInList_reverse (w : List Site) (u v : Site) :
    adjInList w.reverse u v = adjInList w u v := by
  induction w with
  | nil => simp [adjInList]
  | cons a t ih =>
    cases t with
    | nil => simp [adjInList]
    | cons b t' =>
      have h1 : (b :: t').reverse ≠ [] := by simp
      have h2 : [a] ≠ [] := by simp
      rw [List.reverse_cons, adjInList_append h1 h2]
      have hrev_last : (b :: t').reverse.getLast? = some b := by simp
      have ha_head : ([a] : List Site).head? = some a := rfl
      have hcons : adjInList (a :: b :: t') u v =
          (((a == u && b == v) || (a == v && b == u)) || adjInList (b :: t') u v) := by
        simp [adjInList]
      rw [hcons, ← ih, hrev_last, ha_head]
      simp [adjInList, Bool.or_comm, Bool.or_assoc, Bool.and_comm]

private lemma adjInList_idxOf {w : List Site} (hnd : w.Nodup) {u v : Site}
    (h : adjInList w u v = true) :
    w.idxOf u + 1 = w.idxOf v ∨ w.idxOf v + 1 = w.idxOf u := by
  induction w with
  | nil => simp [adjInList] at h
  | cons a t ih =>
    cases t with
    | nil => simp [adjInList] at h
    | cons b t' =>
      rw [List.nodup_cons] at hnd
      have hab : a ≠ b := fun heq => hnd.1 (heq ▸ List.mem_cons_self)
      simp only [adjInList, List.tail_cons, List.zip_cons_cons, List.any_cons, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq] at h
      rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hrest
      · left
        rw [List.idxOf_cons_self, List.idxOf_cons_ne _ hab, List.idxOf_cons_self]
      · right
        rw [List.idxOf_cons_self, List.idxOf_cons_ne _ hab, List.idxOf_cons_self]
      · have huv := adjInList_mem hrest
        have hua : a ≠ u := fun heq => hnd.1 (heq ▸ huv.1)
        have hva : a ≠ v := fun heq => hnd.1 (heq ▸ huv.2)
        rw [List.idxOf_cons_ne _ hua, List.idxOf_cons_ne _ hva]
        rcases ih hnd.2 hrest with h1 | h2
        · left; omega
        · right; omega

private lemma no_cycle_adjInList {w : List Site} (hnd : w.Nodup) {C : List Site}
    (hlen : 4 ≤ C.length) (hc : C.head? = C.getLast?) (hc_nd : C.tail.Nodup)
    (hch : C.IsChain (fun u v => adjInList w u v = true)) : False := by
  cases C with
  | nil => simp at hlen
  | cons x m =>
    simp only [List.tail_cons, List.length_cons] at hlen hc_nd
    have hm_len : 3 ≤ m.length := by omega
    have hx_last : m.getLast? = some x := by
      cases m with
      | nil => simp at hm_len
      | cons y ys =>
        simpa [List.head?_cons, List.getLast?_cons_cons] using hc.symm
    have hm_cyc : ∀ i : Fin m.length,
        adjInList w m[i.val] (m[(i.val + 1) % m.length]'(Nat.mod_lt _ (by omega))) = true := by
      intro i
      by_cases hi : i.val + 1 < m.length
      · have hmod : (i.val + 1) % m.length = i.val + 1 := Nat.mod_eq_of_lt hi
        simp only [hmod]
        have hch_m : m.IsChain (fun u v => adjInList w u v = true) :=
          (List.isChain_cons.mp hch).2
        exact List.isChain_iff_getElem.mp hch_m i.val hi
      · have hilast : i.val = m.length - 1 := by omega
        have hmod : (i.val + 1) % m.length = 0 := by
          have heq : i.val + 1 = m.length := by omega
          rw [heq, Nat.mod_self]
        simp only [hmod]
        have hmx : m[i.val] = x := by
          rcases List.getLast?_eq_some_iff.mp hx_last with ⟨ys, hys⟩
          have hl : m.getLast (by intro h0; simp [h0] at hm_len) = x := by simp [hys]
          simpa [List.getLast_eq_getElem, hilast] using hl
        have hhead : adjInList w x m[0] = true := by
          cases m with
          | nil => simp at hm_len
          | cons y ys => exact (List.isChain_cons_cons.mp hch).1
        rw [hmx]
        exact hhead
    have hmin := Finset.univ.exists_min_image (fun i : Fin m.length => w.idxOf m[i.val])
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    rcases hmin with ⟨i, _, hi_min⟩
    let iNext : Fin m.length := ⟨(i.val + 1) % m.length, Nat.mod_lt _ (by omega)⟩
    let iPrev : Fin m.length := ⟨(i.val + m.length - 1) % m.length, Nat.mod_lt _ (by omega)⟩
    have hprev_succ : (iPrev.val + 1) % m.length = i.val := by
      dsimp only [iPrev]
      have h1 : i.val + m.length - 1 + 1 = i.val + m.length := by omega
      rw [Nat.mod_add_mod, h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    have hadj_next : adjInList w m[i.val] m[iNext.val] = true := hm_cyc i
    have hadj_prev : adjInList w m[i.val] m[iPrev.val] = true := by
      have hp := hm_cyc iPrev
      simp only [hprev_succ] at hp
      rwa [adjInList_symm]
    have hne_pi : iPrev ≠ i := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp only [iPrev] at hv
      have hlt : i.val < m.length := i.isLt
      by_cases h0 : i.val = 0
      · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hv; omega
      · have h1 : i.val + m.length - 1 = (i.val - 1) + m.length := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hv; omega
    have hne_ni : iNext ≠ i := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp only [iNext] at hv
      have hlt : i.val < m.length := i.isLt
      by_cases hi : i.val + 1 < m.length
      · rw [Nat.mod_eq_of_lt hi] at hv; omega
      · have h1 : i.val + 1 = m.length := by omega
        rw [h1, Nat.mod_self] at hv; omega
    have hne_pn : iPrev ≠ iNext := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp only [iPrev, iNext] at hv
      have hlt : i.val < m.length := i.isLt
      by_cases h0 : i.val = 0 <;> by_cases hi : i.val + 1 < m.length
      · rw [h0, Nat.zero_add, Nat.zero_add, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at hv; omega
      · omega
      · have h1 : i.val + m.length - 1 = (i.val - 1) + m.length := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hi] at hv; omega
      · have h1 : i.val + m.length - 1 = (i.val - 1) + m.length := by omega
        have h2 : i.val + 1 = m.length := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), h2, Nat.mod_self] at hv; omega
    have hm_ne_p : m[iPrev.val] ≠ m[i.val] :=
      fun heq => hne_pi (List.nodup_iff_injective_getElem.mp hc_nd heq)
    have hm_ne_n : m[iNext.val] ≠ m[i.val] :=
      fun heq => hne_ni (List.nodup_iff_injective_getElem.mp hc_nd heq)
    have hm_ne_pn : m[iPrev.val] ≠ m[iNext.val] :=
      fun heq => hne_pn (List.nodup_iff_injective_getElem.mp hc_nd heq)
    have hp_mem := adjInList_mem hadj_prev
    have hn_mem := adjInList_mem hadj_next
    have idx_eq : ∀ {a b : Site}, a ∈ w → b ∈ w → w.idxOf a = w.idxOf b → a = b := by
      intro a b ha hb hid
      have ha' := List.getElem_idxOf (List.idxOf_lt_length_of_mem ha)
      have hb' := List.getElem_idxOf (List.idxOf_lt_length_of_mem hb)
      rw [← ha', ← hb']
      congr 1
    have hp_idx : w.idxOf m[iPrev.val] = w.idxOf m[i.val] + 1 := by
      have hle := hi_min iPrev (Finset.mem_univ _)
      rcases adjInList_idxOf hnd hadj_prev with h1 | h2
      · exact h1.symm
      · exfalso
        have : w.idxOf m[i.val] = w.idxOf m[iPrev.val] := by omega
        exact hm_ne_p (idx_eq hp_mem.2 hp_mem.1 this.symm)
    have hn_idx : w.idxOf m[iNext.val] = w.idxOf m[i.val] + 1 := by
      have hle := hi_min iNext (Finset.mem_univ _)
      rcases adjInList_idxOf hnd hadj_next with h1 | h2
      · exact h1.symm
      · exfalso
        have : w.idxOf m[i.val] = w.idxOf m[iNext.val] := by omega
        exact hm_ne_n (idx_eq hn_mem.2 hn_mem.1 this.symm)
    exact hm_ne_pn (idx_eq hp_mem.2 hn_mem.2 (hp_idx.trans hn_idx.symm))

private def hFromWalk (w : List Site) (r : ℕ) (c : Fin 3) : Bool :=
  adjInList w (r, c.val) (r, c.val + 1)

private def vFromWalk (w : List Site) (n r : ℕ) (c : Fin 4) : Bool :=
  if r = 0 then decide (c.val = 0)
  else if r = n then decide (c.val = 0)
  else adjInList w (r - 1, c.val) (r, c.val)

private lemma adjInList_iff_pred_succ {w : List Site} (hnd : w.Nodup) {u v : Site}
    (hu : u ∈ w) :
    adjInList w u v = true ↔
      (∃ (_ : 0 < w.idxOf u), v = w[w.idxOf u - 1]'(by
        have := List.idxOf_lt_length_of_mem hu; omega)) ∨
      (∃ (_ : w.idxOf u + 1 < w.length), v = w[w.idxOf u + 1]) := by
  induction w with
  | nil => simp at hu
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [List.mem_singleton] at hu
      subst hu
      simp [adjInList]
    | cons b t' =>
      rw [List.nodup_cons] at hnd
      have hab : a ≠ b := fun heq => hnd.1 (heq ▸ List.mem_cons_self)
      rcases List.mem_cons.mp hu with rfl | hut
      · simp only [List.idxOf_cons_self, lt_self_iff_false, IsEmpty.exists_iff, false_or, adjInList,
          List.tail_cons, List.zip_cons_cons, List.any_cons, Bool.or_eq_true, Bool.and_eq_true,
          beq_iff_eq]
        constructor
        · rintro ((⟨_, rfl⟩ | ⟨rfl, hbu⟩) | hrest)
          · exact ⟨by simp, by simp⟩
          · exact absurd hbu.symm hab
          · exfalso
            exact hnd.1 (adjInList_mem hrest).1
        · rintro ⟨_, hv⟩
          left; left
          rw [hv]
          simp
      · have hua : a ≠ u := fun heq => hnd.1 (heq ▸ hut)
        have hidx : (a :: b :: t').idxOf u = (b :: t').idxOf u + 1 :=
          List.idxOf_cons_ne _ hua
        have ih' := ih hnd.2 hut
        simp only [adjInList, List.tail_cons, List.zip_cons_cons, List.any_cons, Bool.or_eq_true,
          Bool.and_eq_true, beq_iff_eq]
        constructor
        · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hrest)
          · exact absurd rfl hua
          · left
            have hb_idx : (b :: t').idxOf b = 0 := List.idxOf_cons_self
            refine ⟨by rw [hidx]; omega, ?_⟩
            simp [hidx, hb_idx]
          · rcases ih'.mp hrest with ⟨hlt, rfl⟩ | ⟨hlt, rfl⟩
            · left
              refine ⟨by rw [hidx]; omega, ?_⟩
              have hsub : (a :: b :: t').idxOf u - 1 = ((b :: t').idxOf u - 1) + 1 := by
                rw [hidx]; omega
              simp [hsub]
            · right
              refine ⟨by rw [hidx, List.length_cons]; omega, ?_⟩
              simp [hidx]
        · rintro (⟨hlt, rfl⟩ | ⟨hlt, rfl⟩)
          · by_cases hu0 : (b :: t').idxOf u = 0
            · have hub : u = b := by
                have := List.getElem_idxOf (List.idxOf_lt_length_of_mem hut)
                simp only [hu0] at this
                exact this.symm
              subst hub
              left; right
              simp [hidx, hu0]
            · right
              refine ih'.mpr (Or.inl ⟨by omega, ?_⟩)
              have hsub : (a :: b :: t').idxOf u - 1 = ((b :: t').idxOf u - 1) + 1 := by
                rw [hidx]; omega
              simp [hsub]
          · right
            refine ih'.mpr (Or.inr ⟨by rw [hidx, List.length_cons] at hlt; omega, ?_⟩)
            simp [hidx]

private lemma deg_walk_eq {n : ℕ} (hn : 1 ≤ n) {w : List Site}
    (hw : isWalk n 4 (0, 0) (n - 1, 0) w) (r : Fin n) (c : Fin 4) :
    colDeg (vFromWalk w n r.val) (hFromWalk w r.val) (vFromWalk w n (r.val + 1)) c =
      if (r.val, c.val) ∈ w then 2 else 0 := by
  rcases hw with ⟨hhead, hlast, hnd, hch, hbd⟩
  let u : Site := (r.val, c.val)
  have hu0 : u = (0, 0) ↔ r.val = 0 ∧ c.val = 0 := by
    simp [u, Prod.ext_iff]
  have hun : u = (n - 1, 0) ↔ r.val + 1 = n ∧ c.val = 0 := by
    simp [u, Prod.ext_iff]
    omega
  have htop_eq : (if vFromWalk w n r.val c then (1 : ℕ) else 0) =
      (if r.val = 0 then (if c.val = 0 then 1 else 0)
       else if adjInList w u (r.val - 1, c.val) then 1 else 0) := by
    by_cases hr0 : r.val = 0
    · simp [vFromWalk, hr0]
    · have hrn : r.val ≠ n := by omega
      simp [vFromWalk, hr0, hrn, adjInList_symm, u]
  have hbot_eq : (if vFromWalk w n (r.val + 1) c then (1 : ℕ) else 0) =
      (if r.val + 1 = n then (if c.val = 0 then 1 else 0)
       else if adjInList w u (r.val + 1, c.val) then 1 else 0) := by
    have hr10 : r.val + 1 ≠ 0 := by omega
    by_cases hrn : r.val + 1 = n
    · simp [vFromWalk, hrn]
    · simp [vFromWalk, hrn, u]
  have hleft_eq : (if h0 : 0 < c.val then (if hFromWalk w r.val ⟨c.val - 1, by omega⟩ then 1 else 0) else 0) =
      (if 0 < c.val then (if adjInList w u (r.val, c.val - 1) then 1 else 0) else 0) := by
    by_cases hc0 : 0 < c.val
    · have hsub : c.val - 1 + 1 = c.val := by omega
      simp [hc0, hFromWalk, adjInList_symm, hsub, u]
    · simp [hc0]
  have hright_eq : (if h3 : c.val < 3 then (if hFromWalk w r.val ⟨c.val, h3⟩ then 1 else 0) else 0) =
      (if c.val < 3 then (if adjInList w u (r.val, c.val + 1) then 1 else 0) else 0) := by
    by_cases hc3 : c.val < 3
    · by_cases hadj : adjInList w u (r.val, c.val + 1) = true <;>
        simp [hc3, hFromWalk, u, hadj]
    · simp [hc3]
  have hcol_sum : colDeg (vFromWalk w n r.val) (hFromWalk w r.val) (vFromWalk w n (r.val + 1)) c =
      (if u = (0, 0) then 1 else 0) + (if u = (n - 1, 0) then 1 else 0) +
        ((if 0 < r.val ∧ adjInList w u (r.val - 1, c.val) = true then 1 else 0) +
         (if r.val + 1 < n ∧ adjInList w u (r.val + 1, c.val) = true then 1 else 0) +
         (if 0 < c.val ∧ adjInList w u (r.val, c.val - 1) = true then 1 else 0) +
         (if c.val < 3 ∧ adjInList w u (r.val, c.val + 1) = true then 1 else 0)) := by
    dsimp only [colDeg]
    rw [htop_eq, hbot_eq, hleft_eq, hright_eq]
    simp only [hu0, hun]
    have h1 : (if r.val = 0 then (if c.val = 0 then 1 else 0)
        else if adjInList w u (r.val - 1, c.val) = true then 1 else 0) =
        (if r.val = 0 ∧ c.val = 0 then 1 else 0) +
          (if 0 < r.val ∧ adjInList w u (r.val - 1, c.val) = true then 1 else 0) := by
      by_cases hr0 : r.val = 0 <;> by_cases hc0 : c.val = 0 <;>
        simp [hr0, hc0, Nat.pos_iff_ne_zero]
    have h2 : (if r.val + 1 = n then (if c.val = 0 then 1 else 0)
        else if adjInList w u (r.val + 1, c.val) = true then 1 else 0) =
        (if r.val + 1 = n ∧ c.val = 0 then 1 else 0) +
          (if r.val + 1 < n ∧ adjInList w u (r.val + 1, c.val) = true then 1 else 0) := by
      by_cases hrn : r.val + 1 = n
      · by_cases hc0 : c.val = 0 <;> simp [hrn, hc0]
      · have hlt : r.val + 1 < n := by have := r.isLt; omega
        simp [hrn, hlt]
    have h3 : (if 0 < c.val then if adjInList w u (r.val, c.val - 1) = true then 1 else 0 else 0) =
        if 0 < c.val ∧ adjInList w u (r.val, c.val - 1) = true then 1 else 0 := by
      by_cases hc0 : 0 < c.val <;> simp [hc0]
    have h4 : (if c.val < 3 then if adjInList w u (r.val, c.val + 1) = true then 1 else 0 else 0) =
        if c.val < 3 ∧ adjInList w u (r.val, c.val + 1) = true then 1 else 0 := by
      by_cases hc3 : c.val < 3 <;> simp [hc3]
    omega
  rw [hcol_sum]
  change _ = if u ∈ w then 2 else 0
  by_cases hu : u ∈ w
  · simp only [hu, ↓reduceIte]
    have h00_mem : (0, 0) ∈ w := List.mem_of_head? hhead
    have hn0_mem : (n - 1, 0) ∈ w := List.mem_of_getLast? hlast
    have hne_prev_next : ∀ (h1 : 0 < w.idxOf u) (h2 : w.idxOf u + 1 < w.length),
        w[w.idxOf u - 1] ≠ w[w.idxOf u + 1] := by
      intro h1 h2 heq
      have hidx := (List.nodup_iff_injective_getElem.mp hnd)
        (a₁ := ⟨w.idxOf u - 1, by omega⟩) (a₂ := ⟨w.idxOf u + 1, h2⟩) heq
      have hv := congrArg Fin.val hidx
      dsimp at hv
      omega
    have hadj_in : ∀ v : Site, adjInList w u v = true →
        (v = (r.val - 1, c.val) ∧ 0 < r.val) ∨
        (v = (r.val + 1, c.val) ∧ r.val + 1 < n) ∨
        (v = (r.val, c.val - 1) ∧ 0 < c.val) ∨
        (v = (r.val, c.val + 1) ∧ c.val < 3) := by
      intro v hv
      have hadj := adjInList_adjacent hch hv
      have hv_bd := hbd v (adjInList_mem hv).2
      rcases v with ⟨vr, vc⟩
      dsimp only [adjacent, u, Nat.dist] at hadj
      have hc4 : c.val < 4 := c.isLt
      have hrn : r.val < n := r.isLt
      have hvr : vr < n := hv_bd.1
      have hvc : vc < 4 := hv_bd.2
      simp only [Prod.mk.injEq]
      omega
    have hcount4 :
        (if 0 < r.val ∧ adjInList w u (r.val - 1, c.val) = true then 1 else 0) +
        (if r.val + 1 < n ∧ adjInList w u (r.val + 1, c.val) = true then 1 else 0) +
        (if 0 < c.val ∧ adjInList w u (r.val, c.val - 1) = true then 1 else 0) +
        (if c.val < 3 ∧ adjInList w u (r.val, c.val + 1) = true then 1 else 0) =
        (if 0 < w.idxOf u then 1 else 0) + (if w.idxOf u + 1 < w.length then 1 else 0) := by
      have hcard_int :
          (if 0 < r.val ∧ adjInList w u (r.val - 1, c.val) = true then 1 else 0) +
          (if r.val + 1 < n ∧ adjInList w u (r.val + 1, c.val) = true then 1 else 0) +
          (if 0 < c.val ∧ adjInList w u (r.val, c.val - 1) = true then 1 else 0) +
          (if c.val < 3 ∧ adjInList w u (r.val, c.val + 1) = true then 1 else 0) =
          ((Finset.univ : Finset (Fin 4)).sum fun t =>
            let v : Site := match t with
              | 0 => (r.val - 1, c.val)
              | 1 => (r.val + 1, c.val)
              | 2 => (r.val, c.val - 1)
              | 3 => (r.val, c.val + 1)
            if ((match t with
                | 0 => decide (0 < r.val)
                | 1 => decide (r.val + 1 < n)
                | 2 => decide (0 < c.val)
                | 3 => decide (c.val < 3)) &&
                adjInList w u v) = true then 1 else 0) := by
        have hterm : ∀ (P : Prop) [Decidable P] (Q : Bool),
            (if P ∧ Q = true then (1 : ℕ) else 0) =
              if (decide P && Q) = true then 1 else 0 := by
          intro P _ Q; by_cases hP : P <;> by_cases hQ : Q = true <;> simp [hP, hQ]
        simp only [Fin.sum_univ_four]
        rw [hterm, hterm, hterm, hterm]
      have hbij :
          ((Finset.univ : Finset (Fin 4)).sum fun t =>
            let v : Site := match t with
              | 0 => (r.val - 1, c.val)
              | 1 => (r.val + 1, c.val)
              | 2 => (r.val, c.val - 1)
              | 3 => (r.val, c.val + 1)
            if ((match t with
                | 0 => decide (0 < r.val)
                | 1 => decide (r.val + 1 < n)
                | 2 => decide (0 < c.val)
                | 3 => decide (c.val < 3)) &&
                adjInList w u v) = true then 1 else 0) =
          (Finset.filter (fun v => adjInList w u v = true) w.toFinset).card := by
        rw [Finset.card_eq_sum_ones]
        symm
        let idxFn : Site → Fin 4 := fun v =>
          if v.1 + 1 = r.val then (0 : Fin 4)
          else if v.1 = r.val + 1 then 1
          else if v.2 + 1 = c.val then 2
          else 3
        have hiteT : ∀ (P : Prop) [Decidable P] (a b : Fin 4), P → (if P then a else b) = a :=
          fun _ _ _ _ hP => by split_ifs; rfl
        have hiteF : ∀ (P : Prop) [Decidable P] (a b : Fin 4), ¬ P → (if P then a else b) = b :=
          fun _ _ _ _ hP => by split_ifs; rfl
        have hf0 : 0 < r.val → idxFn (r.val - 1, c.val) = 0 := fun h => by
          dsimp [idxFn]; rw [hiteT _ _ _ (by omega)]
        have hf1 : idxFn (r.val + 1, c.val) = 1 := by
          dsimp [idxFn]; rw [hiteF _ _ _ (by omega), hiteT _ _ _ rfl]
        have hf2 : 0 < c.val → idxFn (r.val, c.val - 1) = 2 := fun h => by
          dsimp [idxFn]; rw [hiteF _ _ _ (by omega), hiteF _ _ _ (by omega), hiteT _ _ _ (by omega)]
        have hf3 : idxFn (r.val, c.val + 1) = 3 := by
          dsimp [idxFn]; rw [hiteF _ _ _ (by omega), hiteF _ _ _ (by omega), hiteF _ _ _ (by omega)]
        have hidx_cases : ∀ v,
            (v = (r.val - 1, c.val) ∧ 0 < r.val ∨ v = (r.val + 1, c.val) ∧ r.val + 1 < n ∨
              v = (r.val, c.val - 1) ∧ 0 < c.val ∨ v = (r.val, c.val + 1) ∧ c.val < 3) →
            v = (r.val - 1, c.val) ∧ idxFn v = 0 ∨ v = (r.val + 1, c.val) ∧ idxFn v = 1 ∨
            v = (r.val, c.val - 1) ∧ idxFn v = 2 ∨ v = (r.val, c.val + 1) ∧ idxFn v = 3 := by
          rintro v (⟨rfl, h⟩ | ⟨rfl, _⟩ | ⟨rfl, h⟩ | ⟨rfl, _⟩)
          · exact Or.inl ⟨rfl, hf0 h⟩
          · exact Or.inr (Or.inl ⟨rfl, hf1⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, hf2 h⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨rfl, hf3⟩))
        refine Finset.sum_bij_ne_zero (fun v _ _ => idxFn v) ?_ ?_ ?_ ?_
        · intro v _ _; exact Finset.mem_univ _
        · intro v₁ hv₁ _ v₂ hv₂ _ heq
          simp only [Finset.mem_filter, List.mem_toFinset] at hv₁ hv₂
          rcases hidx_cases v₁ (hadj_in v₁ hv₁.2) with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ <;>
            rcases hidx_cases v₂ (hadj_in v₂ hv₂.2) with ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ <;>
            first | rfl | (exfalso; rw [e1, e2] at heq; exact absurd heq (by decide))
        · intro t _ ht
          have hpos : (match t with | 0 => 0 < r.val | 1 => r.val + 1 < n | 2 => 0 < c.val | 3 => c.val < 3) ∧
              adjInList w u (match t with
                | 0 => (r.val - 1, c.val)
                | 1 => (r.val + 1, c.val)
                | 2 => (r.val, c.val - 1)
                | 3 => (r.val, c.val + 1)) = true := by
            by_contra h
            fin_cases t <;>
              (dsimp at h ht; split_ifs at ht with hc
               · exact h (by simpa [Bool.and_eq_true, decide_eq_true_eq] using hc)
               · exact ht rfl)
          fin_cases t
          · refine ⟨(r.val - 1, c.val), by simp [Finset.mem_filter, List.mem_toFinset, (adjInList_mem hpos.2).2, hpos.2],
              by simp, hf0 hpos.1⟩
          · refine ⟨(r.val + 1, c.val), by simp [Finset.mem_filter, List.mem_toFinset, (adjInList_mem hpos.2).2, hpos.2],
              by simp, hf1⟩
          · refine ⟨(r.val, c.val - 1), by simp [Finset.mem_filter, List.mem_toFinset, (adjInList_mem hpos.2).2, hpos.2],
              by simp, hf2 hpos.1⟩
          · refine ⟨(r.val, c.val + 1), by simp [Finset.mem_filter, List.mem_toFinset, (adjInList_mem hpos.2).2, hpos.2],
              by simp, hf3⟩
        · intro v hv _
          simp only [Finset.mem_filter, List.mem_toFinset] at hv
          rcases hadj_in v hv.2 with ⟨rfl, h1⟩ | ⟨rfl, h2⟩ | ⟨rfl, h3⟩ | ⟨rfl, h4⟩
          · rw [hf0 h1]; simp [h1, hv.2]
          · rw [hf1]; simp [h2, hv.2]
          · rw [hf2 h3]; simp [h3, hv.2]
          · rw [hf3]; simp [h4, hv.2]
      rw [hcard_int, hbij]
      have hflt_eq : Finset.filter (fun v => adjInList w u v = true) w.toFinset =
          (if h1 : 0 < w.idxOf u then {w[w.idxOf u - 1]'(by have := List.idxOf_lt_length_of_mem hu; omega)} else ∅) ∪
          (if h2 : w.idxOf u + 1 < w.length then {w[w.idxOf u + 1]} else ∅) := by
        ext v
        simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_union]
        constructor
        · rintro ⟨_, hadj⟩
          rcases (adjInList_iff_pred_succ hnd hu).mp hadj with ⟨h1, rfl⟩ | ⟨h2, rfl⟩
          · left; simp [h1]
          · right; simp [h2]
        · rintro (hv | hv)
          · split_ifs at hv with h1
            · rw [Finset.mem_singleton] at hv
              subst hv
              exact ⟨List.getElem_mem _, (adjInList_iff_pred_succ hnd hu).mpr (Or.inl ⟨h1, rfl⟩)⟩
            · simp at hv
          · split_ifs at hv with h2
            · rw [Finset.mem_singleton] at hv
              subst hv
              exact ⟨List.getElem_mem _, (adjInList_iff_pred_succ hnd hu).mpr (Or.inr ⟨h2, rfl⟩)⟩
            · simp at hv
      rw [hflt_eq, Finset.card_union_of_disjoint]
      · split_ifs <;> simp
      · by_cases h1 : 0 < w.idxOf u <;> by_cases h2 : w.idxOf u + 1 < w.length <;> simp [h1, h2]
        exact hne_prev_next h1 h2
    have hk0 : 0 < w.idxOf u ↔ u ≠ (0, 0) := by
      have h0 : w.idxOf (0, 0) = 0 := by
        cases w with
        | nil => simp at hhead
        | cons a t =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst hhead
          exact List.idxOf_cons_self
      constructor
      · intro hp heq
        rw [heq] at hp
        omega
      · intro hne
        by_contra hle
        have hz : w.idxOf u = 0 := by omega
        have := List.getElem_idxOf (List.idxOf_lt_length_of_mem hu)
        cases w with
        | nil => simp at hhead
        | cons a t =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          simp only [hz] at this
          exact hne (this.symm.trans hhead)
    have hkn : w.idxOf u + 1 < w.length ↔ u ≠ (n - 1, 0) := by
      have hlast_idx : w.idxOf (n - 1, 0) + 1 = w.length := by
        have hlen_pos : 0 < w.length := List.length_pos_of_mem hn0_mem
        have hget : w[w.length - 1] = (n - 1, 0) := by
          have hne_w : w ≠ [] := List.ne_nil_of_length_pos hlen_pos
          rw [← List.getLast_eq_getElem hne_w]
          exact (List.getLast_eq_iff_getLast?_eq_some hne_w).mpr hlast
        have hidx_eq : w.idxOf (n - 1, 0) = w.length - 1 := by
          rw [← hget]
          exact hnd.idxOf_getElem (w.length - 1) (by omega)
        omega
      have hlt_len := List.idxOf_lt_length_of_mem hu
      constructor
      · intro hlt heq
        rw [heq] at hlt
        omega
      · intro hne
        by_contra hge
        have heq_len : w.idxOf u + 1 = w.length := by omega
        have heq_idx : w.idxOf u = w.idxOf (n - 1, 0) := by omega
        have := List.getElem_idxOf hlt_len
        have h2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hn0_mem)
        simp only [heq_idx] at this
        exact hne (this.symm.trans h2)
    rw [hcount4]
    have hhk0 : (if 0 < w.idxOf u then 1 else 0) = if u = (0, 0) then 0 else 1 := by
      by_cases h : u = (0, 0)
      · have h0 : ¬ 0 < w.idxOf u := mt hk0.mp (not_not.mpr h)
        simp only [h0, ↓reduceIte]; simp only [h, ↓reduceIte]
      · have h0 : 0 < w.idxOf u := hk0.mpr h
        simp only [h0, ↓reduceIte]; simp only [h, ↓reduceIte]
    have hhkn : (if w.idxOf u + 1 < w.length then 1 else 0) = if u = (n - 1, 0) then 0 else 1 := by
      by_cases h : u = (n - 1, 0)
      · have h0 : ¬ w.idxOf u + 1 < w.length := mt hkn.mp (not_not.mpr h)
        simp only [h0, ↓reduceIte]; simp only [h, ↓reduceIte]
      · have h0 : w.idxOf u + 1 < w.length := hkn.mpr h
        simp only [h0, ↓reduceIte]; simp only [h, ↓reduceIte]
    rw [hhk0, hhkn]
    by_cases h0 : u = (0, 0) <;> by_cases h1 : u = (n - 1, 0) <;>
      simp [h0, h1] <;>
      (dsimp [u] at h0 h1 ⊢; simp only [Prod.ext_iff] at h0 h1; split_ifs <;> omega)
  · simp only [hu, ↓reduceIte]
    have h00_mem : (0, 0) ∈ w := List.mem_of_head? hhead
    have hn0_mem : (n - 1, 0) ∈ w := List.mem_of_getLast? hlast
    have hne0 : u ≠ (0, 0) := fun heq => hu (heq ▸ h00_mem)
    have hnen : u ≠ (n - 1, 0) := fun heq => hu (heq ▸ hn0_mem)
    have hno : ∀ v, adjInList w u v = false := by
      intro v
      by_contra h
      rw [Bool.eq_true_eq_not_eq_false] at h
      exact hu (adjInList_mem (by simpa using h)).1
    simp [hne0, hnen, hno]

private lemma walk_eq_of_edges_eq {n : ℕ} (_hn : 1 ≤ n) {w₁ w₂ : List Site}
    (hw₁ : isWalk n 4 (0, 0) (n - 1, 0) w₁) (hw₂ : isWalk n 4 (0, 0) (n - 1, 0) w₂)
    (hh : ∀ r : Fin n, hFromWalk w₁ r.val = hFromWalk w₂ r.val)
    (hv : ∀ r : Fin (n + 1), vFromWalk w₁ n r.val = vFromWalk w₂ n r.val) :
    w₁ = w₂ := by
  have hadj_eq : ∀ u v : Site, adjInList w₁ u v = adjInList w₂ u v := by
    suffices hdir : ∀ {wa wb : List Site},
        isWalk n 4 (0, 0) (n - 1, 0) wa → isWalk n 4 (0, 0) (n - 1, 0) wb →
        (∀ r : Fin n, hFromWalk wa r.val = hFromWalk wb r.val) →
        (∀ r : Fin (n + 1), vFromWalk wa n r.val = vFromWalk wb n r.val) →
        ∀ u v : Site, adjInList wa u v = true → adjInList wb u v = true by
      intro u v
      apply Bool.eq_iff_iff.mpr
      exact ⟨hdir hw₁ hw₂ hh hv u v, hdir hw₂ hw₁ (fun r => (hh r).symm) (fun r => (hv r).symm) u v⟩
    intro wa wb hwa hwb hha hva u v hadj
    have hmem := adjInList_mem hadj
    have hu_bd := hwa.2.2.2.2 u hmem.1
    have hv_bd := hwa.2.2.2.2 v hmem.2
    have hch := adjInList_adjacent hwa.2.2.2.1 hadj
    rcases u with ⟨ur, uc⟩
    rcases v with ⟨vr, vc⟩
    dsimp only [adjacent, Nat.dist] at hch
    have hur : ur < n := hu_bd.1
    have huc : uc < 4 := hu_bd.2
    have hvr : vr < n := hv_bd.1
    have hvc : vc < 4 := hv_bd.2
    have hcases : (ur = vr ∧ ((uc + 1 = vc ∧ uc < 3) ∨ (vc + 1 = uc ∧ vc < 3))) ∨
        (uc = vc ∧ ((ur + 1 = vr ∧ ur + 1 < n) ∨ (vr + 1 = ur ∧ vr + 1 < n))) := by
      omega
    rcases hcases with ⟨rfl, ⟨rfl, hc3⟩ | ⟨rfl, hc3⟩⟩ | ⟨rfl, ⟨rfl, hrn⟩ | ⟨rfl, hrn⟩⟩
    · have h1 := congrFun (hha ⟨ur, hur⟩) ⟨uc, hc3⟩
      simpa [hFromWalk, hadj] using h1.symm
    · have h1 := congrFun (hha ⟨ur, hur⟩) ⟨vc, hc3⟩
      dsimp only [hFromWalk] at h1
      rw [adjInList_symm, ← h1, adjInList_symm]
      exact hadj
    · have hr0 : ur + 1 ≠ 0 := by omega
      have hrn' : ur + 1 ≠ n := by omega
      have h1 := congrFun (hva ⟨ur + 1, by omega⟩) ⟨uc, huc⟩
      simp only [vFromWalk, hr0, ↓reduceIte, hrn', Nat.add_sub_cancel] at h1
      simpa [hadj] using h1.symm
    · have hr0 : vr + 1 ≠ 0 := by omega
      have hrn' : vr + 1 ≠ n := by omega
      have h1 := congrFun (hva ⟨vr + 1, by omega⟩) ⟨uc, huc⟩
      simp only [vFromWalk, hr0, ↓reduceIte, hrn', Nat.add_sub_cancel] at h1
      rw [adjInList_symm, ← h1, adjInList_symm]
      exact hadj
  have hget : ∀ k : ℕ, w₁[k]? = w₂[k]? := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero =>
        have h1 : w₁ ≠ [] := by intro h0; have := hw₁.1; simp [h0] at this
        have h2 : w₂ ≠ [] := by intro h0; have := hw₂.1; simp [h0] at this
        cases w₁ with
        | nil => exact absurd rfl h1
        | cons x xs =>
          cases w₂ with
          | nil => exact absurd rfl h2
          | cons y ys => simpa using hw₁.1.trans hw₂.1.symm
      | succ k =>
        have hk := ih k (Nat.lt_succ_self k)
        cases h1 : w₁[k]? with
        | none =>
          rw [h1] at hk
          have hl1 : w₁.length ≤ k := List.getElem?_eq_none_iff.mp h1
          have hl2 : w₂.length ≤ k := List.getElem?_eq_none_iff.mp hk.symm
          rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
        | some u =>
          have hk2 : w₂[k]? = some u := hk.symm.trans h1
          have hkl1 : k < w₁.length := (List.getElem?_eq_some_iff.mp h1).choose
          have hkl2 : k < w₂.length := (List.getElem?_eq_some_iff.mp hk2).choose
          have hu1 : w₁[k] = u := (List.getElem?_eq_some_iff.mp h1).choose_spec
          have hu2 : w₂[k] = u := (List.getElem?_eq_some_iff.mp hk2).choose_spec
          have hu_mem1 : u ∈ w₁ := hu1 ▸ List.getElem_mem hkl1
          have hu_mem2 : u ∈ w₂ := hu2 ▸ List.getElem_mem hkl2
          by_cases he : u = (n - 1, 0)
          · have hlast1 : k + 1 = w₁.length := by
              have hne1 : w₁ ≠ [] := List.ne_nil_of_length_pos (by omega)
              have hgl : w₁[w₁.length - 1] = u := by
                rw [← List.getLast_eq_getElem hne1]
                exact ((List.getLast_eq_iff_getLast?_eq_some hne1).mpr hw₁.2.1).trans he.symm
              have hidx := (List.nodup_iff_injective_getElem.mp hw₁.2.2.1)
                (a₁ := ⟨w₁.length - 1, by omega⟩) (a₂ := ⟨k, hkl1⟩) (hgl.trans hu1.symm)
              have hv := congrArg Fin.val hidx
              dsimp at hv
              omega
            have hlast2 : k + 1 = w₂.length := by
              have hne2 : w₂ ≠ [] := List.ne_nil_of_length_pos (by omega)
              have hgl : w₂[w₂.length - 1] = u := by
                rw [← List.getLast_eq_getElem hne2]
                exact ((List.getLast_eq_iff_getLast?_eq_some hne2).mpr hw₂.2.1).trans he.symm
              have hidx := (List.nodup_iff_injective_getElem.mp hw₂.2.2.1)
                (a₁ := ⟨w₂.length - 1, by omega⟩) (a₂ := ⟨k, hkl2⟩) (hgl.trans hu2.symm)
              have hv := congrArg Fin.val hidx
              dsimp at hv
              omega
            rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
          · have hlast1 : k + 1 < w₁.length := by
              by_contra hge
              have hkl : k = w₁.length - 1 := by omega
              have hne1 : w₁ ≠ [] := List.ne_nil_of_length_pos (by omega)
              have hgl : w₁[w₁.length - 1] = (n - 1, 0) := by
                rw [← List.getLast_eq_getElem hne1]
                exact (List.getLast_eq_iff_getLast?_eq_some hne1).mpr hw₁.2.1
              simp only [← hkl, hu1] at hgl
              exact he hgl
            have hlast2 : k + 1 < w₂.length := by
              by_contra hge
              have hkl : k = w₂.length - 1 := by omega
              have hne2 : w₂ ≠ [] := List.ne_nil_of_length_pos (by omega)
              have hgl : w₂[w₂.length - 1] = (n - 1, 0) := by
                rw [← List.getLast_eq_getElem hne2]
                exact (List.getLast_eq_iff_getLast?_eq_some hne2).mpr hw₂.2.1
              simp only [← hkl, hu2] at hgl
              exact he hgl
            rw [List.getElem?_eq_some_iff.mpr ⟨hlast1, rfl⟩,
              List.getElem?_eq_some_iff.mpr ⟨hlast2, rfl⟩]
            congr 1
            have hidx1 : w₁.idxOf u = k := by
              rw [← hu1]
              exact hw₁.2.2.1.idxOf_getElem k hkl1
            have hadj2 : adjInList w₂ u w₂[k + 1] = true := by
              have hidx2 : w₂.idxOf u = k := by
                rw [← hu2]
                exact hw₂.2.2.1.idxOf_getElem k hkl2
              refine (adjInList_iff_pred_succ hw₂.2.2.1 hu_mem2).mpr (Or.inr ⟨by omega, by simp [hidx2]⟩)
            rw [← hadj_eq] at hadj2
            rcases (adjInList_iff_pred_succ hw₁.2.2.1 hu_mem1).mp hadj2 with ⟨hlt0, hprev⟩ | ⟨hlt1, hnext⟩
            · exfalso
              have hk0 : 0 < k := by omega
              have hprev1 := ih (k - 1) (by omega)
              have hpl1 : k - 1 < w₁.length := by omega
              have hpl2 : k - 1 < w₂.length := by omega
              rw [List.getElem?_eq_some_iff.mpr ⟨hpl1, rfl⟩,
                List.getElem?_eq_some_iff.mpr ⟨hpl2, rfl⟩] at hprev1
              have hpeq : w₁[k - 1] = w₂[k - 1] := Option.some.inj hprev1
              have hneq2 : w₂[k + 1] ≠ w₂[k - 1] := by
                intro heq
                have hidx := (List.nodup_iff_injective_getElem.mp hw₂.2.2.1)
                  (a₁ := ⟨k + 1, hlast2⟩) (a₂ := ⟨k - 1, hpl2⟩) heq
                have hv := congrArg Fin.val hidx
                dsimp at hv
                omega
              simp only [hidx1] at hprev
              exact hneq2 (hprev.trans hpeq)
            · simp only [hidx1] at hnext
              exact hnext.symm
  exact List.ext_getElem? hget

private lemma walkH_disjoint_of_noCycle {a b u v : Fin 4} {h : Fin 3 → Bool}
    (hne : a ≠ b) (hua : connH h u a = true) (hbv : connH h b v = true)
    (hnc : (!connH h a b) = true) : List.Disjoint (walkH u a) (walkH b v) := by
  rcases hBits_surj h with ⟨hk, rfl⟩
  have hdec : ((List.finRange 4).all fun a => (List.finRange 4).all fun b =>
      (List.finRange 4).all fun u => (List.finRange 4).all fun v =>
      (List.finRange 8).all fun hk =>
        !(a != b && connH (hBits hk) u a && connH (hBits hk) b v && (!connH (hBits hk) a b)) ||
          ((walkH u a).all fun x => !(walkH b v).elem x)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hdec
  have hrow := hdec a b u v hk
  have hne' : (a != b) = true := bne_iff_ne.mpr hne
  simp only [hne', hua, hbv, hnc, Bool.and_self, Bool.not_true, Bool.false_or,
    List.all_eq_true, Bool.not_eq_true', List.elem_eq_mem, decide_eq_false_iff_not] at hrow
  rw [List.disjoint_iff_ne]
  intro x hx y hy heq
  subst heq
  exact hrow x hx hy

private lemma isChain_append {α : Type*} {R : α → α → Prop} {l₁ l₂ : List α}
    (h₁ : l₁.IsChain R) (h₂ : l₂.IsChain R) (hne1 : l₁ ≠ []) (hne2 : l₂ ≠ [])
    (hjoin : R (l₁.getLast hne1) (l₂.head hne2)) : (l₁ ++ l₂).IsChain R := by
  induction l₁ with
  | nil => exact absurd rfl hne1
  | cons a t ih =>
    cases t with
    | nil =>
      cases l₂ with
      | nil => exact absurd rfl hne2
      | cons b s =>
        rw [List.singleton_append, List.isChain_cons_cons]
        exact ⟨hjoin, h₂⟩
    | cons c cs =>
      rw [List.cons_append, List.cons_append, List.isChain_cons_cons]
      have h₁' := List.isChain_cons_cons.mp h₁
      refine ⟨h₁'.1, ih h₁'.2 (List.cons_ne_nil c cs) ?_⟩
      simpa using hjoin

private lemma isChain_reverse {α : Type*} {R : α → α → Prop} (hsym : ∀ x y, R x y → R y x)
    {l : List α} (h : l.IsChain R) : l.reverse.IsChain R := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b cs =>
      rw [List.isChain_cons_cons] at h
      rw [List.reverse_cons]
      refine isChain_append (ih h.2) (by simp) (by simp) (by simp) ?_
      simp only [List.getLast_reverse, List.head_cons]
      exact hsym _ _ h.1

private lemma walkH_site_isChain_adj {w : List Site} (r : ℕ) {u v : Fin 4}
    (hc : connH (hFromWalk w r) u v = true) :
    ((walkH u v).map fun c : Fin 4 => (r, c.val)).IsChain
      (fun x y => adjInList w x y = true) := by
  rcases hBits_surj (hFromWalk w r) with ⟨hk, hhk⟩
  have hdec : ((List.finRange 4).all fun u => (List.finRange 4).all fun v =>
      (List.finRange 8).all fun hk =>
        !connH (hBits hk) u v ||
          ((walkH u v).zip (walkH u v).tail).all fun p =>
            (p.1.val + 1 == p.2.val && (if hlt : p.1.val < 3 then hBits hk ⟨p.1.val, hlt⟩ else false)) ||
            (p.2.val + 1 == p.1.val && (if hlt : p.2.val < 3 then hBits hk ⟨p.2.val, hlt⟩ else false))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true'] at hdec
  have hc' : connH (hBits hk) u v = true := by simpa [hhk] using hc
  rcases hdec u v hk with hbad | hedges
  · exact absurd hc' (Bool.eq_false_iff.mp hbad)
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_map] at hi
    rw [List.getElem_map, List.getElem_map]
    have hzip : ((walkH u v)[i], (walkH u v)[i + 1]) ∈ (walkH u v).zip (walkH u v).tail := by
      have hzip_len : ((walkH u v).zip (walkH u v).tail).length = (walkH u v).length - 1 := by
        simp [List.length_zip, List.length_tail]
      have hi' : i < ((walkH u v).zip (walkH u v).tail).length := by omega
      have hget : ((walkH u v).zip (walkH u v).tail)[i] = ((walkH u v)[i], (walkH u v)[i + 1]) := by
        simp [List.getElem_zip, List.getElem_tail]
      rw [← hget]
      exact List.getElem_mem hi'
    have hedges' := hedges _ hzip
    simp only [Bool.and_eq_true, beq_iff_eq] at hedges'
    rcases hedges' with ⟨hstep, hval⟩ | ⟨hstep, hval⟩
    · have hlt : (walkH u v)[i].val < 3 := by
        have := (walkH u v)[i + 1].isLt
        omega
      simp only [hlt, ↓reduceDIte] at hval
      rw [hhk] at hval
      simpa [hFromWalk, hstep] using hval
    · have hlt : (walkH u v)[i + 1].val < 3 := by
        have := (walkH u v)[i].isLt
        omega
      simp only [hlt, ↓reduceDIte] at hval
      rw [hhk] at hval
      rw [adjInList_symm]
      simpa [hFromWalk, hstep] using hval

private lemma walkH_site_isChain_adjacent (r : ℕ) (u v : Fin 4) :
    ((walkH u v).map fun c : Fin 4 => (r, c.val)).IsChain adjacent := by
  have hdec : ((List.finRange 4).all fun u => (List.finRange 4).all fun v =>
      ((walkH u v).zip (walkH u v).tail).all fun p =>
        Nat.dist p.1.val p.2.val == 1) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hdec
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [List.length_map] at hi
  rw [List.getElem_map, List.getElem_map]
  have hzip : ((walkH u v)[i], (walkH u v)[i + 1]) ∈ (walkH u v).zip (walkH u v).tail := by
    have hzip_len : ((walkH u v).zip (walkH u v).tail).length = (walkH u v).length - 1 := by
      simp [List.length_zip, List.length_tail]
    have hi' : i < ((walkH u v).zip (walkH u v).tail).length := by omega
    have hget : ((walkH u v).zip (walkH u v).tail)[i] = ((walkH u v)[i], (walkH u v)[i + 1]) := by
      simp [List.getElem_zip, List.getElem_tail]
    rw [← hget]
    exact List.getElem_mem hi'
  have hd := hdec u v _ hzip
  simp [adjacent, Nat.dist_self, hd]

private lemma walkH_site_nodup (r : ℕ) (u v : Fin 4) :
    ((walkH u v).map fun c : Fin 4 => (r, c.val)).Nodup := by
  refine List.Nodup.map ?_ (walkH_nodup u v)
  intro a b h
  exact Fin.ext (by simpa using h)

private lemma walkH_site_head (r : ℕ) (u v : Fin 4) :
    ((walkH u v).map fun c : Fin 4 => (r, c.val)).head? = some (r, u.val) := by
  simp [List.head?_map, walkH_head]

private lemma walkH_site_getLast (r : ℕ) (u v : Fin 4) :
    ((walkH u v).map fun c : Fin 4 => (r, c.val)).getLast? = some (r, v.val) := by
  simp [List.getLast?_map, walkH_getLast]

private lemma walkH_site_mem_row {r : ℕ} {u v : Fin 4} {p : Site}
    (hp : p ∈ (walkH u v).map fun c : Fin 4 => (r, c.val)) : p.1 = r ∧ p.2 < 4 := by
  rcases List.mem_map.mp hp with ⟨c, _, rfl⟩
  exact ⟨rfl, c.isLt⟩

private noncomputable def GridPath (n : ℕ) : Type :=
  {f : Fin (n + 1) → Fin 12 //
    f 0 = 0 ∧ f (Fin.last n) = 0 ∧ ∀ r : Fin n, Tmat (f r.castSucc) (f r.succ) = 1}

private noncomputable instance (n : ℕ) : Fintype (GridPath n) :=
  Subtype.fintype _

private def walkStateSeq (n : ℕ) (w : List Site) : ℕ → Fin 12
  | 0 => 0
  | r + 1 => nextState (walkStateSeq n w r) (hFromWalk w r) (vFromWalk w n (r + 1))

private lemma walkStateSeq_spec {n : ℕ} (hn : 1 ≤ n) {w : List Site}
    (hw : isWalk n 4 (0, 0) (n - 1, 0) w) :
    ∀ r : ℕ, r ≤ n →
      topMask (walkStateSeq n w r) = vFromWalk w n r ∧
      (∀ a b : Fin 4, statePair (walkStateSeq n w r) = some (a, b) →
        ∃ Q : List Site, Q.Nodup ∧ 2 ≤ Q.length ∧
          Q.head? = some (r - 1, a.val) ∧ Q.getLast? = some (r - 1, b.val) ∧
          Q.IsChain (fun u v => adjInList w u v = true) ∧ ∀ p ∈ Q, p.1 < r) ∧
      (r < n → validTrans (walkStateSeq n w r) (hFromWalk w r) (vFromWalk w n (r + 1))
        (walkStateSeq n w (r + 1)) = true) := by
  intro r hr
  induction r with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · ext c; fin_cases c <;> simp [walkStateSeq, vFromWalk, topMask, stateOp, statePair]
    · intro a b hab
      simp [walkStateSeq, statePair] at hab
    · intro h0
      have hdeg : degOK (walkStateSeq n w 0) (hFromWalk w 0) (vFromWalk w n 1) = true := by
        simp only [degOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
          beq_iff_eq]
        intro c
        have htop0 : topMask (walkStateSeq n w 0) = vFromWalk w n 0 := by
          ext c'
          fin_cases c' <;> simp [walkStateSeq, vFromWalk, topMask, stateOp, statePair]
        rw [htop0, deg_walk_eq hn hw ⟨0, h0⟩ c]
        split_ifs <;> simp
      have hnc : noCycle (walkStateSeq n w 0) (hFromWalk w 0) = true := by
        simp [walkStateSeq, noCycle, statePair]
      exact nextState_of_degOK_noCycle hdeg hnc
  | succ r ih =>
    rcases ih (Nat.le_of_lt hr) with ⟨htop_r, hQ_r, htrans_r⟩
    have hvt := htrans_r hr
    have htop_succ : topMask (walkStateSeq n w (r + 1)) = vFromWalk w n (r + 1) :=
      (validTrans_topMask_eq hvt).symm
    have hQ_succ : ∀ a' b' : Fin 4, statePair (walkStateSeq n w (r + 1)) = some (a', b') →
        ∃ Q' : List Site, Q'.Nodup ∧ 2 ≤ Q'.length ∧
          Q'.head? = some (r, a'.val) ∧ Q'.getLast? = some (r, b'.val) ∧
          Q'.IsChain (fun u v => adjInList w u v = true) ∧ ∀ p ∈ Q', p.1 < r + 1 := by
      intro a' b' hpair'
      have hvt' := hvt
      simp only [validTrans, Bool.and_eq_true, hpair'] at hvt'
      have hconn' : connRow (walkStateSeq n w r) (hFromWalk w r) a' b' = true := hvt'.2
      simp only [connRow, Bool.or_eq_true] at hconn'
      rcases hconn' with hdir | hvia
      · refine ⟨(walkH a' b').map fun c => (r, c.val), walkH_site_nodup r a' b', ?_,
          walkH_site_head r a' b', walkH_site_getLast r a' b',
          walkH_site_isChain_adj r hdir, fun p hp => ?_⟩
        · simp only [List.length_map]
          exact walkH_len_ge_two (Fin.ne_of_lt (statePair_lt hpair'))
        · exact (walkH_site_mem_row hp).1 ▸ Nat.lt_succ_self r
      · cases hpair : statePair (walkStateSeq n w r) with
        | none => simp [hpair] at hvia
        | some ab =>
          rcases ab with ⟨a, b⟩
          simp only [hpair, Bool.or_eq_true, Bool.and_eq_true] at hvia
          rcases hQ_r a b hpair with ⟨Q, hQnd, hQlen, hQh, hQl, hQch, hQrow⟩
          have hrpos : 1 ≤ r := by
            by_contra h0
            have hz : r = 0 := by omega
            subst hz
            exact statePair_ne_none_ne_zero hpair rfl
          have hva : adjInList w (r - 1, a.val) (r, a.val) = true := by
            have hta := (statePair_topMask hpair).1
            rw [htop_r] at hta
            have hrn : r ≠ n := by omega
            have hr0 : r ≠ 0 := by omega
            simpa [vFromWalk, hr0, hrn] using hta
          have hvb : adjInList w (r - 1, b.val) (r, b.val) = true := by
            have htb := (statePair_topMask hpair).2
            rw [htop_r] at htb
            have hrn : r ≠ n := by omega
            have hr0 : r ≠ 0 := by omega
            simpa [vFromWalk, hr0, hrn] using htb
          have hnc : (!connH (hFromWalk w r) a b) = true := by
            have hvt0 := hvt
            simp only [validTrans, Bool.and_eq_true, noCycle, hpair] at hvt0
            exact hvt0.1.1.1.2
          have hab_ne : a ≠ b := Fin.ne_of_lt (statePair_lt hpair)
          have hQne : Q ≠ [] := by intro h0; simp [h0] at hQlen
          rcases hvia with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · let S₁ := (walkH a' a).map fun c : Fin 4 => (r, c.val)
            let S₂ := (walkH b b').map fun c : Fin 4 => (r, c.val)
            have hdisj : List.Disjoint S₁ S₂ := by
              have hd := walkH_disjoint_of_noCycle (v := b') hab_ne h1
                (by simpa [connH, min_comm, max_comm] using h2) hnc
              rw [List.disjoint_iff_ne]
              intro x hx y hy heq
              subst heq
              rcases List.mem_map.mp hx with ⟨cx, hcx, hcx_eq⟩
              rcases List.mem_map.mp hy with ⟨cy, hcy, hcy_eq⟩
              have hceq : cx = cy := Fin.ext (by simpa using congrArg Prod.snd (hcx_eq.trans hcy_eq.symm))
              subst hceq
              exact (List.disjoint_iff_ne.mp hd) cx hcx cx hcy rfl
            have hS1ne : S₁ ≠ [] := by simp [S₁, walkH_nonempty]
            have hS2ne : S₂ ≠ [] := by simp [S₂, walkH_nonempty]
            have hQ_S1 : List.Disjoint Q S₁ := by
              rw [List.disjoint_iff_ne]
              intro x hx y hy heq
              subst heq
              have hx1 := hQrow x hx
              have hy1 := (walkH_site_mem_row hy).1
              omega
            have hQ_S2 : List.Disjoint Q S₂ := by
              rw [List.disjoint_iff_ne]
              intro x hx y hy heq
              subst heq
              have hx1 := hQrow x hx
              have hy1 := (walkH_site_mem_row hy).1
              omega
            refine ⟨S₁ ++ Q ++ S₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [List.nodup_append, List.nodup_append]
              refine ⟨⟨walkH_site_nodup r a' a, hQnd, List.disjoint_iff_ne.mp hQ_S1.symm⟩,
                walkH_site_nodup r b b', ?_⟩
              intro x hx y hy heq
              simp only [List.mem_append] at hx
              rcases hx with hx1 | hxQ
              · exact (List.disjoint_iff_ne.mp hdisj) x hx1 y hy heq
              · exact (List.disjoint_iff_ne.mp hQ_S2) x hxQ y hy heq
            · simp only [List.length_append]
              omega
            · rw [List.append_assoc, List.head?_append_of_ne_nil _ hS1ne]
              exact walkH_site_head r a' a
            · rw [List.getLast?_append_of_ne_nil _ hS2ne]
              exact walkH_site_getLast r b b'
            · refine isChain_append ?_ (walkH_site_isChain_adj r (by
                  simpa [connH, min_comm, max_comm] using h2)) (by simp [hQne]) hS2ne ?_
              · refine isChain_append (walkH_site_isChain_adj r h1) hQch hS1ne hQne ?_
                have hs1l : S₁.getLast hS1ne = (r, a.val) := by
                  rw [List.getLast_eq_iff_getLast?_eq_some]
                  exact walkH_site_getLast r a' a
                have hqh : Q.head hQne = (r - 1, a.val) := by
                  rw [List.head_eq_iff_head?_eq_some]
                  exact hQh
                rw [hs1l, hqh, adjInList_symm]
                exact hva
              · have hql : (S₁ ++ Q).getLast (by simp [hQne]) = (r - 1, b.val) := by
                  rw [List.getLast_append_of_ne_nil _ hQne, List.getLast_eq_iff_getLast?_eq_some]
                  exact hQl
                have hs2h : S₂.head hS2ne = (r, b.val) := by
                  rw [List.head_eq_iff_head?_eq_some]
                  exact walkH_site_head r b b'
                rw [hql, hs2h]
                exact hvb
            · intro p hp
              simp only [List.mem_append] at hp
              rcases hp with (hp1 | hpQ) | hp2
              · exact (walkH_site_mem_row hp1).1 ▸ Nat.lt_succ_self r
              · exact Nat.lt_succ_of_lt (hQrow p hpQ)
              · exact (walkH_site_mem_row hp2).1 ▸ Nat.lt_succ_self r
          · let S₁ := (walkH a' b).map fun c : Fin 4 => (r, c.val)
            let S₂ := (walkH a b').map fun c : Fin 4 => (r, c.val)
            have hdisj : List.Disjoint S₁ S₂ := by
              have hnc' : (!connH (hFromWalk w r) b a) = true := by
                simpa [connH, min_comm, max_comm] using hnc
              have hd := walkH_disjoint_of_noCycle (v := b') hab_ne.symm h1
                (by simpa [connH, min_comm, max_comm] using h2) hnc'
              rw [List.disjoint_iff_ne]
              intro x hx y hy heq
              subst heq
              rcases List.mem_map.mp hx with ⟨cx, hcx, hcx_eq⟩
              rcases List.mem_map.mp hy with ⟨cy, hcy, hcy_eq⟩
              have hceq : cx = cy := Fin.ext (by simpa using congrArg Prod.snd (hcx_eq.trans hcy_eq.symm))
              subst hceq
              exact (List.disjoint_iff_ne.mp hd) cx hcx cx hcy rfl
            have hS1ne : S₁ ≠ [] := by simp [S₁, walkH_nonempty]
            have hS2ne : S₂ ≠ [] := by simp [S₂, walkH_nonempty]
            have hQ_S1 : List.Disjoint Q.reverse S₁ := by
              rw [List.disjoint_iff_ne]
              intro x hx y hy heq
              subst heq
              have hx1 := hQrow x (List.mem_reverse.mp hx)
              have hy1 := (walkH_site_mem_row hy).1
              omega
            have hQ_S2 : List.Disjoint Q.reverse S₂ := by
              rw [List.disjoint_iff_ne]
              intro x hx y hy heq
              subst heq
              have hx1 := hQrow x (List.mem_reverse.mp hx)
              have hy1 := (walkH_site_mem_row hy).1
              omega
            refine ⟨S₁ ++ Q.reverse ++ S₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [List.nodup_append, List.nodup_append]
              refine ⟨⟨walkH_site_nodup r a' b, List.nodup_reverse.mpr hQnd,
                List.disjoint_iff_ne.mp hQ_S1.symm⟩, walkH_site_nodup r a b', ?_⟩
              intro x hx y hy heq
              simp only [List.mem_append] at hx
              rcases hx with hx1 | hxQ
              · exact (List.disjoint_iff_ne.mp hdisj) x hx1 y hy heq
              · exact (List.disjoint_iff_ne.mp hQ_S2) x hxQ y hy heq
            · simp only [List.length_append, List.length_reverse]
              omega
            · rw [List.append_assoc, List.head?_append_of_ne_nil _ hS1ne]
              exact walkH_site_head r a' b
            · rw [List.getLast?_append_of_ne_nil _ hS2ne]
              exact walkH_site_getLast r a b'
            · have hQr_ch : Q.reverse.IsChain (fun u v => adjInList w u v = true) :=
                isChain_reverse (fun _ _ h => by rwa [adjInList_symm]) hQch
              have hQrne : Q.reverse ≠ [] := by simp [hQne]
              refine isChain_append ?_ (walkH_site_isChain_adj r (by
                  simpa [connH, min_comm, max_comm] using h2)) (by simp [hQrne]) hS2ne ?_
              · refine isChain_append (walkH_site_isChain_adj r h1) hQr_ch hS1ne hQrne ?_
                have hs1l : S₁.getLast hS1ne = (r, b.val) := by
                  rw [List.getLast_eq_iff_getLast?_eq_some]
                  exact walkH_site_getLast r a' b
                have hqrh : Q.reverse.head hQrne = (r - 1, b.val) := by
                  rw [List.head_eq_iff_head?_eq_some]
                  simpa [List.head?_reverse] using hQl
                rw [hs1l, hqrh, adjInList_symm]
                exact hvb
              · have hqrl : (S₁ ++ Q.reverse).getLast (by simp [hQrne]) = (r - 1, a.val) := by
                  rw [List.getLast_append_of_ne_nil _ hQrne, List.getLast_eq_iff_getLast?_eq_some]
                  simpa [List.getLast?_reverse] using hQh
                have hs2h : S₂.head hS2ne = (r, a.val) := by
                  rw [List.head_eq_iff_head?_eq_some]
                  exact walkH_site_head r a b'
                rw [hqrl, hs2h]
                exact hva
            · intro p hp
              simp only [List.mem_append, List.mem_reverse] at hp
              rcases hp with (hp1 | hpQ) | hp2
              · exact (walkH_site_mem_row hp1).1 ▸ Nat.lt_succ_self r
              · exact Nat.lt_succ_of_lt (hQrow p hpQ)
              · exact (walkH_site_mem_row hp2).1 ▸ Nat.lt_succ_self r
    refine ⟨htop_succ, hQ_succ, ?_⟩
    intro hr1
    have hdeg : degOK (walkStateSeq n w (r + 1)) (hFromWalk w (r + 1))
        (vFromWalk w n (r + 1 + 1)) = true := by
      simp only [degOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
        beq_iff_eq]
      intro c
      rw [htop_succ, deg_walk_eq hn hw ⟨r + 1, hr1⟩ c]
      split_ifs <;> simp
    have hnc : noCycle (walkStateSeq n w (r + 1)) (hFromWalk w (r + 1)) = true := by
      cases hpair : statePair (walkStateSeq n w (r + 1)) with
      | none => simp [noCycle, hpair]
      | some ab =>
        rcases ab with ⟨a, b⟩
        simp only [noCycle, hpair, Bool.not_eq_true']
        by_contra hconn_eq
        have hconn : connH (hFromWalk w (r + 1)) a b = true := by
          simpa using hconn_eq
        rcases hQ_succ a b hpair with ⟨Q, hQnd, hQlen, hQh, hQl, hQch, hQrow⟩
        have hva : adjInList w (r, a.val) (r + 1, a.val) = true := by
          have hta := (statePair_topMask hpair).1
          rw [htop_succ] at hta
          have hrn : r + 1 ≠ n := by omega
          have hr0 : r + 1 ≠ 0 := by omega
          simpa [vFromWalk, hr0, hrn] using hta
        have hvb : adjInList w (r, b.val) (r + 1, b.val) = true := by
          have htb := (statePair_topMask hpair).2
          rw [htop_succ] at htb
          have hrn : r + 1 ≠ n := by omega
          have hr0 : r + 1 ≠ 0 := by omega
          simpa [vFromWalk, hr0, hrn] using htb
        let S := (walkH b a).map fun c : Fin 4 => (r + 1, c.val)
        have hSlen : 2 ≤ S.length := by
          simp only [S, List.length_map]
          exact walkH_len_ge_two (Fin.ne_of_lt (statePair_lt hpair)).symm
        have hSne : S ≠ [] := by intro h0; simp [h0] at hSlen
        have hQne : Q ≠ [] := by intro h0; simp [h0] at hQlen
        have hS_ch : S.IsChain (fun u v => adjInList w u v = true) :=
          walkH_site_isChain_adj (r + 1) (by simpa [connH, min_comm, max_comm] using hconn)
        let C := Q ++ S ++ [(r, a.val)]
        have hC_len : 4 ≤ C.length := by
          simp only [C, List.length_append, List.length_singleton]
          omega
        have hC_hc : C.head? = C.getLast? := by
          have h1 : C.head? = Q.head? := by
            cases Q with
            | nil => simp at hQne
            | cons x xs => simp [C]
          have h2 : C.getLast? = some (r, a.val) := by
            simp [C]
          rw [h1, h2, hQh]
        have hQ_S : List.Disjoint Q S := by
          rw [List.disjoint_iff_ne]
          intro x hx y hy heq
          subst heq
          have hx1 := hQrow x hx
          have hy1 := (walkH_site_mem_row hy).1
          omega
        have hC_nd : C.tail.Nodup := by
          cases Q with
          | nil => simp at hQne
          | cons q0 qt =>
            have hq0_eq : q0 = (r, a.val) := by
              simpa using hQh
            have hqt_nd : qt.Nodup := (List.nodup_cons.mp hQnd).2
            have hq0_notin_qt : q0 ∉ qt := (List.nodup_cons.mp hQnd).1
            have hq0_notin_S : q0 ∉ S := fun hm => by
              have := (walkH_site_mem_row hm).1
              rw [hq0_eq] at this
              simp at this
            have hqt_S : List.Disjoint qt S :=
              List.disjoint_of_subset_left (List.subset_cons_self q0 qt) hQ_S
            simp only [C, List.cons_append, List.tail_cons, List.nodup_append]
            refine ⟨⟨hqt_nd, walkH_site_nodup (r + 1) b a, List.disjoint_iff_ne.mp hqt_S⟩,
              List.nodup_singleton _, ?_⟩
            intro x hx y hy heq
            rw [List.mem_singleton] at hy
            subst hy
            subst heq
            simp only [List.mem_append] at hx
            rcases hx with hxq | hxS
            · exact absurd (hq0_eq ▸ hxq) hq0_notin_qt
            · exact absurd (hq0_eq ▸ hxS) hq0_notin_S
        have hC_ch : C.IsChain (fun u v => adjInList w u v = true) := by
          refine isChain_append ?_ (by simp) (by simp [hSne]) (by simp) ?_
          · refine isChain_append hQch hS_ch hQne hSne ?_
            have hql : Q.getLast hQne = (r, b.val) := by
              rw [List.getLast_eq_iff_getLast?_eq_some]
              exact hQl
            have hsh : S.head hSne = (r + 1, b.val) := by
              rw [List.head_eq_iff_head?_eq_some]
              exact walkH_site_head (r + 1) b a
            rw [hql, hsh]
            exact hvb
          · have hsl : (Q ++ S).getLast (by simp [hSne]) = (r + 1, a.val) := by
              rw [List.getLast_append_of_ne_nil _ hSne, List.getLast_eq_iff_getLast?_eq_some]
              exact walkH_site_getLast (r + 1) b a
            rw [hsl, List.head_singleton, adjInList_symm]
            exact hva
        exact no_cycle_adjInList hw.2.2.1 hC_len hC_hc hC_nd hC_ch
    exact nextState_of_degOK_noCycle hdeg hnc

private def adjHList (l : List (Fin 4)) (c : Fin 3) : Bool :=
  (l.zip l.tail).any fun p =>
    (p.1.val == c.val && p.2.val == c.val + 1) || (p.1.val == c.val + 1 && p.2.val == c.val)

private lemma adjInList_map_row (l : List (Fin 4)) (r : ℕ) (c : Fin 3) :
    adjInList (l.map fun x => (r, x.val)) (r, c.val) (r, c.val + 1) = adjHList l c := by
  induction l with
  | nil => simp [adjInList, adjHList]
  | cons a t ih =>
    cases t with
    | nil => simp [adjInList, adjHList]
    | cons b bs =>
      have heq1 : ∀ x y : ℕ, ((r, x) == (r, y)) = (x == y) := fun x y => by
        by_cases h : x = y <;> simp [h]
      simp only [List.map_cons, adjInList, List.tail_cons, List.zip_cons_cons, List.any_cons,
        adjHList, heq1] at ih ⊢
      rw [ih]

private lemma adjInList_map_row_mem {l : List (Fin 4)} {r : ℕ} {u v : Site}
    (h : adjInList (l.map fun x => (r, x.val)) u v = true) :
    u.1 = r ∧ v.1 = r := by
  have hm := adjInList_mem h
  rcases List.mem_map.mp hm.1 with ⟨_, _, rfl⟩
  rcases List.mem_map.mp hm.2 with ⟨_, _, rfl⟩
  exact ⟨rfl, rfl⟩

private lemma statePair_disjoint {s : Fin 12} {a b : Fin 4} (h : statePair s = some (a, b)) :
    a ≠ b ∧ a ≠ stateOp s ∧ b ≠ stateOp s := by
  fin_cases s <;> simp [statePair] at h <;> rcases h with ⟨rfl, rfl⟩ <;> decide

private def stepPaths (r : ℕ) (s t : Fin 12) (P Q : List Site) : List Site × List Site :=
  let h := transH s t
  let rLift : Fin 4 → Site := fun c => (r, c.val)
  match statePair s with
  | none =>
    let P' := P ++ (walkH (stateOp s) (stateOp t)).map rLift
    let Q' := match statePair t with
      | none => []
      | some (a', b') => (walkH a' b').map rLift
    (P', Q')
  | some (a, b) =>
    if connH h (stateOp s) (stateOp t) then
      let P' := P ++ (walkH (stateOp s) (stateOp t)).map rLift
      let Q' := match statePair t with
        | none => []
        | some (a', b') =>
          if connH h a' a && connH h b b' then
            (walkH a' a).map rLift ++ Q ++ (walkH b b').map rLift
          else
            (walkH a' b).map rLift ++ Q.reverse ++ (walkH a b').map rLift
      (P', Q')
    else
      let P' :=
        if connH h (stateOp s) a && connH h b (stateOp t) then
          P ++ (walkH (stateOp s) a).map rLift ++ Q ++ (walkH b (stateOp t)).map rLift
        else
          P ++ (walkH (stateOp s) b).map rLift ++ Q.reverse ++ (walkH a (stateOp t)).map rLift
      let Q' := match statePair t with
        | none => []
        | some (a', b') => (walkH a' b').map rLift
      (P', Q')

private def rowSegmentsCheck (s t : Fin 12) : Bool :=
  let h := transH s t
  match statePair s with
  | none =>
    let segP := walkH (stateOp s) (stateOp t)
    let segQ := match statePair t with | none => [] | some (a', b') => walkH a' b'
    let okQ := match statePair t with | none => true | some (a', b') => a' != b' && (2 ≤ segQ.length)
    okQ && (segP ++ segQ).Nodup &&
      ((List.finRange 3).all fun c => (adjHList segP c || adjHList segQ c) == h c)
  | some (a, b) =>
    if connH h (stateOp s) (stateOp t) then
      match statePair t with
      | none => false
      | some (a', b') =>
        let segP := walkH (stateOp s) (stateOp t)
        if connH h a' a && connH h b b' then
          let seg1 := walkH a' a
          let seg2 := walkH b b'
          (a' != b') && (segP ++ seg1 ++ seg2).Nodup &&
            ((List.finRange 3).all fun c => (adjHList segP c || adjHList seg1 c || adjHList seg2 c) == h c)
        else
          (connH h a' b && connH h a b') && (a' != b') &&
            let seg1 := walkH a' b
            let seg2 := walkH a b'
            (segP ++ seg1 ++ seg2).Nodup &&
              ((List.finRange 3).all fun c => (adjHList segP c || adjHList seg1 c || adjHList seg2 c) == h c)
    else
      let segQ := match statePair t with | none => [] | some (a', b') => walkH a' b'
      let okQ := match statePair t with | none => true | some (a', b') => a' != b' && (2 ≤ segQ.length)
      if connH h (stateOp s) a && connH h b (stateOp t) then
        let seg1 := walkH (stateOp s) a
        let seg2 := walkH b (stateOp t)
        okQ && (seg1 ++ seg2 ++ segQ).Nodup &&
          ((List.finRange 3).all fun c => (adjHList seg1 c || adjHList seg2 c || adjHList segQ c) == h c)
      else
        (connH h (stateOp s) b && connH h a (stateOp t)) &&
          let seg1 := walkH (stateOp s) b
          let seg2 := walkH a (stateOp t)
          okQ && (seg1 ++ seg2 ++ segQ).Nodup &&
            ((List.finRange 3).all fun c => (adjHList seg1 c || adjHList seg2 c || adjHList segQ c) == h c)

private lemma rowSegmentsCheck_all :
    ((List.finRange 12).all fun s =>
      (List.finRange 12).all fun t =>
        !(Tmat s t == 1) || rowSegmentsCheck s t) = true := by
  decide

private lemma rowSegmentsCheck_of_Tmat {s t : Fin 12} (ht : Tmat s t = 1) :
    rowSegmentsCheck s t = true := by
  have hc := rowSegmentsCheck_all
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
  have hok := hc s t
  simp [ht] at hok
  exact hok

private lemma nodup_map_row {r : ℕ} {l : List (Fin 4)} (h : l.Nodup) :
    (l.map fun c : Fin 4 => (r, c.val)).Nodup := by
  refine List.Nodup.map ?_ h
  intro a b heq
  exact Fin.ext (by simpa using heq)

private lemma disjoint_map_row {r : ℕ} {l₁ l₂ : List (Fin 4)} (h : List.Disjoint l₁ l₂) :
    List.Disjoint (l₁.map fun c : Fin 4 => (r, c.val)) (l₂.map fun c : Fin 4 => (r, c.val)) := by
  rw [List.disjoint_iff_ne]
  intro x hx y hy heq
  subst heq
  rcases List.mem_map.mp hx with ⟨a, ha, ha_eq⟩
  rcases List.mem_map.mp hy with ⟨b, hb, hb_eq⟩
  have hab : a = b := Fin.ext (by simpa using congrArg Prod.snd (ha_eq.trans hb_eq.symm))
  subst hab
  exact (List.disjoint_iff_ne.mp h) a ha a hb rfl

private lemma nodup_append_three_disj {α : Type*} {l₁ l₂ l₃ : List α}
    (h : (l₁ ++ l₂ ++ l₃).Nodup) :
    l₁.Nodup ∧ l₂.Nodup ∧ l₃.Nodup ∧ List.Disjoint l₁ l₂ ∧ List.Disjoint l₁ l₃ ∧ List.Disjoint l₂ l₃ := by
  rw [List.nodup_append, List.nodup_append] at h
  rcases h with ⟨⟨h1, h2, h12⟩, h3, h123⟩
  have h12' : List.Disjoint l₁ l₂ := List.disjoint_iff_ne.mpr h12
  have h123' : List.Disjoint (l₁ ++ l₂) l₃ := List.disjoint_iff_ne.mpr h123
  have h13 : List.Disjoint l₁ l₃ := List.disjoint_of_subset_left (List.subset_append_left l₁ l₂) h123'
  have h23 : List.Disjoint l₂ l₃ := List.disjoint_of_subset_left (List.subset_append_right l₁ l₂) h123'
  exact ⟨h1, h2, h3, h12', h13, h23⟩

private def buildPaths {n : ℕ} (f : Fin (n + 1) → Fin 12) : ∀ r : ℕ, r ≤ n → List Site × List Site
  | 0, _ => ([], [])
  | r + 1, hr =>
    let pq := buildPaths f r (Nat.le_of_lt hr)
    stepPaths r (f ⟨r, Nat.lt_succ_of_lt hr⟩) (f ⟨r + 1, Nat.succ_lt_succ hr⟩) pq.1 pq.2

private lemma disjoint_lt_row {m : ℕ} (l₁ : List Site) (l₂ : List (Fin 4))
    (hl₁ : ∀ p ∈ l₁, p.1 < m ∧ p.2 < 4) :
    List.Disjoint l₁ (l₂.map fun c : Fin 4 => (m, c.val)) := by
  rw [List.disjoint_iff_ne]
  intro x hx y hy heq
  subst heq
  have hx1 := (hl₁ x hx).1
  rcases List.mem_map.mp hy with ⟨cy, _, hcy⟩
  have hy1 : x.1 = m := congrArg Prod.fst hcy.symm
  omega

private lemma adjInList_map_row_lt {m : ℕ} {l : List (Fin 4)} {u v : Site}
    (hu : u.1 < m) :
    adjInList (l.map fun c : Fin 4 => (m, c.val)) u v = false := by
  by_contra htrue
  rw [Bool.eq_true_eq_not_eq_false] at htrue
  have h1 := (adjInList_map_row_mem (by simpa using htrue)).1
  omega

private lemma adjInList_lt_at_row {m : ℕ} {l : List Site} {c : Fin 3}
    (hl : ∀ p ∈ l, p.1 < m ∧ p.2 < 4) :
    adjInList l (m, c.val) (m, c.val + 1) = false := by
  by_contra htrue
  rw [Bool.eq_true_eq_not_eq_false] at htrue
  have hm1 := (hl _ (adjInList_mem (by simpa using htrue)).1).1
  omega

private lemma adjInList_vert_map_row {m r' : ℕ} {l : List (Fin 4)} {c : Fin 4} :
    adjInList (l.map fun c : Fin 4 => (m + 1, c.val)) (r' - 1, c.val) (r', c.val) = false := by
  by_contra htrue
  rw [Bool.eq_true_eq_not_eq_false] at htrue
  have hm := adjInList_map_row_mem (by simpa using htrue)
  omega

private lemma adjInList_vert_map_row_succ {m : ℕ} {l : List (Fin 4)} {c : Fin 4} :
    adjInList (l.map fun c : Fin 4 => (m + 1, c.val)) (m, c.val) (m + 1, c.val) = false := by
  have h := adjInList_vert_map_row (m := m) (r' := m + 1) (l := l) (c := c)
  rwa [Nat.add_sub_cancel] at h

private lemma adjInList_vert_lt_in {m : ℕ} {l : List Site} {c : Fin 4}
    (hl : ∀ p ∈ l, p.1 < m + 1 ∧ p.2 < 4) :
    adjInList l (m, c.val) (m + 1, c.val) = false := by
  by_contra htrue
  rw [Bool.eq_true_eq_not_eq_false] at htrue
  have hm := (hl _ (adjInList_mem (by simpa using htrue)).2).1
  omega

private lemma adjInList_nil_false (u v : Site) : adjInList [] u v = false := rfl

private lemma siteOpt_beq_same (m x y : ℕ) :
    (some (m, x) == some (m, y)) = (x == y) := by
  by_cases h : x = y <;> simp [h, beq_false_of_ne]

private lemma siteOpt_beq_diff {m₁ m₂ : ℕ} (h : m₁ ≠ m₂) (x y : ℕ) :
    (some (m₁, x) == some (m₂, y)) = false :=
  beq_false_of_ne (by simp [h])

private lemma fin_val_beq_decide (a c : Fin 4) : (a.val == c.val) = decide (c = a) := by
  by_cases h : c = a
  · subst h; simp
  · have hne : a.val ≠ c.val := fun e => h (Fin.ext e.symm)
    rw [beq_false_of_ne hne, decide_eq_false h]

private lemma fin_beq_decide (a c : Fin 4) : (c == a) = decide (c = a) := by
  by_cases h : c = a
  · subst h; simp
  · rw [beq_false_of_ne h, decide_eq_false h]

private def PathInv {n : ℕ} (f : Fin (n + 1) → Fin 12) (r : ℕ) (hr : r ≤ n)
    (P Q : List Site) : Prop :=
  let s := f ⟨r, Nat.lt_succ_of_le hr⟩
  P ≠ [] ∧ P.head? = some (0, 0) ∧ P.getLast? = some (r - 1, (stateOp s).val) ∧
  P.Nodup ∧ P.IsChain adjacent ∧ List.Disjoint P Q ∧
  (∀ p ∈ P, p.1 < r ∧ p.2 < 4) ∧ (∀ p ∈ Q, p.1 < r ∧ p.2 < 4) ∧
  (statePair s = none → Q = []) ∧
  (∀ a b, statePair s = some (a, b) →
    Q ≠ [] ∧ Q.head? = some (r - 1, a.val) ∧ Q.getLast? = some (r - 1, b.val) ∧
    Q.Nodup ∧ Q.IsChain adjacent) ∧
  (∀ r' : ℕ, ∀ hr' : r' < r, ∀ c : Fin 3,
    (adjInList P (r', c.val) (r', c.val + 1) || adjInList Q (r', c.val) (r', c.val + 1)) =
      transH (f ⟨r', Nat.lt_succ_of_lt (lt_of_lt_of_le hr' hr)⟩)
             (f ⟨r' + 1, Nat.succ_lt_succ (lt_of_lt_of_le hr' hr)⟩) c) ∧
  (∀ r' : ℕ, 0 < r' → ∀ hr' : r' < r, ∀ c : Fin 4,
    (adjInList P (r' - 1, c.val) (r', c.val) || adjInList Q (r' - 1, c.val) (r', c.val)) =
      topMask (f ⟨r', Nat.lt_succ_of_lt (lt_of_lt_of_le hr' hr)⟩) c)

private lemma stepPaths_zero {n : ℕ} {f : Fin (n + 1) → Fin 12}
    (hf0 : f 0 = 0) (hfT : ∀ r : Fin n, Tmat (f r.castSucc) (f r.succ) = 1)
    (hr : 1 ≤ n) :
    PathInv f 1 hr
      (stepPaths 0 (f ⟨0, Nat.lt_succ_of_lt hr⟩) (f ⟨1, Nat.succ_lt_succ hr⟩)
        (buildPaths f 0 (Nat.le_of_lt hr)).1 (buildPaths f 0 (Nat.le_of_lt hr)).2).1
      (stepPaths 0 (f ⟨0, Nat.lt_succ_of_lt hr⟩) (f ⟨1, Nat.succ_lt_succ hr⟩)
        (buildPaths f 0 (Nat.le_of_lt hr)).1 (buildPaths f 0 (Nat.le_of_lt hr)).2).2 := by
  dsimp only [PathInv]
  let t := f ⟨1, Nat.succ_lt_succ hr⟩
  have hs0 : f ⟨0, Nat.lt_succ_of_lt hr⟩ = 0 := hf0
  have hs_any : ∀ h', f ⟨0, h'⟩ = 0 := fun _ => hf0
  have ht_any : ∀ h', f ⟨1, h'⟩ = t := fun _ => rfl
  have hT : Tmat 0 t = 1 := by simpa [hf0] using hfT ⟨0, hr⟩
  have hchk := rowSegmentsCheck_of_Tmat hT
  have hp0 : statePair 0 = none := rfl
  have ho0 : stateOp 0 = 0 := rfl
  have hbp0 : (buildPaths f 0 (Nat.le_of_lt hr)).1 = [] := rfl
  dsimp only [stepPaths]
  rw [hbp0, List.nil_append, hs0, ht_any]
  simp only [hp0, ho0]
  simp only [rowSegmentsCheck, hp0, ho0] at hchk
  let segP := (walkH 0 (stateOp t)).map fun c : Fin 4 => (0, c.val)
  have hPne : segP ≠ [] := by simp [segP, walkH_nonempty]
  have hPh : segP.head? = some (0, 0) := walkH_site_head 0 0 (stateOp t)
  have hPl : segP.getLast? = some (0, (stateOp t).val) := walkH_site_getLast 0 0 (stateOp t)
  have hPnd : segP.Nodup := walkH_site_nodup 0 0 (stateOp t)
  have hPch : segP.IsChain adjacent := walkH_site_isChain_adjacent 0 0 (stateOp t)
  cases hpt : statePair t with
  | none =>
    simp only [hpt, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
      beq_iff_eq, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨_, hnd⟩, hadj⟩
    refine ⟨hPne, hPh, hPl, hPnd, hPch, by simp,
      fun p hp => by have := walkH_site_mem_row hp; exact ⟨by omega, this.2⟩,
      by simp, fun _ => by simp, fun a b hab => by simp at hab, ?_, ?_⟩
    · intro r' hr' c
      have hr'0 : r' = 0 := by omega
      subst hr'0
      rw [hs_any, ht_any, adjInList_nil_false, Bool.or_false]
      have hsub : adjHList [] c = false := rfl
      simpa [segP, adjInList_map_row, hsub] using hadj c
    · intro r' hr0 hr1'
      omega
  | some ab =>
    rcases ab with ⟨a', b'⟩
    simp only [hpt, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
      beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨⟨_, hlenQ⟩, hnd_app⟩, hadj⟩
    rw [List.nodup_append] at hnd_app
    rcases hnd_app with ⟨hndP, hndQ, hdisj⟩
    let segQ := (walkH a' b').map fun c : Fin 4 => (0, c.val)
    have hQne : segQ ≠ [] := by simp [segQ, walkH_nonempty]
    refine ⟨hPne, hPh, hPl, hPnd, hPch, disjoint_map_row (List.disjoint_iff_ne.mpr hdisj),
      fun p hp => by have := walkH_site_mem_row hp; exact ⟨by omega, this.2⟩,
      fun p hp => by have := walkH_site_mem_row hp; exact ⟨by omega, this.2⟩,
      fun hnone => by simp at hnone, ?_, ?_, ?_⟩
    · intro a'' b'' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact ⟨hQne, walkH_site_head 0 a' b', walkH_site_getLast 0 a' b',
        walkH_site_nodup 0 a' b', walkH_site_isChain_adjacent 0 a' b'⟩
    · intro r' hr' c
      have hr'0 : r' = 0 := by omega
      subst hr'0
      rw [hs_any, ht_any]
      simpa [segP, segQ, adjInList_map_row] using hadj c
    · intro r' hr0 hr1'
      omega

private lemma stepPaths_succ_none {n m : ℕ} {f : Fin (n + 1) → Fin 12}
    (hr : m + 1 + 1 ≤ n) {P Q : List Site} {s t : Fin 12}
    (hs : f ⟨m + 1, Nat.lt_succ_of_lt hr⟩ = s)
    (ht : f ⟨m + 1 + 1, Nat.succ_lt_succ hr⟩ = t)
    (hchk : rowSegmentsCheck s t = true)
    (hps : statePair s = none)
    (hinv : PathInv f (m + 1) (Nat.le_of_lt hr) P Q) :
    PathInv f (m + 1 + 1) hr
      (P ++ (walkH (stateOp s) (stateOp t)).map fun c : Fin 4 => (m + 1, c.val))
      (match statePair t with
       | none => []
       | some (a', b') => (walkH a' b').map fun c : Fin 4 => (m + 1, c.val)) := by
  dsimp only [PathInv] at hinv ⊢
  have hs_any : ∀ h', f ⟨m + 1, h'⟩ = s := fun _ => hs
  have ht_any : ∀ h', f ⟨m + 1 + 1, h'⟩ = t := fun _ => ht
  rcases hinv with ⟨hPne, hPh, hPl, hPnd, hPch, _, hProw, _, hQnone, _, hH_ih, hV_ih⟩
  rw [hs_any] at hPl hQnone
  simp only [Nat.add_sub_cancel] at hPl
  have hQempty : Q = [] := hQnone hps
  simp only [rowSegmentsCheck, hps] at hchk
  let S₁ := (walkH (stateOp s) (stateOp t)).map fun c : Fin 4 => (m + 1, c.val)
  have hS1ne : S₁ ≠ [] := by simp [S₁, walkH_nonempty]
  have hP_S1 : List.Disjoint P S₁ := disjoint_lt_row P _ hProw
  have hPl' : P.getLast hPne = (m, (stateOp s).val) := by
    rw [List.getLast_eq_iff_getLast?_eq_some]; exact hPl
  have hS1h' : S₁.head hS1ne = (m + 1, (stateOp s).val) := by
    rw [List.head_eq_iff_head?_eq_some]; exact walkH_site_head (m + 1) (stateOp s) (stateOp t)
  have hP'ne : P ++ S₁ ≠ [] := fun h => hPne (List.append_eq_nil_iff.mp h).1
  have hP'h : (P ++ S₁).head? = some (0, 0) := by
    rw [List.head?_append_of_ne_nil _ hPne]; exact hPh
  have hP'l : (P ++ S₁).getLast? = some (m + 1, (stateOp t).val) := by
    rw [List.getLast?_append_of_ne_nil _ hS1ne]; exact walkH_site_getLast (m + 1) (stateOp s) (stateOp t)
  have hP'nd : (P ++ S₁).Nodup := by
    rw [List.nodup_append]
    exact ⟨hPnd, walkH_site_nodup (m + 1) (stateOp s) (stateOp t), List.disjoint_iff_ne.mp hP_S1⟩
  have hP'ch : (P ++ S₁).IsChain adjacent := by
    refine isChain_append hPch (walkH_site_isChain_adjacent (m + 1) (stateOp s) (stateOp t)) hPne hS1ne ?_
    rw [hPl', hS1h']; dsimp only [adjacent, Nat.dist]; omega
  have hP'row : ∀ p ∈ P ++ S₁, p.1 < m + 2 ∧ p.2 < 4 := by
    intro p hp
    rcases List.mem_append.mp hp with hpP | hpS
    · have := hProw p hpP; exact ⟨by omega, this.2⟩
    · have := walkH_site_mem_row hpS; exact ⟨by omega, this.2⟩
  rw [ht_any]
  simp only [Nat.add_sub_cancel]
  cases hpt : statePair t with
  | none =>
    simp only [hpt, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
      beq_iff_eq, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨_, hnd⟩, hadj⟩
    refine ⟨hP'ne, hP'h, hP'l, hP'nd, hP'ch, by simp, hP'row, by simp,
      fun _ => by simp, fun a b hab => by simp at hab, ?_, ?_⟩
    · intro r' hr' c
      rw [adjInList_append hPne hS1ne, adjInList_nil_false, Bool.or_false]
      by_cases hrm : r' = m + 1
      · subst hrm
        rw [hs_any, ht_any]
        have hP0 := adjInList_lt_at_row (c := c) hProw
        have hjoin0 : (P.getLast? == some (m + 1, c.val) && S₁.head? == some (m + 1, c.val + 1)) = false ∧
            (P.getLast? == some (m + 1, c.val + 1) && S₁.head? == some (m + 1, c.val)) = false := by
          rw [hPl]
          simp only [siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)), Bool.false_and, and_self]
        have hS1adj := adjInList_map_row (walkH (stateOp s) (stateOp t)) (m + 1) c
        have hadjc := hadj c
        have hsub : adjHList [] c = false := rfl
        rw [hP0, hjoin0.1, hjoin0.2, hS1adj]
        simpa [Bool.false_or, Bool.or_false, hsub] using hadjc
      · have hr'm : r' < m + 1 := by omega
        have hih := hH_ih r' hr'm c
        rw [hQempty, adjInList_nil_false, Bool.or_false] at hih
        have hS10 : adjInList S₁ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hjoin0 : (P.getLast? == some (r', c.val) && S₁.head? == some (r', c.val + 1)) = false ∧
            (P.getLast? == some (r', c.val + 1) && S₁.head? == some (r', c.val)) = false := by
          rw [walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'), Bool.and_false, and_self]
        rw [hS10, hjoin0.1, hjoin0.2]
        simp only [Bool.or_false]
        exact hih
    · intro r' hr0 hr' c
      rw [adjInList_append hPne hS1ne, adjInList_nil_false, Bool.or_false]
      by_cases hrm : r' = m + 1
      · subst hrm
        rw [hs_any, Nat.add_sub_cancel]
        have hP0 := adjInList_vert_lt_in (c := c) hProw
        have hS10 : adjInList S₁ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        rw [hP0, hS10, hPl, walkH_site_head]
        simp only [topMask, hps, Bool.false_or, siteOpt_beq_same,
          siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)),
          siteOpt_beq_diff (Nat.ne_of_gt (Nat.lt_succ_self m)),
          Bool.or_false, Bool.and_self, fin_val_beq_decide, fin_beq_decide]
      · have hr'm : r' < m + 1 := by omega
        have hih := hV_ih r' hr0 hr'm c
        rw [hQempty, adjInList_nil_false, Bool.or_false] at hih
        have hS10 : adjInList S₁ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hjoin0 : (P.getLast? == some (r' - 1, c.val) && S₁.head? == some (r', c.val)) = false ∧
            (P.getLast? == some (r', c.val) && S₁.head? == some (r' - 1, c.val)) = false := by
          rw [walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'),
            siteOpt_beq_diff (by omega : m + 1 ≠ r' - 1), Bool.and_false, and_self]
        rw [hS10, hjoin0.1, hjoin0.2]
        simp only [Bool.or_false]
        exact hih
  | some ab =>
    rcases ab with ⟨a', b'⟩
    simp only [hpt, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
      beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨⟨_, hlenQ⟩, hnd_app⟩, hadj⟩
    rw [List.nodup_append] at hnd_app
    rcases hnd_app with ⟨hnd1, hndQ, hdisj⟩
    let SQ := (walkH a' b').map fun c : Fin 4 => (m + 1, c.val)
    have hSQne : SQ ≠ [] := by simp [SQ, walkH_nonempty]
    have hP'Q : List.Disjoint (P ++ S₁) SQ := by
      rw [List.disjoint_append_left]
      exact ⟨disjoint_lt_row P _ hProw, disjoint_map_row (List.disjoint_iff_ne.mpr hdisj)⟩
    refine ⟨hP'ne, hP'h, hP'l, hP'nd, hP'ch, hP'Q, hP'row,
      fun p hp => by have := walkH_site_mem_row hp; exact ⟨by omega, this.2⟩,
      fun hnone => by simp at hnone, ?_, ?_, ?_⟩
    · intro a'' b'' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact ⟨hSQne, walkH_site_head (m + 1) a' b', walkH_site_getLast (m + 1) a' b',
        walkH_site_nodup (m + 1) a' b', walkH_site_isChain_adjacent (m + 1) a' b'⟩
    · intro r' hr' c
      rw [adjInList_append hPne hS1ne]
      by_cases hrm : r' = m + 1
      · subst hrm
        rw [hs_any, ht_any]
        have hP0 := adjInList_lt_at_row (c := c) hProw
        have hjoin0 : (P.getLast? == some (m + 1, c.val) && S₁.head? == some (m + 1, c.val + 1)) = false ∧
            (P.getLast? == some (m + 1, c.val + 1) && S₁.head? == some (m + 1, c.val)) = false := by
          rw [hPl]
          simp only [siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)), Bool.false_and, and_self]
        have hS1adj := adjInList_map_row (walkH (stateOp s) (stateOp t)) (m + 1) c
        have hSQadj := adjInList_map_row (walkH a' b') (m + 1) c
        rw [hP0, hjoin0.1, hjoin0.2, hS1adj, hSQadj]
        simpa [Bool.false_or, Bool.or_false] using hadj c
      · have hr'm : r' < m + 1 := by omega
        have hih := hH_ih r' hr'm c
        rw [hQempty, adjInList_nil_false, Bool.or_false] at hih
        have hS10 : adjInList S₁ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hSQ0 : adjInList SQ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hjoin0 : (P.getLast? == some (r', c.val) && S₁.head? == some (r', c.val + 1)) = false ∧
            (P.getLast? == some (r', c.val + 1) && S₁.head? == some (r', c.val)) = false := by
          rw [walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'), Bool.and_false, and_self]
        rw [hS10, hjoin0.1, hjoin0.2, hSQ0]
        simp only [Bool.or_false]
        exact hih
    · intro r' hr0 hr' c
      rw [adjInList_append hPne hS1ne]
      by_cases hrm : r' = m + 1
      · subst hrm
        rw [hs_any, Nat.add_sub_cancel]
        have hP0 := adjInList_vert_lt_in (c := c) hProw
        have hS10 : adjInList S₁ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        have hSQ0 : adjInList SQ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        rw [hP0, hS10, hSQ0, hPl, walkH_site_head]
        simp only [topMask, hps, Bool.false_or, siteOpt_beq_same,
          siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)),
          siteOpt_beq_diff (Nat.ne_of_gt (Nat.lt_succ_self m)),
          Bool.or_false, Bool.and_self, fin_val_beq_decide, fin_beq_decide]
      · have hr'm : r' < m + 1 := by omega
        have hih := hV_ih r' hr0 hr'm c
        rw [hQempty, adjInList_nil_false, Bool.or_false] at hih
        have hS10 : adjInList S₁ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hSQ0 : adjInList SQ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hjoin0 : (P.getLast? == some (r' - 1, c.val) && S₁.head? == some (r', c.val)) = false ∧
            (P.getLast? == some (r', c.val) && S₁.head? == some (r' - 1, c.val)) = false := by
          rw [walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'),
            siteOpt_beq_diff (by omega : m + 1 ≠ r' - 1), Bool.and_false, and_self]
        rw [hS10, hjoin0.1, hjoin0.2, hSQ0]
        simp only [Bool.or_false]
        exact hih

private lemma stepPaths_succ_some_conn_dir {n m : ℕ} {f : Fin (n + 1) → Fin 12}
    (hr : m + 1 + 1 ≤ n) {P Q : List Site} {s t : Fin 12} {a b a' b' : Fin 4}
    (hs : f ⟨m + 1, Nat.lt_succ_of_lt hr⟩ = s)
    (ht : f ⟨m + 1 + 1, Nat.succ_lt_succ hr⟩ = t)
    (hps : statePair s = some (a, b)) (hpt : statePair t = some (a', b'))
    (hconn_op : connH (transH s t) (stateOp s) (stateOp t) = true)
    (hdir : (connH (transH s t) a' a && connH (transH s t) b b') = true)
    (hchk : rowSegmentsCheck s t = true)
    (hinv : PathInv f (m + 1) (Nat.le_of_lt hr) P Q) :
    PathInv f (m + 1 + 1) hr
      (P ++ (walkH (stateOp s) (stateOp t)).map fun c : Fin 4 => (m + 1, c.val))
      ((walkH a' a).map (fun c : Fin 4 => (m + 1, c.val)) ++ Q ++
       (walkH b b').map (fun c : Fin 4 => (m + 1, c.val))) := by
  dsimp only [PathInv] at hinv ⊢
  have hs_any : ∀ h', f ⟨m + 1, h'⟩ = s := fun _ => hs
  have ht_any : ∀ h', f ⟨m + 1 + 1, h'⟩ = t := fun _ => ht
  rcases hinv with ⟨hPne, hPh, hPl, hPnd, hPch, hPQ, hProw, hQrow, _, hQsome, hH_ih, hV_ih⟩
  rw [hs_any] at hPl hQsome
  simp only [Nat.add_sub_cancel] at hPl hQsome
  rcases hQsome a b hps with ⟨hQne, hQh, hQl, hQnd, hQch⟩
  have hsdisj := statePair_disjoint hps
  have htop_s : ∀ c : Fin 4,
      (decide (c = stateOp s) || decide (c = a) || decide (c = b)) = topMask s c := by
    intro c; simp only [topMask, hps, fin_beq_decide, Bool.or_assoc]
  simp only [rowSegmentsCheck, hps, hconn_op, ↓reduceIte, hpt, hdir, Bool.and_eq_true,
    List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq, bne_iff_ne,
    decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨_, hnd3⟩, hadj⟩
  rcases nodup_append_three_disj hnd3 with ⟨hndP, hnd1, hnd2, hP1, hP2, h12⟩
  let rLift : Fin 4 → Site := fun c => (m + 1, c.val)
  let S₁ := (walkH (stateOp s) (stateOp t)).map rLift
  let Sa := (walkH a' a).map rLift
  let Sb := (walkH b b').map rLift
  let Q' := Sa ++ Q ++ Sb
  have hS1ne : S₁ ≠ [] := by simp [S₁, walkH_nonempty]
  have hSane : Sa ≠ [] := by simp [Sa, walkH_nonempty]
  have hSbne : Sb ≠ [] := by simp [Sb, walkH_nonempty]
  have hP'ne : P ++ S₁ ≠ [] := fun h => hPne (List.append_eq_nil_iff.mp h).1
  have hP'h : (P ++ S₁).head? = some (0, 0) := by
    rw [List.head?_append_of_ne_nil _ hPne]; exact hPh
  have hP'l : (P ++ S₁).getLast? = some (m + 1, (stateOp t).val) := by
    rw [List.getLast?_append_of_ne_nil _ hS1ne]; exact walkH_site_getLast (m + 1) (stateOp s) (stateOp t)
  have hP'nd : (P ++ S₁).Nodup := by
    rw [List.nodup_append]
    exact ⟨hPnd, walkH_site_nodup (m + 1) (stateOp s) (stateOp t),
      List.disjoint_iff_ne.mp (disjoint_lt_row P _ hProw)⟩
  have hP'ch : (P ++ S₁).IsChain adjacent := by
    refine isChain_append hPch (walkH_site_isChain_adjacent (m + 1) (stateOp s) (stateOp t)) hPne hS1ne ?_
    have hPl' : P.getLast hPne = (m, (stateOp s).val) := by
      rw [List.getLast_eq_iff_getLast?_eq_some]; exact hPl
    have hS1h' : S₁.head hS1ne = (m + 1, (stateOp s).val) := by
      rw [List.head_eq_iff_head?_eq_some]; exact walkH_site_head (m + 1) (stateOp s) (stateOp t)
    rw [hPl', hS1h']; dsimp only [adjacent, Nat.dist]; omega
  have hP'row : ∀ p ∈ P ++ S₁, p.1 < m + 2 ∧ p.2 < 4 := by
    intro p hp
    rcases List.mem_append.mp hp with hpP | hpS
    · have := hProw p hpP; exact ⟨by omega, this.2⟩
    · have := walkH_site_mem_row hpS; exact ⟨by omega, this.2⟩
  have hQ'ne : Q' ≠ [] := by simp [Q', hSbne]
  have hQ'h : Q'.head? = some (m + 1, a'.val) := by
    simp only [Q', List.append_assoc]; rw [List.head?_append_of_ne_nil _ hSane]
    exact walkH_site_head (m + 1) a' a
  have hQ'l : Q'.getLast? = some (m + 1, b'.val) := by
    rw [List.getLast?_append_of_ne_nil _ hSbne]; exact walkH_site_getLast (m + 1) b b'
  have hQ'nd : Q'.Nodup := by
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨walkH_site_nodup (m + 1) a' a, hQnd,
      List.disjoint_iff_ne.mp (disjoint_lt_row Q _ hQrow).symm⟩, walkH_site_nodup (m + 1) b b', ?_⟩
    rw [← List.disjoint_iff_ne, List.disjoint_append_left]
    exact ⟨disjoint_map_row h12, disjoint_lt_row Q _ hQrow⟩
  have hQ'ch : Q'.IsChain adjacent := by
    refine isChain_append ?_ (walkH_site_isChain_adjacent (m + 1) b b') (by simp [hQne]) hSbne ?_
    · refine isChain_append (walkH_site_isChain_adjacent (m + 1) a' a) hQch hSane hQne ?_
      have hSal : Sa.getLast hSane = (m + 1, a.val) := by
        rw [List.getLast_eq_iff_getLast?_eq_some]; exact walkH_site_getLast (m + 1) a' a
      have hQh' : Q.head hQne = (m, a.val) := by rw [List.head_eq_iff_head?_eq_some]; exact hQh
      rw [hSal, hQh']; dsimp only [adjacent, Nat.dist]; omega
    · rw [List.getLast_append_of_ne_nil _ hQne]
      have hQl' : Q.getLast hQne = (m, b.val) := by rw [List.getLast_eq_iff_getLast?_eq_some]; exact hQl
      have hSbh : Sb.head hSbne = (m + 1, b.val) := by
        rw [List.head_eq_iff_head?_eq_some]; exact walkH_site_head (m + 1) b b'
      rw [hQl', hSbh]; dsimp only [adjacent, Nat.dist]; omega
  have hQ'row : ∀ p ∈ Q', p.1 < m + 2 ∧ p.2 < 4 := by
    intro p hp
    simp only [Q', List.mem_append] at hp
    rcases hp with (hp1 | hpQ) | hp2
    · have := walkH_site_mem_row hp1; exact ⟨by omega, this.2⟩
    · have := hQrow p hpQ; exact ⟨by omega, this.2⟩
    · have := walkH_site_mem_row hp2; exact ⟨by omega, this.2⟩
  have hP'Q' : List.Disjoint (P ++ S₁) Q' := by
    rw [List.disjoint_append_left, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right]
    refine ⟨⟨⟨disjoint_lt_row P _ hProw, hPQ⟩, disjoint_lt_row P _ hProw⟩,
      ⟨⟨disjoint_map_row hP1, (disjoint_lt_row Q _ hQrow).symm⟩, disjoint_map_row hP2⟩⟩
  have hQ'split : ∀ u v : Site,
      adjInList Q' u v = (adjInList Sa u v || adjInList Q u v || adjInList Sb u v ||
        ((Sa.getLast? == some u && Q.head? == some v) ||
         (Sa.getLast? == some v && Q.head? == some u) ||
         (Q.getLast? == some u && Sb.head? == some v) ||
         (Q.getLast? == some v && Sb.head? == some u))) := by
    intro u v; dsimp only [Q']
    rw [adjInList_append (by simp [hQne]) hSbne, adjInList_append hSane hQne,
      List.getLast?_append_of_ne_nil _ hQne]
    simp only [Bool.or_assoc]
    rw [Bool.or_left_comm _ (adjInList Sb u v), Bool.or_left_comm _ (adjInList Sb u v)]
  rw [ht_any]
  simp only [Nat.add_sub_cancel, hpt]
  refine ⟨hP'ne, hP'h, hP'l, hP'nd, hP'ch, hP'Q', hP'row, hQ'row,
    fun hnone => by simp at hnone, ?_, ?_, ?_⟩
  · intro a'' b'' heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact ⟨hQ'ne, hQ'h, hQ'l, hQ'nd, hQ'ch⟩
  · intro r' hr' c
    rw [adjInList_append hPne hS1ne, hQ'split]
    by_cases hrm : r' = m + 1
    · subst hrm; rw [hs_any, ht_any]
      have hP0 := adjInList_lt_at_row (c := c) hProw
      have hQ0 := adjInList_lt_at_row (c := c) hQrow
      have hjoin1 : (P.getLast? == some (m + 1, c.val) && S₁.head? == some (m + 1, c.val + 1)) = false ∧
          (P.getLast? == some (m + 1, c.val + 1) && S₁.head? == some (m + 1, c.val)) = false ∧
          (Sa.getLast? == some (m + 1, c.val) && Q.head? == some (m + 1, c.val + 1)) = false ∧
          (Sa.getLast? == some (m + 1, c.val + 1) && Q.head? == some (m + 1, c.val)) = false ∧
          (Q.getLast? == some (m + 1, c.val) && Sb.head? == some (m + 1, c.val + 1)) = false ∧
          (Q.getLast? == some (m + 1, c.val + 1) && Sb.head? == some (m + 1, c.val)) = false := by
        rw [hPl, hQh, hQl]
        simp only [siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)), Bool.false_and,
          Bool.and_false, and_self]
      have hS1adj := adjInList_map_row (walkH (stateOp s) (stateOp t)) (m + 1) c
      have hSaadj := adjInList_map_row (walkH a' a) (m + 1) c
      have hSbadj := adjInList_map_row (walkH b b') (m + 1) c
      rw [hP0, hQ0, hjoin1.1, hjoin1.2.1, hjoin1.2.2.1, hjoin1.2.2.2.1, hjoin1.2.2.2.2.1,
        hjoin1.2.2.2.2.2, hS1adj, hSaadj, hSbadj]
      simpa [Bool.false_or, Bool.or_false, Bool.or_assoc] using hadj c
    · have hr'm : r' < m + 1 := by omega
      have hih := hH_ih r' hr'm c
      have hS10 : adjInList S₁ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
      have hSa0 : adjInList Sa (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
      have hSb0 : adjInList Sb (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
      have hj0 : (P.getLast? == some (r', c.val) && S₁.head? == some (r', c.val + 1)) = false ∧
          (P.getLast? == some (r', c.val + 1) && S₁.head? == some (r', c.val)) = false ∧
          (Sa.getLast? == some (r', c.val) && Q.head? == some (r', c.val + 1)) = false ∧
          (Sa.getLast? == some (r', c.val + 1) && Q.head? == some (r', c.val)) = false ∧
          (Q.getLast? == some (r', c.val) && Sb.head? == some (r', c.val + 1)) = false ∧
          (Q.getLast? == some (r', c.val + 1) && Sb.head? == some (r', c.val)) = false := by
        rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
        simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'), Bool.false_and, Bool.and_false, and_self]
      rw [hS10, hSa0, hSb0, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
      simp only [Bool.false_or, Bool.or_false]
      exact hih
  · intro r' hr0 hr' c
    rw [adjInList_append hPne hS1ne, hQ'split]
    by_cases hrm : r' = m + 1
    · subst hrm; rw [hs_any, Nat.add_sub_cancel]
      have hP0 := adjInList_vert_lt_in (c := c) hProw
      have hQ0 := adjInList_vert_lt_in (c := c) hQrow
      have hS10 : adjInList S₁ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
      have hSa0 : adjInList Sa (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
      have hSb0 : adjInList Sb (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
      rw [hP0, hQ0, hS10, hSa0, hSb0, hPl, walkH_site_head, walkH_site_getLast, hQh, hQl, walkH_site_head]
      rw [← htop_s c]
      simp only [Bool.false_or, Bool.or_false, siteOpt_beq_same,
        siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)),
        siteOpt_beq_diff (Nat.ne_of_gt (Nat.lt_succ_self m)),
        Bool.and_self, fin_val_beq_decide, Bool.or_assoc]
    · have hr'm : r' < m + 1 := by omega
      have hih := hV_ih r' hr0 hr'm c
      have hS10 : adjInList S₁ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
      have hSa0 : adjInList Sa (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
      have hSb0 : adjInList Sb (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
      have hj0 : (P.getLast? == some (r' - 1, c.val) && S₁.head? == some (r', c.val)) = false ∧
          (P.getLast? == some (r', c.val) && S₁.head? == some (r' - 1, c.val)) = false ∧
          (Sa.getLast? == some (r' - 1, c.val) && Q.head? == some (r', c.val)) = false ∧
          (Sa.getLast? == some (r', c.val) && Q.head? == some (r' - 1, c.val)) = false ∧
          (Q.getLast? == some (r' - 1, c.val) && Sb.head? == some (r', c.val)) = false ∧
          (Q.getLast? == some (r', c.val) && Sb.head? == some (r' - 1, c.val)) = false := by
        rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
        simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'),
          siteOpt_beq_diff (by omega : m + 1 ≠ r' - 1), Bool.false_and, Bool.and_false, and_self]
      rw [hS10, hSa0, hSb0, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
      simp only [Bool.false_or, Bool.or_false]
      exact hih

private lemma stepPaths_succ_some_conn_rev {n m : ℕ} {f : Fin (n + 1) → Fin 12}
    (hr : m + 1 + 1 ≤ n) {P Q : List Site} {s t : Fin 12} {a b a' b' : Fin 4}
    (hs : f ⟨m + 1, Nat.lt_succ_of_lt hr⟩ = s)
    (ht : f ⟨m + 1 + 1, Nat.succ_lt_succ hr⟩ = t)
    (hps : statePair s = some (a, b)) (hpt : statePair t = some (a', b'))
    (hconn_op : connH (transH s t) (stateOp s) (stateOp t) = true)
    (hdir : (connH (transH s t) a' a && connH (transH s t) b b') = false)
    (hchk : rowSegmentsCheck s t = true)
    (hinv : PathInv f (m + 1) (Nat.le_of_lt hr) P Q) :
    PathInv f (m + 1 + 1) hr
      (P ++ (walkH (stateOp s) (stateOp t)).map fun c : Fin 4 => (m + 1, c.val))
      ((walkH a' b).map (fun c : Fin 4 => (m + 1, c.val)) ++ Q.reverse ++
       (walkH a b').map (fun c : Fin 4 => (m + 1, c.val))) := by
  dsimp only [PathInv] at hinv ⊢
  have hs_any : ∀ h', f ⟨m + 1, h'⟩ = s := fun _ => hs
  have ht_any : ∀ h', f ⟨m + 1 + 1, h'⟩ = t := fun _ => ht
  rcases hinv with ⟨hPne, hPh, hPl, hPnd, hPch, hPQ, hProw, hQrow, _, hQsome, hH_ih, hV_ih⟩
  rw [hs_any] at hPl hQsome
  simp only [Nat.add_sub_cancel] at hPl hQsome
  rcases hQsome a b hps with ⟨hQne, hQh, hQl, hQnd, hQch⟩
  have htop_s : ∀ c : Fin 4,
      (decide (c = stateOp s) || decide (c = a) || decide (c = b)) = topMask s c := by
    intro c; simp only [topMask, hps, fin_beq_decide, Bool.or_assoc]
  simp only [rowSegmentsCheck, hps, hconn_op, ↓reduceIte, hpt, hdir, Bool.false_eq_true,
    Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq, bne_iff_ne,
    decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨_, _⟩, hnd3, hadj⟩
  rcases nodup_append_three_disj hnd3 with ⟨hndP, hnd1, hnd2, hP1, hP2, h12⟩
  let rLift : Fin 4 → Site := fun c => (m + 1, c.val)
  let S₁ := (walkH (stateOp s) (stateOp t)).map rLift
  let Sa := (walkH a' b).map rLift
  let Sb := (walkH a b').map rLift
  have hS1ne : S₁ ≠ [] := by simp [S₁, walkH_nonempty]
  have hSane : Sa ≠ [] := by simp [Sa, walkH_nonempty]
  have hSbne : Sb ≠ [] := by simp [Sb, walkH_nonempty]
  have hQrne : Q.reverse ≠ [] := by simp [hQne]
  let Q' := Sa ++ Q.reverse ++ Sb
  have hP'ne : P ++ S₁ ≠ [] := fun h => hPne (List.append_eq_nil_iff.mp h).1
  have hP'h : (P ++ S₁).head? = some (0, 0) := by
    rw [List.head?_append_of_ne_nil _ hPne]; exact hPh
  have hP'l : (P ++ S₁).getLast? = some (m + 1, (stateOp t).val) := by
    rw [List.getLast?_append_of_ne_nil _ hS1ne]; exact walkH_site_getLast (m + 1) (stateOp s) (stateOp t)
  have hP'nd : (P ++ S₁).Nodup := by
    rw [List.nodup_append]
    exact ⟨hPnd, walkH_site_nodup (m + 1) (stateOp s) (stateOp t),
      List.disjoint_iff_ne.mp (disjoint_lt_row P _ hProw)⟩
  have hP'ch : (P ++ S₁).IsChain adjacent := by
    refine isChain_append hPch (walkH_site_isChain_adjacent (m + 1) (stateOp s) (stateOp t)) hPne hS1ne ?_
    have hPl' : P.getLast hPne = (m, (stateOp s).val) := by
      rw [List.getLast_eq_iff_getLast?_eq_some]; exact hPl
    have hS1h' : S₁.head hS1ne = (m + 1, (stateOp s).val) := by
      rw [List.head_eq_iff_head?_eq_some]; exact walkH_site_head (m + 1) (stateOp s) (stateOp t)
    rw [hPl', hS1h']; dsimp only [adjacent, Nat.dist]; omega
  have hP'row : ∀ p ∈ P ++ S₁, p.1 < m + 2 ∧ p.2 < 4 := by
    intro p hp
    rcases List.mem_append.mp hp with hpP | hpS
    · have := hProw p hpP; exact ⟨by omega, this.2⟩
    · have := walkH_site_mem_row hpS; exact ⟨by omega, this.2⟩
  have hQ'ne : Q' ≠ [] := by simp [Q', hSbne]
  have hQ'h : Q'.head? = some (m + 1, a'.val) := by
    simp only [Q', List.append_assoc]; rw [List.head?_append_of_ne_nil _ hSane]
    exact walkH_site_head (m + 1) a' b
  have hQ'l : Q'.getLast? = some (m + 1, b'.val) := by
    rw [List.getLast?_append_of_ne_nil _ hSbne]; exact walkH_site_getLast (m + 1) a b'
  have hQr_row : ∀ p ∈ Q.reverse, p.1 < m + 1 ∧ p.2 < 4 := fun p hp => hQrow p (List.mem_reverse.mp hp)
  have hQ'nd : Q'.Nodup := by
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨walkH_site_nodup (m + 1) a' b, List.nodup_reverse.mpr hQnd,
      List.disjoint_iff_ne.mp (disjoint_lt_row Q.reverse _ hQr_row).symm⟩,
      walkH_site_nodup (m + 1) a b', ?_⟩
    rw [← List.disjoint_iff_ne, List.disjoint_append_left]
    exact ⟨disjoint_map_row h12, disjoint_lt_row Q.reverse _ hQr_row⟩
  have hQ'ch : Q'.IsChain adjacent := by
    have hQr_ch : Q.reverse.IsChain adjacent := isChain_reverse (fun _ _ => adjacent_symm) hQch
    refine isChain_append ?_ (walkH_site_isChain_adjacent (m + 1) a b') (by simp [hQrne]) hSbne ?_
    · refine isChain_append (walkH_site_isChain_adjacent (m + 1) a' b) hQr_ch hSane hQrne ?_
      have hSal : Sa.getLast hSane = (m + 1, b.val) := by
        rw [List.getLast_eq_iff_getLast?_eq_some]; exact walkH_site_getLast (m + 1) a' b
      have hQrh : Q.reverse.head hQrne = (m, b.val) := by
        rw [List.head_eq_iff_head?_eq_some]; simpa [List.head?_reverse] using hQl
      rw [hSal, hQrh]; dsimp only [adjacent, Nat.dist]; omega
    · rw [List.getLast_append_of_ne_nil _ hQrne]
      have hQrl : Q.reverse.getLast hQrne = (m, a.val) := by
        rw [List.getLast_eq_iff_getLast?_eq_some]; simpa [List.getLast?_reverse] using hQh
      have hSbh : Sb.head hSbne = (m + 1, a.val) := by
        rw [List.head_eq_iff_head?_eq_some]; exact walkH_site_head (m + 1) a b'
      rw [hQrl, hSbh]; dsimp only [adjacent, Nat.dist]; omega
  have hQ'row : ∀ p ∈ Q', p.1 < m + 2 ∧ p.2 < 4 := by
    intro p hp; simp only [Q', List.mem_append, List.mem_reverse] at hp
    rcases hp with (hp1 | hpQ) | hp2
    · have := walkH_site_mem_row hp1; exact ⟨by omega, this.2⟩
    · have := hQrow p hpQ; exact ⟨by omega, this.2⟩
    · have := walkH_site_mem_row hp2; exact ⟨by omega, this.2⟩
  have hP'Q' : List.Disjoint (P ++ S₁) Q' := by
    rw [List.disjoint_append_left, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right]
    have hPQr : List.Disjoint P Q.reverse := fun _ hx hy => hPQ hx (List.mem_reverse.mp hy)
    refine ⟨⟨⟨disjoint_lt_row P _ hProw, hPQr⟩, disjoint_lt_row P _ hProw⟩,
      ⟨⟨disjoint_map_row hP1, (disjoint_lt_row Q.reverse _ hQr_row).symm⟩, disjoint_map_row hP2⟩⟩
  have hQ'split : ∀ u v : Site,
      adjInList Q' u v = (adjInList Sa u v || adjInList Q u v || adjInList Sb u v ||
        ((Sa.getLast? == some u && Q.reverse.head? == some v) ||
         (Sa.getLast? == some v && Q.reverse.head? == some u) ||
         (Q.reverse.getLast? == some u && Sb.head? == some v) ||
         (Q.reverse.getLast? == some v && Sb.head? == some u))) := by
    intro u v; dsimp only [Q']
    rw [adjInList_append (by simp [hQrne]) hSbne, adjInList_append hSane hQrne,
      List.getLast?_append_of_ne_nil _ hQrne, adjInList_reverse]
    simp only [Bool.or_assoc]
    rw [Bool.or_left_comm _ (adjInList Sb u v), Bool.or_left_comm _ (adjInList Sb u v)]
  rw [ht_any]
  simp only [Nat.add_sub_cancel, hpt]
  refine ⟨hP'ne, hP'h, hP'l, hP'nd, hP'ch, hP'Q', hP'row, hQ'row,
    fun hnone => by simp at hnone, ?_, ?_, ?_⟩
  · intro a'' b'' heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact ⟨hQ'ne, hQ'h, hQ'l, hQ'nd, hQ'ch⟩
  · intro r' hr' c
    rw [adjInList_append hPne hS1ne, hQ'split]
    by_cases hrm : r' = m + 1
    · subst hrm; rw [hs_any, ht_any]
      have hP0 := adjInList_lt_at_row (c := c) hProw
      have hQ0 := adjInList_lt_at_row (c := c) hQrow
      have hjoin1 : (P.getLast? == some (m + 1, c.val) && S₁.head? == some (m + 1, c.val + 1)) = false ∧
          (P.getLast? == some (m + 1, c.val + 1) && S₁.head? == some (m + 1, c.val)) = false ∧
          (Sa.getLast? == some (m + 1, c.val) && Q.reverse.head? == some (m + 1, c.val + 1)) = false ∧
          (Sa.getLast? == some (m + 1, c.val + 1) && Q.reverse.head? == some (m + 1, c.val)) = false ∧
          (Q.reverse.getLast? == some (m + 1, c.val) && Sb.head? == some (m + 1, c.val + 1)) = false ∧
          (Q.reverse.getLast? == some (m + 1, c.val + 1) && Sb.head? == some (m + 1, c.val)) = false := by
        rw [hPl, List.head?_reverse, hQl, List.getLast?_reverse, hQh]
        simp only [siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)), Bool.false_and,
          Bool.and_false, and_self]
      have hS1adj := adjInList_map_row (walkH (stateOp s) (stateOp t)) (m + 1) c
      have hSaadj := adjInList_map_row (walkH a' b) (m + 1) c
      have hSbadj := adjInList_map_row (walkH a b') (m + 1) c
      rw [hP0, hQ0, hjoin1.1, hjoin1.2.1, hjoin1.2.2.1, hjoin1.2.2.2.1, hjoin1.2.2.2.2.1,
        hjoin1.2.2.2.2.2, hS1adj, hSaadj, hSbadj]
      simpa [Bool.false_or, Bool.or_false, Bool.or_assoc] using hadj c
    · have hr'm : r' < m + 1 := by omega
      have hih := hH_ih r' hr'm c
      have hS10 : adjInList S₁ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
      have hSa0 : adjInList Sa (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
      have hSb0 : adjInList Sb (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
      have hj0 : (P.getLast? == some (r', c.val) && S₁.head? == some (r', c.val + 1)) = false ∧
          (P.getLast? == some (r', c.val + 1) && S₁.head? == some (r', c.val)) = false ∧
          (Sa.getLast? == some (r', c.val) && Q.reverse.head? == some (r', c.val + 1)) = false ∧
          (Sa.getLast? == some (r', c.val + 1) && Q.reverse.head? == some (r', c.val)) = false ∧
          (Q.reverse.getLast? == some (r', c.val) && Sb.head? == some (r', c.val + 1)) = false ∧
          (Q.reverse.getLast? == some (r', c.val + 1) && Sb.head? == some (r', c.val)) = false := by
        rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
        simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'), Bool.false_and, Bool.and_false, and_self]
      rw [hS10, hSa0, hSb0, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
      simp only [Bool.false_or, Bool.or_false]
      exact hih
  · intro r' hr0 hr' c
    rw [adjInList_append hPne hS1ne, hQ'split]
    by_cases hrm : r' = m + 1
    · subst hrm; rw [hs_any, Nat.add_sub_cancel]
      have hP0 := adjInList_vert_lt_in (c := c) hProw
      have hQ0 := adjInList_vert_lt_in (c := c) hQrow
      have hS10 : adjInList S₁ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
      have hSa0 : adjInList Sa (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
      have hSb0 : adjInList Sb (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
      rw [hP0, hQ0, hS10, hSa0, hSb0, hPl, walkH_site_head, walkH_site_getLast,
        List.head?_reverse, hQl, List.getLast?_reverse, hQh, walkH_site_head]
      rw [← htop_s c]
      simp only [Bool.false_or, Bool.or_false, siteOpt_beq_same,
        siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)),
        siteOpt_beq_diff (Nat.ne_of_gt (Nat.lt_succ_self m)),
        Bool.and_self, fin_val_beq_decide, Bool.or_assoc]
      rw [Bool.or_comm (decide (c = b)) (decide (c = a))]
    · have hr'm : r' < m + 1 := by omega
      have hih := hV_ih r' hr0 hr'm c
      have hS10 : adjInList S₁ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
      have hSa0 : adjInList Sa (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
      have hSb0 : adjInList Sb (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
      have hj0 : (P.getLast? == some (r' - 1, c.val) && S₁.head? == some (r', c.val)) = false ∧
          (P.getLast? == some (r', c.val) && S₁.head? == some (r' - 1, c.val)) = false ∧
          (Sa.getLast? == some (r' - 1, c.val) && Q.reverse.head? == some (r', c.val)) = false ∧
          (Sa.getLast? == some (r', c.val) && Q.reverse.head? == some (r' - 1, c.val)) = false ∧
          (Q.reverse.getLast? == some (r' - 1, c.val) && Sb.head? == some (r', c.val)) = false ∧
          (Q.reverse.getLast? == some (r', c.val) && Sb.head? == some (r' - 1, c.val)) = false := by
        rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
        simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'),
          siteOpt_beq_diff (by omega : m + 1 ≠ r' - 1), Bool.false_and, Bool.and_false, and_self]
      rw [hS10, hSa0, hSb0, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
      simp only [Bool.false_or, Bool.or_false]
      exact hih

private lemma stepPaths_succ_some_noconn_dir {n m : ℕ} {f : Fin (n + 1) → Fin 12}
    (hr : m + 1 + 1 ≤ n) {P Q : List Site} {s t : Fin 12} {a b : Fin 4}
    (hs : f ⟨m + 1, Nat.lt_succ_of_lt hr⟩ = s)
    (ht : f ⟨m + 1 + 1, Nat.succ_lt_succ hr⟩ = t)
    (hps : statePair s = some (a, b))
    (hconn_op : connH (transH s t) (stateOp s) (stateOp t) = false)
    (hdir : (connH (transH s t) (stateOp s) a && connH (transH s t) b (stateOp t)) = true)
    (hchk : rowSegmentsCheck s t = true)
    (hinv : PathInv f (m + 1) (Nat.le_of_lt hr) P Q) :
    PathInv f (m + 1 + 1) hr
      (P ++ (walkH (stateOp s) a).map (fun c : Fin 4 => (m + 1, c.val)) ++ Q ++
       (walkH b (stateOp t)).map (fun c : Fin 4 => (m + 1, c.val)))
      (match statePair t with
       | none => []
       | some (a', b') => (walkH a' b').map fun c : Fin 4 => (m + 1, c.val)) := by
  dsimp only [PathInv] at hinv ⊢
  have hs_any : ∀ h', f ⟨m + 1, h'⟩ = s := fun _ => hs
  have ht_any : ∀ h', f ⟨m + 1 + 1, h'⟩ = t := fun _ => ht
  rcases hinv with ⟨hPne, hPh, hPl, hPnd, hPch, hPQ, hProw, hQrow, _, hQsome, hH_ih, hV_ih⟩
  rw [hs_any] at hPl hQsome
  simp only [Nat.add_sub_cancel] at hPl hQsome
  rcases hQsome a b hps with ⟨hQne, hQh, hQl, hQnd, hQch⟩
  have htop_s : ∀ c : Fin 4,
      (decide (c = stateOp s) || decide (c = a) || decide (c = b)) = topMask s c := by
    intro c; simp only [topMask, hps, fin_beq_decide, Bool.or_assoc]
  simp only [rowSegmentsCheck, hps, hconn_op, Bool.false_eq_true, ↓reduceIte, hdir,
    Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq,
    decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨_, hnd3⟩, hadj⟩
  rcases nodup_append_three_disj hnd3 with ⟨hnd1, hnd2, hndQ, h12, h1Q, h2Q⟩
  let rLift : Fin 4 → Site := fun c => (m + 1, c.val)
  let S₁ := (walkH (stateOp s) a).map rLift
  let S₂ := (walkH b (stateOp t)).map rLift
  let P' := P ++ S₁ ++ Q ++ S₂
  have hS1ne : S₁ ≠ [] := by simp [S₁, walkH_nonempty]
  have hS2ne : S₂ ≠ [] := by simp [S₂, walkH_nonempty]
  have hP'ne : P' ≠ [] := by simp [P', hS2ne]
  have hP'h : P'.head? = some (0, 0) := by
    simp only [P', List.append_assoc]; rw [List.head?_append_of_ne_nil _ hPne]; exact hPh
  have hP'l : P'.getLast? = some (m + 1, (stateOp t).val) := by
    rw [List.getLast?_append_of_ne_nil _ hS2ne]; exact walkH_site_getLast (m + 1) b (stateOp t)
  have hP'nd : P'.Nodup := by
    rw [List.nodup_append, List.nodup_append, List.nodup_append]
    refine ⟨⟨⟨hPnd, walkH_site_nodup (m + 1) (stateOp s) a,
      List.disjoint_iff_ne.mp (disjoint_lt_row P _ hProw)⟩, hQnd, ?_⟩,
      walkH_site_nodup (m + 1) b (stateOp t), ?_⟩
    · rw [← List.disjoint_iff_ne, List.disjoint_append_left]
      exact ⟨hPQ, (disjoint_lt_row Q _ hQrow).symm⟩
    · rw [← List.disjoint_iff_ne, List.disjoint_append_left, List.disjoint_append_left]
      exact ⟨⟨disjoint_lt_row P _ hProw, disjoint_map_row h12⟩, disjoint_lt_row Q _ hQrow⟩
  have hP'ch : P'.IsChain adjacent := by
    refine isChain_append ?_ (walkH_site_isChain_adjacent (m + 1) b (stateOp t)) (by simp [hQne]) hS2ne ?_
    · refine isChain_append ?_ hQch (by simp [hS1ne]) hQne ?_
      · refine isChain_append hPch (walkH_site_isChain_adjacent (m + 1) (stateOp s) a) hPne hS1ne ?_
        have hPl' : P.getLast hPne = (m, (stateOp s).val) := by
          rw [List.getLast_eq_iff_getLast?_eq_some]; exact hPl
        have hS1h : S₁.head hS1ne = (m + 1, (stateOp s).val) := by
          rw [List.head_eq_iff_head?_eq_some]; exact walkH_site_head (m + 1) (stateOp s) a
        rw [hPl', hS1h]; dsimp only [adjacent, Nat.dist]; omega
      · rw [List.getLast_append_of_ne_nil _ hS1ne]
        have hS1l : S₁.getLast hS1ne = (m + 1, a.val) := by
          rw [List.getLast_eq_iff_getLast?_eq_some]; exact walkH_site_getLast (m + 1) (stateOp s) a
        have hQh' : Q.head hQne = (m, a.val) := by rw [List.head_eq_iff_head?_eq_some]; exact hQh
        rw [hS1l, hQh']; dsimp only [adjacent, Nat.dist]; omega
    · rw [List.getLast_append_of_ne_nil _ hQne]
      have hQl' : Q.getLast hQne = (m, b.val) := by rw [List.getLast_eq_iff_getLast?_eq_some]; exact hQl
      have hS2h : S₂.head hS2ne = (m + 1, b.val) := by
        rw [List.head_eq_iff_head?_eq_some]; exact walkH_site_head (m + 1) b (stateOp t)
      rw [hQl', hS2h]; dsimp only [adjacent, Nat.dist]; omega
  have hP'row : ∀ p ∈ P', p.1 < m + 2 ∧ p.2 < 4 := by
    intro p hp; simp only [P', List.mem_append] at hp
    rcases hp with ((hpP | hp1) | hpQ) | hp2
    · have := hProw p hpP; exact ⟨by omega, this.2⟩
    · have := walkH_site_mem_row hp1; exact ⟨by omega, this.2⟩
    · have := hQrow p hpQ; exact ⟨by omega, this.2⟩
    · have := walkH_site_mem_row hp2; exact ⟨by omega, this.2⟩
  have hP'split : ∀ u v : Site,
      adjInList P' u v = (adjInList P u v || adjInList S₁ u v || adjInList Q u v || adjInList S₂ u v ||
        ((P.getLast? == some u && S₁.head? == some v) ||
         (P.getLast? == some v && S₁.head? == some u) ||
         (S₁.getLast? == some u && Q.head? == some v) ||
         (S₁.getLast? == some v && Q.head? == some u) ||
         (Q.getLast? == some u && S₂.head? == some v) ||
         (Q.getLast? == some v && S₂.head? == some u))) := by
    intro u v; dsimp only [P']
    rw [adjInList_append (by simp [hQne]) hS2ne, adjInList_append (by simp [hS1ne]) hQne,
      adjInList_append hPne hS1ne, List.getLast?_append_of_ne_nil _ hS1ne,
      List.getLast?_append_of_ne_nil _ hQne]
    simp only [Bool.or_assoc]
    rw [Bool.or_left_comm _ (adjInList Q u v), Bool.or_left_comm _ (adjInList Q u v)]
    rw [Bool.or_left_comm _ (adjInList S₂ u v), Bool.or_left_comm _ (adjInList S₂ u v),
      Bool.or_left_comm _ (adjInList S₂ u v), Bool.or_left_comm _ (adjInList S₂ u v)]
  rw [ht_any]
  simp only [Nat.add_sub_cancel]
  cases hpt : statePair t with
  | none =>
    simp only [hpt] at hadj
    refine ⟨hP'ne, hP'h, hP'l, hP'nd, hP'ch, by simp, hP'row, by simp,
      fun _ => by simp, fun a'' b'' hab => by simp at hab, ?_, ?_⟩
    · intro r' hr' c
      rw [hP'split, adjInList_nil_false, Bool.or_false]
      by_cases hrm : r' = m + 1
      · subst hrm; rw [hs_any, ht_any]
        have hP0 := adjInList_lt_at_row (c := c) hProw
        have hQ0 := adjInList_lt_at_row (c := c) hQrow
        have hjoin1 : (P.getLast? == some (m + 1, c.val) && S₁.head? == some (m + 1, c.val + 1)) = false ∧
            (P.getLast? == some (m + 1, c.val + 1) && S₁.head? == some (m + 1, c.val)) = false ∧
            (S₁.getLast? == some (m + 1, c.val) && Q.head? == some (m + 1, c.val + 1)) = false ∧
            (S₁.getLast? == some (m + 1, c.val + 1) && Q.head? == some (m + 1, c.val)) = false ∧
            (Q.getLast? == some (m + 1, c.val) && S₂.head? == some (m + 1, c.val + 1)) = false ∧
            (Q.getLast? == some (m + 1, c.val + 1) && S₂.head? == some (m + 1, c.val)) = false := by
          rw [hPl, hQh, hQl]
          simp only [siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)), Bool.false_and,
            Bool.and_false, and_self]
        have hS1adj := adjInList_map_row (walkH (stateOp s) a) (m + 1) c
        have hS2adj := adjInList_map_row (walkH b (stateOp t)) (m + 1) c
        have hsub : adjHList [] c = false := rfl
        rw [hP0, hQ0, hjoin1.1, hjoin1.2.1, hjoin1.2.2.1, hjoin1.2.2.2.1, hjoin1.2.2.2.2.1,
          hjoin1.2.2.2.2.2, hS1adj, hS2adj]
        simpa [Bool.or_false, hsub] using hadj c
      · have hr'm : r' < m + 1 := by omega
        have hih := hH_ih r' hr'm c
        have hS10 : adjInList S₁ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hS20 : adjInList S₂ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hj0 : (P.getLast? == some (r', c.val) && S₁.head? == some (r', c.val + 1)) = false ∧
            (P.getLast? == some (r', c.val + 1) && S₁.head? == some (r', c.val)) = false ∧
            (S₁.getLast? == some (r', c.val) && Q.head? == some (r', c.val + 1)) = false ∧
            (S₁.getLast? == some (r', c.val + 1) && Q.head? == some (r', c.val)) = false ∧
            (Q.getLast? == some (r', c.val) && S₂.head? == some (r', c.val + 1)) = false ∧
            (Q.getLast? == some (r', c.val + 1) && S₂.head? == some (r', c.val)) = false := by
          rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'), Bool.false_and, Bool.and_false, and_self]
        rw [hS10, hS20, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
        simp only [Bool.or_false]
        exact hih
    · intro r' hr0 hr' c
      rw [hP'split, adjInList_nil_false, Bool.or_false]
      by_cases hrm : r' = m + 1
      · subst hrm; rw [hs_any, Nat.add_sub_cancel]
        have hP0 := adjInList_vert_lt_in (c := c) hProw
        have hQ0 := adjInList_vert_lt_in (c := c) hQrow
        have hS10 : adjInList S₁ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        have hS20 : adjInList S₂ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        rw [hP0, hQ0, hS10, hS20, hPl, walkH_site_head, walkH_site_getLast, hQh, hQl, walkH_site_head]
        rw [← htop_s c]
        simp only [Bool.false_or, Bool.or_false, siteOpt_beq_same,
          siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)),
          siteOpt_beq_diff (Nat.ne_of_gt (Nat.lt_succ_self m)),
          Bool.and_self, fin_val_beq_decide, Bool.or_assoc]
      · have hr'm : r' < m + 1 := by omega
        have hih := hV_ih r' hr0 hr'm c
        have hS10 : adjInList S₁ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hS20 : adjInList S₂ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hj0 : (P.getLast? == some (r' - 1, c.val) && S₁.head? == some (r', c.val)) = false ∧
            (P.getLast? == some (r', c.val) && S₁.head? == some (r' - 1, c.val)) = false ∧
            (S₁.getLast? == some (r' - 1, c.val) && Q.head? == some (r', c.val)) = false ∧
            (S₁.getLast? == some (r', c.val) && Q.head? == some (r' - 1, c.val)) = false ∧
            (Q.getLast? == some (r' - 1, c.val) && S₂.head? == some (r', c.val)) = false ∧
            (Q.getLast? == some (r', c.val) && S₂.head? == some (r' - 1, c.val)) = false := by
          rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'),
            siteOpt_beq_diff (by omega : m + 1 ≠ r' - 1), Bool.false_and, Bool.and_false, and_self]
        rw [hS10, hS20, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
        simp only [Bool.or_false]
        exact hih
  | some ab' =>
    rcases ab' with ⟨a', b'⟩
    simp only [hpt] at h1Q h2Q hadj
    let SQ := (walkH a' b').map rLift
    have hSQne : SQ ≠ [] := by simp [SQ, walkH_nonempty]
    have hP'Q : List.Disjoint P' SQ := by
      rw [List.disjoint_append_left, List.disjoint_append_left, List.disjoint_append_left]
      exact ⟨⟨⟨disjoint_lt_row P _ hProw, disjoint_map_row h1Q⟩, disjoint_lt_row Q _ hQrow⟩,
        disjoint_map_row h2Q⟩
    refine ⟨hP'ne, hP'h, hP'l, hP'nd, hP'ch, hP'Q, hP'row,
      fun p hp => by have := walkH_site_mem_row hp; exact ⟨by omega, this.2⟩,
      fun hnone => by simp at hnone, ?_, ?_, ?_⟩
    · intro a'' b'' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact ⟨hSQne, walkH_site_head (m + 1) a' b', walkH_site_getLast (m + 1) a' b',
        walkH_site_nodup (m + 1) a' b', walkH_site_isChain_adjacent (m + 1) a' b'⟩
    · intro r' hr' c
      rw [hP'split]
      by_cases hrm : r' = m + 1
      · subst hrm; rw [hs_any, ht_any]
        have hP0 := adjInList_lt_at_row (c := c) hProw
        have hQ0 := adjInList_lt_at_row (c := c) hQrow
        have hjoin1 : (P.getLast? == some (m + 1, c.val) && S₁.head? == some (m + 1, c.val + 1)) = false ∧
            (P.getLast? == some (m + 1, c.val + 1) && S₁.head? == some (m + 1, c.val)) = false ∧
            (S₁.getLast? == some (m + 1, c.val) && Q.head? == some (m + 1, c.val + 1)) = false ∧
            (S₁.getLast? == some (m + 1, c.val + 1) && Q.head? == some (m + 1, c.val)) = false ∧
            (Q.getLast? == some (m + 1, c.val) && S₂.head? == some (m + 1, c.val + 1)) = false ∧
            (Q.getLast? == some (m + 1, c.val + 1) && S₂.head? == some (m + 1, c.val)) = false := by
          rw [hPl, hQh, hQl]
          simp only [siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)), Bool.false_and,
            Bool.and_false, and_self]
        have hS1adj := adjInList_map_row (walkH (stateOp s) a) (m + 1) c
        have hS2adj := adjInList_map_row (walkH b (stateOp t)) (m + 1) c
        have hSQadj := adjInList_map_row (walkH a' b') (m + 1) c
        rw [hP0, hQ0, hjoin1.1, hjoin1.2.1, hjoin1.2.2.1, hjoin1.2.2.2.1, hjoin1.2.2.2.2.1,
          hjoin1.2.2.2.2.2, hS1adj, hS2adj, hSQadj]
        simpa [Bool.or_false, Bool.or_assoc] using hadj c
      · have hr'm : r' < m + 1 := by omega
        have hih := hH_ih r' hr'm c
        have hS10 : adjInList S₁ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hS20 : adjInList S₂ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hSQ0 : adjInList SQ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hj0 : (P.getLast? == some (r', c.val) && S₁.head? == some (r', c.val + 1)) = false ∧
            (P.getLast? == some (r', c.val + 1) && S₁.head? == some (r', c.val)) = false ∧
            (S₁.getLast? == some (r', c.val) && Q.head? == some (r', c.val + 1)) = false ∧
            (S₁.getLast? == some (r', c.val + 1) && Q.head? == some (r', c.val)) = false ∧
            (Q.getLast? == some (r', c.val) && S₂.head? == some (r', c.val + 1)) = false ∧
            (Q.getLast? == some (r', c.val + 1) && S₂.head? == some (r', c.val)) = false := by
          rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'), Bool.false_and, Bool.and_false, and_self]
        rw [hS10, hS20, hSQ0, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
        simp only [Bool.or_false]
        exact hih
    · intro r' hr0 hr' c
      rw [hP'split]
      by_cases hrm : r' = m + 1
      · subst hrm; rw [hs_any, Nat.add_sub_cancel]
        have hP0 := adjInList_vert_lt_in (c := c) hProw
        have hQ0 := adjInList_vert_lt_in (c := c) hQrow
        have hS10 : adjInList S₁ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        have hS20 : adjInList S₂ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        have hSQ0 : adjInList SQ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        rw [hP0, hQ0, hS10, hS20, hSQ0, hPl, walkH_site_head, walkH_site_getLast, hQh, hQl, walkH_site_head]
        rw [← htop_s c]
        simp only [Bool.false_or, Bool.or_false, siteOpt_beq_same,
          siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)),
          siteOpt_beq_diff (Nat.ne_of_gt (Nat.lt_succ_self m)),
          Bool.and_self, fin_val_beq_decide, Bool.or_assoc]
      · have hr'm : r' < m + 1 := by omega
        have hih := hV_ih r' hr0 hr'm c
        have hS10 : adjInList S₁ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hS20 : adjInList S₂ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hSQ0 : adjInList SQ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hj0 : (P.getLast? == some (r' - 1, c.val) && S₁.head? == some (r', c.val)) = false ∧
            (P.getLast? == some (r', c.val) && S₁.head? == some (r' - 1, c.val)) = false ∧
            (S₁.getLast? == some (r' - 1, c.val) && Q.head? == some (r', c.val)) = false ∧
            (S₁.getLast? == some (r', c.val) && Q.head? == some (r' - 1, c.val)) = false ∧
            (Q.getLast? == some (r' - 1, c.val) && S₂.head? == some (r', c.val)) = false ∧
            (Q.getLast? == some (r', c.val) && S₂.head? == some (r' - 1, c.val)) = false := by
          rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'),
            siteOpt_beq_diff (by omega : m + 1 ≠ r' - 1), Bool.false_and, Bool.and_false, and_self]
        rw [hS10, hS20, hSQ0, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
        simp only [Bool.or_false]
        exact hih

private lemma stepPaths_succ_some_noconn_rev {n m : ℕ} {f : Fin (n + 1) → Fin 12}
    (hr : m + 1 + 1 ≤ n) {P Q : List Site} {s t : Fin 12} {a b : Fin 4}
    (hs : f ⟨m + 1, Nat.lt_succ_of_lt hr⟩ = s)
    (ht : f ⟨m + 1 + 1, Nat.succ_lt_succ hr⟩ = t)
    (hps : statePair s = some (a, b))
    (hconn_op : connH (transH s t) (stateOp s) (stateOp t) = false)
    (hdir : (connH (transH s t) (stateOp s) a && connH (transH s t) b (stateOp t)) = false)
    (hchk : rowSegmentsCheck s t = true)
    (hinv : PathInv f (m + 1) (Nat.le_of_lt hr) P Q) :
    PathInv f (m + 1 + 1) hr
      (P ++ (walkH (stateOp s) b).map (fun c : Fin 4 => (m + 1, c.val)) ++ Q.reverse ++
       (walkH a (stateOp t)).map (fun c : Fin 4 => (m + 1, c.val)))
      (match statePair t with
       | none => []
       | some (a', b') => (walkH a' b').map fun c : Fin 4 => (m + 1, c.val)) := by
  dsimp only [PathInv] at hinv ⊢
  have hs_any : ∀ h', f ⟨m + 1, h'⟩ = s := fun _ => hs
  have ht_any : ∀ h', f ⟨m + 1 + 1, h'⟩ = t := fun _ => ht
  rcases hinv with ⟨hPne, hPh, hPl, hPnd, hPch, hPQ, hProw, hQrow, _, hQsome, hH_ih, hV_ih⟩
  rw [hs_any] at hPl hQsome
  simp only [Nat.add_sub_cancel] at hPl hQsome
  rcases hQsome a b hps with ⟨hQne, hQh, hQl, hQnd, hQch⟩
  have htop_s : ∀ c : Fin 4,
      (decide (c = stateOp s) || decide (c = a) || decide (c = b)) = topMask s c := by
    intro c; simp only [topMask, hps, fin_beq_decide, Bool.or_assoc]
  simp only [rowSegmentsCheck, hps, hconn_op, Bool.false_eq_true, ↓reduceIte, hdir,
    Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq,
    decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨_, _⟩, ⟨_, hnd3⟩, hadj⟩
  rcases nodup_append_three_disj hnd3 with ⟨hnd1, hnd2, hndQ, h12, h1Q, h2Q⟩
  let rLift : Fin 4 → Site := fun c => (m + 1, c.val)
  let S₁ := (walkH (stateOp s) b).map rLift
  let S₂ := (walkH a (stateOp t)).map rLift
  let P' := P ++ S₁ ++ Q.reverse ++ S₂
  have hS1ne : S₁ ≠ [] := by simp [S₁, walkH_nonempty]
  have hS2ne : S₂ ≠ [] := by simp [S₂, walkH_nonempty]
  have hQrne : Q.reverse ≠ [] := by simp [hQne]
  have hP'ne : P' ≠ [] := by simp [P', hS2ne]
  have hP'h : P'.head? = some (0, 0) := by
    simp only [P', List.append_assoc]; rw [List.head?_append_of_ne_nil _ hPne]; exact hPh
  have hP'l : P'.getLast? = some (m + 1, (stateOp t).val) := by
    rw [List.getLast?_append_of_ne_nil _ hS2ne]; exact walkH_site_getLast (m + 1) a (stateOp t)
  have hQr_row : ∀ p ∈ Q.reverse, p.1 < m + 1 ∧ p.2 < 4 := fun p hp => hQrow p (List.mem_reverse.mp hp)
  have hPQr : List.Disjoint P Q.reverse := fun _ hx hy => hPQ hx (List.mem_reverse.mp hy)
  have hP'nd : P'.Nodup := by
    rw [List.nodup_append, List.nodup_append, List.nodup_append]
    refine ⟨⟨⟨hPnd, walkH_site_nodup (m + 1) (stateOp s) b,
      List.disjoint_iff_ne.mp (disjoint_lt_row P _ hProw)⟩, List.nodup_reverse.mpr hQnd, ?_⟩,
      walkH_site_nodup (m + 1) a (stateOp t), ?_⟩
    · rw [← List.disjoint_iff_ne, List.disjoint_append_left]
      exact ⟨hPQr, (disjoint_lt_row Q.reverse _ hQr_row).symm⟩
    · rw [← List.disjoint_iff_ne, List.disjoint_append_left, List.disjoint_append_left]
      exact ⟨⟨disjoint_lt_row P _ hProw, disjoint_map_row h12⟩, disjoint_lt_row Q.reverse _ hQr_row⟩
  have hP'ch : P'.IsChain adjacent := by
    have hQr_ch : Q.reverse.IsChain adjacent := isChain_reverse (fun _ _ => adjacent_symm) hQch
    refine isChain_append ?_ (walkH_site_isChain_adjacent (m + 1) a (stateOp t)) (by simp [hQrne]) hS2ne ?_
    · refine isChain_append ?_ hQr_ch (by simp [hS1ne]) hQrne ?_
      · refine isChain_append hPch (walkH_site_isChain_adjacent (m + 1) (stateOp s) b) hPne hS1ne ?_
        have hPl' : P.getLast hPne = (m, (stateOp s).val) := by
          rw [List.getLast_eq_iff_getLast?_eq_some]; exact hPl
        have hS1h : S₁.head hS1ne = (m + 1, (stateOp s).val) := by
          rw [List.head_eq_iff_head?_eq_some]; exact walkH_site_head (m + 1) (stateOp s) b
        rw [hPl', hS1h]; dsimp only [adjacent, Nat.dist]; omega
      · rw [List.getLast_append_of_ne_nil _ hS1ne]
        have hS1l : S₁.getLast hS1ne = (m + 1, b.val) := by
          rw [List.getLast_eq_iff_getLast?_eq_some]; exact walkH_site_getLast (m + 1) (stateOp s) b
        have hQrh : Q.reverse.head hQrne = (m, b.val) := by
          rw [List.head_eq_iff_head?_eq_some]; simpa [List.head?_reverse] using hQl
        rw [hS1l, hQrh]; dsimp only [adjacent, Nat.dist]; omega
    · rw [List.getLast_append_of_ne_nil _ hQrne]
      have hQrl : Q.reverse.getLast hQrne = (m, a.val) := by
        rw [List.getLast_eq_iff_getLast?_eq_some]; simpa [List.getLast?_reverse] using hQh
      have hS2h : S₂.head hS2ne = (m + 1, a.val) := by
        rw [List.head_eq_iff_head?_eq_some]; exact walkH_site_head (m + 1) a (stateOp t)
      rw [hQrl, hS2h]; dsimp only [adjacent, Nat.dist]; omega
  have hP'row : ∀ p ∈ P', p.1 < m + 2 ∧ p.2 < 4 := by
    intro p hp; simp only [P', List.mem_append, List.mem_reverse] at hp
    rcases hp with ((hpP | hp1) | hpQ) | hp2
    · have := hProw p hpP; exact ⟨by omega, this.2⟩
    · have := walkH_site_mem_row hp1; exact ⟨by omega, this.2⟩
    · have := hQrow p hpQ; exact ⟨by omega, this.2⟩
    · have := walkH_site_mem_row hp2; exact ⟨by omega, this.2⟩
  have hP'split : ∀ u v : Site,
      adjInList P' u v = (adjInList P u v || adjInList S₁ u v || adjInList Q u v || adjInList S₂ u v ||
        ((P.getLast? == some u && S₁.head? == some v) ||
         (P.getLast? == some v && S₁.head? == some u) ||
         (S₁.getLast? == some u && Q.reverse.head? == some v) ||
         (S₁.getLast? == some v && Q.reverse.head? == some u) ||
         (Q.reverse.getLast? == some u && S₂.head? == some v) ||
         (Q.reverse.getLast? == some v && S₂.head? == some u))) := by
    intro u v; dsimp only [P']
    rw [adjInList_append (by simp [hQrne]) hS2ne, adjInList_append (by simp [hS1ne]) hQrne,
      adjInList_append hPne hS1ne, List.getLast?_append_of_ne_nil _ hS1ne,
      List.getLast?_append_of_ne_nil _ hQrne, adjInList_reverse]
    simp only [Bool.or_assoc]
    rw [Bool.or_left_comm _ (adjInList Q u v), Bool.or_left_comm _ (adjInList Q u v)]
    rw [Bool.or_left_comm _ (adjInList S₂ u v), Bool.or_left_comm _ (adjInList S₂ u v),
      Bool.or_left_comm _ (adjInList S₂ u v), Bool.or_left_comm _ (adjInList S₂ u v)]
  rw [ht_any]
  simp only [Nat.add_sub_cancel]
  cases hpt : statePair t with
  | none =>
    simp only [hpt] at hadj
    refine ⟨hP'ne, hP'h, hP'l, hP'nd, hP'ch, by simp, hP'row, by simp,
      fun _ => by simp, fun a'' b'' hab => by simp at hab, ?_, ?_⟩
    · intro r' hr' c
      rw [hP'split, adjInList_nil_false, Bool.or_false]
      by_cases hrm : r' = m + 1
      · subst hrm; rw [hs_any, ht_any]
        have hP0 := adjInList_lt_at_row (c := c) hProw
        have hQ0 := adjInList_lt_at_row (c := c) hQrow
        have hjoin1 : (P.getLast? == some (m + 1, c.val) && S₁.head? == some (m + 1, c.val + 1)) = false ∧
            (P.getLast? == some (m + 1, c.val + 1) && S₁.head? == some (m + 1, c.val)) = false ∧
            (S₁.getLast? == some (m + 1, c.val) && Q.reverse.head? == some (m + 1, c.val + 1)) = false ∧
            (S₁.getLast? == some (m + 1, c.val + 1) && Q.reverse.head? == some (m + 1, c.val)) = false ∧
            (Q.reverse.getLast? == some (m + 1, c.val) && S₂.head? == some (m + 1, c.val + 1)) = false ∧
            (Q.reverse.getLast? == some (m + 1, c.val + 1) && S₂.head? == some (m + 1, c.val)) = false := by
          rw [hPl, List.head?_reverse, hQl, List.getLast?_reverse, hQh]
          simp only [siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)), Bool.false_and,
            Bool.and_false, and_self]
        have hS1adj := adjInList_map_row (walkH (stateOp s) b) (m + 1) c
        have hS2adj := adjInList_map_row (walkH a (stateOp t)) (m + 1) c
        have hsub : adjHList [] c = false := rfl
        rw [hP0, hQ0, hjoin1.1, hjoin1.2.1, hjoin1.2.2.1, hjoin1.2.2.2.1, hjoin1.2.2.2.2.1,
          hjoin1.2.2.2.2.2, hS1adj, hS2adj]
        simpa [Bool.or_false, hsub] using hadj c
      · have hr'm : r' < m + 1 := by omega
        have hih := hH_ih r' hr'm c
        have hS10 : adjInList S₁ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hS20 : adjInList S₂ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hj0 : (P.getLast? == some (r', c.val) && S₁.head? == some (r', c.val + 1)) = false ∧
            (P.getLast? == some (r', c.val + 1) && S₁.head? == some (r', c.val)) = false ∧
            (S₁.getLast? == some (r', c.val) && Q.reverse.head? == some (r', c.val + 1)) = false ∧
            (S₁.getLast? == some (r', c.val + 1) && Q.reverse.head? == some (r', c.val)) = false ∧
            (Q.reverse.getLast? == some (r', c.val) && S₂.head? == some (r', c.val + 1)) = false ∧
            (Q.reverse.getLast? == some (r', c.val + 1) && S₂.head? == some (r', c.val)) = false := by
          rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'), Bool.false_and, Bool.and_false, and_self]
        rw [hS10, hS20, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
        simp only [Bool.or_false]
        exact hih
    · intro r' hr0 hr' c
      rw [hP'split, adjInList_nil_false, Bool.or_false]
      by_cases hrm : r' = m + 1
      · subst hrm; rw [hs_any, Nat.add_sub_cancel]
        have hP0 := adjInList_vert_lt_in (c := c) hProw
        have hQ0 := adjInList_vert_lt_in (c := c) hQrow
        have hS10 : adjInList S₁ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        have hS20 : adjInList S₂ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        rw [hP0, hQ0, hS10, hS20, hPl, walkH_site_head, walkH_site_getLast,
          List.head?_reverse, hQl, List.getLast?_reverse, hQh, walkH_site_head]
        rw [← htop_s c]
        simp only [Bool.false_or, Bool.or_false, siteOpt_beq_same,
          siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)),
          siteOpt_beq_diff (Nat.ne_of_gt (Nat.lt_succ_self m)),
          Bool.and_self, fin_val_beq_decide, Bool.or_assoc]
        rw [Bool.or_comm (decide (c = b)) (decide (c = a))]
      · have hr'm : r' < m + 1 := by omega
        have hih := hV_ih r' hr0 hr'm c
        have hS10 : adjInList S₁ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hS20 : adjInList S₂ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hj0 : (P.getLast? == some (r' - 1, c.val) && S₁.head? == some (r', c.val)) = false ∧
            (P.getLast? == some (r', c.val) && S₁.head? == some (r' - 1, c.val)) = false ∧
            (S₁.getLast? == some (r' - 1, c.val) && Q.reverse.head? == some (r', c.val)) = false ∧
            (S₁.getLast? == some (r', c.val) && Q.reverse.head? == some (r' - 1, c.val)) = false ∧
            (Q.reverse.getLast? == some (r' - 1, c.val) && S₂.head? == some (r', c.val)) = false ∧
            (Q.reverse.getLast? == some (r', c.val) && S₂.head? == some (r' - 1, c.val)) = false := by
          rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'),
            siteOpt_beq_diff (by omega : m + 1 ≠ r' - 1), Bool.false_and, Bool.and_false, and_self]
        rw [hS10, hS20, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
        simp only [Bool.or_false]
        exact hih
  | some ab' =>
    rcases ab' with ⟨a', b'⟩
    simp only [hpt] at h1Q h2Q hadj
    let SQ := (walkH a' b').map rLift
    have hSQne : SQ ≠ [] := by simp [SQ, walkH_nonempty]
    have hP'Q : List.Disjoint P' SQ := by
      rw [List.disjoint_append_left, List.disjoint_append_left, List.disjoint_append_left]
      exact ⟨⟨⟨disjoint_lt_row P _ hProw, disjoint_map_row h1Q⟩, disjoint_lt_row Q.reverse _ hQr_row⟩,
        disjoint_map_row h2Q⟩
    refine ⟨hP'ne, hP'h, hP'l, hP'nd, hP'ch, hP'Q, hP'row,
      fun p hp => by have := walkH_site_mem_row hp; exact ⟨by omega, this.2⟩,
      fun hnone => by simp at hnone, ?_, ?_, ?_⟩
    · intro a'' b'' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact ⟨hSQne, walkH_site_head (m + 1) a' b', walkH_site_getLast (m + 1) a' b',
        walkH_site_nodup (m + 1) a' b', walkH_site_isChain_adjacent (m + 1) a' b'⟩
    · intro r' hr' c
      rw [hP'split]
      by_cases hrm : r' = m + 1
      · subst hrm; rw [hs_any, ht_any]
        have hP0 := adjInList_lt_at_row (c := c) hProw
        have hQ0 := adjInList_lt_at_row (c := c) hQrow
        have hjoin1 : (P.getLast? == some (m + 1, c.val) && S₁.head? == some (m + 1, c.val + 1)) = false ∧
            (P.getLast? == some (m + 1, c.val + 1) && S₁.head? == some (m + 1, c.val)) = false ∧
            (S₁.getLast? == some (m + 1, c.val) && Q.reverse.head? == some (m + 1, c.val + 1)) = false ∧
            (S₁.getLast? == some (m + 1, c.val + 1) && Q.reverse.head? == some (m + 1, c.val)) = false ∧
            (Q.reverse.getLast? == some (m + 1, c.val) && S₂.head? == some (m + 1, c.val + 1)) = false ∧
            (Q.reverse.getLast? == some (m + 1, c.val + 1) && S₂.head? == some (m + 1, c.val)) = false := by
          rw [hPl, List.head?_reverse, hQl, List.getLast?_reverse, hQh]
          simp only [siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)), Bool.false_and,
            Bool.and_false, and_self]
        have hS1adj := adjInList_map_row (walkH (stateOp s) b) (m + 1) c
        have hS2adj := adjInList_map_row (walkH a (stateOp t)) (m + 1) c
        have hSQadj := adjInList_map_row (walkH a' b') (m + 1) c
        rw [hP0, hQ0, hjoin1.1, hjoin1.2.1, hjoin1.2.2.1, hjoin1.2.2.2.1, hjoin1.2.2.2.2.1,
          hjoin1.2.2.2.2.2, hS1adj, hS2adj, hSQadj]
        simpa [Bool.or_false, Bool.or_assoc] using hadj c
      · have hr'm : r' < m + 1 := by omega
        have hih := hH_ih r' hr'm c
        have hS10 : adjInList S₁ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hS20 : adjInList S₂ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hSQ0 : adjInList SQ (r', c.val) (r', c.val + 1) = false := adjInList_map_row_lt (by omega)
        have hj0 : (P.getLast? == some (r', c.val) && S₁.head? == some (r', c.val + 1)) = false ∧
            (P.getLast? == some (r', c.val + 1) && S₁.head? == some (r', c.val)) = false ∧
            (S₁.getLast? == some (r', c.val) && Q.reverse.head? == some (r', c.val + 1)) = false ∧
            (S₁.getLast? == some (r', c.val + 1) && Q.reverse.head? == some (r', c.val)) = false ∧
            (Q.reverse.getLast? == some (r', c.val) && S₂.head? == some (r', c.val + 1)) = false ∧
            (Q.reverse.getLast? == some (r', c.val + 1) && S₂.head? == some (r', c.val)) = false := by
          rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'), Bool.false_and, Bool.and_false, and_self]
        rw [hS10, hS20, hSQ0, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
        simp only [Bool.or_false]
        exact hih
    · intro r' hr0 hr' c
      rw [hP'split]
      by_cases hrm : r' = m + 1
      · subst hrm; rw [hs_any, Nat.add_sub_cancel]
        have hP0 := adjInList_vert_lt_in (c := c) hProw
        have hQ0 := adjInList_vert_lt_in (c := c) hQrow
        have hS10 : adjInList S₁ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        have hS20 : adjInList S₂ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        have hSQ0 : adjInList SQ (m, c.val) (m + 1, c.val) = false := adjInList_vert_map_row_succ
        rw [hP0, hQ0, hS10, hS20, hSQ0, hPl, walkH_site_head, walkH_site_getLast,
          List.head?_reverse, hQl, List.getLast?_reverse, hQh, walkH_site_head]
        rw [← htop_s c]
        simp only [Bool.false_or, Bool.or_false, siteOpt_beq_same,
          siteOpt_beq_diff (Nat.ne_of_lt (Nat.lt_succ_self m)),
          siteOpt_beq_diff (Nat.ne_of_gt (Nat.lt_succ_self m)),
          Bool.and_self, fin_val_beq_decide, Bool.or_assoc]
        rw [Bool.or_comm (decide (c = b)) (decide (c = a))]
      · have hr'm : r' < m + 1 := by omega
        have hih := hV_ih r' hr0 hr'm c
        have hS10 : adjInList S₁ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hS20 : adjInList S₂ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hSQ0 : adjInList SQ (r' - 1, c.val) (r', c.val) = false := adjInList_vert_map_row
        have hj0 : (P.getLast? == some (r' - 1, c.val) && S₁.head? == some (r', c.val)) = false ∧
            (P.getLast? == some (r', c.val) && S₁.head? == some (r' - 1, c.val)) = false ∧
            (S₁.getLast? == some (r' - 1, c.val) && Q.reverse.head? == some (r', c.val)) = false ∧
            (S₁.getLast? == some (r', c.val) && Q.reverse.head? == some (r' - 1, c.val)) = false ∧
            (Q.reverse.getLast? == some (r' - 1, c.val) && S₂.head? == some (r', c.val)) = false ∧
            (Q.reverse.getLast? == some (r', c.val) && S₂.head? == some (r' - 1, c.val)) = false := by
          rw [walkH_site_head, walkH_site_getLast, walkH_site_head]
          simp only [siteOpt_beq_diff (by omega : m + 1 ≠ r'),
            siteOpt_beq_diff (by omega : m + 1 ≠ r' - 1), Bool.false_and, Bool.and_false, and_self]
        rw [hS10, hS20, hSQ0, hj0.1, hj0.2.1, hj0.2.2.1, hj0.2.2.2.1, hj0.2.2.2.2.1, hj0.2.2.2.2.2]
        simp only [Bool.or_false]
        exact hih

private lemma stepPaths_succ {n : ℕ} {f : Fin (n + 1) → Fin 12}
    (hfT : ∀ r : Fin n, Tmat (f r.castSucc) (f r.succ) = 1)
    {m : ℕ} (hr : m + 1 + 1 ≤ n) {P Q : List Site}
    (hinv : PathInv f (m + 1) (Nat.le_of_lt hr) P Q) :
    PathInv f (m + 1 + 1) hr
      (stepPaths (m + 1) (f ⟨m + 1, Nat.lt_succ_of_lt hr⟩) (f ⟨m + 1 + 1, Nat.succ_lt_succ hr⟩) P Q).1
      (stepPaths (m + 1) (f ⟨m + 1, Nat.lt_succ_of_lt hr⟩) (f ⟨m + 1 + 1, Nat.succ_lt_succ hr⟩) P Q).2 := by
  let s := f ⟨m + 1, Nat.lt_succ_of_lt hr⟩
  let t := f ⟨m + 1 + 1, Nat.succ_lt_succ hr⟩
  have hT : Tmat s t = 1 := hfT ⟨m + 1, hr⟩
  have hchk := rowSegmentsCheck_of_Tmat hT
  have hs_def : f ⟨m + 1, Nat.lt_succ_of_lt hr⟩ = s := rfl
  have ht_def : f ⟨m + 1 + 1, Nat.succ_lt_succ hr⟩ = t := rfl
  dsimp only [stepPaths]
  rw [hs_def, ht_def]
  cases hps : statePair s with
  | none =>
    exact stepPaths_succ_none hr rfl rfl hchk hps hinv
  | some ab =>
    rcases ab with ⟨a, b⟩
    by_cases hconn_op : connH (transH s t) (stateOp s) (stateOp t) = true
    · simp only [hconn_op, ↓reduceIte]
      have hchk_pt := hchk
      simp only [rowSegmentsCheck, hps, hconn_op, ↓reduceIte] at hchk_pt
      cases hpt : statePair t with
      | none => simp [hpt] at hchk_pt
      | some ab' =>
        rcases ab' with ⟨a', b'⟩
        by_cases hdir : (connH (transH s t) a' a && connH (transH s t) b b') = true
        · simp only [hdir, ↓reduceIte]
          exact stepPaths_succ_some_conn_dir hr rfl rfl hps hpt hconn_op hdir hchk hinv
        · have hdir' : (connH (transH s t) a' a && connH (transH s t) b b') = false :=
            Bool.eq_false_iff.mpr hdir
          simp only [hdir', Bool.false_eq_true, ↓reduceIte]
          exact stepPaths_succ_some_conn_rev hr rfl rfl hps hpt hconn_op hdir' hchk hinv
    · have hconn_op' : connH (transH s t) (stateOp s) (stateOp t) = false :=
        Bool.eq_false_iff.mpr hconn_op
      simp only [hconn_op', Bool.false_eq_true, ↓reduceIte]
      by_cases hdir : (connH (transH s t) (stateOp s) a && connH (transH s t) b (stateOp t)) = true
      · simp only [hdir, ↓reduceIte]
        exact stepPaths_succ_some_noconn_dir hr rfl rfl hps hconn_op' hdir hchk hinv
      · have hdir' : (connH (transH s t) (stateOp s) a && connH (transH s t) b (stateOp t)) = false :=
          Bool.eq_false_iff.mpr hdir
        simp only [hdir', Bool.false_eq_true, ↓reduceIte]
        exact stepPaths_succ_some_noconn_rev hr rfl rfl hps hconn_op' hdir' hchk hinv

private lemma buildPaths_spec {n : ℕ} (f : Fin (n + 1) → Fin 12)
    (hf0 : f 0 = 0) (hfT : ∀ r : Fin n, Tmat (f r.castSucc) (f r.succ) = 1) :
    ∀ r : ℕ, ∀ hr : r ≤ n, 1 ≤ r →
      let s := f ⟨r, Nat.lt_succ_of_le hr⟩
      let pq := buildPaths f r hr
      let P := pq.1
      let Q := pq.2
      P ≠ [] ∧ P.head? = some (0, 0) ∧ P.getLast? = some (r - 1, (stateOp s).val) ∧
      P.Nodup ∧ P.IsChain adjacent ∧ List.Disjoint P Q ∧
      (∀ p ∈ P, p.1 < r ∧ p.2 < 4) ∧ (∀ p ∈ Q, p.1 < r ∧ p.2 < 4) ∧
      (statePair s = none → Q = []) ∧
      (∀ a b, statePair s = some (a, b) →
        Q ≠ [] ∧ Q.head? = some (r - 1, a.val) ∧ Q.getLast? = some (r - 1, b.val) ∧
        Q.Nodup ∧ Q.IsChain adjacent) ∧
      (∀ r' : ℕ, ∀ hr' : r' < r, ∀ c : Fin 3,
        (adjInList P (r', c.val) (r', c.val + 1) || adjInList Q (r', c.val) (r', c.val + 1)) =
          transH (f ⟨r', Nat.lt_succ_of_lt (lt_of_lt_of_le hr' hr)⟩)
                 (f ⟨r' + 1, Nat.succ_lt_succ (lt_of_lt_of_le hr' hr)⟩) c) ∧
      (∀ r' : ℕ, 0 < r' → ∀ hr' : r' < r, ∀ c : Fin 4,
        (adjInList P (r' - 1, c.val) (r', c.val) || adjInList Q (r' - 1, c.val) (r', c.val)) =
          topMask (f ⟨r', Nat.lt_succ_of_lt (lt_of_lt_of_le hr' hr)⟩) c) := by
  intro r hr hr1
  change PathInv f r hr (buildPaths f r hr).1 (buildPaths f r hr).2
  induction r with
  | zero => omega
  | succ r ih =>
    rw [buildPaths]
    cases r with
    | zero => exact stepPaths_zero hf0 hfT hr
    | succ m => exact stepPaths_succ hfT hr (ih (Nat.le_of_lt hr) (by omega))

private noncomputable def walkEquivGridPath (n : ℕ) (hn : 1 ≤ n) :
    {w : List Site // isWalk n 4 (0, 0) (n - 1, 0) w} ≃ GridPath n where
  toFun x :=
    let w := x.1
    let hw := x.2
    let f : Fin (n + 1) → Fin 12 := fun r => walkStateSeq n w r.val
    have hsp := walkStateSeq_spec hn hw
    have hf0 : f 0 = 0 := rfl
    have hfn : f (Fin.last n) = 0 := by
      rw [← topMask_eq_zero_iff]
      intro c
      have htop := (hsp n (le_refl n)).1
      change topMask (walkStateSeq n w n) c = _
      rw [htop]
      simp [vFromWalk]
    have hfT : ∀ r : Fin n, Tmat (f r.castSucc) (f r.succ) = 1 := fun r =>
      validTrans_Tmat ((hsp r.val (Nat.le_of_lt r.isLt)).2.2 r.isLt)
    ⟨f, hf0, hfn, hfT⟩
  invFun g :=
    let f := g.1
    have hf0 : f 0 = 0 := g.2.1
    have hfn : f (Fin.last n) = 0 := g.2.2.1
    have hfT : ∀ r : Fin n, Tmat (f r.castSucc) (f r.succ) = 1 := g.2.2.2
    have hbp := buildPaths_spec f hf0 hfT n (le_refl n) hn
    have hflast : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := Fin.ext rfl
    have hQ : (buildPaths f n (le_refl n)).2 = [] := hbp.2.2.2.2.2.2.2.2.1 (by simp [hflast, hfn, statePair])
    ⟨(buildPaths f n (le_refl n)).1,
      ⟨hbp.2.1, by simpa [hflast, hfn, stateOp] using hbp.2.2.1, hbp.2.2.2.1, hbp.2.2.2.2.1,
       hbp.2.2.2.2.2.2.1⟩⟩
  left_inv x := by
    ext1
    dsimp only
    let f : Fin (n + 1) → Fin 12 := fun r => walkStateSeq n x.1 r.val
    have hsp := walkStateSeq_spec hn x.2
    have hf0 : f 0 = 0 := rfl
    have hfn : f (Fin.last n) = 0 := by
      rw [← topMask_eq_zero_iff]
      intro c
      change topMask (walkStateSeq n x.1 n) c = _
      rw [(hsp n (le_refl n)).1]
      simp [vFromWalk]
    have hfT : ∀ r : Fin n, Tmat (f r.castSucc) (f r.succ) = 1 := fun r =>
      validTrans_Tmat ((hsp r.val (Nat.le_of_lt r.isLt)).2.2 r.isLt)
    have hbp := buildPaths_spec f hf0 hfT n (le_refl n) hn
    have hflast : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := Fin.ext rfl
    have hQ : (buildPaths f n (le_refl n)).2 = [] := hbp.2.2.2.2.2.2.2.2.1 (by simp [hflast, hfn, statePair])
    let w' := (buildPaths f n (le_refl n)).1
    have hw' : isWalk n 4 (0, 0) (n - 1, 0) w' :=
      ⟨hbp.2.1, by simpa [hflast, hfn, stateOp] using hbp.2.2.1, hbp.2.2.2.1, hbp.2.2.2.2.1,
       hbp.2.2.2.2.2.2.1⟩
    have hnil : ∀ u v : Site, adjInList [] u v = false := fun _ _ => rfl
    refine walk_eq_of_edges_eq hn hw' x.2 ?_ ?_
    · intro r
      ext c
      have h1 := hbp.2.2.2.2.2.2.2.2.2.2.1 r.val r.isLt c
      rw [hQ] at h1
      have hvt := (hsp r.val (Nat.le_of_lt r.isLt)).2.2 r.isLt
      have heq := (validTrans_eq_transH hvt).1
      simp only [hnil, Bool.or_false] at h1
      change hFromWalk w' r.val c = hFromWalk x.1 r.val c
      rw [hFromWalk, h1, ← heq]
    · intro r
      ext c
      by_cases hr0 : r.val = 0
      · simp [vFromWalk, hr0]
      · by_cases hrn : r.val = n
        · simp [vFromWalk, hrn]
        · have h1 := hbp.2.2.2.2.2.2.2.2.2.2.2 r.val (Nat.pos_of_ne_zero hr0) (by omega) c
          rw [hQ] at h1
          have htop := (hsp r.val (by omega)).1
          simp only [hnil, Bool.or_false] at h1
          have hvL : vFromWalk w' n r.val c = adjInList w' (r.val - 1, c.val) (r.val, c.val) := by
            simp [vFromWalk, hr0, hrn]
          have htopc : topMask (f ⟨r.val, r.isLt⟩) c = vFromWalk x.1 n r.val c :=
            congrFun htop c
          change vFromWalk w' n r.val c = vFromWalk x.1 n r.val c
          rw [hvL, h1, htopc]
  right_inv g := by
    apply Subtype.ext
    funext r
    dsimp only
    let f := g.1
    have hf0 : f 0 = 0 := g.2.1
    have hfn : f (Fin.last n) = 0 := g.2.2.1
    have hfT : ∀ r' : Fin n, Tmat (f r'.castSucc) (f r'.succ) = 1 := g.2.2.2
    have hbp := buildPaths_spec f hf0 hfT n (le_refl n) hn
    have hflast : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := Fin.ext rfl
    have hQ : (buildPaths f n (le_refl n)).2 = [] := hbp.2.2.2.2.2.2.2.2.1 (by simp [hflast, hfn, statePair])
    let w' := (buildPaths f n (le_refl n)).1
    have hnil : ∀ u v : Site, adjInList [] u v = false := fun _ _ => rfl
    suffices h : ∀ k : ℕ, ∀ hk : k ≤ n, walkStateSeq n w' k = f ⟨k, Nat.lt_succ_of_le hk⟩ from
      h r.val (Nat.le_of_lt_succ r.isLt)
    intro k hk
    induction k with
    | zero => exact hf0.symm
    | succ k ihk =>
      have hk1 : k ≤ n := Nat.le_of_lt hk
      have hprev := ihk hk1
      rw [walkStateSeq, hprev]
      have hvt := validTrans_transH_spec (hfT ⟨k, hk⟩)
      have hh : hFromWalk w' k = transH (f ⟨k, Nat.lt_succ_of_le hk1⟩) (f ⟨k + 1, Nat.succ_lt_succ hk⟩) := by
        ext c
        have h1 := hbp.2.2.2.2.2.2.2.2.2.2.1 k hk c
        rw [hQ] at h1
        simpa [hFromWalk, hnil] using h1
      have hbot : vFromWalk w' n (k + 1) = topMask (f ⟨k + 1, Nat.succ_lt_succ hk⟩) := by
        ext c
        by_cases hkn : k + 1 = n
        · have heq : (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (n + 1)) = Fin.last n := Fin.ext hkn
          rw [heq, hfn]
          fin_cases c <;> simp [vFromWalk, hkn, topMask, stateOp, statePair]
        · have h1 := hbp.2.2.2.2.2.2.2.2.2.2.2 (k + 1) (Nat.succ_pos k) (by omega) c
          rw [hQ] at h1
          simp only [vFromWalk, Nat.succ_ne_zero, ↓reduceIte, hkn, Nat.add_sub_cancel]
          simpa [hnil] using h1
      rw [hh, hbot]
      exact (eq_nextState_of_validTrans hvt).symm

private noncomputable def GridPathTo (n : ℕ) (t : Fin 12) : Type :=
  {f : Fin (n + 1) → Fin 12 //
    f 0 = 0 ∧ f (Fin.last n) = t ∧ ∀ r : Fin n, Tmat (f r.castSucc) (f r.succ) = 1}

private noncomputable instance (n : ℕ) (t : Fin 12) : Fintype (GridPathTo n t) :=
  Subtype.fintype _

private lemma card_gridPathTo (n : ℕ) (t : Fin 12) :
    (Fintype.card (GridPathTo n t) : ℤ) = (Tmat ^ n) 0 t := by
  induction n generalizing t with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    have heq : Fintype.card (GridPathTo 0 t) = if (0 : Fin 12) = t then 1 else 0 := by
      by_cases ht : (0 : Fin 12) = t
      · subst ht
        simp only [↓reduceIte, Fintype.card_eq_one_iff]
        refine ⟨⟨fun _ => 0, rfl, rfl, fun r => Fin.elim0 r⟩, fun f => ?_⟩
        apply Subtype.ext
        funext i
        fin_cases i
        exact f.2.1
      · simp only [ht, ↓reduceIte, Fintype.card_eq_zero_iff]
        refine ⟨fun f => ht (f.2.1.symm.trans f.2.2.1)⟩
    rw [heq]
    split_ifs <;> rfl
  | succ n ih =>
    have heq : GridPathTo (n + 1) t ≃
        Σ s : {s : Fin 12 // Tmat s t = 1}, GridPathTo n s.1 :=
      { toFun := fun g =>
          ⟨⟨g.1 ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩, by
            have hsucc : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).succ = Fin.last (n + 1) := Fin.ext rfl
            have hcs : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).castSucc =
                ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ := Fin.ext rfl
            have hs := g.2.2.2 ⟨n, Nat.lt_succ_self n⟩
            rwa [hcs, hsucc, g.2.2.1] at hs⟩,
           ⟨fun r => g.1 r.castSucc, g.2.1, rfl, fun r => by
             have hsuc : r.castSucc.succ = r.succ.castSucc :=
               Fin.ext (by simp [Fin.val_succ, Fin.val_castSucc])
             have hs := g.2.2.2 r.castSucc
             simpa only [hsuc] using hs⟩⟩
        invFun := fun ⟨s, g⟩ =>
          ⟨Fin.snoc g.1 t,
           by
             rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from Fin.ext rfl,
               Fin.snoc_castSucc]
             exact g.2.1,
           by simp [Fin.snoc_last],
           fun r => by
             refine Fin.lastCases ?_ ?_ r
             · have hsucc : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext rfl
               rw [hsucc, Fin.snoc_last, Fin.snoc_castSucc, g.2.2.1]
               exact s.2
             · intro r'
               have hsuc : r'.castSucc.succ = r'.succ.castSucc :=
                 Fin.ext (by simp [Fin.val_succ, Fin.val_castSucc])
               rw [hsuc, Fin.snoc_castSucc, Fin.snoc_castSucc]
               exact g.2.2.2 r'⟩
        left_inv := fun g => by
          apply Subtype.ext
          funext i
          refine Fin.lastCases ?_ ?_ i
          · simpa [Fin.snoc_last] using g.2.2.1.symm
          · intro j
            simp [Fin.snoc_castSucc]
        right_inv := fun ⟨s, g⟩ => by
          have hlastn : (⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ : Fin (n + 2)) =
              (Fin.last n).castSucc := Fin.ext rfl
          have hfst : Fin.snoc (α := fun _ => Fin 12) g.1 t ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ = s.1 := by
            rw [hlastn, Fin.snoc_castSucc]
            exact g.2.2.1
          have hheq : ∀ {a b : Fin 12} (_ : a = b) (x : GridPathTo n a) (y : GridPathTo n b),
              x.1 = y.1 → HEq x y := by
            rintro a b rfl x y h
            exact heq_of_eq (Subtype.ext h)
          refine Sigma.ext (Subtype.ext hfst) ?_
          exact hheq hfst _ g (funext fun r => by simp [Fin.snoc_castSucc]) }
    rw [Fintype.card_congr heq, Fintype.card_sigma, Nat.cast_sum]
    have hsum : (∑ s : {s : Fin 12 // Tmat s t = 1}, (Fintype.card (GridPathTo n s.1) : ℤ)) =
        ∑ s : Fin 12, (Tmat ^ n) 0 s * Tmat s t := by
      have hsum0 : (∑ s : {s : Fin 12 // Tmat s t = 1}, (Fintype.card (GridPathTo n s.1) : ℤ)) =
          ∑ s : {s : Fin 12 // Tmat s t = 1}, ((Tmat ^ n) 0 s.1 * Tmat s.1 t) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [ih s.1, s.2, mul_one]
      rw [hsum0, ← Finset.sum_subtype (Finset.univ.filter fun s => Tmat s t = 1) (fun s => by simp)
        (fun s => (Tmat ^ n) 0 s * Tmat s t)]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => Tmat s t = 1)
        (fun s => (Tmat ^ n) 0 s * Tmat s t)]
      have hzero : ∑ s ∈ Finset.univ.filter (fun s => ¬ Tmat s t = 1), (Tmat ^ n) 0 s * Tmat s t = 0 := by
        refine Finset.sum_eq_zero fun s hs => ?_
        have hne : Tmat s t ≠ 1 := (Finset.mem_filter.mp hs).2
        rcases Tmat_zero_one s t with h0 | h1
        · rw [h0, mul_zero]
        · exact absurd h1 hne
      rw [hzero, add_zero]
    rw [hsum, pow_succ, Matrix.mul_apply]

private lemma count_zero : count 0 = 0 := by
  rw [count]
  have hemp : IsEmpty {w : List Site // isWalk 0 4 (0, 0) (0 - 1, 0) w} := by
    refine ⟨fun ⟨w, hw⟩ => ?_⟩
    have h00 : (0, 0) ∈ w := List.mem_of_head? hw.1
    have hbd := hw.2.2.2.2 (0, 0) h00
    omega
  simp [Nat.card_of_isEmpty]

private lemma count_pos {n : ℕ} (hn : 1 ≤ n) : count n = (Tmat ^ n) 0 0 := by
  rw [count, Nat.card_congr (walkEquivGridPath n hn), Nat.card_eq_fintype_card]
  have hgp : Fintype.card (GridPath n) = Fintype.card (GridPathTo n 0) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hgp, card_gridPathTo n 0]

private lemma count_recurrence (n : ℕ) :
    count (n + 13) =
      12 * count (n + 12) - 54 * count (n + 11) + 124 * count (n + 10) -
        133 * count (n + 9) - 16 * count (n + 8) + 175 * count (n + 7) -
        94 * count (n + 6) - 69 * count (n + 5) + 40 * count (n + 4) +
        12 * count (n + 3) - 4 * count (n + 2) - count (n + 1) := by
  have hmul : Tmat ^ (n + 1) *
      (Tmat ^ 12 - 12 • Tmat ^ 11 + 54 • Tmat ^ 10 - 124 • Tmat ^ 9 + 133 • Tmat ^ 8 +
        16 • Tmat ^ 7 - 175 • Tmat ^ 6 + 94 • Tmat ^ 5 + 69 • Tmat ^ 4 - 40 • Tmat ^ 3 -
        12 • Tmat ^ 2 + 4 • Tmat ^ 1 + 1) = 0 := by
    rw [Tmat_char, mul_zero]
  simp only [mul_add, mul_sub, mul_smul_comm, mul_one, ← pow_add] at hmul
  have hentry := congrArg (fun M : Matrix (Fin 12) (Fin 12) ℤ => M 0 0) hmul
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply] at hentry
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hentry
  rw [show n + 1 + 12 = n + 13 by omega, show n + 1 + 11 = n + 12 by omega,
    show n + 1 + 10 = n + 11 by omega, show n + 1 + 9 = n + 10 by omega,
    show n + 1 + 8 = n + 9 by omega, show n + 1 + 7 = n + 8 by omega,
    show n + 1 + 6 = n + 7 by omega, show n + 1 + 5 = n + 6 by omega,
    show n + 1 + 4 = n + 5 by omega, show n + 1 + 3 = n + 4 by omega,
    show n + 1 + 2 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega] at hentry
  rw [← count_pos (by omega : 1 ≤ n + 13), ← count_pos (by omega : 1 ≤ n + 12),
    ← count_pos (by omega : 1 ≤ n + 11), ← count_pos (by omega : 1 ≤ n + 10),
    ← count_pos (by omega : 1 ≤ n + 9), ← count_pos (by omega : 1 ≤ n + 8),
    ← count_pos (by omega : 1 ≤ n + 7), ← count_pos (by omega : 1 ≤ n + 6),
    ← count_pos (by omega : 1 ≤ n + 5), ← count_pos (by omega : 1 ≤ n + 4),
    ← count_pos (by omega : 1 ≤ n + 3), ← count_pos (by omega : 1 ≤ n + 2),
    ← count_pos (by omega : 1 ≤ n + 1)] at hentry
  linarith

private lemma count_1 : count 1 = 1 := by
  rw [count_pos (by omega), tpow_1]; decide
private lemma count_2 : count 2 = 4 := by
  rw [count_pos (by omega), tpow_2]; decide
private lemma count_3 : count 3 = 28 := by
  rw [count_pos (by omega), tpow_3]; decide
private lemma count_4 : count 4 = 178 := by
  rw [count_pos (by omega), tpow_4]; decide
private lemma count_5 : count 5 = 1008 := by
  rw [count_pos (by omega), tpow_5]; decide
private lemma count_6 : count 6 = 5493 := by
  rw [count_pos (by omega), tpow_6]; decide
private lemma count_7 : count 7 = 29879 := by
  rw [count_pos (by omega), tpow_7]; decide
private lemma count_8 : count 8 = 163357 := by
  rw [count_pos (by omega), tpow_8]; decide
private lemma count_9 : count 9 = 895519 := by
  rw [count_pos (by omega), tpow_9]; decide
private lemma count_10 : count 10 = 4911542 := by
  rw [count_pos (by omega), tpow_10]; decide
private lemma count_11 : count 11 = 26932856 := by
  rw [count_pos (by omega), tpow_11]; decide
private lemma count_12 : count 12 = 147666219 := by
  rw [count_pos (by omega), tpow_12]; decide

private lemma coeff_mul_X_pow_exact (f : PowerSeries ℤ) (k m : ℕ) :
    PowerSeries.coeff m (f * (PowerSeries.X : PowerSeries ℤ) ^ k) =
      if k ≤ m then PowerSeries.coeff (m - k) f else 0 := by
  by_cases hk : k ≤ m
  · simp only [hk, ↓reduceIte]
    rw [show m = (m - k) + k by omega, PowerSeries.coeff_mul_X_pow, Nat.add_sub_cancel]
  · simp only [hk, ↓reduceIte]
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hp2 : p.2 ≠ k := by omega
    rw [PowerSeries.coeff_X_pow]
    simp [hp2]

private def dVec : Fin 13 → ℤ := ![1, -12, 54, -124, 133, 16, -175, 94, 69, -40, -12, 4, 1]
private def nVec : Fin 13 → ℤ := ![0, 1, -8, 34, -66, 21, 85, -64, -45, 26, 11, -3, -1]

end OMA.S_oeis_a216211_proof

open scoped BigOperators
open OMA.S_oeis_a216211 OMA.S_oeis_a216211_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a216211.main := by
  constructor
  · dsimp only
    let x : PowerSeries ℤ := PowerSeries.X
    have hD :
        ((1 - 8 * x + 15 * x ^ 2 - 5 * x ^ 3 - 9 * x ^ 4 + 2 * x ^ 5 + x ^ 6) *
          (1 - 4 * x + 7 * x ^ 2 - 3 * x ^ 3 - 7 * x ^ 4 + 2 * x ^ 5 + x ^ 6)) =
          ∑ i : Fin 13, PowerSeries.C (dVec i) * x ^ i.val := by
      simp [Fin.sum_univ_succ, dVec]
      ring
    have hN :
        x * (1 - 8 * x + 34 * x ^ 2 - 66 * x ^ 3 + 21 * x ^ 4 + 85 * x ^ 5 - 64 * x ^ 6 -
          45 * x ^ 7 + 26 * x ^ 8 + 11 * x ^ 9 - 3 * x ^ 10 - x ^ 11) =
          ∑ i : Fin 13, PowerSeries.C (nVec i) * x ^ i.val := by
      simp [Fin.sum_univ_succ, nVec]
      ring
    rw [hD, hN]
    ext m
    rw [Finset.mul_sum, map_sum, map_sum]
    have hL : ∀ i : Fin 13,
        PowerSeries.coeff m (PowerSeries.mk count * (PowerSeries.C (dVec i) * x ^ i.val)) =
          dVec i * (if i.val ≤ m then count (m - i.val) else 0) := by
      intro i
      rw [mul_left_comm, PowerSeries.coeff_C_mul, coeff_mul_X_pow_exact, PowerSeries.coeff_mk]
    have hR : ∀ i : Fin 13,
        PowerSeries.coeff m (PowerSeries.C (nVec i) * x ^ i.val) =
          if m = i.val then nVec i else 0 := by
      intro i
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      split_ifs <;> ring
    simp_rw [hL, hR]
    rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1, count_2]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1, count_2, count_3]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1, count_2, count_3, count_4]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1, count_2, count_3, count_4, count_5]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1, count_2, count_3, count_4,
        count_5, count_6]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1, count_2, count_3, count_4,
        count_5, count_6, count_7]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1, count_2, count_3, count_4,
        count_5, count_6, count_7, count_8]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1, count_2, count_3, count_4,
        count_5, count_6, count_7, count_8, count_9]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1, count_2, count_3, count_4,
        count_5, count_6, count_7, count_8, count_9, count_10]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1, count_2, count_3, count_4,
        count_5, count_6, count_7, count_8, count_9, count_10, count_11]
    · simp [Fin.sum_univ_succ, dVec, nVec, count_zero, count_1, count_2, count_3, count_4,
        count_5, count_6, count_7, count_8, count_9, count_10, count_11, count_12]
    · have hrec := count_recurrence k
      simp [Fin.sum_univ_succ, dVec, nVec]
      linarith
  · exact count_recurrence
