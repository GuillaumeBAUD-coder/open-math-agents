import OMAReductions.R_OeisA262403_conjecture_2_R1

-- Step OeisA262403.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA262403.conjecture_2.R1
-- Credit: @luciusacarr
-- Proof by reflection: a trial-division prime test (sound via `Nat.minFac`), prime counts
-- chained between consecutive triangular numbers, and a balanced lookup table for
-- `π(T(x))`, `x ≤ 727`, so that `a n` is evaluated by the kernel.

namespace OMA.A262403H1

/-- The primes up to 514 (note `515 ^ 2 = 265225 > T(727) + 1`). -/
def ps : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509]

/-- Trial division by the primes of `l` up to `√n`. -/
def chk (n : ℕ) : List ℕ → Bool
  | [] => true
  | p :: l => if n < p * p then true else if n % p = 0 then false else chk n l

/-- Primality test, correct below `265225`. -/
def isP (n : ℕ) : Bool := decide (2 ≤ n) && chk n ps

theorem ps_sorted : ps.Pairwise (· ≤ ·) := by decide +kernel

theorem ps_two_le : ∀ p ∈ ps, 2 ≤ p := by decide +kernel

theorem ps_cover : ∀ m < 515, Nat.Prime m → m ∈ ps := by decide +kernel

theorem chk_sound (n : ℕ) (l : List ℕ) :
    l.Pairwise (· ≤ ·) → chk n l = true → ∀ p ∈ l, p * p ≤ n → ¬ p ∣ n := by
  induction l with
  | nil =>
    intro _ _ p hp
    simp at hp
  | cons q l ih =>
    intro hs hc p hp hpn hd
    rw [List.pairwise_cons] at hs
    rw [chk] at hc
    by_cases h1 : n < q * q
    · rcases List.mem_cons.mp hp with rfl | hp'
      · exact absurd (lt_of_lt_of_le h1 hpn) (lt_irrefl n)
      · have hqp : q ≤ p := hs.1 p hp'
        exact absurd (lt_of_lt_of_le h1 (le_trans (Nat.mul_le_mul hqp hqp) hpn)) (lt_irrefl n)
    · by_cases h2 : n % q = 0
      · rw [if_neg h1, if_pos h2] at hc
        exact absurd hc (by decide)
      · rw [if_neg h1, if_neg h2] at hc
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact h2 (Nat.mod_eq_zero_of_dvd hd)
        · exact ih hs.2 hc p hp' hpn hd

theorem chk_complete (n : ℕ) (hn : n.Prime) (l : List ℕ) :
    (∀ p ∈ l, 2 ≤ p) → chk n l = true := by
  induction l with
  | nil => intro _; rfl
  | cons q l ih =>
    intro hl
    have hq2 : 2 ≤ q := hl q (List.mem_cons_self ..)
    rw [chk]
    by_cases h1 : n < q * q
    · rw [if_pos h1]
    · by_cases h2 : n % q = 0
      · exfalso
        rcases hn.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero h2) with h | h
        · omega
        · rw [← h] at h1
          exact h1 (lt_of_lt_of_le (by omega : q < q * 2) (Nat.mul_le_mul (le_refl q) hq2))
      · rw [if_neg h1, if_neg h2]
        exact ih (fun p hp => hl p (List.mem_cons_of_mem _ hp))

theorem isP_iff (n : ℕ) (hn : n < 265225) : isP n = true ↔ Nat.Prime n := by
  simp only [isP, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h2, hc⟩
    by_contra hnp
    have hn1 : n ≠ 1 := by omega
    have hsq : n.minFac * n.minFac ≤ n := by
      have := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
      rwa [pow_two] at this
    have hle : n.minFac < 515 := by
      by_contra h
      have h' : 515 ≤ n.minFac := by omega
      have := Nat.mul_le_mul h' h'
      omega
    exact chk_sound n ps ps_sorted hc _ (ps_cover _ hle (Nat.minFac_prime hn1)) hsq
      (Nat.minFac_dvd n)
  · intro hp
    exact ⟨hp.two_le, chk_complete n hp ps ps_two_le⟩

/-- Number of primes in `[a, a + b)`. -/
def cntFrom (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => cntFrom a b + if isP (a + b) then 1 else 0

theorem count_eq (a : ℕ) :
    ∀ b, a + b ≤ 265225 → Nat.count Nat.Prime (a + b) = Nat.count Nat.Prime a + cntFrom a b
  | 0, _ => by simp [cntFrom]
  | b + 1, h => by
    rw [show a + (b + 1) = (a + b) + 1 by omega, Nat.count_succ, count_eq a b (by omega)]
    show _ = _ + (cntFrom a b + if isP (a + b) then 1 else 0)
    have hp := isP_iff (a + b) (by omega)
    by_cases hA : Nat.Prime (a + b)
    · rw [if_pos hA, if_pos (hp.mpr hA)]
      all_goals omega
    · rw [if_neg hA, if_neg (fun h => hA (hp.mp h))]
      all_goals omega

/-- `g x = π(T(x))` for `x ≤ 727`, as a balanced lookup tree. -/
def g (x : ℕ) : ℕ :=
  if x < 364 then
    if x < 182 then
      if x < 91 then
        if x < 45 then
          if x < 22 then
            if x < 11 then
              if x < 5 then
                if x < 2 then
                  if x < 1 then
                    0
                  else
                    0
                else
                  if x < 3 then
                    2
                  else
                    if x < 4 then
                      3
                    else
                      4
              else
                if x < 8 then
                  if x < 6 then
                    6
                  else
                    if x < 7 then
                      8
                    else
                      9
                else
                  if x < 9 then
                    11
                  else
                    if x < 10 then
                      14
                    else
                      16
            else
              if x < 16 then
                if x < 13 then
                  if x < 12 then
                    18
                  else
                    21
                else
                  if x < 14 then
                    24
                  else
                    if x < 15 then
                      27
                    else
                      30
              else
                if x < 19 then
                  if x < 17 then
                    32
                  else
                    if x < 18 then
                      36
                    else
                      39
                else
                  if x < 20 then
                    42
                  else
                    if x < 21 then
                      46
                    else
                      50
          else
            if x < 33 then
              if x < 27 then
                if x < 24 then
                  if x < 23 then
                    54
                  else
                    58
                else
                  if x < 25 then
                    62
                  else
                    if x < 26 then
                      66
                    else
                      70
              else
                if x < 30 then
                  if x < 28 then
                    74
                  else
                    if x < 29 then
                      79
                    else
                      84
                else
                  if x < 31 then
                    90
                  else
                    if x < 32 then
                      94
                    else
                      99
            else
              if x < 39 then
                if x < 36 then
                  if x < 34 then
                    102
                  else
                    if x < 35 then
                      108
                    else
                      114
                else
                  if x < 37 then
                    121
                  else
                    if x < 38 then
                      126
                    else
                      131
              else
                if x < 42 then
                  if x < 40 then
                    137
                  else
                    if x < 41 then
                      141
                    else
                      149
                else
                  if x < 43 then
                    154
                  else
                    if x < 44 then
                      160
                    else
                      166
        else
          if x < 68 then
            if x < 56 then
              if x < 50 then
                if x < 47 then
                  if x < 46 then
                    174
                  else
                    180
                else
                  if x < 48 then
                    188
                  else
                    if x < 49 then
                      193
                    else
                      200
              else
                if x < 53 then
                  if x < 51 then
                    205
                  else
                    if x < 52 then
                      216
                    else
                      220
                else
                  if x < 54 then
                    226
                  else
                    if x < 55 then
                      235
                    else
                      242
            else
              if x < 62 then
                if x < 59 then
                  if x < 57 then
                    250
                  else
                    if x < 58 then
                      259
                    else
                      267
                else
                  if x < 60 then
                    274
                  else
                    if x < 61 then
                      281
                    else
                      290
              else
                if x < 65 then
                  if x < 63 then
                    297
                  else
                    if x < 64 then
                      305
                    else
                      312
                else
                  if x < 66 then
                    324
                  else
                    if x < 67 then
                      329
                    else
                      338
          else
            if x < 79 then
              if x < 73 then
                if x < 70 then
                  if x < 69 then
                    347
                  else
                    358
                else
                  if x < 71 then
                    367
                  else
                    if x < 72 then
                      374
                    else
                      381
              else
                if x < 76 then
                  if x < 74 then
                    393
                  else
                    if x < 75 then
                      403
                    else
                      413
                else
                  if x < 77 then
                    422
                  else
                    if x < 78 then
                      431
                    else
                      440
            else
              if x < 85 then
                if x < 82 then
                  if x < 80 then
                    446
                  else
                    if x < 81 then
                      457
                    else
                      467
                else
                  if x < 83 then
                    478
                  else
                    if x < 84 then
                      487
                    else
                      499
              else
                if x < 88 then
                  if x < 86 then
                    510
                  else
                    if x < 87 then
                      522
                    else
                      531
                else
                  if x < 89 then
                    541
                  else
                    if x < 90 then
                      552
                    else
                      564
      else
        if x < 136 then
          if x < 113 then
            if x < 102 then
              if x < 96 then
                if x < 93 then
                  if x < 92 then
                    574
                  else
                    587
                else
                  if x < 94 then
                    596
                  else
                    if x < 95 then
                      607
                    else
                      617
              else
                if x < 99 then
                  if x < 97 then
                    629
                  else
                    if x < 98 then
                      640
                    else
                      650
                else
                  if x < 100 then
                    661
                  else
                    if x < 101 then
                      675
                    else
                      686
            else
              if x < 107 then
                if x < 104 then
                  if x < 103 then
                    697
                  else
                    708
                else
                  if x < 105 then
                    721
                  else
                    if x < 106 then
                      734
                    else
                      747
              else
                if x < 110 then
                  if x < 108 then
                    757
                  else
                    if x < 109 then
                      775
                    else
                      783
                else
                  if x < 111 then
                    796
                  else
                    if x < 112 then
                      808
                    else
                      823
          else
            if x < 124 then
              if x < 118 then
                if x < 115 then
                  if x < 114 then
                    836
                  else
                    847
                else
                  if x < 116 then
                    859
                  else
                    if x < 117 then
                      873
                    else
                      887
              else
                if x < 121 then
                  if x < 119 then
                    903
                  else
                    if x < 120 then
                      914
                    else
                      928
                else
                  if x < 122 then
                    938
                  else
                    if x < 123 then
                      950
                    else
                      968
            else
              if x < 130 then
                if x < 127 then
                  if x < 125 then
                    982
                  else
                    if x < 126 then
                      994
                    else
                      1007
                else
                  if x < 128 then
                    1022
                  else
                    if x < 129 then
                      1035
                    else
                      1049
              else
                if x < 133 then
                  if x < 131 then
                    1061
                  else
                    if x < 132 then
                      1076
                    else
                      1093
                else
                  if x < 134 then
                    1108
                  else
                    if x < 135 then
                      1124
                    else
                      1137
        else
          if x < 159 then
            if x < 147 then
              if x < 141 then
                if x < 138 then
                  if x < 137 then
                    1152
                  else
                    1170
                else
                  if x < 139 then
                    1184
                  else
                    if x < 140 then
                      1199
                    else
                      1217
              else
                if x < 144 then
                  if x < 142 then
                    1231
                  else
                    if x < 143 then
                      1246
                    else
                      1262
                else
                  if x < 145 then
                    1277
                  else
                    if x < 146 then
                      1290
                    else
                      1308
            else
              if x < 153 then
                if x < 150 then
                  if x < 148 then
                    1322
                  else
                    if x < 149 then
                      1336
                    else
                      1354
                else
                  if x < 151 then
                    1369
                  else
                    if x < 152 then
                      1383
                    else
                      1398
              else
                if x < 156 then
                  if x < 154 then
                    1411
                  else
                    if x < 155 then
                      1430
                    else
                      1446
                else
                  if x < 157 then
                    1463
                  else
                    if x < 158 then
                      1480
                    else
                      1500
          else
            if x < 170 then
              if x < 164 then
                if x < 161 then
                  if x < 160 then
                    1518
                  else
                    1532
                else
                  if x < 162 then
                    1553
                  else
                    if x < 163 then
                      1570
                    else
                      1585
              else
                if x < 167 then
                  if x < 165 then
                    1602
                  else
                    if x < 166 then
                      1619
                    else
                      1637
                else
                  if x < 168 then
                    1654
                  else
                    if x < 169 then
                      1669
                    else
                      1683
            else
              if x < 176 then
                if x < 173 then
                  if x < 171 then
                    1701
                  else
                    if x < 172 then
                      1720
                    else
                      1742
                else
                  if x < 174 then
                    1757
                  else
                    if x < 175 then
                      1776
                    else
                      1799
              else
                if x < 179 then
                  if x < 177 then
                    1816
                  else
                    if x < 178 then
                      1837
                    else
                      1857
                else
                  if x < 180 then
                    1875
                  else
                    if x < 181 then
                      1891
                    else
                      1908
    else
      if x < 273 then
        if x < 227 then
          if x < 204 then
            if x < 193 then
              if x < 187 then
                if x < 184 then
                  if x < 183 then
                    1926
                  else
                    1943
                else
                  if x < 185 then
                    1961
                  else
                    if x < 186 then
                      1981
                    else
                      2000
              else
                if x < 190 then
                  if x < 188 then
                    2020
                  else
                    if x < 189 then
                      2039
                    else
                      2057
                else
                  if x < 191 then
                    2080
                  else
                    if x < 192 then
                      2101
                    else
                      2122
            else
              if x < 198 then
                if x < 195 then
                  if x < 194 then
                    2137
                  else
                    2152
                else
                  if x < 196 then
                    2169
                  else
                    if x < 197 then
                      2188
                    else
                      2213
              else
                if x < 201 then
                  if x < 199 then
                    2230
                  else
                    if x < 200 then
                      2250
                    else
                      2271
                else
                  if x < 202 then
                    2293
                  else
                    if x < 203 then
                      2313
                    else
                      2330
          else
            if x < 215 then
              if x < 209 then
                if x < 206 then
                  if x < 205 then
                    2352
                  else
                    2373
                else
                  if x < 207 then
                    2394
                  else
                    if x < 208 then
                      2416
                    else
                      2437
              else
                if x < 212 then
                  if x < 210 then
                    2460
                  else
                    if x < 211 then
                      2484
                    else
                      2502
                else
                  if x < 213 then
                    2524
                  else
                    if x < 214 then
                      2547
                    else
                      2565
            else
              if x < 221 then
                if x < 218 then
                  if x < 216 then
                    2591
                  else
                    if x < 217 then
                      2609
                    else
                      2631
                else
                  if x < 219 then
                    2654
                  else
                    if x < 220 then
                      2679
                    else
                      2700
              else
                if x < 224 then
                  if x < 222 then
                    2721
                  else
                    if x < 223 then
                      2738
                    else
                      2759
                else
                  if x < 225 then
                    2781
                  else
                    if x < 226 then
                      2803
                    else
                      2825
        else
          if x < 250 then
            if x < 238 then
              if x < 232 then
                if x < 229 then
                  if x < 228 then
                    2847
                  else
                    2868
                else
                  if x < 230 then
                    2893
                  else
                    if x < 231 then
                      2915
                    else
                      2939
              else
                if x < 235 then
                  if x < 233 then
                    2963
                  else
                    if x < 234 then
                      2984
                    else
                      3004
                else
                  if x < 236 then
                    3022
                  else
                    if x < 237 then
                      3052
                    else
                      3074
            else
              if x < 244 then
                if x < 241 then
                  if x < 239 then
                    3095
                  else
                    if x < 240 then
                      3124
                    else
                      3147
                else
                  if x < 242 then
                    3169
                  else
                    if x < 243 then
                      3195
                    else
                      3217
              else
                if x < 247 then
                  if x < 245 then
                    3238
                  else
                    if x < 246 then
                      3259
                    else
                      3282
                else
                  if x < 248 then
                    3302
                  else
                    if x < 249 then
                      3330
                    else
                      3352
          else
            if x < 261 then
              if x < 255 then
                if x < 252 then
                  if x < 251 then
                    3380
                  else
                    3401
                else
                  if x < 253 then
                    3424
                  else
                    if x < 254 then
                      3447
                    else
                      3476
              else
                if x < 258 then
                  if x < 256 then
                    3503
                  else
                    if x < 257 then
                      3525
                    else
                      3553
                else
                  if x < 259 then
                    3578
                  else
                    if x < 260 then
                      3607
                    else
                      3632
            else
              if x < 267 then
                if x < 264 then
                  if x < 262 then
                    3653
                  else
                    if x < 263 then
                      3679
                    else
                      3707
                else
                  if x < 265 then
                    3731
                  else
                    if x < 266 then
                      3754
                    else
                      3780
              else
                if x < 270 then
                  if x < 268 then
                    3801
                  else
                    if x < 269 then
                      3829
                    else
                      3854
                else
                  if x < 271 then
                    3879
                  else
                    if x < 272 then
                      3907
                    else
                      3935
      else
        if x < 318 then
          if x < 295 then
            if x < 284 then
              if x < 278 then
                if x < 275 then
                  if x < 274 then
                    3960
                  else
                    3990
                else
                  if x < 276 then
                    4009
                  else
                    if x < 277 then
                      4034
                    else
                      4059
              else
                if x < 281 then
                  if x < 279 then
                    4086
                  else
                    if x < 280 then
                      4112
                    else
                      4140
                else
                  if x < 282 then
                    4166
                  else
                    if x < 283 then
                      4196
                    else
                      4221
            else
              if x < 289 then
                if x < 286 then
                  if x < 285 then
                    4241
                  else
                    4266
                else
                  if x < 287 then
                    4295
                  else
                    if x < 288 then
                      4324
                    else
                      4352
              else
                if x < 292 then
                  if x < 290 then
                    4381
                  else
                    if x < 291 then
                      4411
                    else
                      4444
                else
                  if x < 293 then
                    4473
                  else
                    if x < 294 then
                      4502
                    else
                      4522
          else
            if x < 306 then
              if x < 300 then
                if x < 297 then
                  if x < 296 then
                    4549
                  else
                    4572
                else
                  if x < 298 then
                    4604
                  else
                    if x < 299 then
                      4632
                    else
                      4660
              else
                if x < 303 then
                  if x < 301 then
                    4687
                  else
                    if x < 302 then
                      4714
                    else
                      4739
                else
                  if x < 304 then
                    4765
                  else
                    if x < 305 then
                      4794
                    else
                      4822
            else
              if x < 312 then
                if x < 309 then
                  if x < 307 then
                    4849
                  else
                    if x < 308 then
                      4873
                    else
                      4905
                else
                  if x < 310 then
                    4935
                  else
                    if x < 311 then
                      4963
                    else
                      4990
              else
                if x < 315 then
                  if x < 313 then
                    5022
                  else
                    if x < 314 then
                      5051
                    else
                      5081
                else
                  if x < 316 then
                    5110
                  else
                    if x < 317 then
                      5141
                    else
                      5172
        else
          if x < 341 then
            if x < 329 then
              if x < 323 then
                if x < 320 then
                  if x < 319 then
                    5197
                  else
                    5224
                else
                  if x < 321 then
                    5254
                  else
                    if x < 322 then
                      5289
                    else
                      5319
              else
                if x < 326 then
                  if x < 324 then
                    5349
                  else
                    if x < 325 then
                      5375
                    else
                      5406
                else
                  if x < 327 then
                    5437
                  else
                    if x < 328 then
                      5465
                    else
                      5497
            else
              if x < 335 then
                if x < 332 then
                  if x < 330 then
                    5521
                  else
                    if x < 331 then
                      5557
                    else
                      5585
                else
                  if x < 333 then
                    5615
                  else
                    if x < 334 then
                      5641
                    else
                      5679
              else
                if x < 338 then
                  if x < 336 then
                    5709
                  else
                    if x < 337 then
                      5741
                    else
                      5776
                else
                  if x < 339 then
                    5811
                  else
                    if x < 340 then
                      5836
                    else
                      5870
          else
            if x < 352 then
              if x < 346 then
                if x < 343 then
                  if x < 342 then
                    5903
                  else
                    5933
                else
                  if x < 344 then
                    5962
                  else
                    if x < 345 then
                      5996
                    else
                      6033
              else
                if x < 349 then
                  if x < 347 then
                    6060
                  else
                    if x < 348 then
                      6091
                    else
                      6120
                else
                  if x < 350 then
                    6152
                  else
                    if x < 351 then
                      6179
                    else
                      6214
            else
              if x < 358 then
                if x < 355 then
                  if x < 353 then
                    6243
                  else
                    if x < 354 then
                      6273
                    else
                      6304
                else
                  if x < 356 then
                    6333
                  else
                    if x < 357 then
                      6369
                    else
                      6407
              else
                if x < 361 then
                  if x < 359 then
                    6434
                  else
                    if x < 360 then
                      6462
                    else
                      6492
                else
                  if x < 362 then
                    6526
                  else
                    if x < 363 then
                      6563
                    else
                      6595
  else
    if x < 546 then
      if x < 455 then
        if x < 409 then
          if x < 386 then
            if x < 375 then
              if x < 369 then
                if x < 366 then
                  if x < 365 then
                    6623
                  else
                    6656
                else
                  if x < 367 then
                    6691
                  else
                    if x < 368 then
                      6727
                    else
                      6762
              else
                if x < 372 then
                  if x < 370 then
                    6794
                  else
                    if x < 371 then
                      6822
                    else
                      6855
                else
                  if x < 373 then
                    6885
                  else
                    if x < 374 then
                      6914
                    else
                      6949
            else
              if x < 380 then
                if x < 377 then
                  if x < 376 then
                    6985
                  else
                    7016
                else
                  if x < 378 then
                    7053
                  else
                    if x < 379 then
                      7091
                    else
                      7128
              else
                if x < 383 then
                  if x < 381 then
                    7164
                  else
                    if x < 382 then
                      7197
                    else
                      7232
                else
                  if x < 384 then
                    7260
                  else
                    if x < 385 then
                      7295
                    else
                      7330
          else
            if x < 397 then
              if x < 391 then
                if x < 388 then
                  if x < 387 then
                    7363
                  else
                    7399
                else
                  if x < 389 then
                    7434
                  else
                    if x < 390 then
                      7472
                    else
                      7503
              else
                if x < 394 then
                  if x < 392 then
                    7537
                  else
                    if x < 393 then
                      7570
                    else
                      7606
                else
                  if x < 395 then
                    7649
                  else
                    if x < 396 then
                      7681
                    else
                      7713
            else
              if x < 403 then
                if x < 400 then
                  if x < 398 then
                    7746
                  else
                    if x < 399 then
                      7782
                    else
                      7813
                else
                  if x < 401 then
                    7852
                  else
                    if x < 402 then
                      7885
                    else
                      7926
              else
                if x < 406 then
                  if x < 404 then
                    7965
                  else
                    if x < 405 then
                      8000
                    else
                      8038
                else
                  if x < 407 then
                    8078
                  else
                    if x < 408 then
                      8109
                    else
                      8145
        else
          if x < 432 then
            if x < 420 then
              if x < 414 then
                if x < 411 then
                  if x < 410 then
                    8178
                  else
                    8214
                else
                  if x < 412 then
                    8250
                  else
                    if x < 413 then
                      8283
                    else
                      8321
              else
                if x < 417 then
                  if x < 415 then
                    8357
                  else
                    if x < 416 then
                      8393
                    else
                      8429
                else
                  if x < 418 then
                    8464
                  else
                    if x < 419 then
                      8502
                    else
                      8542
            else
              if x < 426 then
                if x < 423 then
                  if x < 421 then
                    8569
                  else
                    if x < 422 then
                      8605
                    else
                      8644
                else
                  if x < 424 then
                    8686
                  else
                    if x < 425 then
                      8726
                    else
                      8763
              else
                if x < 429 then
                  if x < 427 then
                    8798
                  else
                    if x < 428 then
                      8835
                    else
                      8869
                else
                  if x < 430 then
                    8908
                  else
                    if x < 431 then
                      8949
                    else
                      8991
          else
            if x < 443 then
              if x < 437 then
                if x < 434 then
                  if x < 433 then
                    9032
                  else
                    9065
                else
                  if x < 435 then
                    9102
                  else
                    if x < 436 then
                      9143
                    else
                      9184
              else
                if x < 440 then
                  if x < 438 then
                    9222
                  else
                    if x < 439 then
                      9261
                    else
                      9299
                else
                  if x < 441 then
                    9339
                  else
                    if x < 442 then
                      9373
                    else
                      9410
            else
              if x < 449 then
                if x < 446 then
                  if x < 444 then
                    9443
                  else
                    if x < 445 then
                      9482
                    else
                      9526
                else
                  if x < 447 then
                    9563
                  else
                    if x < 448 then
                      9600
                    else
                      9641
              else
                if x < 452 then
                  if x < 450 then
                    9675
                  else
                    if x < 451 then
                      9716
                    else
                      9759
                else
                  if x < 453 then
                    9804
                  else
                    if x < 454 then
                      9841
                    else
                      9872
      else
        if x < 500 then
          if x < 477 then
            if x < 466 then
              if x < 460 then
                if x < 457 then
                  if x < 456 then
                    9911
                  else
                    9952
                else
                  if x < 458 then
                    9989
                  else
                    if x < 459 then
                      10031
                    else
                      10073
              else
                if x < 463 then
                  if x < 461 then
                    10108
                  else
                    if x < 462 then
                      10151
                    else
                      10193
                else
                  if x < 464 then
                    10229
                  else
                    if x < 465 then
                      10264
                    else
                      10306
            else
              if x < 471 then
                if x < 468 then
                  if x < 467 then
                    10344
                  else
                    10388
                else
                  if x < 469 then
                    10430
                  else
                    if x < 470 then
                      10465
                    else
                      10508
              else
                if x < 474 then
                  if x < 472 then
                    10549
                  else
                    if x < 473 then
                      10586
                    else
                      10627
                else
                  if x < 475 then
                    10668
                  else
                    if x < 476 then
                      10708
                    else
                      10752
          else
            if x < 488 then
              if x < 482 then
                if x < 479 then
                  if x < 478 then
                    10790
                  else
                    10828
                else
                  if x < 480 then
                    10868
                  else
                    if x < 481 then
                      10909
                    else
                      10958
              else
                if x < 485 then
                  if x < 483 then
                    10995
                  else
                    if x < 484 then
                      11033
                    else
                      11076
                else
                  if x < 486 then
                    11121
                  else
                    if x < 487 then
                      11159
                    else
                      11200
            else
              if x < 494 then
                if x < 491 then
                  if x < 489 then
                    11243
                  else
                    if x < 490 then
                      11282
                    else
                      11326
                else
                  if x < 492 then
                    11367
                  else
                    if x < 493 then
                      11411
                    else
                      11458
              else
                if x < 497 then
                  if x < 495 then
                    11501
                  else
                    if x < 496 then
                      11543
                    else
                      11583
                else
                  if x < 498 then
                    11630
                  else
                    if x < 499 then
                      11671
                    else
                      11712
        else
          if x < 523 then
            if x < 511 then
              if x < 505 then
                if x < 502 then
                  if x < 501 then
                    11756
                  else
                    11800
                else
                  if x < 503 then
                    11843
                  else
                    if x < 504 then
                      11885
                    else
                      11920
              else
                if x < 508 then
                  if x < 506 then
                    11969
                  else
                    if x < 507 then
                      12007
                    else
                      12055
                else
                  if x < 509 then
                    12100
                  else
                    if x < 510 then
                      12146
                    else
                      12186
            else
              if x < 517 then
                if x < 514 then
                  if x < 512 then
                    12232
                  else
                    if x < 513 then
                      12271
                    else
                      12314
                else
                  if x < 515 then
                    12355
                  else
                    if x < 516 then
                      12403
                    else
                      12448
              else
                if x < 520 then
                  if x < 518 then
                    12488
                  else
                    if x < 519 then
                      12535
                    else
                      12572
                else
                  if x < 521 then
                    12617
                  else
                    if x < 522 then
                      12665
                    else
                      12714
          else
            if x < 534 then
              if x < 528 then
                if x < 525 then
                  if x < 524 then
                    12761
                  else
                    12805
                else
                  if x < 526 then
                    12846
                  else
                    if x < 527 then
                      12896
                    else
                      12934
              else
                if x < 531 then
                  if x < 529 then
                    12978
                  else
                    if x < 530 then
                      13022
                    else
                      13071
                else
                  if x < 532 then
                    13117
                  else
                    if x < 533 then
                      13166
                    else
                      13210
            else
              if x < 540 then
                if x < 537 then
                  if x < 535 then
                    13252
                  else
                    if x < 536 then
                      13289
                    else
                      13337
                else
                  if x < 538 then
                    13378
                  else
                    if x < 539 then
                      13422
                    else
                      13466
              else
                if x < 543 then
                  if x < 541 then
                    13516
                  else
                    if x < 542 then
                      13559
                    else
                      13603
                else
                  if x < 544 then
                    13651
                  else
                    if x < 545 then
                      13693
                    else
                      13738
    else
      if x < 637 then
        if x < 591 then
          if x < 568 then
            if x < 557 then
              if x < 551 then
                if x < 548 then
                  if x < 547 then
                    13789
                  else
                    13838
                else
                  if x < 549 then
                    13886
                  else
                    if x < 550 then
                      13930
                    else
                      13979
              else
                if x < 554 then
                  if x < 552 then
                    14030
                  else
                    if x < 553 then
                      14076
                    else
                      14123
                else
                  if x < 555 then
                    14168
                  else
                    if x < 556 then
                      14214
                    else
                      14260
            else
              if x < 562 then
                if x < 559 then
                  if x < 558 then
                    14307
                  else
                    14357
                else
                  if x < 560 then
                    14395
                  else
                    if x < 561 then
                      14441
                    else
                      14493
              else
                if x < 565 then
                  if x < 563 then
                    14535
                  else
                    if x < 564 then
                      14582
                    else
                      14623
                else
                  if x < 566 then
                    14677
                  else
                    if x < 567 then
                      14721
                    else
                      14770
          else
            if x < 579 then
              if x < 573 then
                if x < 570 then
                  if x < 569 then
                    14817
                  else
                    14862
                else
                  if x < 571 then
                    14909
                  else
                    if x < 572 then
                      14955
                    else
                      15005
              else
                if x < 576 then
                  if x < 574 then
                    15057
                  else
                    if x < 575 then
                      15094
                    else
                      15143
                else
                  if x < 577 then
                    15185
                  else
                    if x < 578 then
                      15233
                    else
                      15287
            else
              if x < 585 then
                if x < 582 then
                  if x < 580 then
                    15332
                  else
                    if x < 581 then
                      15373
                    else
                      15418
                else
                  if x < 583 then
                    15465
                  else
                    if x < 584 then
                      15517
                    else
                      15570
              else
                if x < 588 then
                  if x < 586 then
                    15615
                  else
                    if x < 587 then
                      15665
                    else
                      15716
                else
                  if x < 589 then
                    15765
                  else
                    if x < 590 then
                      15812
                    else
                      15864
        else
          if x < 614 then
            if x < 602 then
              if x < 596 then
                if x < 593 then
                  if x < 592 then
                    15912
                  else
                    15952
                else
                  if x < 594 then
                    16002
                  else
                    if x < 595 then
                      16062
                    else
                      16108
              else
                if x < 599 then
                  if x < 597 then
                    16150
                  else
                    if x < 598 then
                      16202
                    else
                      16257
                else
                  if x < 600 then
                    16313
                  else
                    if x < 601 then
                      16366
                    else
                      16410
            else
              if x < 608 then
                if x < 605 then
                  if x < 603 then
                    16451
                  else
                    if x < 604 then
                      16503
                    else
                      16558
                else
                  if x < 606 then
                    16604
                  else
                    if x < 607 then
                      16656
                    else
                      16706
              else
                if x < 611 then
                  if x < 609 then
                    16757
                  else
                    if x < 610 then
                      16810
                    else
                      16869
                else
                  if x < 612 then
                    16915
                  else
                    if x < 613 then
                      16970
                    else
                      17014
          else
            if x < 625 then
              if x < 619 then
                if x < 616 then
                  if x < 615 then
                    17064
                  else
                    17115
                else
                  if x < 617 then
                    17172
                  else
                    if x < 618 then
                      17216
                    else
                      17267
              else
                if x < 622 then
                  if x < 620 then
                    17318
                  else
                    if x < 621 then
                      17369
                    else
                      17424
                else
                  if x < 623 then
                    17475
                  else
                    if x < 624 then
                      17525
                    else
                      17573
            else
              if x < 631 then
                if x < 628 then
                  if x < 626 then
                    17625
                  else
                    if x < 627 then
                      17678
                    else
                      17726
                else
                  if x < 629 then
                    17778
                  else
                    if x < 630 then
                      17832
                    else
                      17884
              else
                if x < 634 then
                  if x < 632 then
                    17932
                  else
                    if x < 633 then
                      17988
                    else
                      18035
                else
                  if x < 635 then
                    18084
                  else
                    if x < 636 then
                      18141
                    else
                      18188
      else
        if x < 682 then
          if x < 659 then
            if x < 648 then
              if x < 642 then
                if x < 639 then
                  if x < 638 then
                    18236
                  else
                    18289
                else
                  if x < 640 then
                    18341
                  else
                    if x < 641 then
                      18391
                    else
                      18446
              else
                if x < 645 then
                  if x < 643 then
                    18502
                  else
                    if x < 644 then
                      18552
                    else
                      18611
                else
                  if x < 646 then
                    18664
                  else
                    if x < 647 then
                      18716
                    else
                      18774
            else
              if x < 653 then
                if x < 650 then
                  if x < 649 then
                    18834
                  else
                    18887
                else
                  if x < 651 then
                    18940
                  else
                    if x < 652 then
                      18992
                    else
                      19036
              else
                if x < 656 then
                  if x < 654 then
                    19090
                  else
                    if x < 655 then
                      19145
                    else
                      19202
                else
                  if x < 657 then
                    19249
                  else
                    if x < 658 then
                      19299
                    else
                      19349
          else
            if x < 670 then
              if x < 664 then
                if x < 661 then
                  if x < 660 then
                    19406
                  else
                    19454
                else
                  if x < 662 then
                    19508
                  else
                    if x < 663 then
                      19563
                    else
                      19624
              else
                if x < 667 then
                  if x < 665 then
                    19675
                  else
                    if x < 666 then
                      19729
                    else
                      19787
                else
                  if x < 668 then
                    19835
                  else
                    if x < 669 then
                      19899
                    else
                      19947
            else
              if x < 676 then
                if x < 673 then
                  if x < 671 then
                    20003
                  else
                    if x < 672 then
                      20057
                    else
                      20113
                else
                  if x < 674 then
                    20167
                  else
                    if x < 675 then
                      20220
                    else
                      20271
              else
                if x < 679 then
                  if x < 677 then
                    20330
                  else
                    if x < 678 then
                      20389
                    else
                      20452
                else
                  if x < 680 then
                    20509
                  else
                    if x < 681 then
                      20563
                    else
                      20618
        else
          if x < 705 then
            if x < 693 then
              if x < 687 then
                if x < 684 then
                  if x < 683 then
                    20669
                  else
                    20715
                else
                  if x < 685 then
                    20769
                  else
                    if x < 686 then
                      20827
                    else
                      20880
              else
                if x < 690 then
                  if x < 688 then
                    20928
                  else
                    if x < 689 then
                      20983
                    else
                      21032
                else
                  if x < 691 then
                    21093
                  else
                    if x < 692 then
                      21148
                    else
                      21202
            else
              if x < 699 then
                if x < 696 then
                  if x < 694 then
                    21258
                  else
                    if x < 695 then
                      21314
                    else
                      21375
                else
                  if x < 697 then
                    21435
                  else
                    if x < 698 then
                      21488
                    else
                      21542
              else
                if x < 702 then
                  if x < 700 then
                    21605
                  else
                    if x < 701 then
                      21659
                    else
                      21716
                else
                  if x < 703 then
                    21773
                  else
                    if x < 704 then
                      21830
                    else
                      21890
          else
            if x < 716 then
              if x < 710 then
                if x < 707 then
                  if x < 706 then
                    21953
                  else
                    22011
                else
                  if x < 708 then
                    22064
                  else
                    if x < 709 then
                      22114
                    else
                      22179
              else
                if x < 713 then
                  if x < 711 then
                    22235
                  else
                    if x < 712 then
                      22288
                    else
                      22347
                else
                  if x < 714 then
                    22400
                  else
                    if x < 715 then
                      22466
                    else
                      22521
            else
              if x < 722 then
                if x < 719 then
                  if x < 717 then
                    22577
                  else
                    if x < 718 then
                      22630
                    else
                      22685
                else
                  if x < 720 then
                    22749
                  else
                    if x < 721 then
                      22801
                    else
                      22858
              else
                if x < 725 then
                  if x < 723 then
                    22914
                  else
                    if x < 724 then
                      22970
                    else
                      23024
                else
                  if x < 726 then
                    23080
                  else
                    if x < 727 then
                      23141
                    else
                      23197

theorem steps : ∀ x < 727,
    Nat.triangular (x + 1) = Nat.triangular x + (x + 1) ∧
    Nat.triangular x + 1 + (x + 1) ≤ 265225 ∧
    g (x + 1) = g x + cntFrom (Nat.triangular x + 1) (x + 1) := by
  decide +kernel

theorem pct_eq (x : ℕ) : x ≤ 727 → OeisA262403.primeCountTriangular x = g x := by
  induction x with
  | zero => intro _; decide +kernel
  | succ x ih =>
    intro hx
    obtain ⟨h1, h2, h3⟩ := steps x (by omega)
    have h0 := ih (by omega)
    unfold OeisA262403.primeCountTriangular Nat.primeCounting Nat.primeCounting' at h0 ⊢
    rw [h1, show Nat.triangular x + (x + 1) + 1 = (Nat.triangular x + 1) + (x + 1) by omega,
      count_eq (Nat.triangular x + 1) (x + 1) h2, h0, h3]

/-- The body of `OeisA262403.a` with the prime-count function abstracted. -/
def aG (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 2 (n - 2),
    ((Finset.Icc (k + 1) (n - 1)).filter (fun m => f n = f k + f m)).card

theorem aG_congr (f h : ℕ → ℕ) (n : ℕ) (hfh : ∀ x ≤ n, f x = h x) : aG f n = aG h n := by
  unfold aG
  rw [hfh n le_rfl]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  congr 1
  apply Finset.filter_congr
  intro m hm
  rw [Finset.mem_Icc] at hm
  rw [hfh k (by omega), hfh m (by omega)]

theorem a_eq (n : ℕ) (hn : n ≤ 727) : OeisA262403.a n = aG g n :=
  aG_congr OeisA262403.primeCountTriangular g n (fun x hx => pct_eq x (by omega))

end OMA.A262403H1

theorem OMA.solution : OMA.R_OeisA262403_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rw [OMA.A262403H1.a_eq n (by omega)]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
