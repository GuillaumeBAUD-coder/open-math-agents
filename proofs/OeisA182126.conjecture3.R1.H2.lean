import OMAReductions.R_OeisA182126_conjecture3_R1

/-! Finite half of A182126: among a(1)..a(61) the only primes are 2, 7, 11, 13, 29. -/

private def primes63 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 40000000 in
private theorem nth_eq (k : ℕ) (hk : k ≤ 63) :
    Nat.nth Nat.Prime k = primes63.getD k 0 := by
  interval_cases k
  · have hc : Nat.count Nat.Prime 2 = 0 := by decide
    have h := (2).nth_count (by decide : Nat.Prime 2)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 3 = 1 := by decide
    have h := (3).nth_count (by decide : Nat.Prime 3)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 5 = 2 := by decide
    have h := (5).nth_count (by decide : Nat.Prime 5)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 7 = 3 := by decide
    have h := (7).nth_count (by decide : Nat.Prime 7)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 11 = 4 := by decide
    have h := (11).nth_count (by decide : Nat.Prime 11)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 13 = 5 := by decide
    have h := (13).nth_count (by decide : Nat.Prime 13)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 17 = 6 := by decide
    have h := (17).nth_count (by decide : Nat.Prime 17)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 19 = 7 := by decide
    have h := (19).nth_count (by decide : Nat.Prime 19)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 23 = 8 := by decide
    have h := (23).nth_count (by decide : Nat.Prime 23)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 29 = 9 := by decide
    have h := (29).nth_count (by decide : Nat.Prime 29)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 31 = 10 := by decide
    have h := (31).nth_count (by decide : Nat.Prime 31)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 37 = 11 := by decide
    have h := (37).nth_count (by decide : Nat.Prime 37)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 41 = 12 := by decide
    have h := (41).nth_count (by decide : Nat.Prime 41)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 43 = 13 := by decide
    have h := (43).nth_count (by decide : Nat.Prime 43)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 47 = 14 := by decide
    have h := (47).nth_count (by decide : Nat.Prime 47)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 53 = 15 := by decide
    have h := (53).nth_count (by decide : Nat.Prime 53)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 59 = 16 := by decide
    have h := (59).nth_count (by decide : Nat.Prime 59)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 61 = 17 := by decide
    have h := (61).nth_count (by decide : Nat.Prime 61)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 67 = 18 := by decide
    have h := (67).nth_count (by decide : Nat.Prime 67)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 71 = 19 := by decide
    have h := (71).nth_count (by decide : Nat.Prime 71)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 73 = 20 := by decide
    have h := (73).nth_count (by decide : Nat.Prime 73)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 79 = 21 := by decide
    have h := (79).nth_count (by decide : Nat.Prime 79)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 83 = 22 := by decide
    have h := (83).nth_count (by decide : Nat.Prime 83)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 89 = 23 := by decide
    have h := (89).nth_count (by decide : Nat.Prime 89)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 97 = 24 := by decide
    have h := (97).nth_count (by decide : Nat.Prime 97)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 101 = 25 := by decide
    have h := (101).nth_count (by decide : Nat.Prime 101)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 103 = 26 := by decide
    have h := (103).nth_count (by decide : Nat.Prime 103)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 107 = 27 := by decide
    have h := (107).nth_count (by decide : Nat.Prime 107)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 109 = 28 := by decide
    have h := (109).nth_count (by decide : Nat.Prime 109)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 113 = 29 := by decide
    have h := (113).nth_count (by decide : Nat.Prime 113)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 127 = 30 := by decide
    have h := (127).nth_count (by decide : Nat.Prime 127)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 131 = 31 := by decide
    have h := (131).nth_count (by decide : Nat.Prime 131)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 137 = 32 := by decide
    have h := (137).nth_count (by decide : Nat.Prime 137)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 139 = 33 := by decide
    have h := (139).nth_count (by decide : Nat.Prime 139)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 149 = 34 := by decide
    have h := (149).nth_count (by decide : Nat.Prime 149)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 151 = 35 := by decide
    have h := (151).nth_count (by decide : Nat.Prime 151)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 157 = 36 := by decide
    have h := (157).nth_count (by decide : Nat.Prime 157)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 163 = 37 := by decide
    have h := (163).nth_count (by decide : Nat.Prime 163)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 167 = 38 := by decide
    have h := (167).nth_count (by decide : Nat.Prime 167)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 173 = 39 := by decide
    have h := (173).nth_count (by decide : Nat.Prime 173)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 179 = 40 := by decide
    have h := (179).nth_count (by decide : Nat.Prime 179)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 181 = 41 := by decide
    have h := (181).nth_count (by decide : Nat.Prime 181)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 191 = 42 := by decide
    have h := (191).nth_count (by decide : Nat.Prime 191)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 193 = 43 := by decide
    have h := (193).nth_count (by decide : Nat.Prime 193)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 197 = 44 := by decide
    have h := (197).nth_count (by decide : Nat.Prime 197)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 199 = 45 := by decide
    have h := (199).nth_count (by decide : Nat.Prime 199)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 211 = 46 := by decide
    have h := (211).nth_count (by decide : Nat.Prime 211)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 223 = 47 := by decide
    have h := (223).nth_count (by decide : Nat.Prime 223)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 227 = 48 := by decide
    have h := (227).nth_count (by decide : Nat.Prime 227)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 229 = 49 := by decide
    have h := (229).nth_count (by decide : Nat.Prime 229)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 233 = 50 := by decide
    have h := (233).nth_count (by decide : Nat.Prime 233)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 239 = 51 := by decide
    have h := (239).nth_count (by decide : Nat.Prime 239)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 241 = 52 := by decide
    have h := (241).nth_count (by decide : Nat.Prime 241)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 251 = 53 := by decide
    have h := (251).nth_count (by decide : Nat.Prime 251)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 257 = 54 := by decide
    have h := (257).nth_count (by decide : Nat.Prime 257)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 263 = 55 := by decide
    have h := (263).nth_count (by decide : Nat.Prime 263)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 269 = 56 := by decide
    have h := (269).nth_count (by decide : Nat.Prime 269)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 271 = 57 := by decide
    have h := (271).nth_count (by decide : Nat.Prime 271)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 277 = 58 := by decide
    have h := (277).nth_count (by decide : Nat.Prime 277)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 281 = 59 := by decide
    have h := (281).nth_count (by decide : Nat.Prime 281)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 283 = 60 := by decide
    have h := (283).nth_count (by decide : Nat.Prime 283)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 293 = 61 := by decide
    have h := (293).nth_count (by decide : Nat.Prime 293)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 307 = 62 := by decide
    have h := (307).nth_count (by decide : Nat.Prime 307)
    rw [hc] at h
    simpa [primes63] using h
  · have hc : Nat.count Nat.Prime 311 = 63 := by decide
    have h := (311).nth_count (by decide : Nat.Prime 311)
    rw [hc] at h
    simpa [primes63] using h

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 40000000 in
theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := by
  intro n hn1 hn2 hprime
  interval_cases n
  · have e : OeisA182126.a 1 = 1 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (1 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (0) = 2 from by simpa [primes63] using nth_eq (0) (by decide),
          show Nat.nth Nat.Prime (1) = 3 from by simpa [primes63] using nth_eq (1) (by decide),
          show Nat.nth Nat.Prime (2) = 5 from by simpa [primes63] using nth_eq (2) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 2 = 1 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (2 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (1) = 3 from by simpa [primes63] using nth_eq (1) (by decide),
          show Nat.nth Nat.Prime (2) = 5 from by simpa [primes63] using nth_eq (2) (by decide),
          show Nat.nth Nat.Prime (3) = 7 from by simpa [primes63] using nth_eq (3) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 3 = 2 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (3 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (2) = 5 from by simpa [primes63] using nth_eq (2) (by decide),
          show Nat.nth Nat.Prime (3) = 7 from by simpa [primes63] using nth_eq (3) (by decide),
          show Nat.nth Nat.Prime (4) = 11 from by simpa [primes63] using nth_eq (4) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 4 = 12 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (4 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (3) = 7 from by simpa [primes63] using nth_eq (3) (by decide),
          show Nat.nth Nat.Prime (4) = 11 from by simpa [primes63] using nth_eq (4) (by decide),
          show Nat.nth Nat.Prime (5) = 13 from by simpa [primes63] using nth_eq (5) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 5 = 7 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (5 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (4) = 11 from by simpa [primes63] using nth_eq (4) (by decide),
          show Nat.nth Nat.Prime (5) = 13 from by simpa [primes63] using nth_eq (5) (by decide),
          show Nat.nth Nat.Prime (6) = 17 from by simpa [primes63] using nth_eq (6) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 6 = 12 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (6 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (5) = 13 from by simpa [primes63] using nth_eq (5) (by decide),
          show Nat.nth Nat.Prime (6) = 17 from by simpa [primes63] using nth_eq (6) (by decide),
          show Nat.nth Nat.Prime (7) = 19 from by simpa [primes63] using nth_eq (7) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 7 = 1 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (7 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (6) = 17 from by simpa [primes63] using nth_eq (6) (by decide),
          show Nat.nth Nat.Prime (7) = 19 from by simpa [primes63] using nth_eq (7) (by decide),
          show Nat.nth Nat.Prime (8) = 23 from by simpa [primes63] using nth_eq (8) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 8 = 2 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (8 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (7) = 19 from by simpa [primes63] using nth_eq (7) (by decide),
          show Nat.nth Nat.Prime (8) = 23 from by simpa [primes63] using nth_eq (8) (by decide),
          show Nat.nth Nat.Prime (9) = 29 from by simpa [primes63] using nth_eq (9) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 9 = 16 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (9 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (8) = 23 from by simpa [primes63] using nth_eq (8) (by decide),
          show Nat.nth Nat.Prime (9) = 29 from by simpa [primes63] using nth_eq (9) (by decide),
          show Nat.nth Nat.Prime (10) = 31 from by simpa [primes63] using nth_eq (10) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 10 = 11 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (10 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (9) = 29 from by simpa [primes63] using nth_eq (9) (by decide),
          show Nat.nth Nat.Prime (10) = 31 from by simpa [primes63] using nth_eq (10) (by decide),
          show Nat.nth Nat.Prime (11) = 37 from by simpa [primes63] using nth_eq (11) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 11 = 40 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (11 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (10) = 31 from by simpa [primes63] using nth_eq (10) (by decide),
          show Nat.nth Nat.Prime (11) = 37 from by simpa [primes63] using nth_eq (11) (by decide),
          show Nat.nth Nat.Prime (12) = 41 from by simpa [primes63] using nth_eq (12) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 12 = 12 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (12 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (11) = 37 from by simpa [primes63] using nth_eq (11) (by decide),
          show Nat.nth Nat.Prime (12) = 41 from by simpa [primes63] using nth_eq (12) (by decide),
          show Nat.nth Nat.Prime (13) = 43 from by simpa [primes63] using nth_eq (13) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 13 = 24 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (13 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (12) = 41 from by simpa [primes63] using nth_eq (12) (by decide),
          show Nat.nth Nat.Prime (13) = 43 from by simpa [primes63] using nth_eq (13) (by decide),
          show Nat.nth Nat.Prime (14) = 47 from by simpa [primes63] using nth_eq (14) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 14 = 7 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (14 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (13) = 43 from by simpa [primes63] using nth_eq (13) (by decide),
          show Nat.nth Nat.Prime (14) = 47 from by simpa [primes63] using nth_eq (14) (by decide),
          show Nat.nth Nat.Prime (15) = 53 from by simpa [primes63] using nth_eq (15) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 15 = 13 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (15 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (14) = 47 from by simpa [primes63] using nth_eq (14) (by decide),
          show Nat.nth Nat.Prime (15) = 53 from by simpa [primes63] using nth_eq (15) (by decide),
          show Nat.nth Nat.Prime (16) = 59 from by simpa [primes63] using nth_eq (16) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 16 = 16 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (16 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (15) = 53 from by simpa [primes63] using nth_eq (15) (by decide),
          show Nat.nth Nat.Prime (16) = 59 from by simpa [primes63] using nth_eq (16) (by decide),
          show Nat.nth Nat.Prime (17) = 61 from by simpa [primes63] using nth_eq (17) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 17 = 48 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (17 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (16) = 59 from by simpa [primes63] using nth_eq (16) (by decide),
          show Nat.nth Nat.Prime (17) = 61 from by simpa [primes63] using nth_eq (17) (by decide),
          show Nat.nth Nat.Prime (18) = 67 from by simpa [primes63] using nth_eq (18) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 18 = 40 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (18 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (17) = 61 from by simpa [primes63] using nth_eq (17) (by decide),
          show Nat.nth Nat.Prime (18) = 67 from by simpa [primes63] using nth_eq (18) (by decide),
          show Nat.nth Nat.Prime (19) = 71 from by simpa [primes63] using nth_eq (19) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 19 = 12 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (19 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (18) = 67 from by simpa [primes63] using nth_eq (18) (by decide),
          show Nat.nth Nat.Prime (19) = 71 from by simpa [primes63] using nth_eq (19) (by decide),
          show Nat.nth Nat.Prime (20) = 73 from by simpa [primes63] using nth_eq (20) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 20 = 48 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (20 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (19) = 71 from by simpa [primes63] using nth_eq (19) (by decide),
          show Nat.nth Nat.Prime (20) = 73 from by simpa [primes63] using nth_eq (20) (by decide),
          show Nat.nth Nat.Prime (21) = 79 from by simpa [primes63] using nth_eq (21) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 21 = 40 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (21 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (20) = 73 from by simpa [primes63] using nth_eq (20) (by decide),
          show Nat.nth Nat.Prime (21) = 79 from by simpa [primes63] using nth_eq (21) (by decide),
          show Nat.nth Nat.Prime (22) = 83 from by simpa [primes63] using nth_eq (22) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 22 = 60 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (22 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (21) = 79 from by simpa [primes63] using nth_eq (21) (by decide),
          show Nat.nth Nat.Prime (22) = 83 from by simpa [primes63] using nth_eq (22) (by decide),
          show Nat.nth Nat.Prime (23) = 89 from by simpa [primes63] using nth_eq (23) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 23 = 15 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (23 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (22) = 83 from by simpa [primes63] using nth_eq (22) (by decide),
          show Nat.nth Nat.Prime (23) = 89 from by simpa [primes63] using nth_eq (23) (by decide),
          show Nat.nth Nat.Prime (24) = 97 from by simpa [primes63] using nth_eq (24) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 24 = 48 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (24 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (23) = 89 from by simpa [primes63] using nth_eq (23) (by decide),
          show Nat.nth Nat.Prime (24) = 97 from by simpa [primes63] using nth_eq (24) (by decide),
          show Nat.nth Nat.Prime (25) = 101 from by simpa [primes63] using nth_eq (25) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 25 = 12 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (25 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (24) = 97 from by simpa [primes63] using nth_eq (24) (by decide),
          show Nat.nth Nat.Prime (25) = 101 from by simpa [primes63] using nth_eq (25) (by decide),
          show Nat.nth Nat.Prime (26) = 103 from by simpa [primes63] using nth_eq (26) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 26 = 24 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (26 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (25) = 101 from by simpa [primes63] using nth_eq (25) (by decide),
          show Nat.nth Nat.Prime (26) = 103 from by simpa [primes63] using nth_eq (26) (by decide),
          show Nat.nth Nat.Prime (27) = 107 from by simpa [primes63] using nth_eq (27) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 27 = 12 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (27 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (26) = 103 from by simpa [primes63] using nth_eq (26) (by decide),
          show Nat.nth Nat.Prime (27) = 107 from by simpa [primes63] using nth_eq (27) (by decide),
          show Nat.nth Nat.Prime (28) = 109 from by simpa [primes63] using nth_eq (28) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 28 = 24 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (28 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (27) = 107 from by simpa [primes63] using nth_eq (27) (by decide),
          show Nat.nth Nat.Prime (28) = 109 from by simpa [primes63] using nth_eq (28) (by decide),
          show Nat.nth Nat.Prime (29) = 113 from by simpa [primes63] using nth_eq (29) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 29 = 125 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (29 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (28) = 109 from by simpa [primes63] using nth_eq (28) (by decide),
          show Nat.nth Nat.Prime (29) = 113 from by simpa [primes63] using nth_eq (29) (by decide),
          show Nat.nth Nat.Prime (30) = 127 from by simpa [primes63] using nth_eq (30) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 30 = 72 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (30 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (29) = 113 from by simpa [primes63] using nth_eq (29) (by decide),
          show Nat.nth Nat.Prime (30) = 127 from by simpa [primes63] using nth_eq (30) (by decide),
          show Nat.nth Nat.Prime (31) = 131 from by simpa [primes63] using nth_eq (31) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 31 = 60 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (31 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (30) = 127 from by simpa [primes63] using nth_eq (30) (by decide),
          show Nat.nth Nat.Prime (31) = 131 from by simpa [primes63] using nth_eq (31) (by decide),
          show Nat.nth Nat.Prime (32) = 137 from by simpa [primes63] using nth_eq (32) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 32 = 16 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (32 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (31) = 131 from by simpa [primes63] using nth_eq (31) (by decide),
          show Nat.nth Nat.Prime (32) = 137 from by simpa [primes63] using nth_eq (32) (by decide),
          show Nat.nth Nat.Prime (33) = 139 from by simpa [primes63] using nth_eq (33) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 33 = 120 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (33 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (32) = 137 from by simpa [primes63] using nth_eq (32) (by decide),
          show Nat.nth Nat.Prime (33) = 139 from by simpa [primes63] using nth_eq (33) (by decide),
          show Nat.nth Nat.Prime (34) = 149 from by simpa [primes63] using nth_eq (34) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 34 = 24 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (34 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (33) = 139 from by simpa [primes63] using nth_eq (33) (by decide),
          show Nat.nth Nat.Prime (34) = 149 from by simpa [primes63] using nth_eq (34) (by decide),
          show Nat.nth Nat.Prime (35) = 151 from by simpa [primes63] using nth_eq (35) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 35 = 48 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (35 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (34) = 149 from by simpa [primes63] using nth_eq (34) (by decide),
          show Nat.nth Nat.Prime (35) = 151 from by simpa [primes63] using nth_eq (35) (by decide),
          show Nat.nth Nat.Prime (36) = 157 from by simpa [primes63] using nth_eq (36) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 36 = 72 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (36 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (35) = 151 from by simpa [primes63] using nth_eq (35) (by decide),
          show Nat.nth Nat.Prime (36) = 157 from by simpa [primes63] using nth_eq (36) (by decide),
          show Nat.nth Nat.Prime (37) = 163 from by simpa [primes63] using nth_eq (37) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 37 = 40 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (37 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (36) = 157 from by simpa [primes63] using nth_eq (36) (by decide),
          show Nat.nth Nat.Prime (37) = 163 from by simpa [primes63] using nth_eq (37) (by decide),
          show Nat.nth Nat.Prime (38) = 167 from by simpa [primes63] using nth_eq (38) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 38 = 60 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (38 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (37) = 163 from by simpa [primes63] using nth_eq (37) (by decide),
          show Nat.nth Nat.Prime (38) = 167 from by simpa [primes63] using nth_eq (38) (by decide),
          show Nat.nth Nat.Prime (39) = 173 from by simpa [primes63] using nth_eq (39) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 39 = 72 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (39 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (38) = 167 from by simpa [primes63] using nth_eq (38) (by decide),
          show Nat.nth Nat.Prime (39) = 173 from by simpa [primes63] using nth_eq (39) (by decide),
          show Nat.nth Nat.Prime (40) = 179 from by simpa [primes63] using nth_eq (40) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 40 = 16 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (40 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (39) = 173 from by simpa [primes63] using nth_eq (39) (by decide),
          show Nat.nth Nat.Prime (40) = 179 from by simpa [primes63] using nth_eq (40) (by decide),
          show Nat.nth Nat.Prime (41) = 181 from by simpa [primes63] using nth_eq (41) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 41 = 120 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (41 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (40) = 179 from by simpa [primes63] using nth_eq (40) (by decide),
          show Nat.nth Nat.Prime (41) = 181 from by simpa [primes63] using nth_eq (41) (by decide),
          show Nat.nth Nat.Prime (42) = 191 from by simpa [primes63] using nth_eq (42) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 42 = 24 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (42 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (41) = 181 from by simpa [primes63] using nth_eq (41) (by decide),
          show Nat.nth Nat.Prime (42) = 191 from by simpa [primes63] using nth_eq (42) (by decide),
          show Nat.nth Nat.Prime (43) = 193 from by simpa [primes63] using nth_eq (43) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 43 = 24 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (43 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (42) = 191 from by simpa [primes63] using nth_eq (42) (by decide),
          show Nat.nth Nat.Prime (43) = 193 from by simpa [primes63] using nth_eq (43) (by decide),
          show Nat.nth Nat.Prime (44) = 197 from by simpa [primes63] using nth_eq (44) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 44 = 12 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (44 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (43) = 193 from by simpa [primes63] using nth_eq (43) (by decide),
          show Nat.nth Nat.Prime (44) = 197 from by simpa [primes63] using nth_eq (44) (by decide),
          show Nat.nth Nat.Prime (45) = 199 from by simpa [primes63] using nth_eq (45) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 45 = 168 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (45 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (44) = 197 from by simpa [primes63] using nth_eq (44) (by decide),
          show Nat.nth Nat.Prime (45) = 199 from by simpa [primes63] using nth_eq (45) (by decide),
          show Nat.nth Nat.Prime (46) = 211 from by simpa [primes63] using nth_eq (46) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 46 = 65 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (46 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (45) = 199 from by simpa [primes63] using nth_eq (45) (by decide),
          show Nat.nth Nat.Prime (46) = 211 from by simpa [primes63] using nth_eq (46) (by decide),
          show Nat.nth Nat.Prime (47) = 223 from by simpa [primes63] using nth_eq (47) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 47 = 64 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (47 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (46) = 211 from by simpa [primes63] using nth_eq (46) (by decide),
          show Nat.nth Nat.Prime (47) = 223 from by simpa [primes63] using nth_eq (47) (by decide),
          show Nat.nth Nat.Prime (48) = 227 from by simpa [primes63] using nth_eq (48) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 48 = 12 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (48 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (47) = 223 from by simpa [primes63] using nth_eq (47) (by decide),
          show Nat.nth Nat.Prime (48) = 227 from by simpa [primes63] using nth_eq (48) (by decide),
          show Nat.nth Nat.Prime (49) = 229 from by simpa [primes63] using nth_eq (49) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 49 = 24 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (49 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (48) = 227 from by simpa [primes63] using nth_eq (48) (by decide),
          show Nat.nth Nat.Prime (49) = 229 from by simpa [primes63] using nth_eq (49) (by decide),
          show Nat.nth Nat.Prime (50) = 233 from by simpa [primes63] using nth_eq (50) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 50 = 60 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (50 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (49) = 229 from by simpa [primes63] using nth_eq (49) (by decide),
          show Nat.nth Nat.Prime (50) = 233 from by simpa [primes63] using nth_eq (50) (by decide),
          show Nat.nth Nat.Prime (51) = 239 from by simpa [primes63] using nth_eq (51) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 51 = 16 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (51 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (50) = 233 from by simpa [primes63] using nth_eq (50) (by decide),
          show Nat.nth Nat.Prime (51) = 239 from by simpa [primes63] using nth_eq (51) (by decide),
          show Nat.nth Nat.Prime (52) = 241 from by simpa [primes63] using nth_eq (52) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 52 = 120 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (52 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (51) = 239 from by simpa [primes63] using nth_eq (51) (by decide),
          show Nat.nth Nat.Prime (52) = 241 from by simpa [primes63] using nth_eq (52) (by decide),
          show Nat.nth Nat.Prime (53) = 251 from by simpa [primes63] using nth_eq (53) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 53 = 96 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (53 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (52) = 241 from by simpa [primes63] using nth_eq (52) (by decide),
          show Nat.nth Nat.Prime (53) = 251 from by simpa [primes63] using nth_eq (53) (by decide),
          show Nat.nth Nat.Prime (54) = 257 from by simpa [primes63] using nth_eq (54) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 54 = 72 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (54 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (53) = 251 from by simpa [primes63] using nth_eq (53) (by decide),
          show Nat.nth Nat.Prime (54) = 257 from by simpa [primes63] using nth_eq (54) (by decide),
          show Nat.nth Nat.Prime (55) = 263 from by simpa [primes63] using nth_eq (55) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 55 = 72 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (55 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (54) = 257 from by simpa [primes63] using nth_eq (54) (by decide),
          show Nat.nth Nat.Prime (55) = 263 from by simpa [primes63] using nth_eq (55) (by decide),
          show Nat.nth Nat.Prime (56) = 269 from by simpa [primes63] using nth_eq (56) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 56 = 16 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (56 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (55) = 263 from by simpa [primes63] using nth_eq (55) (by decide),
          show Nat.nth Nat.Prime (56) = 269 from by simpa [primes63] using nth_eq (56) (by decide),
          show Nat.nth Nat.Prime (57) = 271 from by simpa [primes63] using nth_eq (57) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 57 = 48 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (57 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (56) = 269 from by simpa [primes63] using nth_eq (56) (by decide),
          show Nat.nth Nat.Prime (57) = 271 from by simpa [primes63] using nth_eq (57) (by decide),
          show Nat.nth Nat.Prime (58) = 277 from by simpa [primes63] using nth_eq (58) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 58 = 40 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (58 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (57) = 271 from by simpa [primes63] using nth_eq (57) (by decide),
          show Nat.nth Nat.Prime (58) = 277 from by simpa [primes63] using nth_eq (58) (by decide),
          show Nat.nth Nat.Prime (59) = 281 from by simpa [primes63] using nth_eq (59) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 59 = 12 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (59 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (58) = 277 from by simpa [primes63] using nth_eq (58) (by decide),
          show Nat.nth Nat.Prime (59) = 281 from by simpa [primes63] using nth_eq (59) (by decide),
          show Nat.nth Nat.Prime (60) = 283 from by simpa [primes63] using nth_eq (60) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 60 = 120 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (60 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (59) = 281 from by simpa [primes63] using nth_eq (59) (by decide),
          show Nat.nth Nat.Prime (60) = 283 from by simpa [primes63] using nth_eq (60) (by decide),
          show Nat.nth Nat.Prime (61) = 293 from by simpa [primes63] using nth_eq (61) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
  · have e : OeisA182126.a 61 = 29 := by
      simp only [OeisA182126.a, OeisA182126.prime, if_neg (by decide : (61 : ℕ) ≠ 0)]
      rw [show Nat.nth Nat.Prime (60) = 283 from by simpa [primes63] using nth_eq (60) (by decide),
          show Nat.nth Nat.Prime (61) = 293 from by simpa [primes63] using nth_eq (61) (by decide),
          show Nat.nth Nat.Prime (62) = 307 from by simpa [primes63] using nth_eq (62) (by decide)]
    rw [e] at hprime ⊢
    first | exact absurd hprime (by decide) | decide
