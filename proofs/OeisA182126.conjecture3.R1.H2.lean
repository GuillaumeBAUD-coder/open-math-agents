import OMAReductions.R_OeisA182126_conjecture3_R1
import Mathlib.Tactic

private lemma a_eq_of_primes {n k p q r : ℕ} (hn : n = k + 1)
    (hp : Nat.nth Nat.Prime k = p)
    (hq : Nat.nth Nat.Prime (k + 1) = q)
    (hr : Nat.nth Nat.Prime (k + 2) = r) :
    OeisA182126.a n = (p * q) % r := by
  subst hn
  unfold OeisA182126.a OeisA182126.prime
  simp [hp, hq, hr]

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 400000 in
private theorem prove_A182126_H2 :
    ∀ n : ℕ, 0 < n → n ≤ 61 → (OeisA182126.a n).Prime →
      OeisA182126.a n ∈ ([2, 7, 11, 13, 29] : List ℕ) := by
  have hp0 : Nat.nth Nat.Prime 0 = 2 := (2).nth_count (by decide : (2).Prime)
  have hp1 : Nat.nth Nat.Prime 1 = 3 := (3).nth_count (by decide : (3).Prime)
  have hp2 : Nat.nth Nat.Prime 2 = 5 := (5).nth_count (by decide : (5).Prime)
  have hp3 : Nat.nth Nat.Prime 3 = 7 := (7).nth_count (by decide : (7).Prime)
  have hp4 : Nat.nth Nat.Prime 4 = 11 := (11).nth_count (by decide : (11).Prime)
  have hp5 : Nat.nth Nat.Prime 5 = 13 := (13).nth_count (by decide : (13).Prime)
  have hp6 : Nat.nth Nat.Prime 6 = 17 := (17).nth_count (by decide : (17).Prime)
  have hp7 : Nat.nth Nat.Prime 7 = 19 := (19).nth_count (by decide : (19).Prime)
  have hp8 : Nat.nth Nat.Prime 8 = 23 := (23).nth_count (by decide : (23).Prime)
  have hp9 : Nat.nth Nat.Prime 9 = 29 := (29).nth_count (by decide : (29).Prime)
  have hp10 : Nat.nth Nat.Prime 10 = 31 := (31).nth_count (by decide : (31).Prime)
  have hp11 : Nat.nth Nat.Prime 11 = 37 := (37).nth_count (by decide : (37).Prime)
  have hp12 : Nat.nth Nat.Prime 12 = 41 := (41).nth_count (by decide : (41).Prime)
  have hp13 : Nat.nth Nat.Prime 13 = 43 := (43).nth_count (by decide : (43).Prime)
  have hp14 : Nat.nth Nat.Prime 14 = 47 := (47).nth_count (by decide : (47).Prime)
  have hp15 : Nat.nth Nat.Prime 15 = 53 := (53).nth_count (by decide : (53).Prime)
  have hp16 : Nat.nth Nat.Prime 16 = 59 := (59).nth_count (by decide : (59).Prime)
  have hp17 : Nat.nth Nat.Prime 17 = 61 := (61).nth_count (by decide : (61).Prime)
  have hp18 : Nat.nth Nat.Prime 18 = 67 := (67).nth_count (by decide : (67).Prime)
  have hp19 : Nat.nth Nat.Prime 19 = 71 := (71).nth_count (by decide : (71).Prime)
  have hp20 : Nat.nth Nat.Prime 20 = 73 := (73).nth_count (by decide : (73).Prime)
  have hp21 : Nat.nth Nat.Prime 21 = 79 := (79).nth_count (by decide : (79).Prime)
  have hp22 : Nat.nth Nat.Prime 22 = 83 := (83).nth_count (by decide : (83).Prime)
  have hp23 : Nat.nth Nat.Prime 23 = 89 := (89).nth_count (by decide : (89).Prime)
  have hp24 : Nat.nth Nat.Prime 24 = 97 := (97).nth_count (by decide : (97).Prime)
  have hp25 : Nat.nth Nat.Prime 25 = 101 := (101).nth_count (by decide : (101).Prime)
  have hp26 : Nat.nth Nat.Prime 26 = 103 := (103).nth_count (by decide : (103).Prime)
  have hp27 : Nat.nth Nat.Prime 27 = 107 := (107).nth_count (by decide : (107).Prime)
  have hp28 : Nat.nth Nat.Prime 28 = 109 := (109).nth_count (by decide : (109).Prime)
  have hp29 : Nat.nth Nat.Prime 29 = 113 := (113).nth_count (by decide : (113).Prime)
  have hp30 : Nat.nth Nat.Prime 30 = 127 := (127).nth_count (by decide : (127).Prime)
  have hp31 : Nat.nth Nat.Prime 31 = 131 := (131).nth_count (by decide : (131).Prime)
  have hp32 : Nat.nth Nat.Prime 32 = 137 := (137).nth_count (by decide : (137).Prime)
  have hp33 : Nat.nth Nat.Prime 33 = 139 := (139).nth_count (by decide : (139).Prime)
  have hp34 : Nat.nth Nat.Prime 34 = 149 := (149).nth_count (by decide : (149).Prime)
  have hp35 : Nat.nth Nat.Prime 35 = 151 := (151).nth_count (by decide : (151).Prime)
  have hp36 : Nat.nth Nat.Prime 36 = 157 := (157).nth_count (by decide : (157).Prime)
  have hp37 : Nat.nth Nat.Prime 37 = 163 := (163).nth_count (by decide : (163).Prime)
  have hp38 : Nat.nth Nat.Prime 38 = 167 := (167).nth_count (by decide : (167).Prime)
  have hp39 : Nat.nth Nat.Prime 39 = 173 := (173).nth_count (by decide : (173).Prime)
  have hp40 : Nat.nth Nat.Prime 40 = 179 := (179).nth_count (by decide : (179).Prime)
  have hp41 : Nat.nth Nat.Prime 41 = 181 := (181).nth_count (by decide : (181).Prime)
  have hp42 : Nat.nth Nat.Prime 42 = 191 := (191).nth_count (by decide : (191).Prime)
  have hp43 : Nat.nth Nat.Prime 43 = 193 := (193).nth_count (by decide : (193).Prime)
  have hp44 : Nat.nth Nat.Prime 44 = 197 := (197).nth_count (by decide : (197).Prime)
  have hp45 : Nat.nth Nat.Prime 45 = 199 := (199).nth_count (by decide : (199).Prime)
  have hp46 : Nat.nth Nat.Prime 46 = 211 := (211).nth_count (by decide : (211).Prime)
  have hp47 : Nat.nth Nat.Prime 47 = 223 := (223).nth_count (by decide : (223).Prime)
  have hp48 : Nat.nth Nat.Prime 48 = 227 := (227).nth_count (by decide : (227).Prime)
  have hp49 : Nat.nth Nat.Prime 49 = 229 := (229).nth_count (by decide : (229).Prime)
  have hp50 : Nat.nth Nat.Prime 50 = 233 := (233).nth_count (by decide : (233).Prime)
  have hp51 : Nat.nth Nat.Prime 51 = 239 := (239).nth_count (by decide : (239).Prime)
  have hp52 : Nat.nth Nat.Prime 52 = 241 := (241).nth_count (by decide : (241).Prime)
  have hp53 : Nat.nth Nat.Prime 53 = 251 := (251).nth_count (by decide : (251).Prime)
  have hp54 : Nat.nth Nat.Prime 54 = 257 := (257).nth_count (by decide : (257).Prime)
  have hp55 : Nat.nth Nat.Prime 55 = 263 := (263).nth_count (by decide : (263).Prime)
  have hp56 : Nat.nth Nat.Prime 56 = 269 := (269).nth_count (by decide : (269).Prime)
  have hp57 : Nat.nth Nat.Prime 57 = 271 := (271).nth_count (by decide : (271).Prime)
  have hp58 : Nat.nth Nat.Prime 58 = 277 := (277).nth_count (by decide : (277).Prime)
  have hp59 : Nat.nth Nat.Prime 59 = 281 := (281).nth_count (by decide : (281).Prime)
  have hp60 : Nat.nth Nat.Prime 60 = 283 := (283).nth_count (by decide : (283).Prime)
  have hp61 : Nat.nth Nat.Prime 61 = 293 := (293).nth_count (by decide : (293).Prime)
  have hp62 : Nat.nth Nat.Prime 62 = 307 := (307).nth_count (by decide : (307).Prime)
  intro n hn0 hn61 hpr
  interval_cases n
  · rw [a_eq_of_primes rfl hp0 hp1 hp2] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp1 hp2 hp3] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp2 hp3 hp4]; decide
  · rw [a_eq_of_primes rfl hp3 hp4 hp5] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp4 hp5 hp6]; decide
  · rw [a_eq_of_primes rfl hp5 hp6 hp7] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp6 hp7 hp8] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp7 hp8 hp9]; decide
  · rw [a_eq_of_primes rfl hp8 hp9 hp10] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp9 hp10 hp11]; decide
  · rw [a_eq_of_primes rfl hp10 hp11 hp12] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp11 hp12 hp13] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp12 hp13 hp14] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp13 hp14 hp15]; decide
  · rw [a_eq_of_primes rfl hp14 hp15 hp16]; decide
  · rw [a_eq_of_primes rfl hp15 hp16 hp17] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp16 hp17 hp18] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp17 hp18 hp19] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp18 hp19 hp20] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp19 hp20 hp21] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp20 hp21 hp22] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp21 hp22 hp23] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp22 hp23 hp24] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp23 hp24 hp25] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp24 hp25 hp26] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp25 hp26 hp27] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp26 hp27 hp28] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp27 hp28 hp29] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp28 hp29 hp30] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp29 hp30 hp31] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp30 hp31 hp32] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp31 hp32 hp33] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp32 hp33 hp34] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp33 hp34 hp35] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp34 hp35 hp36] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp35 hp36 hp37] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp36 hp37 hp38] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp37 hp38 hp39] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp38 hp39 hp40] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp39 hp40 hp41] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp40 hp41 hp42] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp41 hp42 hp43] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp42 hp43 hp44] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp43 hp44 hp45] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp44 hp45 hp46] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp45 hp46 hp47] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp46 hp47 hp48] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp47 hp48 hp49] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp48 hp49 hp50] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp49 hp50 hp51] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp50 hp51 hp52] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp51 hp52 hp53] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp52 hp53 hp54] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp53 hp54 hp55] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp54 hp55 hp56] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp55 hp56 hp57] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp56 hp57 hp58] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp57 hp58 hp59] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp58 hp59 hp60] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp59 hp60 hp61] at hpr; norm_num at hpr
  · rw [a_eq_of_primes rfl hp60 hp61 hp62]; decide

theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 :=
  prove_A182126_H2
