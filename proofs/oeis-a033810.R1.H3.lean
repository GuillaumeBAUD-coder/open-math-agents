import OMAReductions.R_oeis_a033810_R1

open OMA.S_oeis_a033810

namespace BirthdayFinite

private noncomputable def lowerLog : ℝ := 693147180 / 1000000000
private noncomputable def upperLog : ℝ := 693147181 / 1000000000

private noncomputable def estimate (n s t l : ℝ) : ℝ :=
  s + (3 - 2 * l) / 6 + (9 - 4 * l ^ 2) / (72 * t) - 2 * l ^ 2 / (135 * n)

private noncomputable def formula (n : ℕ) : ℝ :=
  estimate n (Real.sqrt (2 * n * Real.log 2)) (Real.sqrt (2 * n * Real.log 2)) (Real.log 2)

private theorem estimate_le_estimate {n₁ n₂ s₁ s₂ t₁ t₂ l₁ l₂ : ℝ}
    (hn₀ : 0 < n₁) (hn : n₁ ≤ n₂) (hs : s₁ ≤ s₂) (ht₀ : 0 < t₂) (ht : t₂ ≤ t₁)
    (hl₀ : 0 ≤ l₂) (hl : l₂ ≤ l₁) (hl₁ : l₁ ≤ 1) :
    estimate n₁ s₁ t₁ l₁ ≤ estimate n₂ s₂ t₂ l₂ := by
  have hlpos : 0 ≤ l₁ := hl₀.trans hl
  have hsquare : l₂ ^ 2 ≤ l₁ ^ 2 := by gcongr
  have hbounded : l₁ ^ 2 ≤ 1 := by
    calc l₁ ^ 2 ≤ (1 : ℝ) ^ 2 := by gcongr
         _ = 1 := by norm_num
  have hconstant : (3 - 2 * l₁) / 6 ≤ (3 - 2 * l₂) / 6 := by linarith
  have hreciprocal : (9 - 4 * l₁ ^ 2) / (72 * t₁) ≤ (9 - 4 * l₂ ^ 2) / (72 * t₂) := by
    have htpos : 0 < 72 * t₂ := by positivity
    have hd : 72 * t₂ ≤ 72 * t₁ := by linarith
    have hnum : 0 ≤ 9 - 4 * l₁ ^ 2 := by linarith
    exact (div_le_div_of_nonneg_left hnum htpos hd).trans (div_le_div_of_nonneg_right (by linarith) htpos.le)
  have hinverse : 2 * l₂ ^ 2 / (135 * n₂) ≤ 2 * l₁ ^ 2 / (135 * n₁) := by
    have hnpos : 0 < 135 * n₁ := by positivity
    have hd : 135 * n₁ ≤ 135 * n₂ := by linarith
    exact (div_le_div_of_nonneg_left (by positivity) hnpos hd).trans
      (div_le_div_of_nonneg_right (by linarith) hnpos.le)
  unfold estimate
  linarith

private theorem ceil_in_block (n lo hi k : ℕ) (slo shi : ℝ)
    (hlo : lo ≤ n) (hhi : n ≤ hi) (hlop : 0 < lo) (hslo : 0 < slo)
    (hshi : 0 ≤ shi) (hlosq : slo ^ 2 ≤ 2 * lo * lowerLog)
    (hhisq : 2 * hi * upperLog ≤ shi ^ 2)
    (hlower : (k : ℝ) - 1 < estimate lo slo shi upperLog)
    (hupper : estimate hi shi slo lowerLog ≤ k) :
    (Int.ceil (formula n)).toNat = k := by
  have hLogLo : lowerLog ≤ Real.log 2 := by
    unfold lowerLog
    linarith [Real.log_two_gt_d9]
  have hLogHi : Real.log 2 ≤ upperLog := by
    unfold upperLog
    linarith [Real.log_two_lt_d9]
  have hLogNonneg : 0 ≤ lowerLog := by norm_num [lowerLog]
  have hLogLeOne : upperLog ≤ 1 := by norm_num [upperLog]
  have hlo' : (lo : ℝ) ≤ n := by exact_mod_cast hlo
  have hhi' : (n : ℝ) ≤ hi := by exact_mod_cast hhi
  have hpos : (0 : ℝ) < lo := by exact_mod_cast hlop
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hpos hlo'
  have hLog : 0 ≤ Real.log 2 := hLogNonneg.trans hLogLo
  let s := Real.sqrt (2 * (n : ℝ) * Real.log 2)
  have hsL : slo ≤ s := by
    apply Real.le_sqrt_of_sq_le
    refine hlosq.trans ?_
    gcongr
  have hsU : s ≤ shi := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hshi, ?_⟩
    refine le_trans ?_ hhisq
    gcongr
  have hLo : estimate lo slo shi upperLog ≤ formula n :=
    estimate_le_estimate hpos hlo' hsL (hslo.trans_le hsL) hsU hLog hLogHi hLogLeOne
  have hHi : formula n ≤ estimate hi shi slo lowerLog :=
    estimate_le_estimate hnpos hhi' hsU hslo hsL hLogNonneg hLogLo (hLogHi.trans hLogLeOne)
  have hc : Int.ceil (formula n) = (k : ℤ) := by
    apply Int.ceil_eq_iff.mpr
    exact ⟨by exact_mod_cast hlower.trans_le hLo, by exact_mod_cast hHi.trans hupper⟩
  simp [hc]

private theorem pDistinct_days {m n k : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hk : k ≤ m + 1) :
    pDistinct m k ≤ pDistinct n k := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hn' := hm'.trans_le hmn'
  unfold pDistinct
  apply Finset.prod_le_prod
  · intro i hi
    have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hi')) hm'.le
  · intro i _
    rw [sub_div, sub_div, div_self hm'.ne', div_self hn'.ne']
    exact sub_le_sub_left (div_le_div_of_nonneg_left (Nat.cast_nonneg i) hm' hmn') 1

private theorem pDistinct_factorial (n k : ℕ) (hk : k ≤ n + 1) :
    pDistinct n k = (n.descFactorial k : ℝ) / (n : ℝ) ^ k := by
  induction k with
  | zero => simp [pDistinct]
  | succ k ih =>
    have hkn : k ≤ n := by omega
    rw [pDistinct, Finset.prod_range_succ]
    change pDistinct n k * _ = _
    rw [ih (by omega), Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hkn, pow_succ, mul_div_mul_comm]
    ring

private theorem upper_endpoint (n k : ℕ) (hn : 0 < n) (hk : k ≤ n + 1)
    (h : 2 * n.descFactorial k ≤ n ^ k) : (1 : ℝ) / 2 ≤ 1 - pDistinct n k := by
  have h' : 2 * (n.descFactorial k : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast h
  have hp : (0 : ℝ) < (n : ℝ) ^ k := pow_pos (by exact_mod_cast hn) _
  have hh : pDistinct n k ≤ (1 : ℝ) / 2 := by
    rw [pDistinct_factorial n k hk]
    exact (div_le_iff₀ hp).mpr (by linarith)
  linarith

private theorem lower_endpoint (n k : ℕ) (hn : 0 < n) (hk : k ≤ n + 1)
    (h : n ^ k < 2 * n.descFactorial k) : 1 - pDistinct n k < (1 : ℝ) / 2 := by
  have h' : (n : ℝ) ^ k < 2 * (n.descFactorial k : ℝ) := by exact_mod_cast h
  have hp : (0 : ℝ) < (n : ℝ) ^ k := pow_pos (by exact_mod_cast hn) _
  have hh : (1 : ℝ) / 2 < pDistinct n k := by
    rw [pDistinct_factorial n k hk]
    exact (lt_div_iff₀ hp).mpr (by linarith)
  linarith

private theorem check_block (n lo hi k : ℕ) (slo shi : ℝ)
    (hlo : lo ≤ n) (hhi : n ≤ hi) (hlop : 0 < lo) (hk : k ≤ lo + 1)
    (hslo : 0 < slo) (hshi : 0 ≤ shi) (hlosq : slo ^ 2 ≤ 2 * lo * lowerLog)
    (hhisq : 2 * hi * upperLog ≤ shi ^ 2)
    (hlower : (k : ℝ) - 1 < estimate lo slo shi upperLog)
    (hupper : estimate hi shi slo lowerLog ≤ k)
    (dHi : 2 * hi.descFactorial k ≤ hi ^ k) (dLo : lo ^ (k - 1) < 2 * lo.descFactorial (k - 1)) :
    ((1 : ℝ) / 2 ≤ 1 - pDistinct n (Int.ceil (formula n)).toNat) ∧
      (1 - pDistinct n ((Int.ceil (formula n)).toNat - 1) < (1 : ℝ) / 2) := by
  rw [ceil_in_block n lo hi k slo shi hlo hhi hlop hslo hshi hlosq hhisq hlower hupper]
  have htop := upper_endpoint hi k (by omega) (by omega) dHi
  have hbottom := lower_endpoint lo (k - 1) hlop (by omega) dLo
  have hmonoHi : pDistinct n k ≤ pDistinct hi k := pDistinct_days (by omega) hhi (by omega)
  have hmonoLo : pDistinct lo (k - 1) ≤ pDistinct n (k - 1) := pDistinct_days hlop hlo (by omega)
  constructor <;> linarith

end BirthdayFinite

namespace BirthdayFinite

set_option maxHeartbeats 4000000 in
private theorem both (n : ℕ) (hn : 1 ≤ n) (hbound : n < 1000) :
    ((1 : ℝ) / 2 ≤ 1 - pDistinct n (Int.ceil (formula n)).toNat) ∧
      (1 - pDistinct n ((Int.ceil (formula n)).toNat - 1) < (1 : ℝ) / 2) := by
  by_cases within1 : n ≤ 1
  · exact check_block n 1 1 2 (11774100220 / 10000000000) (11774100229 / 10000000000)
      (by omega) within1 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within2 : n ≤ 2
  · exact check_block n 2 2 2 (16651092216 / 10000000000) (16651092229 / 10000000000)
      (by omega) within2 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within5 : n ≤ 5
  · exact check_block n 3 5 3 (20393339795 / 10000000000) (26327688486 / 10000000000)
      (by omega) within5 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within9 : n ≤ 9
  · exact check_block n 6 9 4 (28840537720 / 10000000000) (35322300687 / 10000000000)
      (by omega) within9 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within15 : n ≤ 15
  · exact check_block n 10 15 5 (37232974095 / 10000000000) (45600894104 / 10000000000)
      (by omega) within15 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within16 : n ≤ 16
  · exact check_block n 16 16 5 (47096400881 / 10000000000) (47096400916 / 10000000000)
      (by omega) within16 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within23 : n ≤ 23
  · exact check_block n 17 23 6 (48545858855 / 10000000000) (56466601037 / 10000000000)
      (by omega) within23 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within32 : n ≤ 32
  · exact check_block n 24 32 7 (57681075440 / 10000000000) (66604368914 / 10000000000)
      (by omega) within32 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within42 : n ≤ 42
  · exact check_block n 33 42 8 (67637056322 / 10000000000) (76304890541 / 10000000000)
      (by omega) within42 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within54 : n ≤ 54
  · exact check_block n 43 54 9 (77207938374 / 10000000000) (86521613224 / 10000000000)
      (by omega) within54 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within68 : n ≤ 68
  · exact check_block n 55 68 10 (87319064241 / 10000000000) (97091717781 / 10000000000)
      (by omega) within68 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within82 : n ≤ 82
  · exact check_block n 69 82 11 (97803021855 / 10000000000) (106619012228 / 10000000000)
      (by omega) within82 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within99 : n ≤ 99
  · exact check_block n 83 99 12 (107267158012 / 10000000000) (117150818110 / 10000000000)
      (by omega) within99 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within116 : n ≤ 116
  · exact check_block n 100 116 13 (117741002203 / 10000000000) (126810940377 / 10000000000)
      (by omega) within116 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within135 : n ≤ 135
  · exact check_block n 117 135 14 (127356366201 / 10000000000) (136802682310 / 10000000000)
      (by omega) within135 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within156 : n ≤ 156
  · exact check_block n 136 156 15 (137308423980 / 10000000000) (147058464725 / 10000000000)
      (by omega) within156 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within178 : n ≤ 178
  · exact check_block n 157 178 16 (147529052908 / 10000000000) (157086089912 / 10000000000)
      (by omega) within178 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within201 : n ≤ 201
  · exact check_block n 179 201 17 (157526724856 / 10000000000) (166926680541 / 10000000000)
      (by omega) within201 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within226 : n ≤ 226
  · exact check_block n 202 226 18 (167341405730 / 10000000000) (177003538330 / 10000000000)
      (by omega) within226 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within252 : n ≤ 252
  · exact check_block n 227 252 19 (177394706719 / 10000000000) (186908046704 / 10000000000)
      (by omega) within252 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within280 : n ≤ 280
  · exact check_block n 253 280 20 (187278528689 / 10000000000) (197018380199 / 10000000000)
      (by omega) within280 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within309 : n ≤ 309
  · exact check_block n 281 309 21 (197369885028 / 10000000000) (206969794381 / 10000000000)
      (by omega) within309 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within340 : n ≤ 340
  · exact check_block n 310 340 22 (207304426291 / 10000000000) (217103681010 / 10000000000)
      (by omega) within340 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within372 : n ≤ 372
  · exact check_block n 341 372 23 (217422716559 / 10000000000) (227090621265 / 10000000000)
      (by omega) within372 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within406 : n ≤ 406
  · exact check_block n 373 406 24 (227395645578 / 10000000000) (237241545892 / 10000000000)
      (by omega) within406 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within441 : n ≤ 441
  · exact check_block n 407 441 25 (237533535426 / 10000000000) (247256104807 / 10000000000)
      (by omega) within441 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within477 : n ≤ 477
  · exact check_block n 442 477 26 (247536281607 / 10000000000) (257150230542 / 10000000000)
      (by omega) within477 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within515 : n ≤ 515
  · exact check_block n 478 515 27 (257419638737 / 10000000000) (267196855601 / 10000000000)
      (by omega) within515 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within554 : n ≤ 554
  · exact check_block n 516 554 28 (267456144023 / 10000000000) (277129405973 / 10000000000)
      (by omega) within554 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within595 : n ≤ 595
  · exact check_block n 555 595 29 (277379409798 / 10000000000) (287201174335 / 10000000000)
      (by omega) within595 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within637 : n ≤ 637
  · exact check_block n 596 637 30 (287442418331 / 10000000000) (297164854685 / 10000000000)
      (by omega) within637 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within681 : n ≤ 681
  · exact check_block n 638 681 31 (297398016415 / 10000000000) (307256645254 / 10000000000)
      (by omega) within681 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within726 : n ≤ 726
  · exact check_block n 682 726 32 (307482154526 / 10000000000) (317245915153 / 10000000000)
      (by omega) within726 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within772 : n ≤ 772
  · exact check_block n 727 772 33 (317464328660 / 10000000000) (327142055913 / 10000000000)
      (by omega) within772 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within820 : n ≤ 820
  · exact check_block n 773 820 34 (327353866676 / 10000000000) (337158920517 / 10000000000)
      (by omega) within820 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within869 : n ≤ 869
  · exact check_block n 821 869 35 (337364442340 / 10000000000) (347086415836 / 10000000000)
      (by omega) within869 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within920 : n ≤ 920
  · exact check_block n 870 920 36 (347286062663 / 10000000000) (357126142006 / 10000000000)
      (by omega) within920 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within973 : n ≤ 973
  · exact check_block n 921 973 37 (357320179329 / 10000000000) (367268895257 / 10000000000)
      (by omega) within973 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  by_cases within999 : n ≤ 999
  · exact check_block n 974 999 38 (367457576686 / 10000000000) (372143529789 / 10000000000)
      (by omega) within999 (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num [lowerLog]) (by norm_num [upperLog])
      (by norm_num [estimate, upperLog]) (by norm_num [estimate, lowerLog])
      (by decide) (by decide)
  omega

end BirthdayFinite

theorem OMA.solution : OMA.R_oeis_a033810_R1.H3 := by
  intro n hn hbound
  exact (BirthdayFinite.both n hn hbound).1
