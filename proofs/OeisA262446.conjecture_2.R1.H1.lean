import OMAReductions.R_OeisA262446_conjecture_2_R1

-- Step OeisA262446.conjecture_2.R1.H1
-- Credit: @caa1982

private def primesLe230 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229]

private lemma primesLe230_sorted : primesLe230.Pairwise (· ≤ ·) := by decide +kernel

private lemma primesLe230_prime : ∀ p ∈ primesLe230, p.Prime := by decide +kernel

private lemma mem_primesLe230_of_prime :
    ∀ p ∈ Finset.range 231, p.Prime → p ∈ primesLe230 := by decide +kernel

private def checkDivs : List ℕ → ℕ → Bool
  | [], _ => true
  | p :: ps, m =>
    if m < p * p then true
    else if m % p == 0 then false
    else checkDivs ps m

private def isPrimeFast (m : ℕ) : Bool :=
  decide (2 ≤ m) && checkDivs primesLe230 m

private lemma checkDivs_eq_true_iff {ps : List ℕ} (hs : ps.Pairwise (· ≤ ·)) (m : ℕ) :
    checkDivs ps m = true ↔ ∀ p ∈ ps, p * p ≤ m → m % p ≠ 0 := by
  induction ps with
  | nil => simp [checkDivs]
  | cons p ps ih =>
    obtain ⟨hple, hps⟩ := List.pairwise_cons.mp hs
    simp only [checkDivs]
    split_ifs with hlt hmod
    · constructor
      · intro _ q hq hq2
        rcases List.mem_cons.mp hq with rfl | hq'
        · omega
        · have hpq : p ≤ q := hple q hq'
          have : p * p ≤ q * q := Nat.mul_le_mul hpq hpq
          omega
      · intro _; rfl
    · constructor
      · intro h; simp at h
      · intro h
        have hm0 : m % p = 0 := beq_iff_eq.mp hmod
        exact absurd hm0 (h p (List.mem_cons_self ..) (by omega))
    · constructor
      · intro h q hq hq2
        rcases List.mem_cons.mp hq with rfl | hq'
        · intro hm0
          exact hmod (beq_iff_eq.mpr hm0)
        · exact (ih hps).mp h q hq' hq2
      · intro h
        apply (ih hps).mpr
        intro q hq hq2
        exact h q (List.mem_cons_of_mem p hq) hq2

private lemma isPrimeFast_iff {m : ℕ} (hm : m ≤ 52976) :
    isPrimeFast m = true ↔ m.Prime := by
  simp only [isPrimeFast, Bool.and_eq_true, decide_eq_true_eq,
    checkDivs_eq_true_iff primesLe230_sorted]
  constructor
  · rintro ⟨hm2, hnodiv⟩
    rw [Nat.prime_def_minFac]
    refine ⟨hm2, ?_⟩
    by_contra hne
    have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
    have hsq : m.minFac * m.minFac ≤ m := by
      have := Nat.minFac_sq_le_self (by omega : 0 < m) (fun hmp => hne hmp.minFac_eq)
      simpa [sq] using this
    have hp230 : m.minFac < 231 := by nlinarith
    have hmem : m.minFac ∈ primesLe230 :=
      mem_primesLe230_of_prime m.minFac (Finset.mem_range.mpr hp230) hp
    have hmod : m % m.minFac = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd m)
    exact hnodiv m.minFac hmem hsq hmod
  · intro hmp
    refine ⟨hmp.two_le, ?_⟩
    intro p hp hp2 hmod
    have hp_prime : p.Prime := primesLe230_prime p hp
    have hdvd : p ∣ m := Nat.dvd_of_mod_eq_zero hmod
    rcases hmp.eq_one_or_self_of_dvd p hdvd with h1 | hpm
    · exact hp_prime.ne_one h1
    · have hp2' : 2 ≤ p := hp_prime.two_le
      nlinarith

private def countAcc (lo : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | rem + 1, acc =>
    countAcc (lo + 1) rem (if isPrimeFast lo then acc + 1 else acc)

private lemma countAcc_add (lo rem acc : ℕ) :
    countAcc lo rem acc = acc + countAcc lo rem 0 := by
  induction rem generalizing lo acc with
  | zero => simp [countAcc]
  | succ r ih =>
    simp only [countAcc]
    split_ifs
    · rw [ih (lo + 1) (acc + 1), ih (lo + 1) 1]
      omega
    · rw [ih (lo + 1) acc]

private lemma count_eq_add_countAcc (lo rem : ℕ) (hhi : lo + rem ≤ 52977) :
    Nat.count Nat.Prime (lo + rem) = Nat.count Nat.Prime lo + countAcc lo rem 0 := by
  induction rem generalizing lo with
  | zero => simp [countAcc]
  | succ r ih =>
    have hstep : lo + (r + 1) = (lo + 1) + r := by omega
    rw [hstep, ih (lo + 1) (by omega), Nat.count_succ]
    simp only [countAcc]
    rw [countAcc_add (lo + 1) r (if isPrimeFast lo then 1 else 0)]
    have hiff : isPrimeFast lo = true ↔ lo.Prime := isPrimeFast_iff (by omega)
    by_cases hp : lo.Prime
    · have ht : isPrimeFast lo = true := hiff.mpr hp
      simp only [ht, ↓reduceIte, hp]
      omega
    · have hf : isPrimeFast lo = false := Bool.eq_false_iff.mpr (fun h => hp (hiff.mp h))
      simp only [hf, Bool.false_eq_true, ↓reduceIte, hp, zero_add]
      omega

private inductive T
  | leaf (v : ℕ)
  | node (l r : T)

private def T.get : T → ℕ → ℕ → ℕ
  | T.leaf v, _, _ => v
  | T.node l _r, 0, _ => l.get 0 0
  | T.node l r, d + 1, i =>
    if i < 2 ^ d then l.get d i else r.get d (i - 2 ^ d)

private def bTree : T := T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 0) (T.leaf 1)) (T.node (T.leaf 2) (T.leaf 4))) (T.node (T.node (T.leaf 5) (T.leaf 6)) (T.node (T.leaf 8) (T.leaf 10)))) (T.node (T.node (T.node (T.leaf 12) (T.leaf 14)) (T.node (T.leaf 16) (T.leaf 19))) (T.node (T.node (T.leaf 22) (T.leaf 24)) (T.node (T.leaf 27) (T.leaf 30))))) (T.node (T.node (T.node (T.node (T.leaf 33) (T.leaf 36)) (T.node (T.leaf 39) (T.leaf 43))) (T.node (T.node (T.leaf 47) (T.leaf 50)) (T.node (T.leaf 54) (T.leaf 59)))) (T.node (T.node (T.node (T.leaf 62) (T.leaf 66)) (T.node (T.leaf 70) (T.leaf 75))) (T.node (T.node (T.leaf 79) (T.leaf 84)) (T.node (T.leaf 90) (T.leaf 94)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 99) (T.leaf 102)) (T.node (T.leaf 108) (T.leaf 115))) (T.node (T.node (T.leaf 121) (T.leaf 126)) (T.node (T.leaf 131) (T.leaf 137)))) (T.node (T.node (T.node (T.leaf 142) (T.leaf 149)) (T.node (T.leaf 154) (T.leaf 161))) (T.node (T.node (T.leaf 167) (T.leaf 174)) (T.node (T.leaf 180) (T.leaf 189))))) (T.node (T.node (T.node (T.node (T.leaf 193) (T.leaf 200)) (T.node (T.leaf 205) (T.leaf 217))) (T.node (T.node (T.leaf 220) (T.leaf 226)) (T.node (T.leaf 235) (T.leaf 242)))) (T.node (T.node (T.node (T.leaf 251) (T.leaf 259)) (T.node (T.leaf 267) (T.leaf 274))) (T.node (T.node (T.leaf 282) (T.leaf 290)) (T.node (T.leaf 297) (T.leaf 306))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 313) (T.leaf 324)) (T.node (T.leaf 329) (T.leaf 338))) (T.node (T.node (T.leaf 348) (T.leaf 358)) (T.node (T.leaf 367) (T.leaf 375)))) (T.node (T.node (T.node (T.leaf 381) (T.leaf 393)) (T.node (T.leaf 403) (T.leaf 414))) (T.node (T.node (T.leaf 423) (T.leaf 431)) (T.node (T.leaf 440) (T.leaf 446))))) (T.node (T.node (T.node (T.node (T.leaf 457) (T.leaf 467)) (T.node (T.leaf 478) (T.leaf 487))) (T.node (T.node (T.leaf 500) (T.leaf 510)) (T.node (T.leaf 522) (T.leaf 531)))) (T.node (T.node (T.node (T.leaf 542) (T.leaf 552)) (T.node (T.leaf 564) (T.leaf 574))) (T.node (T.node (T.leaf 587) (T.leaf 596)) (T.node (T.leaf 607) (T.leaf 618)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 630) (T.leaf 640)) (T.node (T.leaf 650) (T.leaf 662))) (T.node (T.node (T.leaf 676) (T.leaf 686)) (T.node (T.leaf 697) (T.leaf 708)))) (T.node (T.node (T.node (T.leaf 721) (T.leaf 734)) (T.node (T.leaf 747) (T.leaf 758))) (T.node (T.node (T.leaf 775) (T.leaf 783)) (T.node (T.leaf 796) (T.leaf 809))))) (T.node (T.node (T.node (T.node (T.leaf 824) (T.leaf 836)) (T.node (T.leaf 847) (T.leaf 859))) (T.node (T.node (T.leaf 873) (T.leaf 887)) (T.node (T.leaf 903) (T.leaf 914)))) (T.node (T.node (T.node (T.leaf 928) (T.leaf 938)) (T.node (T.leaf 950) (T.leaf 968))) (T.node (T.node (T.leaf 982) (T.leaf 994)) (T.node (T.leaf 1007) (T.leaf 1022)))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 1035) (T.leaf 1049)) (T.node (T.leaf 1061) (T.leaf 1077))) (T.node (T.node (T.leaf 1094) (T.leaf 1108)) (T.node (T.leaf 1124) (T.leaf 1138)))) (T.node (T.node (T.node (T.leaf 1152) (T.leaf 1170)) (T.node (T.leaf 1184) (T.leaf 1199))) (T.node (T.node (T.leaf 1218) (T.leaf 1231)) (T.node (T.leaf 1246) (T.leaf 1262))))) (T.node (T.node (T.node (T.node (T.leaf 1277) (T.leaf 1290)) (T.node (T.leaf 1308) (T.leaf 1322))) (T.node (T.node (T.leaf 1337) (T.leaf 1354)) (T.node (T.leaf 1369) (T.leaf 1383)))) (T.node (T.node (T.node (T.leaf 1398) (T.leaf 1411)) (T.node (T.leaf 1430) (T.leaf 1446))) (T.node (T.node (T.leaf 1463) (T.leaf 1480)) (T.node (T.leaf 1500) (T.leaf 1519)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 1532) (T.leaf 1553)) (T.node (T.leaf 1570) (T.leaf 1586))) (T.node (T.node (T.leaf 1602) (T.leaf 1619)) (T.node (T.leaf 1637) (T.leaf 1655)))) (T.node (T.node (T.node (T.leaf 1670) (T.leaf 1683)) (T.node (T.leaf 1701) (T.leaf 1720))) (T.node (T.node (T.leaf 1743) (T.leaf 1757)) (T.node (T.leaf 1776) (T.leaf 1800))))) (T.node (T.node (T.node (T.node (T.leaf 1816) (T.leaf 1837)) (T.node (T.leaf 1857) (T.leaf 1876))) (T.node (T.node (T.leaf 1891) (T.leaf 1908)) (T.node (T.leaf 1926) (T.leaf 1943)))) (T.node (T.node (T.node (T.leaf 1962) (T.leaf 1981)) (T.node (T.leaf 2000) (T.leaf 2021))) (T.node (T.node (T.leaf 2039) (T.leaf 2057)) (T.node (T.leaf 2080) (T.leaf 2101))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 2122) (T.leaf 2137)) (T.node (T.leaf 2152) (T.leaf 2169))) (T.node (T.node (T.leaf 2188) (T.leaf 2213)) (T.node (T.leaf 2230) (T.leaf 2250)))) (T.node (T.node (T.node (T.leaf 2272) (T.leaf 2293)) (T.node (T.leaf 2313) (T.leaf 2331))) (T.node (T.node (T.leaf 2352) (T.leaf 2373)) (T.node (T.leaf 2394) (T.leaf 2417))))) (T.node (T.node (T.node (T.node (T.leaf 2438) (T.leaf 2460)) (T.node (T.leaf 2484) (T.leaf 2503))) (T.node (T.node (T.leaf 2524) (T.leaf 2547)) (T.node (T.leaf 2565) (T.leaf 2591)))) (T.node (T.node (T.node (T.leaf 2609) (T.leaf 2631)) (T.node (T.leaf 2654) (T.leaf 2680))) (T.node (T.node (T.leaf 2700) (T.leaf 2721)) (T.node (T.leaf 2738) (T.leaf 2760)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 2781) (T.leaf 2803)) (T.node (T.leaf 2825) (T.leaf 2847))) (T.node (T.node (T.leaf 2869) (T.leaf 2893)) (T.node (T.leaf 2915) (T.leaf 2939)))) (T.node (T.node (T.node (T.leaf 2963) (T.leaf 2984)) (T.node (T.leaf 3004) (T.leaf 3022))) (T.node (T.node (T.leaf 3053) (T.leaf 3074)) (T.node (T.leaf 3095) (T.leaf 3124))))) (T.node (T.node (T.node (T.node (T.leaf 3148) (T.leaf 3169)) (T.node (T.leaf 3195) (T.leaf 3217))) (T.node (T.node (T.leaf 3238) (T.leaf 3259)) (T.node (T.leaf 3282) (T.leaf 3302)))) (T.node (T.node (T.node (T.leaf 3330) (T.leaf 3352)) (T.node (T.leaf 3380) (T.leaf 3402))) (T.node (T.node (T.leaf 3424) (T.leaf 3447)) (T.node (T.leaf 3476) (T.leaf 3503))))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 3525) (T.leaf 3553)) (T.node (T.leaf 3578) (T.leaf 3607))) (T.node (T.node (T.leaf 3633) (T.leaf 3653)) (T.node (T.leaf 3679) (T.leaf 3707)))) (T.node (T.node (T.node (T.leaf 3732) (T.leaf 3754)) (T.node (T.leaf 3780) (T.leaf 3801))) (T.node (T.node (T.leaf 3829) (T.leaf 3854)) (T.node (T.leaf 3879) (T.leaf 3908))))) (T.node (T.node (T.node (T.node (T.leaf 3935) (T.leaf 3960)) (T.node (T.leaf 3990) (T.leaf 4010))) (T.node (T.node (T.leaf 4034) (T.leaf 4059)) (T.node (T.leaf 4086) (T.leaf 4112)))) (T.node (T.node (T.node (T.leaf 4141) (T.leaf 4166)) (T.node (T.leaf 4196) (T.leaf 4221))) (T.node (T.node (T.leaf 4242) (T.leaf 4266)) (T.node (T.leaf 4295) (T.leaf 4324)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 4353) (T.leaf 4381)) (T.node (T.leaf 4411) (T.leaf 4445))) (T.node (T.node (T.leaf 4473) (T.leaf 4502)) (T.node (T.leaf 4522) (T.leaf 4550)))) (T.node (T.node (T.node (T.leaf 4572) (T.leaf 4604)) (T.node (T.leaf 4632) (T.leaf 4661))) (T.node (T.node (T.leaf 4687) (T.leaf 4714)) (T.node (T.leaf 4739) (T.leaf 4765))))) (T.node (T.node (T.node (T.node (T.leaf 4794) (T.leaf 4822)) (T.node (T.leaf 4849) (T.leaf 4874))) (T.node (T.node (T.leaf 4905) (T.leaf 4935)) (T.node (T.leaf 4963) (T.leaf 4990)))) (T.node (T.node (T.node (T.leaf 5022) (T.leaf 5051)) (T.node (T.leaf 5081) (T.leaf 5110))) (T.node (T.node (T.leaf 5142) (T.leaf 5172)) (T.node (T.leaf 5197) (T.leaf 5224))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 5255) (T.leaf 5289)) (T.node (T.leaf 5319) (T.leaf 5349))) (T.node (T.node (T.leaf 5375) (T.leaf 5406)) (T.leaf 0))) (T.leaf 0)) (T.leaf 0)) (T.leaf 0))) (T.leaf 0))

private def bTbl (k : ℕ) : ℕ := bTree.get 9 k

private def checkStep (k : ℕ) : Bool :=
  bTbl (k + 1) == bTbl k + countAcc (Nat.triangular k + 2) (k + 1) 0

private def checkChunk (start : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 => checkStep start && checkChunk (start + 1) len

private lemma checkChunk_spec {start len : ℕ} (h : checkChunk start len = true) :
    ∀ k, start ≤ k → k < start + len → checkStep k = true := by
  induction len generalizing start with
  | zero => intro k h1 h2; omega
  | succ l ih =>
    simp only [checkChunk, Bool.and_eq_true] at h
    intro k h1 h2
    by_cases heq : k = start
    · subst heq; exact h.1
    · exact ih h.2 k (by omega) (by omega)

set_option maxHeartbeats 800000 in
private lemma hc0 : checkChunk 0 65 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma hc1 : checkChunk 65 65 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma hc2 : checkChunk 130 65 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma hc3 : checkChunk 195 65 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma hc4 : checkChunk 260 65 = true := by decide +kernel

private lemma hstep_all (k : ℕ) (hk : k < 325) :
    bTbl (k + 1) = bTbl k + countAcc (Nat.triangular k + 2) (k + 1) 0 := by
  have hc : checkStep k = true := by
    by_cases h0 : k < 65
    · exact checkChunk_spec hc0 k (by omega) h0
    by_cases h1 : k < 130
    · exact checkChunk_spec hc1 k (by omega) h1
    by_cases h2 : k < 195
    · exact checkChunk_spec hc2 k (by omega) h2
    by_cases h3 : k < 260
    · exact checkChunk_spec hc3 k (by omega) h3
    · exact checkChunk_spec hc4 k (by omega) (by omega)
  exact beq_iff_eq.mp hc

private lemma tri_succ (k : ℕ) : Nat.triangular (k + 1) = Nat.triangular k + (k + 1) := by
  rw [Nat.triangular, Nat.triangular]
  have h1 : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
  rw [h1, Nat.add_mul_div_left _ _ (by omega : 0 < 2)]

private lemma b_eq_bTbl (k : ℕ) (hk : k ≤ 325) : OeisA262446.b k = bTbl k := by
  induction k with
  | zero =>
    unfold OeisA262446.b
    decide +kernel
  | succ m ih =>
    have hm : m < 325 := by omega
    have htri : Nat.triangular m + 2 + (m + 1) ≤ 52977 := by
      rw [Nat.triangular]
      have : m * (m + 1) ≤ 324 * 325 := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hcount := count_eq_add_countAcc (Nat.triangular m + 2) (m + 1) htri
    have heq : Nat.triangular (m + 1) + 2 = Nat.triangular m + 2 + (m + 1) := by
      rw [tri_succ]; omega
    unfold OeisA262446.b at ih ⊢
    rw [Nat.primeCounting, Nat.primeCounting'] at ih ⊢
    rw [show Nat.triangular (m + 1) + 1 + 1 = Nat.triangular m + 2 + (m + 1) by omega,
      hcount, show Nat.triangular m + 2 = Nat.triangular m + 1 + 1 by omega,
      ih (by omega), ← hstep_all m hm]

private def aFast (n : ℕ) : ℕ :=
  let target := bTbl n
  ∑ k ∈ Finset.Ico 1 n,
    ((Finset.Ico (k + 1) n).filter (fun m => target = bTbl k + bTbl m)).card

private lemma a_eq_aFast {n : ℕ} (hn : n ≤ 325) : OeisA262446.a n = aFast n := by
  unfold OeisA262446.a aFast
  rw [b_eq_bTbl n hn]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 325 := by
    have := (Finset.mem_Ico.mp hk).2
    omega
  congr 1
  apply Finset.filter_congr
  intro m hm
  have hm' : m ≤ 325 := by
    have := (Finset.mem_Ico.mp hm).2
    omega
  rw [b_eq_bTbl k hk', b_eq_bTbl m hm']

private lemma hFast :
    ∀ n ∈ ({4, 6, 11, 21, 54, 253, 325} : Finset ℕ), aFast n = 1 := by decide +kernel

theorem OMA.solution : OMA.R_OeisA262446_conjecture_2_R1.H1 := by
  intro n hn
  have hle : n ≤ 325 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  rw [a_eq_aFast hle]
  exact hFast n hn
