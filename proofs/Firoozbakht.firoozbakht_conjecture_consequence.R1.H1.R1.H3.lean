import OMAReductions.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Push

/-!
A Legendre sieve certificate for the lower bound on the number of primes up to
90,000,000. At each prime, multiples of that prime are removed by a bijection.
The numerical lemmas record the survivor count after each sieve stage so that
the kernel can check the stages separately.
-/

namespace PrimeCountCertificate

open Finset Nat

def survivors (k n : ℕ) : Finset ℕ :=
  (Icc 1 n).filter fun x => x.Coprime (primorial k)

lemma mem_survivors {k n x : ℕ} : x ∈ survivors k n ↔
    1 ≤ x ∧ x ≤ n ∧ x.Coprime (primorial k) := by
  simp [survivors, and_assoc]

lemma next_product (k : ℕ) : primorial (k+1) =
    if (k+1).Prime then primorial k * (k+1) else primorial k := by
  simp [primorial, Finset.prod_filter, Finset.prod_range_succ]

lemma sieve_step (k n : ℕ) (hp : (k+1).Prime) :
    (survivors (k+1) n).card =
      (survivors k n).card - (survivors k (n/(k+1))).card := by
  let p := k+1
  have hpos : 0 < p := hp.pos
  have hc : p.Coprime (primorial k) :=
    hp.coprime_iff_not_dvd.mpr (fun h => by have := hp.dvd_primorial_iff.mp h; omega)
  have split := Finset.card_filter_add_card_filter_not (s := survivors k n) (fun x => p ∣ x)
  have rest : ((survivors k n).filter fun x => ¬ p ∣ x) = survivors (k+1) n := by
    ext x
    simp [mem_survivors, next_product, hp, Nat.coprime_mul_iff_right,
      Nat.coprime_comm (n := x) (m := p), hp.coprime_iff_not_dvd, p, and_assoc]
  have multiples : (survivors k (n/p)).card = ((survivors k n).filter fun x => p ∣ x).card := by
    apply Finset.card_bij (fun x _ => x*p)
    · intro x hx
      obtain ⟨hx1,hxn,hxc⟩ := mem_survivors.mp hx
      exact mem_filter.mpr ⟨mem_survivors.mpr ⟨Nat.mul_pos hx1 hpos,
        (Nat.le_div_iff_mul_le hpos).mp hxn, Nat.coprime_mul_iff_left.mpr ⟨hxc,hc⟩⟩,
        dvd_mul_left _ _⟩
    · intro x hx y hy he
      exact Nat.eq_of_mul_eq_mul_right hpos he
    · intro y hy
      obtain ⟨hy,hd⟩ := mem_filter.mp hy
      obtain ⟨hy1,hyn,hyc⟩ := mem_survivors.mp hy
      obtain ⟨x,rfl⟩ := hd
      rw [Nat.mul_comm p x] at *
      exact ⟨x,mem_survivors.mpr ⟨by by_contra! h; simp [show x = 0 by omega] at hy1,
        (Nat.le_div_iff_mul_le hpos).mpr hyn,(Nat.coprime_mul_iff_left.mp hyc).1⟩,rfl⟩
  rw [rest, ← multiples] at split
  change (survivors (k+1) n).card = (survivors k n).card - (survivors k (n/p)).card
  omega

lemma small_count {k n : ℕ} (h : n ≤ k) : (survivors k n).card = min n 1 := by
  cases n with
  | zero => simp [survivors]
  | succ n =>
    have hset : survivors k (n+1) = {1} := by
      ext x
      simp only [mem_survivors, mem_singleton]
      constructor
      · rintro ⟨hx,hxn,hc⟩
        by_contra hne
        have q := Nat.minFac_prime hne
        exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨_, q, Nat.minFac_dvd x,
          q.dvd_primorial_iff.mpr ((Nat.minFac_le hx).trans (hxn.trans h))⟩) hc
      · rintro rfl
        simp
    simp [hset]

def primeList : ℕ → List ℕ
  | 0 => []
  | k+1 => if (k+1).Prime then (k+1) :: primeList k else primeList k

def legendreCount : List ℕ → ℕ → ℕ
  | [], n => n
  | p :: ps, n => if n ≤ p then min n 1 else legendreCount ps n - legendreCount ps (n/p)

theorem legendre_correct (k n : ℕ) :
    legendreCount (primeList k) n = (survivors k n).card := by
  induction k generalizing n with
  | zero => simp [primeList, legendreCount, survivors, Nat.card_Icc]
  | succ k ih =>
    by_cases hp : (k+1).Prime
    · simp only [primeList, if_pos hp, legendreCount]
      split
      · exact (small_count (by assumption)).symm
      · rw [ih, ih, sieve_step k n hp]
    · simp only [primeList, if_neg hp, ih]
      simp [survivors, next_product, hp]

theorem certified_lower {k n : ℕ} (hkn : k ≤ n) (hsq : n < (k+1)^2) :
    legendreCount (primeList k) n + Nat.primeCounting k ≤ Nat.primeCounting n + 1 := by
  have hsub : survivors k n ⊆ insert 1 (n.primesLE \ k.primesLE) := by
    intro x hx
    obtain ⟨hx1,hxn,hc⟩ := mem_survivors.mp hx
    by_cases he : x = 1
    · simp [he]
    have hp := Nat.minFac_prime he
    have hmin : k < x.minFac := by
      by_contra! hle
      exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨_,hp,Nat.minFac_dvd x,hp.dvd_primorial_iff.mpr hle⟩) hc
    have hprime : x.Prime := by
      by_contra hnp
      have := Nat.minFac_sq_le_self hx1 hnp
      have hpow := Nat.pow_le_pow_left (show k+1 ≤ x.minFac by omega) 2
      omega
    exact mem_insert_of_mem <| mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hxn,hprime⟩,
      fun hm => by have := Nat.le_of_mem_primesLE hm; rw [hprime.minFac_eq] at hmin; omega⟩
  have hb := Finset.card_le_card hsub
  have hi := Finset.card_insert_le 1 (n.primesLE \ k.primesLE)
  have hs := Nat.primesLE_mono hkn
  rw [Finset.card_sdiff_of_subset hs] at hi
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting, legendre_correct]
  have := Finset.card_le_card hs
  omega

def quickPrime (x : ℕ) : Bool :=
  if x ≤ 97 ∨ 9486 < x then decide x.Prime else decide (x.Coprime 96192759682482119853328425949563698712343813919172976158104477319333745612481875498805879175589072651261284189679678167647067832320000000000000000000000)

lemma quickPrime_spec (x : ℕ) : quickPrime x = decide x.Prime := by
  unfold quickPrime
  split
  · rfl
  · rename_i hh
    have hx : x ≠ 1 := by omega
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [show 96192759682482119853328425949563698712343813919172976158104477319333745612481875498805879175589072651261284189679678167647067832320000000000000000000000 = Nat.factorial 97 by decide +kernel, Nat.coprime_factorial_iff hx]
    constructor
    · intro h
      by_contra hnp
      have hsq := Nat.minFac_sq_le_self (show 0 < x by omega) hnp
      have h98 := Nat.pow_le_pow_left (show 98 ≤ x.minFac by omega) 2
      omega
    · intro h
      rw [h.minFac_eq]
      omega
def extendPrimes (start : ℕ) : ℕ → List ℕ
  | 0 => []
  | d+1 => if quickPrime (start+d+1) then (start+d+1)::extendPrimes start d else extendPrimes start d

lemma primeList_extend (start d : ℕ) :
    primeList (start+d) = extendPrimes start d ++ primeList start := by
  induction d with
  | zero => simp [extendPrimes]
  | succ d ih =>
    simp only [extendPrimes, quickPrime_spec, decide_eq_true_eq]
    change primeList ((start+d)+1) = (if (start+d+1).Prime then _ :: extendPrimes start d else extendPrimes start d) ++ primeList start
    rw [primeList]
    by_cases h : (start+d+1).Prime <;> simp [h, ih]

lemma length_primeList (k : ℕ) : (primeList k).length = Nat.primeCounting k := by
  induction k with
  | zero => simp [primeList]
  | succ k ih =>
    change (primeList (k+1)).length = Nat.count Nat.Prime ((k+1)+1)
    rw [Nat.count_succ]
    change (primeList (k+1)).length = Nat.primeCounting k + _
    by_cases hp : (k+1).Prime <;> simp [primeList, hp, ih]


lemma extend_count {ps : List ℕ} {p x y z : ℕ} (hp : p < 90000000)
    (hx : legendreCount ps 90000000 = x) (hy : legendreCount ps (90000000/p) = y)
    (hz : x-y = z) : legendreCount (p::ps) 90000000 = z := by
  simpa [legendreCount, if_neg (Nat.not_le.mpr hp), hx, hy] using hz

/-- The empty sieve retains every positive integer up to the bound. -/
def primes0 : List ℕ := []
def primes2 := 2 :: primes0
def primes3 := 3 :: primes2
def primes5 := 5 :: primes3
def primes7 := 7 :: primes5
def primes11 := 11 :: primes7
def primes13 := 13 :: primes11
def primes17 := 17 :: primes13
def primes19 := 19 :: primes17
def primes23 := 23 :: primes19
def primes29 := 29 :: primes23
def primes31 := 31 :: primes29
def primes37 := 37 :: primes31
def primes41 := 41 :: primes37
def primes43 := 43 :: primes41
def primes47 := 47 :: primes43
def primes53 := 53 :: primes47
def primes59 := 59 :: primes53
def primes61 := 61 :: primes59
def primes67 := 67 :: primes61
def primes71 := 71 :: primes67
def primes73 := 73 :: primes71
def primes79 := 79 :: primes73
def primes83 := 83 :: primes79
def primes89 := 89 :: primes83
def primes97 := 97 :: primes89
def primes101 := 101 :: primes97
def primes103 := 103 :: primes101
def primes107 := 107 :: primes103
def primes109 := 109 :: primes107
def primes113 := 113 :: primes109
def primes127 := 127 :: primes113
def primes131 := 131 :: primes127
def primes137 := 137 :: primes131
def primes139 := 139 :: primes137
def primes149 := 149 :: primes139
def primes151 := 151 :: primes149
def primes157 := 157 :: primes151
def primes163 := 163 :: primes157
def primes167 := 167 :: primes163
def primes173 := 173 :: primes167
def primes179 := 179 :: primes173
def primes181 := 181 :: primes179
def primes191 := 191 :: primes181
def primes193 := 193 :: primes191
def primes197 := 197 :: primes193
def primes199 := 199 :: primes197
def primes211 := 211 :: primes199
def primes223 := 223 :: primes211
def primes227 := 227 :: primes223
def primes229 := 229 :: primes227
def primes233 := 233 :: primes229
def primes239 := 239 :: primes233
def primes241 := 241 :: primes239
def primes251 := 251 :: primes241
def primes257 := 257 :: primes251
def primes263 := 263 :: primes257
def primes269 := 269 :: primes263
def primes271 := 271 :: primes269
def primes277 := 277 :: primes271
def primes281 := 281 :: primes277
def primes283 := 283 :: primes281
def primes293 := 293 :: primes283
def primes307 := 307 :: primes293
def primes311 := 311 :: primes307
def primes313 := 313 :: primes311
def primes317 := 317 :: primes313
def primes331 := 331 :: primes317
def primes337 := 337 :: primes331
def primes347 := 347 :: primes337
def primes349 := 349 :: primes347
def primes353 := 353 :: primes349
def primes359 := 359 :: primes353
def primes367 := 367 :: primes359
def primes373 := 373 :: primes367
def primes379 := 379 :: primes373
def primes383 := 383 :: primes379
def primes389 := 389 :: primes383
def primes397 := 397 :: primes389
def primes401 := 401 :: primes397
def primes409 := 409 :: primes401
def primes419 := 419 :: primes409
def primes421 := 421 :: primes419
def primes431 := 431 :: primes421
def primes433 := 433 :: primes431
def primes439 := 439 :: primes433
def primes443 := 443 :: primes439
def primes449 := 449 :: primes443
def primes457 := 457 :: primes449
def primes461 := 461 :: primes457
def primes463 := 463 :: primes461
def primes467 := 467 :: primes463
def primes479 := 479 :: primes467
def primes487 := 487 :: primes479
def primes491 := 491 :: primes487
def primes499 := 499 :: primes491
def primes503 := 503 :: primes499
def primes509 := 509 :: primes503
def primes521 := 521 :: primes509
def primes523 := 523 :: primes521
def primes541 := 541 :: primes523
def primes547 := 547 :: primes541
def primes557 := 557 :: primes547
def primes563 := 563 :: primes557
def primes569 := 569 :: primes563
def primes571 := 571 :: primes569
def primes577 := 577 :: primes571
def primes587 := 587 :: primes577
def primes593 := 593 :: primes587
def primes599 := 599 :: primes593
def primes601 := 601 :: primes599
def primes607 := 607 :: primes601
def primes613 := 613 :: primes607
def primes617 := 617 :: primes613
def primes619 := 619 :: primes617
def primes631 := 631 :: primes619
def primes641 := 641 :: primes631
def primes643 := 643 :: primes641
def primes647 := 647 :: primes643
def primes653 := 653 :: primes647
def primes659 := 659 :: primes653
def primes661 := 661 :: primes659
def primes673 := 673 :: primes661
def primes677 := 677 :: primes673
def primes683 := 683 :: primes677
def primes691 := 691 :: primes683
def primes701 := 701 :: primes691
def primes709 := 709 :: primes701
def primes719 := 719 :: primes709
def primes727 := 727 :: primes719
def primes733 := 733 :: primes727
def primes739 := 739 :: primes733
def primes743 := 743 :: primes739
def primes751 := 751 :: primes743
def primes757 := 757 :: primes751
def primes761 := 761 :: primes757
def primes769 := 769 :: primes761
def primes773 := 773 :: primes769
def primes787 := 787 :: primes773
def primes797 := 797 :: primes787
def primes809 := 809 :: primes797
def primes811 := 811 :: primes809
def primes821 := 821 :: primes811
def primes823 := 823 :: primes821
def primes827 := 827 :: primes823
def primes829 := 829 :: primes827
def primes839 := 839 :: primes829
def primes853 := 853 :: primes839
def primes857 := 857 :: primes853
def primes859 := 859 :: primes857
def primes863 := 863 :: primes859
def primes877 := 877 :: primes863
def primes881 := 881 :: primes877
def primes883 := 883 :: primes881
def primes887 := 887 :: primes883
def primes907 := 907 :: primes887
def primes911 := 911 :: primes907
def primes919 := 919 :: primes911
def primes929 := 929 :: primes919
def primes937 := 937 :: primes929
def primes941 := 941 :: primes937
def primes947 := 947 :: primes941
def primes953 := 953 :: primes947
def primes967 := 967 :: primes953
def primes971 := 971 :: primes967
def primes977 := 977 :: primes971
def primes983 := 983 :: primes977
def primes991 := 991 :: primes983
def primes997 := 997 :: primes991
def primes1009 := 1009 :: primes997
def primes1013 := 1013 :: primes1009
def primes1019 := 1019 :: primes1013
def primes1021 := 1021 :: primes1019
def primes1031 := 1031 :: primes1021
def primes1033 := 1033 :: primes1031
def primes1039 := 1039 :: primes1033
def primes1049 := 1049 :: primes1039
def primes1051 := 1051 :: primes1049
def primes1061 := 1061 :: primes1051
def primes1063 := 1063 :: primes1061
def primes1069 := 1069 :: primes1063
def primes1087 := 1087 :: primes1069
def primes1091 := 1091 :: primes1087
def primes1093 := 1093 :: primes1091
def primes1097 := 1097 :: primes1093
def primes1103 := 1103 :: primes1097
def primes1109 := 1109 :: primes1103
def primes1117 := 1117 :: primes1109
def primes1123 := 1123 :: primes1117
def primes1129 := 1129 :: primes1123
def primes1151 := 1151 :: primes1129
def primes1153 := 1153 :: primes1151
def primes1163 := 1163 :: primes1153
def primes1171 := 1171 :: primes1163
def primes1181 := 1181 :: primes1171
def primes1187 := 1187 :: primes1181
def primes1193 := 1193 :: primes1187
def primes1201 := 1201 :: primes1193
def primes1213 := 1213 :: primes1201
def primes1217 := 1217 :: primes1213
def primes1223 := 1223 :: primes1217
def primes1229 := 1229 :: primes1223
def primes1231 := 1231 :: primes1229
def primes1237 := 1237 :: primes1231
def primes1249 := 1249 :: primes1237
def primes1259 := 1259 :: primes1249
def primes1277 := 1277 :: primes1259
def primes1279 := 1279 :: primes1277
def primes1283 := 1283 :: primes1279
def primes1289 := 1289 :: primes1283
def primes1291 := 1291 :: primes1289
def primes1297 := 1297 :: primes1291
def primes1301 := 1301 :: primes1297
def primes1303 := 1303 :: primes1301
def primes1307 := 1307 :: primes1303
def primes1319 := 1319 :: primes1307
def primes1321 := 1321 :: primes1319
def primes1327 := 1327 :: primes1321
def primes1361 := 1361 :: primes1327
def primes1367 := 1367 :: primes1361
def primes1373 := 1373 :: primes1367
def primes1381 := 1381 :: primes1373
def primes1399 := 1399 :: primes1381
def primes1409 := 1409 :: primes1399
def primes1423 := 1423 :: primes1409
def primes1427 := 1427 :: primes1423
def primes1429 := 1429 :: primes1427
def primes1433 := 1433 :: primes1429
def primes1439 := 1439 :: primes1433
def primes1447 := 1447 :: primes1439
def primes1451 := 1451 :: primes1447
def primes1453 := 1453 :: primes1451
def primes1459 := 1459 :: primes1453
def primes1471 := 1471 :: primes1459
def primes1481 := 1481 :: primes1471
def primes1483 := 1483 :: primes1481
def primes1487 := 1487 :: primes1483
def primes1489 := 1489 :: primes1487
def primes1493 := 1493 :: primes1489
def primes1499 := 1499 :: primes1493
def primes1511 := 1511 :: primes1499
def primes1523 := 1523 :: primes1511
def primes1531 := 1531 :: primes1523
def primes1543 := 1543 :: primes1531
def primes1549 := 1549 :: primes1543
def primes1553 := 1553 :: primes1549
def primes1559 := 1559 :: primes1553
def primes1567 := 1567 :: primes1559
def primes1571 := 1571 :: primes1567
def primes1579 := 1579 :: primes1571
def primes1583 := 1583 :: primes1579
def primes1597 := 1597 :: primes1583
def primes1601 := 1601 :: primes1597
def primes1607 := 1607 :: primes1601
def primes1609 := 1609 :: primes1607
def primes1613 := 1613 :: primes1609
def primes1619 := 1619 :: primes1613
def primes1621 := 1621 :: primes1619
def primes1627 := 1627 :: primes1621
def primes1637 := 1637 :: primes1627
def primes1657 := 1657 :: primes1637
def primes1663 := 1663 :: primes1657
def primes1667 := 1667 :: primes1663
def primes1669 := 1669 :: primes1667
def primes1693 := 1693 :: primes1669
def primes1697 := 1697 :: primes1693
def primes1699 := 1699 :: primes1697
def primes1709 := 1709 :: primes1699
def primes1721 := 1721 :: primes1709
def primes1723 := 1723 :: primes1721
def primes1733 := 1733 :: primes1723
def primes1741 := 1741 :: primes1733
def primes1747 := 1747 :: primes1741
def primes1753 := 1753 :: primes1747
def primes1759 := 1759 :: primes1753
def primes1777 := 1777 :: primes1759
def primes1783 := 1783 :: primes1777
def primes1787 := 1787 :: primes1783
def primes1789 := 1789 :: primes1787
def primes1801 := 1801 :: primes1789
def primes1811 := 1811 :: primes1801
def primes1823 := 1823 :: primes1811
def primes1831 := 1831 :: primes1823
def primes1847 := 1847 :: primes1831
def primes1861 := 1861 :: primes1847
def primes1867 := 1867 :: primes1861
def primes1871 := 1871 :: primes1867
def primes1873 := 1873 :: primes1871
def primes1877 := 1877 :: primes1873
def primes1879 := 1879 :: primes1877
def primes1889 := 1889 :: primes1879
def primes1901 := 1901 :: primes1889
def primes1907 := 1907 :: primes1901
def primes1913 := 1913 :: primes1907
def primes1931 := 1931 :: primes1913
def primes1933 := 1933 :: primes1931
def primes1949 := 1949 :: primes1933
def primes1951 := 1951 :: primes1949
def primes1973 := 1973 :: primes1951
def primes1979 := 1979 :: primes1973
def primes1987 := 1987 :: primes1979
def primes1993 := 1993 :: primes1987
def primes1997 := 1997 :: primes1993
def primes1999 := 1999 :: primes1997
def primes2003 := 2003 :: primes1999
def primes2011 := 2011 :: primes2003
def primes2017 := 2017 :: primes2011
def primes2027 := 2027 :: primes2017
def primes2029 := 2029 :: primes2027
def primes2039 := 2039 :: primes2029
def primes2053 := 2053 :: primes2039
def primes2063 := 2063 :: primes2053
def primes2069 := 2069 :: primes2063
def primes2081 := 2081 :: primes2069
def primes2083 := 2083 :: primes2081
def primes2087 := 2087 :: primes2083
def primes2089 := 2089 :: primes2087
def primes2099 := 2099 :: primes2089
def primes2111 := 2111 :: primes2099
def primes2113 := 2113 :: primes2111
def primes2129 := 2129 :: primes2113
def primes2131 := 2131 :: primes2129
def primes2137 := 2137 :: primes2131
def primes2141 := 2141 :: primes2137
def primes2143 := 2143 :: primes2141
def primes2153 := 2153 :: primes2143
def primes2161 := 2161 :: primes2153
def primes2179 := 2179 :: primes2161
def primes2203 := 2203 :: primes2179
def primes2207 := 2207 :: primes2203
def primes2213 := 2213 :: primes2207
def primes2221 := 2221 :: primes2213
def primes2237 := 2237 :: primes2221
def primes2239 := 2239 :: primes2237
def primes2243 := 2243 :: primes2239
def primes2251 := 2251 :: primes2243
def primes2267 := 2267 :: primes2251
def primes2269 := 2269 :: primes2267
def primes2273 := 2273 :: primes2269
def primes2281 := 2281 :: primes2273
def primes2287 := 2287 :: primes2281
def primes2293 := 2293 :: primes2287
def primes2297 := 2297 :: primes2293
def primes2309 := 2309 :: primes2297
def primes2311 := 2311 :: primes2309
def primes2333 := 2333 :: primes2311
def primes2339 := 2339 :: primes2333
def primes2341 := 2341 :: primes2339
def primes2347 := 2347 :: primes2341
def primes2351 := 2351 :: primes2347
def primes2357 := 2357 :: primes2351
def primes2371 := 2371 :: primes2357
def primes2377 := 2377 :: primes2371
def primes2381 := 2381 :: primes2377
def primes2383 := 2383 :: primes2381
def primes2389 := 2389 :: primes2383
def primes2393 := 2393 :: primes2389
def primes2399 := 2399 :: primes2393
def primes2411 := 2411 :: primes2399
def primes2417 := 2417 :: primes2411
def primes2423 := 2423 :: primes2417
def primes2437 := 2437 :: primes2423
def primes2441 := 2441 :: primes2437
def primes2447 := 2447 :: primes2441
def primes2459 := 2459 :: primes2447
def primes2467 := 2467 :: primes2459
def primes2473 := 2473 :: primes2467
def primes2477 := 2477 :: primes2473
def primes2503 := 2503 :: primes2477
def primes2521 := 2521 :: primes2503
def primes2531 := 2531 :: primes2521
def primes2539 := 2539 :: primes2531
def primes2543 := 2543 :: primes2539
def primes2549 := 2549 :: primes2543
def primes2551 := 2551 :: primes2549
def primes2557 := 2557 :: primes2551
def primes2579 := 2579 :: primes2557
def primes2591 := 2591 :: primes2579
def primes2593 := 2593 :: primes2591
def primes2609 := 2609 :: primes2593
def primes2617 := 2617 :: primes2609
def primes2621 := 2621 :: primes2617
def primes2633 := 2633 :: primes2621
def primes2647 := 2647 :: primes2633
def primes2657 := 2657 :: primes2647
def primes2659 := 2659 :: primes2657
def primes2663 := 2663 :: primes2659
def primes2671 := 2671 :: primes2663
def primes2677 := 2677 :: primes2671
def primes2683 := 2683 :: primes2677
def primes2687 := 2687 :: primes2683
def primes2689 := 2689 :: primes2687
def primes2693 := 2693 :: primes2689
def primes2699 := 2699 :: primes2693
def primes2707 := 2707 :: primes2699
def primes2711 := 2711 :: primes2707
def primes2713 := 2713 :: primes2711
def primes2719 := 2719 :: primes2713
def primes2729 := 2729 :: primes2719
def primes2731 := 2731 :: primes2729
def primes2741 := 2741 :: primes2731
def primes2749 := 2749 :: primes2741
def primes2753 := 2753 :: primes2749
def primes2767 := 2767 :: primes2753
def primes2777 := 2777 :: primes2767
def primes2789 := 2789 :: primes2777
def primes2791 := 2791 :: primes2789
def primes2797 := 2797 :: primes2791
def primes2801 := 2801 :: primes2797
def primes2803 := 2803 :: primes2801
def primes2819 := 2819 :: primes2803
def primes2833 := 2833 :: primes2819
def primes2837 := 2837 :: primes2833
def primes2843 := 2843 :: primes2837
def primes2851 := 2851 :: primes2843
def primes2857 := 2857 :: primes2851
def primes2861 := 2861 :: primes2857
def primes2879 := 2879 :: primes2861
def primes2887 := 2887 :: primes2879
def primes2897 := 2897 :: primes2887
def primes2903 := 2903 :: primes2897
def primes2909 := 2909 :: primes2903
def primes2917 := 2917 :: primes2909
def primes2927 := 2927 :: primes2917
def primes2939 := 2939 :: primes2927
def primes2953 := 2953 :: primes2939
def primes2957 := 2957 :: primes2953
def primes2963 := 2963 :: primes2957
def primes2969 := 2969 :: primes2963
def primes2971 := 2971 :: primes2969
def primes2999 := 2999 :: primes2971
def primes3001 := 3001 :: primes2999
def primes3011 := 3011 :: primes3001
def primes3019 := 3019 :: primes3011
def primes3023 := 3023 :: primes3019
def primes3037 := 3037 :: primes3023
def primes3041 := 3041 :: primes3037
def primes3049 := 3049 :: primes3041
def primes3061 := 3061 :: primes3049
def primes3067 := 3067 :: primes3061
def primes3079 := 3079 :: primes3067
def primes3083 := 3083 :: primes3079
def primes3089 := 3089 :: primes3083
def primes3109 := 3109 :: primes3089
def primes3119 := 3119 :: primes3109
def primes3121 := 3121 :: primes3119
def primes3137 := 3137 :: primes3121
def primes3163 := 3163 :: primes3137
def primes3167 := 3167 :: primes3163
def primes3169 := 3169 :: primes3167
def primes3181 := 3181 :: primes3169
def primes3187 := 3187 :: primes3181
def primes3191 := 3191 :: primes3187
def primes3203 := 3203 :: primes3191
def primes3209 := 3209 :: primes3203
def primes3217 := 3217 :: primes3209
def primes3221 := 3221 :: primes3217
def primes3229 := 3229 :: primes3221
def primes3251 := 3251 :: primes3229
def primes3253 := 3253 :: primes3251
def primes3257 := 3257 :: primes3253
def primes3259 := 3259 :: primes3257
def primes3271 := 3271 :: primes3259
def primes3299 := 3299 :: primes3271
def primes3301 := 3301 :: primes3299
def primes3307 := 3307 :: primes3301
def primes3313 := 3313 :: primes3307
def primes3319 := 3319 :: primes3313
def primes3323 := 3323 :: primes3319
def primes3329 := 3329 :: primes3323
def primes3331 := 3331 :: primes3329
def primes3343 := 3343 :: primes3331
def primes3347 := 3347 :: primes3343
def primes3359 := 3359 :: primes3347
def primes3361 := 3361 :: primes3359
def primes3371 := 3371 :: primes3361
def primes3373 := 3373 :: primes3371
def primes3389 := 3389 :: primes3373
def primes3391 := 3391 :: primes3389
def primes3407 := 3407 :: primes3391
def primes3413 := 3413 :: primes3407
def primes3433 := 3433 :: primes3413
def primes3449 := 3449 :: primes3433
def primes3457 := 3457 :: primes3449
def primes3461 := 3461 :: primes3457
def primes3463 := 3463 :: primes3461
def primes3467 := 3467 :: primes3463
def primes3469 := 3469 :: primes3467
def primes3491 := 3491 :: primes3469
def primes3499 := 3499 :: primes3491
def primes3511 := 3511 :: primes3499
def primes3517 := 3517 :: primes3511
def primes3527 := 3527 :: primes3517
def primes3529 := 3529 :: primes3527
def primes3533 := 3533 :: primes3529
def primes3539 := 3539 :: primes3533
def primes3541 := 3541 :: primes3539
def primes3547 := 3547 :: primes3541
def primes3557 := 3557 :: primes3547
def primes3559 := 3559 :: primes3557
def primes3571 := 3571 :: primes3559
def primes3581 := 3581 :: primes3571
def primes3583 := 3583 :: primes3581
def primes3593 := 3593 :: primes3583
def primes3607 := 3607 :: primes3593
def primes3613 := 3613 :: primes3607
def primes3617 := 3617 :: primes3613
def primes3623 := 3623 :: primes3617
def primes3631 := 3631 :: primes3623
def primes3637 := 3637 :: primes3631
def primes3643 := 3643 :: primes3637
def primes3659 := 3659 :: primes3643
def primes3671 := 3671 :: primes3659
def primes3673 := 3673 :: primes3671
def primes3677 := 3677 :: primes3673
def primes3691 := 3691 :: primes3677
def primes3697 := 3697 :: primes3691
def primes3701 := 3701 :: primes3697
def primes3709 := 3709 :: primes3701
def primes3719 := 3719 :: primes3709
def primes3727 := 3727 :: primes3719
def primes3733 := 3733 :: primes3727
def primes3739 := 3739 :: primes3733
def primes3761 := 3761 :: primes3739
def primes3767 := 3767 :: primes3761
def primes3769 := 3769 :: primes3767
def primes3779 := 3779 :: primes3769
def primes3793 := 3793 :: primes3779
def primes3797 := 3797 :: primes3793
def primes3803 := 3803 :: primes3797
def primes3821 := 3821 :: primes3803
def primes3823 := 3823 :: primes3821
def primes3833 := 3833 :: primes3823
def primes3847 := 3847 :: primes3833
def primes3851 := 3851 :: primes3847
def primes3853 := 3853 :: primes3851
def primes3863 := 3863 :: primes3853
def primes3877 := 3877 :: primes3863
def primes3881 := 3881 :: primes3877
def primes3889 := 3889 :: primes3881
def primes3907 := 3907 :: primes3889
def primes3911 := 3911 :: primes3907
def primes3917 := 3917 :: primes3911
def primes3919 := 3919 :: primes3917
def primes3923 := 3923 :: primes3919
def primes3929 := 3929 :: primes3923
def primes3931 := 3931 :: primes3929
def primes3943 := 3943 :: primes3931
def primes3947 := 3947 :: primes3943
def primes3967 := 3967 :: primes3947
def primes3989 := 3989 :: primes3967
def primes4001 := 4001 :: primes3989
def primes4003 := 4003 :: primes4001
def primes4007 := 4007 :: primes4003
def primes4013 := 4013 :: primes4007
def primes4019 := 4019 :: primes4013
def primes4021 := 4021 :: primes4019
def primes4027 := 4027 :: primes4021
def primes4049 := 4049 :: primes4027
def primes4051 := 4051 :: primes4049
def primes4057 := 4057 :: primes4051
def primes4073 := 4073 :: primes4057
def primes4079 := 4079 :: primes4073
def primes4091 := 4091 :: primes4079
def primes4093 := 4093 :: primes4091
def primes4099 := 4099 :: primes4093
def primes4111 := 4111 :: primes4099
def primes4127 := 4127 :: primes4111
def primes4129 := 4129 :: primes4127
def primes4133 := 4133 :: primes4129
def primes4139 := 4139 :: primes4133
def primes4153 := 4153 :: primes4139
def primes4157 := 4157 :: primes4153
def primes4159 := 4159 :: primes4157
def primes4177 := 4177 :: primes4159
def primes4201 := 4201 :: primes4177
def primes4211 := 4211 :: primes4201
def primes4217 := 4217 :: primes4211
def primes4219 := 4219 :: primes4217
def primes4229 := 4229 :: primes4219
def primes4231 := 4231 :: primes4229
def primes4241 := 4241 :: primes4231
def primes4243 := 4243 :: primes4241
def primes4253 := 4253 :: primes4243
def primes4259 := 4259 :: primes4253
def primes4261 := 4261 :: primes4259
def primes4271 := 4271 :: primes4261
def primes4273 := 4273 :: primes4271
def primes4283 := 4283 :: primes4273
def primes4289 := 4289 :: primes4283
def primes4297 := 4297 :: primes4289
def primes4327 := 4327 :: primes4297
def primes4337 := 4337 :: primes4327
def primes4339 := 4339 :: primes4337
def primes4349 := 4349 :: primes4339
def primes4357 := 4357 :: primes4349
def primes4363 := 4363 :: primes4357
def primes4373 := 4373 :: primes4363
def primes4391 := 4391 :: primes4373
def primes4397 := 4397 :: primes4391
def primes4409 := 4409 :: primes4397
def primes4421 := 4421 :: primes4409
def primes4423 := 4423 :: primes4421
def primes4441 := 4441 :: primes4423
def primes4447 := 4447 :: primes4441
def primes4451 := 4451 :: primes4447
def primes4457 := 4457 :: primes4451
def primes4463 := 4463 :: primes4457
def primes4481 := 4481 :: primes4463
def primes4483 := 4483 :: primes4481
def primes4493 := 4493 :: primes4483
def primes4507 := 4507 :: primes4493
def primes4513 := 4513 :: primes4507
def primes4517 := 4517 :: primes4513
def primes4519 := 4519 :: primes4517
def primes4523 := 4523 :: primes4519
def primes4547 := 4547 :: primes4523
def primes4549 := 4549 :: primes4547
def primes4561 := 4561 :: primes4549
def primes4567 := 4567 :: primes4561
def primes4583 := 4583 :: primes4567
def primes4591 := 4591 :: primes4583
def primes4597 := 4597 :: primes4591
def primes4603 := 4603 :: primes4597
def primes4621 := 4621 :: primes4603
def primes4637 := 4637 :: primes4621
def primes4639 := 4639 :: primes4637
def primes4643 := 4643 :: primes4639
def primes4649 := 4649 :: primes4643
def primes4651 := 4651 :: primes4649
def primes4657 := 4657 :: primes4651
def primes4663 := 4663 :: primes4657
def primes4673 := 4673 :: primes4663
def primes4679 := 4679 :: primes4673
def primes4691 := 4691 :: primes4679
def primes4703 := 4703 :: primes4691
def primes4721 := 4721 :: primes4703
def primes4723 := 4723 :: primes4721
def primes4729 := 4729 :: primes4723
def primes4733 := 4733 :: primes4729
def primes4751 := 4751 :: primes4733
def primes4759 := 4759 :: primes4751
def primes4783 := 4783 :: primes4759
def primes4787 := 4787 :: primes4783
def primes4789 := 4789 :: primes4787
def primes4793 := 4793 :: primes4789
def primes4799 := 4799 :: primes4793
def primes4801 := 4801 :: primes4799
def primes4813 := 4813 :: primes4801
def primes4817 := 4817 :: primes4813
def primes4831 := 4831 :: primes4817
def primes4861 := 4861 :: primes4831
def primes4871 := 4871 :: primes4861
def primes4877 := 4877 :: primes4871
def primes4889 := 4889 :: primes4877
def primes4903 := 4903 :: primes4889
def primes4909 := 4909 :: primes4903
def primes4919 := 4919 :: primes4909
def primes4931 := 4931 :: primes4919
def primes4933 := 4933 :: primes4931
def primes4937 := 4937 :: primes4933
def primes4943 := 4943 :: primes4937
def primes4951 := 4951 :: primes4943
def primes4957 := 4957 :: primes4951
def primes4967 := 4967 :: primes4957
def primes4969 := 4969 :: primes4967
def primes4973 := 4973 :: primes4969
def primes4987 := 4987 :: primes4973
def primes4993 := 4993 :: primes4987
def primes4999 := 4999 :: primes4993
def primes5003 := 5003 :: primes4999
def primes5009 := 5009 :: primes5003
def primes5011 := 5011 :: primes5009
def primes5021 := 5021 :: primes5011
def primes5023 := 5023 :: primes5021
def primes5039 := 5039 :: primes5023
def primes5051 := 5051 :: primes5039
def primes5059 := 5059 :: primes5051
def primes5077 := 5077 :: primes5059
def primes5081 := 5081 :: primes5077
def primes5087 := 5087 :: primes5081
def primes5099 := 5099 :: primes5087
def primes5101 := 5101 :: primes5099
def primes5107 := 5107 :: primes5101
def primes5113 := 5113 :: primes5107
def primes5119 := 5119 :: primes5113
def primes5147 := 5147 :: primes5119
def primes5153 := 5153 :: primes5147
def primes5167 := 5167 :: primes5153
def primes5171 := 5171 :: primes5167
def primes5179 := 5179 :: primes5171
def primes5189 := 5189 :: primes5179
def primes5197 := 5197 :: primes5189
def primes5209 := 5209 :: primes5197
def primes5227 := 5227 :: primes5209
def primes5231 := 5231 :: primes5227
def primes5233 := 5233 :: primes5231
def primes5237 := 5237 :: primes5233
def primes5261 := 5261 :: primes5237
def primes5273 := 5273 :: primes5261
def primes5279 := 5279 :: primes5273
def primes5281 := 5281 :: primes5279
def primes5297 := 5297 :: primes5281
def primes5303 := 5303 :: primes5297
def primes5309 := 5309 :: primes5303
def primes5323 := 5323 :: primes5309
def primes5333 := 5333 :: primes5323
def primes5347 := 5347 :: primes5333
def primes5351 := 5351 :: primes5347
def primes5381 := 5381 :: primes5351
def primes5387 := 5387 :: primes5381
def primes5393 := 5393 :: primes5387
def primes5399 := 5399 :: primes5393
def primes5407 := 5407 :: primes5399
def primes5413 := 5413 :: primes5407
def primes5417 := 5417 :: primes5413
def primes5419 := 5419 :: primes5417
def primes5431 := 5431 :: primes5419
def primes5437 := 5437 :: primes5431
def primes5441 := 5441 :: primes5437
def primes5443 := 5443 :: primes5441
def primes5449 := 5449 :: primes5443
def primes5471 := 5471 :: primes5449
def primes5477 := 5477 :: primes5471
def primes5479 := 5479 :: primes5477
def primes5483 := 5483 :: primes5479
def primes5501 := 5501 :: primes5483
def primes5503 := 5503 :: primes5501
def primes5507 := 5507 :: primes5503
def primes5519 := 5519 :: primes5507
def primes5521 := 5521 :: primes5519
def primes5527 := 5527 :: primes5521
def primes5531 := 5531 :: primes5527
def primes5557 := 5557 :: primes5531
def primes5563 := 5563 :: primes5557
def primes5569 := 5569 :: primes5563
def primes5573 := 5573 :: primes5569
def primes5581 := 5581 :: primes5573
def primes5591 := 5591 :: primes5581
def primes5623 := 5623 :: primes5591
def primes5639 := 5639 :: primes5623
def primes5641 := 5641 :: primes5639
def primes5647 := 5647 :: primes5641
def primes5651 := 5651 :: primes5647
def primes5653 := 5653 :: primes5651
def primes5657 := 5657 :: primes5653
def primes5659 := 5659 :: primes5657
def primes5669 := 5669 :: primes5659
def primes5683 := 5683 :: primes5669
def primes5689 := 5689 :: primes5683
def primes5693 := 5693 :: primes5689
def primes5701 := 5701 :: primes5693
def primes5711 := 5711 :: primes5701
def primes5717 := 5717 :: primes5711
def primes5737 := 5737 :: primes5717
def primes5741 := 5741 :: primes5737
def primes5743 := 5743 :: primes5741
def primes5749 := 5749 :: primes5743
def primes5779 := 5779 :: primes5749
def primes5783 := 5783 :: primes5779
def primes5791 := 5791 :: primes5783
def primes5801 := 5801 :: primes5791
def primes5807 := 5807 :: primes5801
def primes5813 := 5813 :: primes5807
def primes5821 := 5821 :: primes5813
def primes5827 := 5827 :: primes5821
def primes5839 := 5839 :: primes5827
def primes5843 := 5843 :: primes5839
def primes5849 := 5849 :: primes5843
def primes5851 := 5851 :: primes5849
def primes5857 := 5857 :: primes5851
def primes5861 := 5861 :: primes5857
def primes5867 := 5867 :: primes5861
def primes5869 := 5869 :: primes5867
def primes5879 := 5879 :: primes5869
def primes5881 := 5881 :: primes5879
def primes5897 := 5897 :: primes5881
def primes5903 := 5903 :: primes5897
def primes5923 := 5923 :: primes5903
def primes5927 := 5927 :: primes5923
def primes5939 := 5939 :: primes5927
def primes5953 := 5953 :: primes5939
def primes5981 := 5981 :: primes5953
def primes5987 := 5987 :: primes5981
def primes6007 := 6007 :: primes5987
def primes6011 := 6011 :: primes6007
def primes6029 := 6029 :: primes6011
def primes6037 := 6037 :: primes6029
def primes6043 := 6043 :: primes6037
def primes6047 := 6047 :: primes6043
def primes6053 := 6053 :: primes6047
def primes6067 := 6067 :: primes6053
def primes6073 := 6073 :: primes6067
def primes6079 := 6079 :: primes6073
def primes6089 := 6089 :: primes6079
def primes6091 := 6091 :: primes6089
def primes6101 := 6101 :: primes6091
def primes6113 := 6113 :: primes6101
def primes6121 := 6121 :: primes6113
def primes6131 := 6131 :: primes6121
def primes6133 := 6133 :: primes6131
def primes6143 := 6143 :: primes6133
def primes6151 := 6151 :: primes6143
def primes6163 := 6163 :: primes6151
def primes6173 := 6173 :: primes6163
def primes6197 := 6197 :: primes6173
def primes6199 := 6199 :: primes6197
def primes6203 := 6203 :: primes6199
def primes6211 := 6211 :: primes6203
def primes6217 := 6217 :: primes6211
def primes6221 := 6221 :: primes6217
def primes6229 := 6229 :: primes6221
def primes6247 := 6247 :: primes6229
def primes6257 := 6257 :: primes6247
def primes6263 := 6263 :: primes6257
def primes6269 := 6269 :: primes6263
def primes6271 := 6271 :: primes6269
def primes6277 := 6277 :: primes6271
def primes6287 := 6287 :: primes6277
def primes6299 := 6299 :: primes6287
def primes6301 := 6301 :: primes6299
def primes6311 := 6311 :: primes6301
def primes6317 := 6317 :: primes6311
def primes6323 := 6323 :: primes6317
def primes6329 := 6329 :: primes6323
def primes6337 := 6337 :: primes6329
def primes6343 := 6343 :: primes6337
def primes6353 := 6353 :: primes6343
def primes6359 := 6359 :: primes6353
def primes6361 := 6361 :: primes6359
def primes6367 := 6367 :: primes6361
def primes6373 := 6373 :: primes6367
def primes6379 := 6379 :: primes6373
def primes6389 := 6389 :: primes6379
def primes6397 := 6397 :: primes6389
def primes6421 := 6421 :: primes6397
def primes6427 := 6427 :: primes6421
def primes6449 := 6449 :: primes6427
def primes6451 := 6451 :: primes6449
def primes6469 := 6469 :: primes6451
def primes6473 := 6473 :: primes6469
def primes6481 := 6481 :: primes6473
def primes6491 := 6491 :: primes6481
def primes6521 := 6521 :: primes6491
def primes6529 := 6529 :: primes6521
def primes6547 := 6547 :: primes6529
def primes6551 := 6551 :: primes6547
def primes6553 := 6553 :: primes6551
def primes6563 := 6563 :: primes6553
def primes6569 := 6569 :: primes6563
def primes6571 := 6571 :: primes6569
def primes6577 := 6577 :: primes6571
def primes6581 := 6581 :: primes6577
def primes6599 := 6599 :: primes6581
def primes6607 := 6607 :: primes6599
def primes6619 := 6619 :: primes6607
def primes6637 := 6637 :: primes6619
def primes6653 := 6653 :: primes6637
def primes6659 := 6659 :: primes6653
def primes6661 := 6661 :: primes6659
def primes6673 := 6673 :: primes6661
def primes6679 := 6679 :: primes6673
def primes6689 := 6689 :: primes6679
def primes6691 := 6691 :: primes6689
def primes6701 := 6701 :: primes6691
def primes6703 := 6703 :: primes6701
def primes6709 := 6709 :: primes6703
def primes6719 := 6719 :: primes6709
def primes6733 := 6733 :: primes6719
def primes6737 := 6737 :: primes6733
def primes6761 := 6761 :: primes6737
def primes6763 := 6763 :: primes6761
def primes6779 := 6779 :: primes6763
def primes6781 := 6781 :: primes6779
def primes6791 := 6791 :: primes6781
def primes6793 := 6793 :: primes6791
def primes6803 := 6803 :: primes6793
def primes6823 := 6823 :: primes6803
def primes6827 := 6827 :: primes6823
def primes6829 := 6829 :: primes6827
def primes6833 := 6833 :: primes6829
def primes6841 := 6841 :: primes6833
def primes6857 := 6857 :: primes6841
def primes6863 := 6863 :: primes6857
def primes6869 := 6869 :: primes6863
def primes6871 := 6871 :: primes6869
def primes6883 := 6883 :: primes6871
def primes6899 := 6899 :: primes6883
def primes6907 := 6907 :: primes6899
def primes6911 := 6911 :: primes6907
def primes6917 := 6917 :: primes6911
def primes6947 := 6947 :: primes6917
def primes6949 := 6949 :: primes6947
def primes6959 := 6959 :: primes6949
def primes6961 := 6961 :: primes6959
def primes6967 := 6967 :: primes6961
def primes6971 := 6971 :: primes6967
def primes6977 := 6977 :: primes6971
def primes6983 := 6983 :: primes6977
def primes6991 := 6991 :: primes6983
def primes6997 := 6997 :: primes6991
def primes7001 := 7001 :: primes6997
def primes7013 := 7013 :: primes7001
def primes7019 := 7019 :: primes7013
def primes7027 := 7027 :: primes7019
def primes7039 := 7039 :: primes7027
def primes7043 := 7043 :: primes7039
def primes7057 := 7057 :: primes7043
def primes7069 := 7069 :: primes7057
def primes7079 := 7079 :: primes7069
def primes7103 := 7103 :: primes7079
def primes7109 := 7109 :: primes7103
def primes7121 := 7121 :: primes7109
def primes7127 := 7127 :: primes7121
def primes7129 := 7129 :: primes7127
def primes7151 := 7151 :: primes7129
def primes7159 := 7159 :: primes7151
def primes7177 := 7177 :: primes7159
def primes7187 := 7187 :: primes7177
def primes7193 := 7193 :: primes7187
def primes7207 := 7207 :: primes7193
def primes7211 := 7211 :: primes7207
def primes7213 := 7213 :: primes7211
def primes7219 := 7219 :: primes7213
def primes7229 := 7229 :: primes7219
def primes7237 := 7237 :: primes7229
def primes7243 := 7243 :: primes7237
def primes7247 := 7247 :: primes7243
def primes7253 := 7253 :: primes7247
def primes7283 := 7283 :: primes7253
def primes7297 := 7297 :: primes7283
def primes7307 := 7307 :: primes7297
def primes7309 := 7309 :: primes7307
def primes7321 := 7321 :: primes7309
def primes7331 := 7331 :: primes7321
def primes7333 := 7333 :: primes7331
def primes7349 := 7349 :: primes7333
def primes7351 := 7351 :: primes7349
def primes7369 := 7369 :: primes7351
def primes7393 := 7393 :: primes7369
def primes7411 := 7411 :: primes7393
def primes7417 := 7417 :: primes7411
def primes7433 := 7433 :: primes7417
def primes7451 := 7451 :: primes7433
def primes7457 := 7457 :: primes7451
def primes7459 := 7459 :: primes7457
def primes7477 := 7477 :: primes7459
def primes7481 := 7481 :: primes7477
def primes7487 := 7487 :: primes7481
def primes7489 := 7489 :: primes7487
def primes7499 := 7499 :: primes7489
def primes7507 := 7507 :: primes7499
def primes7517 := 7517 :: primes7507
def primes7523 := 7523 :: primes7517
def primes7529 := 7529 :: primes7523
def primes7537 := 7537 :: primes7529
def primes7541 := 7541 :: primes7537
def primes7547 := 7547 :: primes7541
def primes7549 := 7549 :: primes7547
def primes7559 := 7559 :: primes7549
def primes7561 := 7561 :: primes7559
def primes7573 := 7573 :: primes7561
def primes7577 := 7577 :: primes7573
def primes7583 := 7583 :: primes7577
def primes7589 := 7589 :: primes7583
def primes7591 := 7591 :: primes7589
def primes7603 := 7603 :: primes7591
def primes7607 := 7607 :: primes7603
def primes7621 := 7621 :: primes7607
def primes7639 := 7639 :: primes7621
def primes7643 := 7643 :: primes7639
def primes7649 := 7649 :: primes7643
def primes7669 := 7669 :: primes7649
def primes7673 := 7673 :: primes7669
def primes7681 := 7681 :: primes7673
def primes7687 := 7687 :: primes7681
def primes7691 := 7691 :: primes7687
def primes7699 := 7699 :: primes7691
def primes7703 := 7703 :: primes7699
def primes7717 := 7717 :: primes7703
def primes7723 := 7723 :: primes7717
def primes7727 := 7727 :: primes7723
def primes7741 := 7741 :: primes7727
def primes7753 := 7753 :: primes7741
def primes7757 := 7757 :: primes7753
def primes7759 := 7759 :: primes7757
def primes7789 := 7789 :: primes7759
def primes7793 := 7793 :: primes7789
def primes7817 := 7817 :: primes7793
def primes7823 := 7823 :: primes7817
def primes7829 := 7829 :: primes7823
def primes7841 := 7841 :: primes7829
def primes7853 := 7853 :: primes7841
def primes7867 := 7867 :: primes7853
def primes7873 := 7873 :: primes7867
def primes7877 := 7877 :: primes7873
def primes7879 := 7879 :: primes7877
def primes7883 := 7883 :: primes7879
def primes7901 := 7901 :: primes7883
def primes7907 := 7907 :: primes7901
def primes7919 := 7919 :: primes7907
def primes7927 := 7927 :: primes7919
def primes7933 := 7933 :: primes7927
def primes7937 := 7937 :: primes7933
def primes7949 := 7949 :: primes7937
def primes7951 := 7951 :: primes7949
def primes7963 := 7963 :: primes7951
def primes7993 := 7993 :: primes7963
def primes8009 := 8009 :: primes7993
def primes8011 := 8011 :: primes8009
def primes8017 := 8017 :: primes8011
def primes8039 := 8039 :: primes8017
def primes8053 := 8053 :: primes8039
def primes8059 := 8059 :: primes8053
def primes8069 := 8069 :: primes8059
def primes8081 := 8081 :: primes8069
def primes8087 := 8087 :: primes8081
def primes8089 := 8089 :: primes8087
def primes8093 := 8093 :: primes8089
def primes8101 := 8101 :: primes8093
def primes8111 := 8111 :: primes8101
def primes8117 := 8117 :: primes8111
def primes8123 := 8123 :: primes8117
def primes8147 := 8147 :: primes8123
def primes8161 := 8161 :: primes8147
def primes8167 := 8167 :: primes8161
def primes8171 := 8171 :: primes8167
def primes8179 := 8179 :: primes8171
def primes8191 := 8191 :: primes8179
def primes8209 := 8209 :: primes8191
def primes8219 := 8219 :: primes8209
def primes8221 := 8221 :: primes8219
def primes8231 := 8231 :: primes8221
def primes8233 := 8233 :: primes8231
def primes8237 := 8237 :: primes8233
def primes8243 := 8243 :: primes8237
def primes8263 := 8263 :: primes8243
def primes8269 := 8269 :: primes8263
def primes8273 := 8273 :: primes8269
def primes8287 := 8287 :: primes8273
def primes8291 := 8291 :: primes8287
def primes8293 := 8293 :: primes8291
def primes8297 := 8297 :: primes8293
def primes8311 := 8311 :: primes8297
def primes8317 := 8317 :: primes8311
def primes8329 := 8329 :: primes8317
def primes8353 := 8353 :: primes8329
def primes8363 := 8363 :: primes8353
def primes8369 := 8369 :: primes8363
def primes8377 := 8377 :: primes8369
def primes8387 := 8387 :: primes8377
def primes8389 := 8389 :: primes8387
def primes8419 := 8419 :: primes8389
def primes8423 := 8423 :: primes8419
def primes8429 := 8429 :: primes8423
def primes8431 := 8431 :: primes8429
def primes8443 := 8443 :: primes8431
def primes8447 := 8447 :: primes8443
def primes8461 := 8461 :: primes8447
def primes8467 := 8467 :: primes8461
def primes8501 := 8501 :: primes8467
def primes8513 := 8513 :: primes8501
def primes8521 := 8521 :: primes8513
def primes8527 := 8527 :: primes8521
def primes8537 := 8537 :: primes8527
def primes8539 := 8539 :: primes8537
def primes8543 := 8543 :: primes8539
def primes8563 := 8563 :: primes8543
def primes8573 := 8573 :: primes8563
def primes8581 := 8581 :: primes8573
def primes8597 := 8597 :: primes8581
def primes8599 := 8599 :: primes8597
def primes8609 := 8609 :: primes8599
def primes8623 := 8623 :: primes8609
def primes8627 := 8627 :: primes8623
def primes8629 := 8629 :: primes8627
def primes8641 := 8641 :: primes8629
def primes8647 := 8647 :: primes8641
def primes8663 := 8663 :: primes8647
def primes8669 := 8669 :: primes8663
def primes8677 := 8677 :: primes8669
def primes8681 := 8681 :: primes8677
def primes8689 := 8689 :: primes8681
def primes8693 := 8693 :: primes8689
def primes8699 := 8699 :: primes8693
def primes8707 := 8707 :: primes8699
def primes8713 := 8713 :: primes8707
def primes8719 := 8719 :: primes8713
def primes8731 := 8731 :: primes8719
def primes8737 := 8737 :: primes8731
def primes8741 := 8741 :: primes8737
def primes8747 := 8747 :: primes8741
def primes8753 := 8753 :: primes8747
def primes8761 := 8761 :: primes8753
def primes8779 := 8779 :: primes8761
def primes8783 := 8783 :: primes8779
def primes8803 := 8803 :: primes8783
def primes8807 := 8807 :: primes8803
def primes8819 := 8819 :: primes8807
def primes8821 := 8821 :: primes8819
def primes8831 := 8831 :: primes8821
def primes8837 := 8837 :: primes8831
def primes8839 := 8839 :: primes8837
def primes8849 := 8849 :: primes8839
def primes8861 := 8861 :: primes8849
def primes8863 := 8863 :: primes8861
def primes8867 := 8867 :: primes8863
def primes8887 := 8887 :: primes8867
def primes8893 := 8893 :: primes8887
def primes8923 := 8923 :: primes8893
def primes8929 := 8929 :: primes8923
def primes8933 := 8933 :: primes8929
def primes8941 := 8941 :: primes8933
def primes8951 := 8951 :: primes8941
def primes8963 := 8963 :: primes8951
def primes8969 := 8969 :: primes8963
def primes8971 := 8971 :: primes8969
def primes8999 := 8999 :: primes8971
def primes9001 := 9001 :: primes8999
def primes9007 := 9007 :: primes9001
def primes9011 := 9011 :: primes9007
def primes9013 := 9013 :: primes9011
def primes9029 := 9029 :: primes9013
def primes9041 := 9041 :: primes9029
def primes9043 := 9043 :: primes9041
def primes9049 := 9049 :: primes9043
def primes9059 := 9059 :: primes9049
def primes9067 := 9067 :: primes9059
def primes9091 := 9091 :: primes9067
def primes9103 := 9103 :: primes9091
def primes9109 := 9109 :: primes9103
def primes9127 := 9127 :: primes9109
def primes9133 := 9133 :: primes9127
def primes9137 := 9137 :: primes9133
def primes9151 := 9151 :: primes9137
def primes9157 := 9157 :: primes9151
def primes9161 := 9161 :: primes9157
def primes9173 := 9173 :: primes9161
def primes9181 := 9181 :: primes9173
def primes9187 := 9187 :: primes9181
def primes9199 := 9199 :: primes9187
def primes9203 := 9203 :: primes9199
def primes9209 := 9209 :: primes9203
def primes9221 := 9221 :: primes9209
def primes9227 := 9227 :: primes9221
def primes9239 := 9239 :: primes9227
def primes9241 := 9241 :: primes9239
def primes9257 := 9257 :: primes9241
def primes9277 := 9277 :: primes9257
def primes9281 := 9281 :: primes9277
def primes9283 := 9283 :: primes9281
def primes9293 := 9293 :: primes9283
def primes9311 := 9311 :: primes9293
def primes9319 := 9319 :: primes9311
def primes9323 := 9323 :: primes9319
def primes9337 := 9337 :: primes9323
def primes9341 := 9341 :: primes9337
def primes9343 := 9343 :: primes9341
def primes9349 := 9349 :: primes9343
def primes9371 := 9371 :: primes9349
def primes9377 := 9377 :: primes9371
def primes9391 := 9391 :: primes9377
def primes9397 := 9397 :: primes9391
def primes9403 := 9403 :: primes9397
def primes9413 := 9413 :: primes9403
def primes9419 := 9419 :: primes9413
def primes9421 := 9421 :: primes9419
def primes9431 := 9431 :: primes9421
def primes9433 := 9433 :: primes9431
def primes9437 := 9437 :: primes9433
def primes9439 := 9439 :: primes9437
def primes9461 := 9461 :: primes9439
def primes9463 := 9463 :: primes9461
def primes9467 := 9467 :: primes9463
def primes9473 := 9473 :: primes9467
def primes9479 := 9479 :: primes9473

/- Check each sieve stage in sequence to bound peak memory. -/
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
lemma count9479 : legendreCount primes9479 90000000 = 5215780 := by
  refine extend_count (ps := primes9473) (p := 9479) (x := 5215783) (y := 3) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9467) (p := 9473) (x := 5215788) (y := 5) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9463) (p := 9467) (x := 5215794) (y := 6) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9461) (p := 9463) (x := 5215801) (y := 7) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9439) (p := 9461) (x := 5215810) (y := 9) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9437) (p := 9439) (x := 5215822) (y := 12) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9433) (p := 9437) (x := 5215835) (y := 13) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9431) (p := 9433) (x := 5215850) (y := 15) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9421) (p := 9431) (x := 5215866) (y := 16) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9419) (p := 9421) (x := 5215885) (y := 19) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9413) (p := 9419) (x := 5215905) (y := 20) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9403) (p := 9413) (x := 5215926) (y := 21) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9397) (p := 9403) (x := 5215948) (y := 22) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9391) (p := 9397) (x := 5215971) (y := 23) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9377) (p := 9391) (x := 5215995) (y := 24) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9371) (p := 9377) (x := 5216021) (y := 26) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9349) (p := 9371) (x := 5216049) (y := 28) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9343) (p := 9349) (x := 5216081) (y := 32) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9341) (p := 9343) (x := 5216116) (y := 35) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9337) (p := 9341) (x := 5216152) (y := 36) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9323) (p := 9337) (x := 5216189) (y := 37) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9319) (p := 9323) (x := 5216229) (y := 40) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9311) (p := 9319) (x := 5216270) (y := 41) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9293) (p := 9311) (x := 5216313) (y := 43) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9283) (p := 9293) (x := 5216359) (y := 46) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9281) (p := 9283) (x := 5216407) (y := 48) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9277) (p := 9281) (x := 5216457) (y := 50) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9257) (p := 9277) (x := 5216508) (y := 51) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9241) (p := 9257) (x := 5216562) (y := 54) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9239) (p := 9241) (x := 5216619) (y := 57) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9227) (p := 9239) (x := 5216677) (y := 58) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9221) (p := 9227) (x := 5216738) (y := 61) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9209) (p := 9221) (x := 5216800) (y := 62) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9203) (p := 9209) (x := 5216865) (y := 65) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9199) (p := 9203) (x := 5216931) (y := 66) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9187) (p := 9199) (x := 5216999) (y := 68) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9181) (p := 9187) (x := 5217070) (y := 71) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9173) (p := 9181) (x := 5217142) (y := 72) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9161) (p := 9173) (x := 5217217) (y := 75) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9157) (p := 9161) (x := 5217294) (y := 77) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9151) (p := 9157) (x := 5217372) (y := 78) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9137) (p := 9151) (x := 5217453) (y := 81) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9133) (p := 9137) (x := 5217536) (y := 83) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9127) (p := 9133) (x := 5217621) (y := 85) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9109) (p := 9127) (x := 5217709) (y := 88) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9103) (p := 9109) (x := 5217799) (y := 90) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9091) (p := 9103) (x := 5217891) (y := 92) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9067) (p := 9091) (x := 5217985) (y := 94) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9059) (p := 9067) (x := 5218083) (y := 98) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9049) (p := 9059) (x := 5218184) (y := 101) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9043) (p := 9049) (x := 5218287) (y := 103) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9041) (p := 9043) (x := 5218392) (y := 105) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9029) (p := 9041) (x := 5218498) (y := 106) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9013) (p := 9029) (x := 5218606) (y := 108) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9011) (p := 9013) (x := 5218716) (y := 110) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9007) (p := 9011) (x := 5218827) (y := 111) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes9001) (p := 9007) (x := 5218939) (y := 112) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8999) (p := 9001) (x := 5219052) (y := 113) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8971) (p := 8999) (x := 5219166) (y := 114) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8969) (p := 8971) (x := 5219283) (y := 117) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8963) (p := 8969) (x := 5219401) (y := 118) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8951) (p := 8963) (x := 5219522) (y := 121) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8941) (p := 8951) (x := 5219644) (y := 122) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8933) (p := 8941) (x := 5219768) (y := 124) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8929) (p := 8933) (x := 5219895) (y := 127) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8923) (p := 8929) (x := 5220024) (y := 129) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8893) (p := 8923) (x := 5220154) (y := 130) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8887) (p := 8893) (x := 5220290) (y := 136) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8867) (p := 8887) (x := 5220427) (y := 137) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8863) (p := 8867) (x := 5220568) (y := 141) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8861) (p := 8863) (x := 5220711) (y := 143) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8849) (p := 8861) (x := 5220855) (y := 144) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8839) (p := 8849) (x := 5221003) (y := 148) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8837) (p := 8839) (x := 5221154) (y := 151) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8831) (p := 8837) (x := 5221306) (y := 152) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8821) (p := 8831) (x := 5221459) (y := 153) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8819) (p := 8821) (x := 5221614) (y := 155) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8807) (p := 8819) (x := 5221770) (y := 156) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8803) (p := 8807) (x := 5221928) (y := 158) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8783) (p := 8803) (x := 5222088) (y := 160) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8779) (p := 8783) (x := 5222251) (y := 163) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8761) (p := 8779) (x := 5222415) (y := 164) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8753) (p := 8761) (x := 5222584) (y := 169) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8747) (p := 8753) (x := 5222755) (y := 171) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8741) (p := 8747) (x := 5222928) (y := 173) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8737) (p := 8741) (x := 5223102) (y := 174) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8731) (p := 8737) (x := 5223278) (y := 176) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8719) (p := 8731) (x := 5223456) (y := 178) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8713) (p := 8719) (x := 5223637) (y := 181) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8707) (p := 8713) (x := 5223819) (y := 182) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8699) (p := 8707) (x := 5224004) (y := 185) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8693) (p := 8699) (x := 5224192) (y := 188) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8689) (p := 8693) (x := 5224381) (y := 189) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8681) (p := 8689) (x := 5224572) (y := 191) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8677) (p := 8681) (x := 5224764) (y := 192) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8669) (p := 8677) (x := 5224958) (y := 194) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8663) (p := 8669) (x := 5225153) (y := 195) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8647) (p := 8663) (x := 5225349) (y := 196) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8641) (p := 8647) (x := 5225548) (y := 199) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8629) (p := 8641) (x := 5225748) (y := 200) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8627) (p := 8629) (x := 5225951) (y := 203) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8623) (p := 8627) (x := 5226155) (y := 204) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8609) (p := 8623) (x := 5226361) (y := 206) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8599) (p := 8609) (x := 5226569) (y := 208) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8597) (p := 8599) (x := 5226781) (y := 212) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8581) (p := 8597) (x := 5226994) (y := 213) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8573) (p := 8581) (x := 5227210) (y := 216) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8563) (p := 8573) (x := 5227427) (y := 217) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8543) (p := 8563) (x := 5227647) (y := 220) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8539) (p := 8543) (x := 5227871) (y := 224) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8537) (p := 8539) (x := 5228096) (y := 225) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8527) (p := 8537) (x := 5228322) (y := 226) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8521) (p := 8527) (x := 5228549) (y := 227) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8513) (p := 8521) (x := 5228778) (y := 229) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8501) (p := 8513) (x := 5229009) (y := 231) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8467) (p := 8501) (x := 5229241) (y := 232) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8461) (p := 8467) (x := 5229480) (y := 239) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8447) (p := 8461) (x := 5229721) (y := 241) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8443) (p := 8447) (x := 5229965) (y := 244) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8431) (p := 8443) (x := 5230211) (y := 246) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8429) (p := 8431) (x := 5230460) (y := 249) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8423) (p := 8429) (x := 5230710) (y := 250) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8419) (p := 8423) (x := 5230961) (y := 251) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8389) (p := 8419) (x := 5231214) (y := 253) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8387) (p := 8389) (x := 5231472) (y := 258) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8377) (p := 8387) (x := 5231732) (y := 260) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8369) (p := 8377) (x := 5231995) (y := 263) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8363) (p := 8369) (x := 5232260) (y := 265) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8353) (p := 8363) (x := 5232526) (y := 266) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8329) (p := 8353) (x := 5232794) (y := 268) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8317) (p := 8329) (x := 5233066) (y := 272) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8311) (p := 8317) (x := 5233339) (y := 273) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8297) (p := 8311) (x := 5233613) (y := 274) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8293) (p := 8297) (x := 5233891) (y := 278) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8291) (p := 8293) (x := 5234170) (y := 279) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8287) (p := 8291) (x := 5234451) (y := 281) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8273) (p := 8287) (x := 5234734) (y := 283) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8269) (p := 8273) (x := 5235020) (y := 286) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8263) (p := 8269) (x := 5235308) (y := 288) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8243) (p := 8263) (x := 5235599) (y := 291) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8237) (p := 8243) (x := 5235893) (y := 294) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8233) (p := 8237) (x := 5236188) (y := 295) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8231) (p := 8233) (x := 5236484) (y := 296) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8221) (p := 8231) (x := 5236781) (y := 297) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8219) (p := 8221) (x := 5237081) (y := 300) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8209) (p := 8219) (x := 5237383) (y := 302) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8191) (p := 8209) (x := 5237687) (y := 304) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8179) (p := 8191) (x := 5237995) (y := 308) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8171) (p := 8179) (x := 5238306) (y := 311) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8167) (p := 8171) (x := 5238618) (y := 312) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8161) (p := 8167) (x := 5238931) (y := 313) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8147) (p := 8161) (x := 5239246) (y := 315) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8123) (p := 8147) (x := 5239563) (y := 317) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8117) (p := 8123) (x := 5239885) (y := 322) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8111) (p := 8117) (x := 5240210) (y := 325) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8101) (p := 8111) (x := 5240537) (y := 327) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8093) (p := 8101) (x := 5240865) (y := 328) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8089) (p := 8093) (x := 5241197) (y := 332) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8087) (p := 8089) (x := 5241530) (y := 333) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8081) (p := 8087) (x := 5241864) (y := 334) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8069) (p := 8081) (x := 5242200) (y := 336) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8059) (p := 8069) (x := 5242538) (y := 338) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8053) (p := 8059) (x := 5242879) (y := 341) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8039) (p := 8053) (x := 5243223) (y := 344) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8017) (p := 8039) (x := 5243569) (y := 346) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8011) (p := 8017) (x := 5243918) (y := 349) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes8009) (p := 8011) (x := 5244268) (y := 350) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7993) (p := 8009) (x := 5244619) (y := 351) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7963) (p := 7993) (x := 5244975) (y := 356) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7951) (p := 7963) (x := 5245337) (y := 362) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7949) (p := 7951) (x := 5245702) (y := 365) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7937) (p := 7949) (x := 5246069) (y := 367) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7933) (p := 7937) (x := 5246438) (y := 369) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7927) (p := 7933) (x := 5246808) (y := 370) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7919) (p := 7927) (x := 5247181) (y := 373) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7907) (p := 7919) (x := 5247555) (y := 374) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7901) (p := 7907) (x := 5247931) (y := 376) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7883) (p := 7901) (x := 5248309) (y := 378) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7879) (p := 7883) (x := 5248691) (y := 382) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7877) (p := 7879) (x := 5249074) (y := 383) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7873) (p := 7877) (x := 5249459) (y := 385) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7867) (p := 7873) (x := 5249845) (y := 386) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7853) (p := 7867) (x := 5250233) (y := 388) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7841) (p := 7853) (x := 5250624) (y := 391) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7829) (p := 7841) (x := 5251018) (y := 394) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7823) (p := 7829) (x := 5251416) (y := 398) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7817) (p := 7823) (x := 5251817) (y := 401) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7793) (p := 7817) (x := 5252219) (y := 402) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7789) (p := 7793) (x := 5252624) (y := 405) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7759) (p := 7789) (x := 5253032) (y := 408) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7757) (p := 7759) (x := 5253445) (y := 413) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7753) (p := 7757) (x := 5253859) (y := 414) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7741) (p := 7753) (x := 5254274) (y := 415) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7727) (p := 7741) (x := 5254692) (y := 418) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7723) (p := 7727) (x := 5255112) (y := 420) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7717) (p := 7723) (x := 5255533) (y := 421) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7703) (p := 7717) (x := 5255956) (y := 423) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7699) (p := 7703) (x := 5256382) (y := 426) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7691) (p := 7699) (x := 5256810) (y := 428) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7687) (p := 7691) (x := 5257241) (y := 431) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7681) (p := 7687) (x := 5257673) (y := 432) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7673) (p := 7681) (x := 5258107) (y := 434) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7669) (p := 7673) (x := 5258543) (y := 436) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7649) (p := 7669) (x := 5258981) (y := 438) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7643) (p := 7649) (x := 5259421) (y := 440) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7639) (p := 7643) (x := 5259862) (y := 441) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7621) (p := 7639) (x := 5260306) (y := 444) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7607) (p := 7621) (x := 5260755) (y := 449) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7603) (p := 7607) (x := 5261209) (y := 454) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7591) (p := 7603) (x := 5261665) (y := 456) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7589) (p := 7591) (x := 5262123) (y := 458) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7583) (p := 7589) (x := 5262582) (y := 459) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7577) (p := 7583) (x := 5263044) (y := 462) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7573) (p := 7577) (x := 5263507) (y := 463) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7561) (p := 7573) (x := 5263971) (y := 464) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7559) (p := 7561) (x := 5264439) (y := 468) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7549) (p := 7559) (x := 5264908) (y := 469) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7547) (p := 7549) (x := 5265379) (y := 471) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7541) (p := 7547) (x := 5265852) (y := 473) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7537) (p := 7541) (x := 5266328) (y := 476) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7529) (p := 7537) (x := 5266807) (y := 479) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7523) (p := 7529) (x := 5267288) (y := 481) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7517) (p := 7523) (x := 5267771) (y := 483) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7507) (p := 7517) (x := 5268257) (y := 486) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7499) (p := 7507) (x := 5268746) (y := 489) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7489) (p := 7499) (x := 5269236) (y := 490) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7487) (p := 7489) (x := 5269729) (y := 493) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7481) (p := 7487) (x := 5270223) (y := 494) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7477) (p := 7481) (x := 5270718) (y := 495) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7459) (p := 7477) (x := 5271214) (y := 496) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7457) (p := 7459) (x := 5271715) (y := 501) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7451) (p := 7457) (x := 5272217) (y := 502) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7433) (p := 7451) (x := 5272722) (y := 505) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7417) (p := 7433) (x := 5273231) (y := 509) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7411) (p := 7417) (x := 5273744) (y := 513) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7393) (p := 7411) (x := 5274259) (y := 515) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7369) (p := 7393) (x := 5274779) (y := 520) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7351) (p := 7369) (x := 5275303) (y := 524) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7349) (p := 7351) (x := 5275831) (y := 528) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7333) (p := 7349) (x := 5276360) (y := 529) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7331) (p := 7333) (x := 5276894) (y := 534) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7321) (p := 7331) (x := 5277429) (y := 535) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7309) (p := 7321) (x := 5277968) (y := 539) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7307) (p := 7309) (x := 5278509) (y := 541) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7297) (p := 7307) (x := 5279051) (y := 542) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7283) (p := 7297) (x := 5279596) (y := 545) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7253) (p := 7283) (x := 5280144) (y := 548) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7247) (p := 7253) (x := 5280698) (y := 554) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7243) (p := 7247) (x := 5281255) (y := 557) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7237) (p := 7243) (x := 5281814) (y := 559) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7229) (p := 7237) (x := 5282375) (y := 561) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7219) (p := 7229) (x := 5282938) (y := 563) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7213) (p := 7219) (x := 5283504) (y := 566) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7211) (p := 7213) (x := 5284072) (y := 568) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7207) (p := 7211) (x := 5284642) (y := 570) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7193) (p := 7207) (x := 5285214) (y := 572) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7187) (p := 7193) (x := 5285791) (y := 577) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7177) (p := 7187) (x := 5286370) (y := 579) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7159) (p := 7177) (x := 5286952) (y := 582) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7151) (p := 7159) (x := 5287539) (y := 587) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7129) (p := 7151) (x := 5288129) (y := 590) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7127) (p := 7129) (x := 5288725) (y := 596) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7121) (p := 7127) (x := 5289322) (y := 597) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7109) (p := 7121) (x := 5289921) (y := 599) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7103) (p := 7109) (x := 5290525) (y := 604) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7079) (p := 7103) (x := 5291130) (y := 605) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7069) (p := 7079) (x := 5291741) (y := 611) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7057) (p := 7069) (x := 5292354) (y := 613) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7043) (p := 7057) (x := 5292970) (y := 616) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7039) (p := 7043) (x := 5293589) (y := 619) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7027) (p := 7039) (x := 5294210) (y := 621) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7019) (p := 7027) (x := 5294834) (y := 624) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7013) (p := 7019) (x := 5295461) (y := 627) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7001) (p := 7013) (x := 5296091) (y := 630) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6997) (p := 7001) (x := 5296724) (y := 633) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6991) (p := 6997) (x := 5297358) (y := 634) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6983) (p := 6991) (x := 5297993) (y := 635) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6977) (p := 6983) (x := 5298629) (y := 636) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6971) (p := 6977) (x := 5299269) (y := 640) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6967) (p := 6971) (x := 5299911) (y := 642) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6961) (p := 6967) (x := 5300556) (y := 645) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6959) (p := 6961) (x := 5301204) (y := 648) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6949) (p := 6959) (x := 5301853) (y := 649) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6947) (p := 6949) (x := 5302504) (y := 651) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6917) (p := 6947) (x := 5303157) (y := 653) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6911) (p := 6917) (x := 5303820) (y := 663) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6907) (p := 6911) (x := 5304484) (y := 664) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6899) (p := 6907) (x := 5305149) (y := 665) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6883) (p := 6899) (x := 5305818) (y := 669) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6871) (p := 6883) (x := 5306490) (y := 672) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6869) (p := 6871) (x := 5307164) (y := 674) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6863) (p := 6869) (x := 5307840) (y := 676) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6857) (p := 6863) (x := 5308519) (y := 679) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6841) (p := 6857) (x := 5309200) (y := 681) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6833) (p := 6841) (x := 5309885) (y := 685) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6829) (p := 6833) (x := 5310574) (y := 689) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6827) (p := 6829) (x := 5311265) (y := 691) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6823) (p := 6827) (x := 5311957) (y := 692) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6803) (p := 6823) (x := 5312652) (y := 695) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6793) (p := 6803) (x := 5313351) (y := 699) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6791) (p := 6793) (x := 5314052) (y := 701) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6781) (p := 6791) (x := 5314755) (y := 703) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6779) (p := 6781) (x := 5315461) (y := 706) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6763) (p := 6779) (x := 5316168) (y := 707) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6761) (p := 6763) (x := 5316878) (y := 710) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6737) (p := 6761) (x := 5317590) (y := 712) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6733) (p := 6737) (x := 5318308) (y := 718) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6719) (p := 6733) (x := 5319027) (y := 719) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6709) (p := 6719) (x := 5319749) (y := 722) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6703) (p := 6709) (x := 5320475) (y := 726) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6701) (p := 6703) (x := 5321204) (y := 729) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6691) (p := 6701) (x := 5321934) (y := 730) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6689) (p := 6691) (x := 5322666) (y := 732) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6679) (p := 6689) (x := 5323400) (y := 734) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6673) (p := 6679) (x := 5324138) (y := 738) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6661) (p := 6673) (x := 5324879) (y := 741) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6659) (p := 6661) (x := 5325622) (y := 743) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6653) (p := 6659) (x := 5326367) (y := 745) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6637) (p := 6653) (x := 5327114) (y := 747) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6619) (p := 6637) (x := 5327864) (y := 750) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6607) (p := 6619) (x := 5328619) (y := 755) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6599) (p := 6607) (x := 5329377) (y := 758) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6581) (p := 6599) (x := 5330138) (y := 761) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6577) (p := 6581) (x := 5330902) (y := 764) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6571) (p := 6577) (x := 5331669) (y := 767) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6569) (p := 6571) (x := 5332440) (y := 771) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6563) (p := 6569) (x := 5333213) (y := 773) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6553) (p := 6563) (x := 5333989) (y := 776) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6551) (p := 6553) (x := 5334769) (y := 780) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6547) (p := 6551) (x := 5335550) (y := 781) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6529) (p := 6547) (x := 5336332) (y := 782) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6521) (p := 6529) (x := 5337120) (y := 788) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6491) (p := 6521) (x := 5337911) (y := 791) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6481) (p := 6491) (x := 5338708) (y := 797) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6473) (p := 6481) (x := 5339510) (y := 802) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6469) (p := 6473) (x := 5340315) (y := 805) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6451) (p := 6469) (x := 5341122) (y := 807) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6449) (p := 6451) (x := 5341934) (y := 812) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6427) (p := 6449) (x := 5342747) (y := 813) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6421) (p := 6427) (x := 5343565) (y := 818) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6397) (p := 6421) (x := 5344386) (y := 821) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6389) (p := 6397) (x := 5345212) (y := 826) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6379) (p := 6389) (x := 5346042) (y := 830) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6373) (p := 6379) (x := 5346875) (y := 833) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6367) (p := 6373) (x := 5347709) (y := 834) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6361) (p := 6367) (x := 5348544) (y := 835) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6359) (p := 6361) (x := 5349381) (y := 837) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6353) (p := 6359) (x := 5350221) (y := 840) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6343) (p := 6353) (x := 5351063) (y := 842) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6337) (p := 6343) (x := 5351908) (y := 845) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6329) (p := 6337) (x := 5352755) (y := 847) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6323) (p := 6329) (x := 5353604) (y := 849) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6317) (p := 6323) (x := 5354455) (y := 851) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6311) (p := 6317) (x := 5355308) (y := 853) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6301) (p := 6311) (x := 5356164) (y := 856) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6299) (p := 6301) (x := 5357022) (y := 858) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6287) (p := 6299) (x := 5357881) (y := 859) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6277) (p := 6287) (x := 5358743) (y := 862) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6271) (p := 6277) (x := 5359609) (y := 866) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6269) (p := 6271) (x := 5360478) (y := 869) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6263) (p := 6269) (x := 5361348) (y := 870) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6257) (p := 6263) (x := 5362220) (y := 872) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6247) (p := 6257) (x := 5363093) (y := 873) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6229) (p := 6247) (x := 5363970) (y := 877) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6221) (p := 6229) (x := 5364855) (y := 885) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6217) (p := 6221) (x := 5365743) (y := 888) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6211) (p := 6217) (x := 5366632) (y := 889) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6203) (p := 6211) (x := 5367524) (y := 892) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6199) (p := 6203) (x := 5368418) (y := 894) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6197) (p := 6199) (x := 5369313) (y := 895) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6173) (p := 6197) (x := 5370210) (y := 897) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6163) (p := 6173) (x := 5371116) (y := 906) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6151) (p := 6163) (x := 5372025) (y := 909) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6143) (p := 6151) (x := 5372938) (y := 913) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6133) (p := 6143) (x := 5373854) (y := 916) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6131) (p := 6133) (x := 5374774) (y := 920) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6121) (p := 6131) (x := 5375695) (y := 921) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6113) (p := 6121) (x := 5376619) (y := 924) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6101) (p := 6113) (x := 5377546) (y := 927) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6091) (p := 6101) (x := 5378479) (y := 933) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6089) (p := 6091) (x := 5379417) (y := 938) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6079) (p := 6089) (x := 5380357) (y := 940) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6073) (p := 6079) (x := 5381300) (y := 943) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6067) (p := 6073) (x := 5382245) (y := 945) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6053) (p := 6067) (x := 5383194) (y := 949) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6047) (p := 6053) (x := 5384147) (y := 953) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6043) (p := 6047) (x := 5385103) (y := 956) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6037) (p := 6043) (x := 5386062) (y := 959) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6029) (p := 6037) (x := 5387023) (y := 961) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6011) (p := 6029) (x := 5387986) (y := 963) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes6007) (p := 6011) (x := 5388956) (y := 970) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5987) (p := 6007) (x := 5389927) (y := 971) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5981) (p := 5987) (x := 5390903) (y := 976) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5953) (p := 5981) (x := 5391880) (y := 977) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5939) (p := 5953) (x := 5392866) (y := 986) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5927) (p := 5939) (x := 5393858) (y := 992) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5923) (p := 5927) (x := 5394853) (y := 995) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5903) (p := 5923) (x := 5395851) (y := 998) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5897) (p := 5903) (x := 5396855) (y := 1004) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5881) (p := 5897) (x := 5397861) (y := 1006) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5879) (p := 5881) (x := 5398875) (y := 1014) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5869) (p := 5879) (x := 5399891) (y := 1016) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5867) (p := 5869) (x := 5400912) (y := 1021) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5861) (p := 5867) (x := 5401934) (y := 1022) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5857) (p := 5861) (x := 5402958) (y := 1024) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5851) (p := 5857) (x := 5403985) (y := 1027) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5849) (p := 5851) (x := 5405015) (y := 1030) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5843) (p := 5849) (x := 5406047) (y := 1032) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5839) (p := 5843) (x := 5407082) (y := 1035) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5827) (p := 5839) (x := 5408119) (y := 1037) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5821) (p := 5827) (x := 5409160) (y := 1041) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5813) (p := 5821) (x := 5410204) (y := 1044) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5807) (p := 5813) (x := 5411251) (y := 1047) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5801) (p := 5807) (x := 5412301) (y := 1050) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5791) (p := 5801) (x := 5413353) (y := 1052) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5783) (p := 5791) (x := 5414408) (y := 1055) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5779) (p := 5783) (x := 5415466) (y := 1058) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5749) (p := 5779) (x := 5416526) (y := 1060) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5743) (p := 5749) (x := 5417597) (y := 1071) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5741) (p := 5743) (x := 5418672) (y := 1075) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5737) (p := 5741) (x := 5419748) (y := 1076) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5717) (p := 5737) (x := 5420827) (y := 1079) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5711) (p := 5717) (x := 5421912) (y := 1085) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5701) (p := 5711) (x := 5422999) (y := 1087) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5693) (p := 5701) (x := 5424090) (y := 1091) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5689) (p := 5693) (x := 5425186) (y := 1096) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5683) (p := 5689) (x := 5426285) (y := 1099) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5669) (p := 5683) (x := 5427386) (y := 1101) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5659) (p := 5669) (x := 5428489) (y := 1103) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5657) (p := 5659) (x := 5429598) (y := 1109) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5653) (p := 5657) (x := 5430709) (y := 1111) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5651) (p := 5653) (x := 5431823) (y := 1114) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5647) (p := 5651) (x := 5432939) (y := 1116) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5641) (p := 5647) (x := 5434057) (y := 1118) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5639) (p := 5641) (x := 5435176) (y := 1119) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5623) (p := 5639) (x := 5436297) (y := 1121) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5591) (p := 5623) (x := 5437423) (y := 1126) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5581) (p := 5591) (x := 5438561) (y := 1138) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5573) (p := 5581) (x := 5439702) (y := 1141) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5569) (p := 5573) (x := 5440847) (y := 1145) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5563) (p := 5569) (x := 5441993) (y := 1146) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5557) (p := 5563) (x := 5443140) (y := 1147) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5531) (p := 5557) (x := 5444292) (y := 1152) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5527) (p := 5531) (x := 5445452) (y := 1160) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5521) (p := 5527) (x := 5446614) (y := 1162) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5519) (p := 5521) (x := 5447778) (y := 1164) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5507) (p := 5519) (x := 5448943) (y := 1165) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5503) (p := 5507) (x := 5450112) (y := 1169) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5501) (p := 5503) (x := 5451283) (y := 1171) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5483) (p := 5501) (x := 5452455) (y := 1172) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5479) (p := 5483) (x := 5453633) (y := 1178) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5477) (p := 5479) (x := 5454814) (y := 1181) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5471) (p := 5477) (x := 5455997) (y := 1183) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5449) (p := 5471) (x := 5457183) (y := 1186) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5443) (p := 5449) (x := 5458376) (y := 1193) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5441) (p := 5443) (x := 5459572) (y := 1196) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5437) (p := 5441) (x := 5460769) (y := 1197) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5431) (p := 5437) (x := 5461969) (y := 1200) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5419) (p := 5431) (x := 5463172) (y := 1203) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5417) (p := 5419) (x := 5464379) (y := 1207) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5413) (p := 5417) (x := 5465587) (y := 1208) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5407) (p := 5413) (x := 5466797) (y := 1210) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5399) (p := 5407) (x := 5468010) (y := 1213) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5393) (p := 5399) (x := 5469228) (y := 1218) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5387) (p := 5393) (x := 5470448) (y := 1220) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5381) (p := 5387) (x := 5471673) (y := 1225) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5351) (p := 5381) (x := 5472899) (y := 1226) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5347) (p := 5351) (x := 5474133) (y := 1234) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5333) (p := 5347) (x := 5475371) (y := 1238) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5323) (p := 5333) (x := 5476612) (y := 1241) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5309) (p := 5323) (x := 5477859) (y := 1247) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5303) (p := 5309) (x := 5479112) (y := 1253) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5297) (p := 5303) (x := 5480367) (y := 1255) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5281) (p := 5297) (x := 5481626) (y := 1259) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5279) (p := 5281) (x := 5482893) (y := 1267) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5273) (p := 5279) (x := 5484162) (y := 1269) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5261) (p := 5273) (x := 5485433) (y := 1271) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5237) (p := 5261) (x := 5486709) (y := 1276) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5233) (p := 5237) (x := 5487992) (y := 1283) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5231) (p := 5233) (x := 5489278) (y := 1286) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5227) (p := 5231) (x := 5490566) (y := 1288) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5209) (p := 5227) (x := 5491857) (y := 1291) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5197) (p := 5209) (x := 5493152) (y := 1295) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5189) (p := 5197) (x := 5494452) (y := 1300) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5179) (p := 5189) (x := 5495757) (y := 1305) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5171) (p := 5179) (x := 5497066) (y := 1309) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5167) (p := 5171) (x := 5498381) (y := 1315) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5153) (p := 5167) (x := 5499698) (y := 1317) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5147) (p := 5153) (x := 5501020) (y := 1322) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5119) (p := 5147) (x := 5502347) (y := 1327) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5113) (p := 5119) (x := 5503686) (y := 1339) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5107) (p := 5113) (x := 5505028) (y := 1342) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5101) (p := 5107) (x := 5506372) (y := 1344) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5099) (p := 5101) (x := 5507719) (y := 1347) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5087) (p := 5099) (x := 5509067) (y := 1348) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5081) (p := 5087) (x := 5510421) (y := 1354) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5077) (p := 5081) (x := 5511778) (y := 1357) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5059) (p := 5077) (x := 5513136) (y := 1358) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5051) (p := 5059) (x := 5514502) (y := 1366) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5039) (p := 5051) (x := 5515871) (y := 1369) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5023) (p := 5039) (x := 5517245) (y := 1374) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5021) (p := 5023) (x := 5518626) (y := 1381) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5011) (p := 5021) (x := 5520010) (y := 1384) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5009) (p := 5011) (x := 5521399) (y := 1389) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5003) (p := 5009) (x := 5522789) (y := 1390) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4999) (p := 5003) (x := 5524185) (y := 1396) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4993) (p := 4999) (x := 5525582) (y := 1397) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4987) (p := 4993) (x := 5526981) (y := 1399) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4973) (p := 4987) (x := 5528383) (y := 1402) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4969) (p := 4973) (x := 5529793) (y := 1410) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4967) (p := 4969) (x := 5531204) (y := 1411) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4957) (p := 4967) (x := 5532617) (y := 1413) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4951) (p := 4957) (x := 5534037) (y := 1420) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4943) (p := 4951) (x := 5535459) (y := 1422) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4937) (p := 4943) (x := 5536885) (y := 1426) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4933) (p := 4937) (x := 5538316) (y := 1431) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4931) (p := 4933) (x := 5539749) (y := 1433) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4919) (p := 4931) (x := 5541184) (y := 1435) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4909) (p := 4919) (x := 5542625) (y := 1441) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4903) (p := 4909) (x := 5544072) (y := 1447) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4889) (p := 4903) (x := 5545522) (y := 1450) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4877) (p := 4889) (x := 5546978) (y := 1456) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4871) (p := 4877) (x := 5548441) (y := 1463) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4861) (p := 4871) (x := 5549907) (y := 1466) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4831) (p := 4861) (x := 5551377) (y := 1470) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4817) (p := 4831) (x := 5552858) (y := 1481) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4813) (p := 4817) (x := 5554344) (y := 1486) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4801) (p := 4813) (x := 5555832) (y := 1488) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4799) (p := 4801) (x := 5557326) (y := 1494) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4793) (p := 4799) (x := 5558822) (y := 1496) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4789) (p := 4793) (x := 5560321) (y := 1499) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4787) (p := 4789) (x := 5561823) (y := 1502) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4783) (p := 4787) (x := 5563327) (y := 1504) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4759) (p := 4783) (x := 5564833) (y := 1506) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4751) (p := 4759) (x := 5566345) (y := 1512) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4733) (p := 4751) (x := 5567861) (y := 1516) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4729) (p := 4733) (x := 5569385) (y := 1524) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4723) (p := 4729) (x := 5570911) (y := 1526) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4721) (p := 4723) (x := 5572440) (y := 1529) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4703) (p := 4721) (x := 5573970) (y := 1530) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4691) (p := 4703) (x := 5575507) (y := 1537) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4679) (p := 4691) (x := 5577051) (y := 1544) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4673) (p := 4679) (x := 5578601) (y := 1550) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4663) (p := 4673) (x := 5580155) (y := 1554) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4657) (p := 4663) (x := 5581713) (y := 1558) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4651) (p := 4657) (x := 5583275) (y := 1562) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4649) (p := 4651) (x := 5584839) (y := 1564) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4643) (p := 4649) (x := 5586404) (y := 1565) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4639) (p := 4643) (x := 5587973) (y := 1569) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4637) (p := 4639) (x := 5589545) (y := 1572) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4621) (p := 4637) (x := 5591119) (y := 1574) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4603) (p := 4621) (x := 5592706) (y := 1587) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4597) (p := 4603) (x := 5594302) (y := 1596) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4591) (p := 4597) (x := 5595903) (y := 1601) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4583) (p := 4591) (x := 5597508) (y := 1605) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4567) (p := 4583) (x := 5599115) (y := 1607) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4561) (p := 4567) (x := 5600728) (y := 1613) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4549) (p := 4561) (x := 5602345) (y := 1617) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4547) (p := 4549) (x := 5603969) (y := 1624) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4523) (p := 4547) (x := 5605595) (y := 1626) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4519) (p := 4523) (x := 5607232) (y := 1637) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4517) (p := 4519) (x := 5608871) (y := 1639) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4513) (p := 4517) (x := 5610512) (y := 1641) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4507) (p := 4513) (x := 5612156) (y := 1644) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4493) (p := 4507) (x := 5613804) (y := 1648) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4483) (p := 4493) (x := 5615462) (y := 1658) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4481) (p := 4483) (x := 5617125) (y := 1663) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4463) (p := 4481) (x := 5618789) (y := 1664) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4457) (p := 4463) (x := 5620465) (y := 1676) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4451) (p := 4457) (x := 5622145) (y := 1680) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4447) (p := 4451) (x := 5623828) (y := 1683) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4441) (p := 4447) (x := 5625514) (y := 1686) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4423) (p := 4441) (x := 5627203) (y := 1689) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4421) (p := 4423) (x := 5628901) (y := 1698) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4409) (p := 4421) (x := 5630602) (y := 1701) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4397) (p := 4409) (x := 5632311) (y := 1709) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4391) (p := 4397) (x := 5634024) (y := 1713) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4373) (p := 4391) (x := 5635741) (y := 1717) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4363) (p := 4373) (x := 5637467) (y := 1726) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4357) (p := 4363) (x := 5639198) (y := 1731) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4349) (p := 4357) (x := 5640932) (y := 1734) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4339) (p := 4349) (x := 5642670) (y := 1738) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4337) (p := 4339) (x := 5644413) (y := 1743) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4327) (p := 4337) (x := 5646160) (y := 1747) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4297) (p := 4327) (x := 5647913) (y := 1753) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4289) (p := 4297) (x := 5649680) (y := 1767) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4283) (p := 4289) (x := 5651453) (y := 1773) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4273) (p := 4283) (x := 5653230) (y := 1777) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4271) (p := 4273) (x := 5655014) (y := 1784) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4261) (p := 4271) (x := 5656800) (y := 1786) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4259) (p := 4261) (x := 5658591) (y := 1791) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4253) (p := 4259) (x := 5660383) (y := 1792) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4243) (p := 4253) (x := 5662180) (y := 1797) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4241) (p := 4243) (x := 5663985) (y := 1805) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4231) (p := 4241) (x := 5665792) (y := 1807) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4229) (p := 4231) (x := 5667603) (y := 1811) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4219) (p := 4229) (x := 5669416) (y := 1813) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4217) (p := 4219) (x := 5671235) (y := 1819) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4211) (p := 4217) (x := 5673056) (y := 1821) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4201) (p := 4211) (x := 5674879) (y := 1823) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4177) (p := 4201) (x := 5676711) (y := 1832) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4159) (p := 4177) (x := 5678556) (y := 1845) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4157) (p := 4159) (x := 5680414) (y := 1858) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4153) (p := 4157) (x := 5682275) (y := 1861) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4139) (p := 4153) (x := 5684138) (y := 1863) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4133) (p := 4139) (x := 5686009) (y := 1871) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4129) (p := 4133) (x := 5687885) (y := 1876) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4127) (p := 4129) (x := 5689763) (y := 1878) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4111) (p := 4127) (x := 5691644) (y := 1881) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4099) (p := 4111) (x := 5693535) (y := 1891) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4093) (p := 4099) (x := 5695432) (y := 1897) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4091) (p := 4093) (x := 5697332) (y := 1900) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4079) (p := 4091) (x := 5699235) (y := 1903) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4073) (p := 4079) (x := 5701147) (y := 1912) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4057) (p := 4073) (x := 5703065) (y := 1918) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4051) (p := 4057) (x := 5704994) (y := 1929) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4049) (p := 4051) (x := 5706926) (y := 1932) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4027) (p := 4049) (x := 5708859) (y := 1933) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4021) (p := 4027) (x := 5710806) (y := 1947) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4019) (p := 4021) (x := 5712757) (y := 1951) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4013) (p := 4019) (x := 5714710) (y := 1953) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4007) (p := 4013) (x := 5716666) (y := 1956) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4003) (p := 4007) (x := 5718627) (y := 1961) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes4001) (p := 4003) (x := 5720592) (y := 1965) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3989) (p := 4001) (x := 5722558) (y := 1966) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3967) (p := 3989) (x := 5724531) (y := 1973) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3947) (p := 3967) (x := 5726517) (y := 1986) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3943) (p := 3947) (x := 5728518) (y := 2001) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3931) (p := 3943) (x := 5730523) (y := 2005) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3929) (p := 3931) (x := 5732534) (y := 2011) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3923) (p := 3929) (x := 5734547) (y := 2013) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3919) (p := 3923) (x := 5736564) (y := 2017) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3917) (p := 3919) (x := 5738585) (y := 2021) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3911) (p := 3917) (x := 5740608) (y := 2023) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3907) (p := 3911) (x := 5742635) (y := 2027) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3889) (p := 3907) (x := 5744667) (y := 2032) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3881) (p := 3889) (x := 5746712) (y := 2045) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3877) (p := 3881) (x := 5748763) (y := 2051) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3863) (p := 3877) (x := 5750819) (y := 2056) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3853) (p := 3863) (x := 5752883) (y := 2064) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3851) (p := 3853) (x := 5754954) (y := 2071) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3847) (p := 3851) (x := 5757027) (y := 2073) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3833) (p := 3847) (x := 5759102) (y := 2075) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3823) (p := 3833) (x := 5761184) (y := 2082) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3821) (p := 3823) (x := 5763272) (y := 2088) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3803) (p := 3821) (x := 5765362) (y := 2090) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3797) (p := 3803) (x := 5767467) (y := 2105) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3793) (p := 3797) (x := 5769578) (y := 2111) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3779) (p := 3793) (x := 5771691) (y := 2113) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3769) (p := 3779) (x := 5773815) (y := 2124) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3767) (p := 3769) (x := 5775948) (y := 2133) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3761) (p := 3767) (x := 5778083) (y := 2135) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3739) (p := 3761) (x := 5780225) (y := 2142) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3733) (p := 3739) (x := 5782381) (y := 2156) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3727) (p := 3733) (x := 5784546) (y := 2165) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3719) (p := 3727) (x := 5786716) (y := 2170) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3709) (p := 3719) (x := 5788892) (y := 2176) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3701) (p := 3709) (x := 5791075) (y := 2183) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3697) (p := 3701) (x := 5793261) (y := 2186) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3691) (p := 3697) (x := 5795450) (y := 2189) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3677) (p := 3691) (x := 5797644) (y := 2194) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3673) (p := 3677) (x := 5799848) (y := 2204) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3671) (p := 3673) (x := 5802055) (y := 2207) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3659) (p := 3671) (x := 5804264) (y := 2209) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3643) (p := 3659) (x := 5806481) (y := 2217) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3637) (p := 3643) (x := 5808708) (y := 2227) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3631) (p := 3637) (x := 5810938) (y := 2230) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3623) (p := 3631) (x := 5813173) (y := 2235) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3617) (p := 3623) (x := 5815414) (y := 2241) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3613) (p := 3617) (x := 5817660) (y := 2246) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3607) (p := 3613) (x := 5819909) (y := 2249) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3593) (p := 3607) (x := 5822163) (y := 2254) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3583) (p := 3593) (x := 5824428) (y := 2265) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3581) (p := 3583) (x := 5826700) (y := 2272) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3571) (p := 3581) (x := 5828975) (y := 2275) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3559) (p := 3571) (x := 5831258) (y := 2283) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3557) (p := 3559) (x := 5833549) (y := 2291) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3547) (p := 3557) (x := 5835842) (y := 2293) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3541) (p := 3547) (x := 5838146) (y := 2304) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3539) (p := 3541) (x := 5840454) (y := 2308) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3533) (p := 3539) (x := 5842764) (y := 2310) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3529) (p := 3533) (x := 5845082) (y := 2318) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3527) (p := 3529) (x := 5847401) (y := 2319) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3517) (p := 3527) (x := 5849721) (y := 2320) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3511) (p := 3517) (x := 5852050) (y := 2329) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3499) (p := 3511) (x := 5854385) (y := 2335) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3491) (p := 3499) (x := 5856730) (y := 2345) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3469) (p := 3491) (x := 5859082) (y := 2352) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3467) (p := 3469) (x := 5861452) (y := 2370) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3463) (p := 3467) (x := 5863824) (y := 2372) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3461) (p := 3463) (x := 5866199) (y := 2375) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3457) (p := 3461) (x := 5868578) (y := 2379) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3449) (p := 3457) (x := 5870961) (y := 2383) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3433) (p := 3449) (x := 5873348) (y := 2387) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3413) (p := 3433) (x := 5875750) (y := 2402) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3407) (p := 3413) (x := 5878168) (y := 2418) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3391) (p := 3407) (x := 5880592) (y := 2424) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3389) (p := 3391) (x := 5883029) (y := 2437) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3373) (p := 3389) (x := 5885467) (y := 2438) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3371) (p := 3373) (x := 5887917) (y := 2450) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3361) (p := 3371) (x := 5890371) (y := 2454) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3359) (p := 3361) (x := 5892837) (y := 2466) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3347) (p := 3359) (x := 5895305) (y := 2468) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3343) (p := 3347) (x := 5897784) (y := 2479) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3331) (p := 3343) (x := 5900268) (y := 2484) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3329) (p := 3331) (x := 5902763) (y := 2495) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3323) (p := 3329) (x := 5905260) (y := 2497) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3319) (p := 3323) (x := 5907764) (y := 2504) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3313) (p := 3319) (x := 5910273) (y := 2509) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3307) (p := 3313) (x := 5912785) (y := 2512) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3301) (p := 3307) (x := 5915302) (y := 2517) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3299) (p := 3301) (x := 5917824) (y := 2522) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3271) (p := 3299) (x := 5920349) (y := 2525) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3259) (p := 3271) (x := 5922894) (y := 2545) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3257) (p := 3259) (x := 5925448) (y := 2554) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3253) (p := 3257) (x := 5928005) (y := 2557) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3251) (p := 3253) (x := 5930565) (y := 2560) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3229) (p := 3251) (x := 5933127) (y := 2562) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3221) (p := 3229) (x := 5935714) (y := 2587) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3217) (p := 3221) (x := 5938308) (y := 2594) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3209) (p := 3217) (x := 5940908) (y := 2600) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3203) (p := 3209) (x := 5943515) (y := 2607) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3191) (p := 3203) (x := 5946129) (y := 2614) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3187) (p := 3191) (x := 5948753) (y := 2624) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3181) (p := 3187) (x := 5951381) (y := 2628) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3169) (p := 3181) (x := 5954014) (y := 2633) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3167) (p := 3169) (x := 5956656) (y := 2642) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3163) (p := 3167) (x := 5959302) (y := 2646) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3137) (p := 3163) (x := 5961953) (y := 2651) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3121) (p := 3137) (x := 5964634) (y := 2681) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3119) (p := 3121) (x := 5967330) (y := 2696) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3109) (p := 3119) (x := 5970029) (y := 2699) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3089) (p := 3109) (x := 5972738) (y := 2709) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3083) (p := 3089) (x := 5975464) (y := 2726) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3079) (p := 3083) (x := 5978198) (y := 2734) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3067) (p := 3079) (x := 5980937) (y := 2739) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3061) (p := 3067) (x := 5983688) (y := 2751) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3049) (p := 3061) (x := 5986447) (y := 2759) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3041) (p := 3049) (x := 5989216) (y := 2769) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3037) (p := 3041) (x := 5991994) (y := 2778) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3023) (p := 3037) (x := 5994777) (y := 2783) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3019) (p := 3023) (x := 5997572) (y := 2795) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3011) (p := 3019) (x := 6000370) (y := 2798) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3001) (p := 3011) (x := 6003178) (y := 2808) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2999) (p := 3001) (x := 6005994) (y := 2816) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2971) (p := 2999) (x := 6008811) (y := 2817) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2969) (p := 2971) (x := 6011658) (y := 2847) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2963) (p := 2969) (x := 6014509) (y := 2851) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2957) (p := 2963) (x := 6017366) (y := 2857) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2953) (p := 2957) (x := 6020229) (y := 2863) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2939) (p := 2953) (x := 6023096) (y := 2867) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2927) (p := 2939) (x := 6025976) (y := 2880) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2917) (p := 2927) (x := 6028870) (y := 2894) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2909) (p := 2917) (x := 6031777) (y := 2907) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2903) (p := 2909) (x := 6034693) (y := 2916) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2897) (p := 2903) (x := 6037615) (y := 2922) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2887) (p := 2897) (x := 6040544) (y := 2929) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2879) (p := 2887) (x := 6043485) (y := 2941) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2861) (p := 2879) (x := 6046440) (y := 2955) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2857) (p := 2861) (x := 6049411) (y := 2971) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2851) (p := 2857) (x := 6052387) (y := 2976) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2843) (p := 2851) (x := 6055372) (y := 2985) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2837) (p := 2843) (x := 6058365) (y := 2993) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2833) (p := 2837) (x := 6061366) (y := 3001) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2819) (p := 2833) (x := 6064372) (y := 3006) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2803) (p := 2819) (x := 6067391) (y := 3019) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2801) (p := 2803) (x := 6070429) (y := 3038) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2797) (p := 2801) (x := 6073470) (y := 3041) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2791) (p := 2797) (x := 6076516) (y := 3046) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2789) (p := 2791) (x := 6079570) (y := 3054) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2777) (p := 2789) (x := 6082628) (y := 3058) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2767) (p := 2777) (x := 6085703) (y := 3075) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2753) (p := 2767) (x := 6088791) (y := 3088) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2749) (p := 2753) (x := 6091897) (y := 3106) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2741) (p := 2749) (x := 6095009) (y := 3112) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2731) (p := 2741) (x := 6098132) (y := 3123) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2729) (p := 2731) (x := 6101266) (y := 3134) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2719) (p := 2729) (x := 6104404) (y := 3138) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2713) (p := 2719) (x := 6107557) (y := 3153) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2711) (p := 2713) (x := 6110717) (y := 3160) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2707) (p := 2711) (x := 6113881) (y := 3164) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2699) (p := 2707) (x := 6117051) (y := 3170) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2693) (p := 2699) (x := 6120230) (y := 3179) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2689) (p := 2693) (x := 6123419) (y := 3189) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2687) (p := 2689) (x := 6126613) (y := 3194) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2683) (p := 2687) (x := 6129811) (y := 3198) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2677) (p := 2683) (x := 6133014) (y := 3203) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2671) (p := 2677) (x := 6136230) (y := 3216) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2663) (p := 2671) (x := 6139453) (y := 3223) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2659) (p := 2663) (x := 6142688) (y := 3235) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2657) (p := 2659) (x := 6145929) (y := 3241) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2647) (p := 2657) (x := 6149175) (y := 3246) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2633) (p := 2647) (x := 6152432) (y := 3257) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2621) (p := 2633) (x := 6155704) (y := 3272) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2617) (p := 2621) (x := 6158995) (y := 3291) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2609) (p := 2617) (x := 6162292) (y := 3297) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2593) (p := 2609) (x := 6165599) (y := 3307) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2591) (p := 2593) (x := 6168930) (y := 3331) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2579) (p := 2591) (x := 6172264) (y := 3334) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2557) (p := 2579) (x := 6175615) (y := 3351) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2551) (p := 2557) (x := 6178993) (y := 3378) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2549) (p := 2551) (x := 6182379) (y := 3386) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2543) (p := 2549) (x := 6185768) (y := 3389) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2539) (p := 2543) (x := 6189166) (y := 3398) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2531) (p := 2539) (x := 6192572) (y := 3406) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2521) (p := 2531) (x := 6195990) (y := 3418) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2503) (p := 2521) (x := 6199418) (y := 3428) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2477) (p := 2503) (x := 6202870) (y := 3452) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2473) (p := 2477) (x := 6206360) (y := 3490) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2467) (p := 2473) (x := 6209857) (y := 3497) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2459) (p := 2467) (x := 6213362) (y := 3505) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2447) (p := 2459) (x := 6216881) (y := 3519) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2441) (p := 2447) (x := 6220419) (y := 3538) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2437) (p := 2441) (x := 6223967) (y := 3548) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2423) (p := 2437) (x := 6227525) (y := 3558) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2417) (p := 2423) (x := 6231103) (y := 3578) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2411) (p := 2417) (x := 6234690) (y := 3587) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2399) (p := 2411) (x := 6238286) (y := 3596) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2393) (p := 2399) (x := 6241902) (y := 3616) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2389) (p := 2393) (x := 6245532) (y := 3630) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2383) (p := 2389) (x := 6249169) (y := 3637) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2381) (p := 2383) (x := 6252812) (y := 3643) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2377) (p := 2381) (x := 6256459) (y := 3647) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2371) (p := 2377) (x := 6260113) (y := 3654) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2357) (p := 2371) (x := 6263775) (y := 3662) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2351) (p := 2357) (x := 6267457) (y := 3682) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2347) (p := 2351) (x := 6271150) (y := 3693) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2341) (p := 2347) (x := 6274852) (y := 3702) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2339) (p := 2341) (x := 6278560) (y := 3708) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2333) (p := 2339) (x := 6282274) (y := 3714) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2311) (p := 2333) (x := 6285995) (y := 3721) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2309) (p := 2311) (x := 6289755) (y := 3760) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2297) (p := 2309) (x := 6293520) (y := 3765) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2293) (p := 2297) (x := 6297305) (y := 3785) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2287) (p := 2293) (x := 6301100) (y := 3795) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2281) (p := 2287) (x := 6304904) (y := 3804) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2273) (p := 2281) (x := 6308720) (y := 3816) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2269) (p := 2273) (x := 6312548) (y := 3828) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2267) (p := 2269) (x := 6316382) (y := 3834) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2251) (p := 2267) (x := 6320220) (y := 3838) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2243) (p := 2251) (x := 6324088) (y := 3868) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2239) (p := 2243) (x := 6327970) (y := 3882) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2237) (p := 2239) (x := 6331862) (y := 3892) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2221) (p := 2237) (x := 6335757) (y := 3895) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2213) (p := 2221) (x := 6339676) (y := 3919) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2207) (p := 2213) (x := 6343608) (y := 3932) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2203) (p := 2207) (x := 6347550) (y := 3942) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2179) (p := 2203) (x := 6351503) (y := 3953) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2161) (p := 2179) (x := 6355502) (y := 3999) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2153) (p := 2161) (x := 6359535) (y := 4033) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2143) (p := 2153) (x := 6363582) (y := 4047) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2141) (p := 2143) (x := 6367651) (y := 4069) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2137) (p := 2141) (x := 6371726) (y := 4075) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2131) (p := 2137) (x := 6375809) (y := 4083) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2129) (p := 2131) (x := 6379906) (y := 4097) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2113) (p := 2129) (x := 6384006) (y := 4100) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2111) (p := 2113) (x := 6388143) (y := 4137) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2099) (p := 2111) (x := 6392282) (y := 4139) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2089) (p := 2099) (x := 6396450) (y := 4168) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2087) (p := 2089) (x := 6400638) (y := 4188) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2083) (p := 2087) (x := 6404830) (y := 4192) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2081) (p := 2083) (x := 6409029) (y := 4199) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2069) (p := 2081) (x := 6413232) (y := 4203) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2063) (p := 2069) (x := 6417456) (y := 4224) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2053) (p := 2063) (x := 6421692) (y := 4236) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2039) (p := 2053) (x := 6425948) (y := 4256) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2029) (p := 2039) (x := 6430236) (y := 4288) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2027) (p := 2029) (x := 6434543) (y := 4307) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2017) (p := 2027) (x := 6438856) (y := 4313) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2011) (p := 2017) (x := 6443188) (y := 4332) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2003) (p := 2011) (x := 6447536) (y := 4348) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1999) (p := 2003) (x := 6451902) (y := 4366) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1997) (p := 1999) (x := 6456278) (y := 4376) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1993) (p := 1997) (x := 6460657) (y := 4379) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1987) (p := 1993) (x := 6465045) (y := 4388) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1979) (p := 1987) (x := 6469446) (y := 4401) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1973) (p := 1979) (x := 6473863) (y := 4417) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1951) (p := 1973) (x := 6478295) (y := 4432) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1949) (p := 1951) (x := 6482771) (y := 4476) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1933) (p := 1949) (x := 6487253) (y := 4482) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1931) (p := 1933) (x := 6491771) (y := 4518) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1913) (p := 1931) (x := 6496295) (y := 4524) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1907) (p := 1913) (x := 6500857) (y := 4562) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1901) (p := 1907) (x := 6505435) (y := 4578) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1889) (p := 1901) (x := 6510027) (y := 4592) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1879) (p := 1889) (x := 6514650) (y := 4623) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1877) (p := 1879) (x := 6519298) (y := 4648) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1873) (p := 1877) (x := 6523953) (y := 4655) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1871) (p := 1873) (x := 6528618) (y := 4665) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1867) (p := 1871) (x := 6533287) (y := 4669) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1861) (p := 1867) (x := 6537967) (y := 4680) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1847) (p := 1861) (x := 6542660) (y := 4693) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1831) (p := 1847) (x := 6547387) (y := 4727) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1823) (p := 1831) (x := 6552158) (y := 4771) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1811) (p := 1823) (x := 6556952) (y := 4794) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1801) (p := 1811) (x := 6561777) (y := 4825) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1789) (p := 1801) (x := 6566630) (y := 4853) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1787) (p := 1789) (x := 6571516) (y := 4886) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1783) (p := 1787) (x := 6576410) (y := 4894) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1777) (p := 1783) (x := 6581314) (y := 4904) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1759) (p := 1777) (x := 6586234) (y := 4920) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1753) (p := 1759) (x := 6591197) (y := 4963) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1747) (p := 1753) (x := 6596176) (y := 4979) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1741) (p := 1747) (x := 6601178) (y := 5002) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1733) (p := 1741) (x := 6606200) (y := 5022) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1723) (p := 1733) (x := 6611245) (y := 5045) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1721) (p := 1723) (x := 6616317) (y := 5072) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1709) (p := 1721) (x := 6621397) (y := 5080) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1699) (p := 1709) (x := 6626507) (y := 5110) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1697) (p := 1699) (x := 6631648) (y := 5141) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1693) (p := 1697) (x := 6636795) (y := 5147) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1669) (p := 1693) (x := 6641956) (y := 5161) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1667) (p := 1669) (x := 6647189) (y := 5233) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1663) (p := 1667) (x := 6652428) (y := 5239) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1657) (p := 1663) (x := 6657678) (y := 5250) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1637) (p := 1657) (x := 6662944) (y := 5266) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1627) (p := 1637) (x := 6668275) (y := 5331) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1621) (p := 1627) (x := 6673636) (y := 5361) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1619) (p := 1621) (x := 6679015) (y := 5379) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1613) (p := 1619) (x := 6684400) (y := 5385) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1609) (p := 1613) (x := 6689807) (y := 5407) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1607) (p := 1609) (x := 6695234) (y := 5427) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1601) (p := 1607) (x := 6700667) (y := 5433) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1597) (p := 1601) (x := 6706120) (y := 5453) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1583) (p := 1597) (x := 6711583) (y := 5463) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1579) (p := 1583) (x := 6717099) (y := 5516) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1571) (p := 1579) (x := 6722633) (y := 5534) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1567) (p := 1571) (x := 6728198) (y := 5565) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1559) (p := 1567) (x := 6733776) (y := 5578) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1553) (p := 1559) (x := 6739380) (y := 5604) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1549) (p := 1553) (x := 6745007) (y := 5627) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1543) (p := 1549) (x := 6750648) (y := 5641) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1531) (p := 1543) (x := 6756312) (y := 5664) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1523) (p := 1531) (x := 6762018) (y := 5706) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1511) (p := 1523) (x := 6767754) (y := 5736) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1499) (p := 1511) (x := 6773537) (y := 5783) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1493) (p := 1499) (x := 6779361) (y := 5824) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1489) (p := 1493) (x := 6785208) (y := 5847) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1487) (p := 1489) (x := 6791069) (y := 5861) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1483) (p := 1487) (x := 6796937) (y := 5868) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1481) (p := 1483) (x := 6802821) (y := 5884) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1471) (p := 1481) (x := 6808715) (y := 5894) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1459) (p := 1471) (x := 6814644) (y := 5929) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1453) (p := 1459) (x := 6820621) (y := 5977) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1451) (p := 1453) (x := 6826617) (y := 5996) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1447) (p := 1451) (x := 6832624) (y := 6007) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1439) (p := 1447) (x := 6838648) (y := 6024) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1433) (p := 1439) (x := 6844701) (y := 6053) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1429) (p := 1433) (x := 6850778) (y := 6077) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1427) (p := 1429) (x := 6856871) (y := 6093) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1423) (p := 1427) (x := 6862972) (y := 6101) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1409) (p := 1423) (x := 6869087) (y := 6115) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1399) (p := 1409) (x := 6875272) (y := 6185) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1381) (p := 1399) (x := 6881493) (y := 6221) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1373) (p := 1381) (x := 6887785) (y := 6292) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1367) (p := 1373) (x := 6894112) (y := 6327) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1361) (p := 1367) (x := 6900471) (y := 6359) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1327) (p := 1361) (x := 6906857) (y := 6386) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1321) (p := 1327) (x := 6913398) (y := 6541) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1319) (p := 1321) (x := 6919967) (y := 6569) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1307) (p := 1319) (x := 6926546) (y := 6579) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1303) (p := 1307) (x := 6933175) (y := 6629) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1301) (p := 1303) (x := 6939825) (y := 6650) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1297) (p := 1301) (x := 6946484) (y := 6659) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1291) (p := 1297) (x := 6953163) (y := 6679) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1289) (p := 1291) (x := 6959867) (y := 6704) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1283) (p := 1289) (x := 6966580) (y := 6713) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1279) (p := 1283) (x := 6973325) (y := 6745) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1277) (p := 1279) (x := 6980092) (y := 6767) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1259) (p := 1277) (x := 6986870) (y := 6778) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1249) (p := 1259) (x := 6993749) (y := 6879) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1237) (p := 1249) (x := 7000680) (y := 6931) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1231) (p := 1237) (x := 7007674) (y := 6994) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1229) (p := 1231) (x := 7014702) (y := 7028) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1223) (p := 1229) (x := 7021737) (y := 7035) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1217) (p := 1223) (x := 7028805) (y := 7068) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1213) (p := 1217) (x := 7035906) (y := 7101) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1201) (p := 1213) (x := 7043029) (y := 7123) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1193) (p := 1201) (x := 7050225) (y := 7196) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1187) (p := 1193) (x := 7057465) (y := 7240) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1181) (p := 1187) (x := 7064742) (y := 7277) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1171) (p := 1181) (x := 7072049) (y := 7307) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1163) (p := 1171) (x := 7079414) (y := 7365) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1153) (p := 1163) (x := 7086828) (y := 7414) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1151) (p := 1153) (x := 7094306) (y := 7478) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1129) (p := 1151) (x := 7101797) (y := 7491) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1123) (p := 1129) (x := 7109420) (y := 7623) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1117) (p := 1123) (x := 7117079) (y := 7659) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1109) (p := 1117) (x := 7124778) (y := 7699) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1103) (p := 1109) (x := 7132536) (y := 7758) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1097) (p := 1103) (x := 7140333) (y := 7797) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1093) (p := 1097) (x := 7148176) (y := 7843) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1091) (p := 1093) (x := 7156045) (y := 7869) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1087) (p := 1091) (x := 7163929) (y := 7884) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1069) (p := 1087) (x := 7171842) (y := 7913) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1063) (p := 1069) (x := 7179870) (y := 8028) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1061) (p := 1063) (x := 7187943) (y := 8073) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1051) (p := 1061) (x := 7196031) (y := 8088) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1049) (p := 1051) (x := 7204190) (y := 8159) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1039) (p := 1049) (x := 7212363) (y := 8173) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1033) (p := 1039) (x := 7220611) (y := 8248) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1031) (p := 1033) (x := 7228900) (y := 8289) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1021) (p := 1031) (x := 7237205) (y := 8305) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1019) (p := 1021) (x := 7245588) (y := 8383) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1013) (p := 1019) (x := 7253983) (y := 8395) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes1009) (p := 1013) (x := 7262421) (y := 8438) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes997) (p := 1009) (x := 7270892) (y := 8471) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes991) (p := 997) (x := 7279468) (y := 8576) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes983) (p := 991) (x := 7288088) (y := 8620) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes977) (p := 983) (x := 7296775) (y := 8687) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes971) (p := 977) (x := 7305508) (y := 8733) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes967) (p := 971) (x := 7314299) (y := 8791) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes953) (p := 967) (x := 7323126) (y := 8827) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes947) (p := 953) (x := 7332073) (y := 8947) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes941) (p := 947) (x := 7341075) (y := 9002) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes937) (p := 941) (x := 7350137) (y := 9062) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes929) (p := 937) (x := 7359236) (y := 9099) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes919) (p := 929) (x := 7368406) (y := 9170) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes911) (p := 919) (x := 7377664) (y := 9258) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes907) (p := 911) (x := 7386992) (y := 9328) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes887) (p := 907) (x := 7396364) (y := 9372) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes883) (p := 887) (x := 7405927) (y := 9563) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes881) (p := 883) (x := 7415535) (y := 9608) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes877) (p := 881) (x := 7425168) (y := 9633) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes863) (p := 877) (x := 7434845) (y := 9677) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes859) (p := 863) (x := 7444656) (y := 9811) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes857) (p := 859) (x := 7454512) (y := 9856) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes853) (p := 857) (x := 7464390) (y := 9878) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes839) (p := 853) (x := 7474311) (y := 9921) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes829) (p := 839) (x := 7484387) (y := 10076) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes827) (p := 829) (x := 7494570) (y := 10183) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes823) (p := 827) (x := 7504774) (y := 10204) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes821) (p := 823) (x := 7515027) (y := 10253) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes811) (p := 821) (x := 7525310) (y := 10283) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes809) (p := 811) (x := 7535705) (y := 10395) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes797) (p := 809) (x := 7546122) (y := 10417) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes787) (p := 797) (x := 7556680) (y := 10558) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes773) (p := 787) (x := 7567364) (y := 10684) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes769) (p := 773) (x := 7578226) (y := 10862) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes761) (p := 769) (x := 7589139) (y := 10913) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes757) (p := 761) (x := 7600162) (y := 11023) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes751) (p := 757) (x := 7611234) (y := 11072) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes743) (p := 751) (x := 7622390) (y := 11156) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes739) (p := 743) (x := 7633660) (y := 11270) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes733) (p := 739) (x := 7644989) (y := 11329) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes727) (p := 733) (x := 7656406) (y := 11417) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes719) (p := 727) (x := 7667912) (y := 11506) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes709) (p := 719) (x := 7679534) (y := 11622) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes701) (p := 709) (x := 7691305) (y := 11771) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes691) (p := 701) (x := 7703199) (y := 11894) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes683) (p := 691) (x := 7715256) (y := 12057) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes677) (p := 683) (x := 7727442) (y := 12186) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes673) (p := 677) (x := 7739728) (y := 12286) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes661) (p := 673) (x := 7752085) (y := 12357) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes659) (p := 661) (x := 7764643) (y := 12558) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes653) (p := 659) (x := 7777247) (y := 12604) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes647) (p := 653) (x := 7789955) (y := 12708) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes643) (p := 647) (x := 7802770) (y := 12815) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes641) (p := 643) (x := 7815660) (y := 12890) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes631) (p := 641) (x := 7828587) (y := 12927) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes619) (p := 631) (x := 7841711) (y := 13124) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes617) (p := 619) (x := 7855050) (y := 13339) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes613) (p := 617) (x := 7868435) (y := 13385) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes607) (p := 613) (x := 7881899) (y := 13464) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes601) (p := 607) (x := 7895485) (y := 13586) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes599) (p := 601) (x := 7909204) (y := 13719) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes593) (p := 599) (x := 7922970) (y := 13766) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes587) (p := 593) (x := 7936868) (y := 13898) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes577) (p := 587) (x := 7950896) (y := 14028) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes571) (p := 577) (x := 7965149) (y := 14253) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes569) (p := 571) (x := 7979536) (y := 14387) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes563) (p := 569) (x := 7993967) (y := 14431) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes557) (p := 563) (x := 8008541) (y := 14574) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes547) (p := 557) (x := 8023257) (y := 14716) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes541) (p := 547) (x := 8038220) (y := 14963) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes523) (p := 541) (x := 8053323) (y := 15103) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes521) (p := 523) (x := 8068899) (y := 15576) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes509) (p := 521) (x := 8084537) (y := 15638) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes503) (p := 509) (x := 8100514) (y := 15977) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes499) (p := 503) (x := 8116662) (y := 16148) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes491) (p := 499) (x := 8132941) (y := 16279) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes487) (p := 491) (x := 8149451) (y := 16510) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes479) (p := 487) (x := 8166088) (y := 16637) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes467) (p := 479) (x := 8182990) (y := 16902) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes463) (p := 467) (x := 8200289) (y := 17299) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes461) (p := 463) (x := 8217727) (y := 17438) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes457) (p := 461) (x := 8235233) (y := 17506) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes449) (p := 457) (x := 8252878) (y := 17645) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes443) (p := 449) (x := 8270815) (y := 17937) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes439) (p := 443) (x := 8288969) (y := 18154) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes433) (p := 439) (x := 8307278) (y := 18309) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes431) (p := 433) (x := 8325844) (y := 18566) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes421) (p := 431) (x := 8344504) (y := 18660) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes419) (p := 421) (x := 8363596) (y := 19092) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes409) (p := 419) (x := 8382799) (y := 19203) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes401) (p := 409) (x := 8402465) (y := 19666) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes397) (p := 401) (x := 8422523) (y := 20058) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes389) (p := 397) (x := 8442807) (y := 20284) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes383) (p := 389) (x := 8463532) (y := 20725) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes379) (p := 383) (x := 8484599) (y := 21067) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes373) (p := 379) (x := 8505906) (y := 21307) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes367) (p := 373) (x := 8527594) (y := 21688) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes359) (p := 367) (x := 8549682) (y := 22088) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes353) (p := 359) (x := 8572311) (y := 22629) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes349) (p := 353) (x := 8595380) (y := 23069) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes347) (p := 349) (x := 8618771) (y := 23391) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes337) (p := 347) (x := 8642363) (y := 23592) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes331) (p := 337) (x := 8666722) (y := 24359) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes317) (p := 331) (x := 8691608) (y := 24886) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes313) (p := 317) (x := 8717676) (y := 26068) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes311) (p := 313) (x := 8744169) (y := 26493) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes307) (p := 311) (x := 8770928) (y := 26759) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes293) (p := 307) (x := 8798134) (y := 27206) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes283) (p := 293) (x := 8826764) (y := 28630) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes281) (p := 283) (x := 8856548) (y := 29784) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes277) (p := 281) (x := 8886687) (y := 30139) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes271) (p := 277) (x := 8917403) (y := 30716) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes269) (p := 271) (x := 8948960) (y := 31557) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes263) (p := 269) (x := 8980898) (y := 31938) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes257) (p := 263) (x := 9013735) (y := 32837) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes251) (p := 257) (x := 9047524) (y := 33789) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes241) (p := 251) (x := 9082298) (y := 34774) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes239) (p := 241) (x := 9118721) (y := 36423) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes233) (p := 239) (x := 9155652) (y := 36931) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes229) (p := 233) (x := 9193768) (y := 38116) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes227) (p := 229) (x := 9232792) (y := 39024) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes223) (p := 227) (x := 9272389) (y := 39597) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes211) (p := 223) (x := 9312932) (y := 40543) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes199) (p := 211) (x := 9356085) (y := 43153) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes197) (p := 199) (x := 9402211) (y := 46126) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes193) (p := 197) (x := 9449102) (y := 46891) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes191) (p := 193) (x := 9497285) (y := 48183) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes181) (p := 191) (x := 9546316) (y := 49031) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes179) (p := 181) (x := 9598469) (y := 52153) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes173) (p := 179) (x := 9651583) (y := 53114) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes167) (p := 173) (x := 9706970) (y := 55387) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes163) (p := 167) (x := 9764805) (y := 57835) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes157) (p := 163) (x := 9824512) (y := 59707) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes151) (p := 157) (x := 9887005) (y := 62493) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes149) (p := 151) (x := 9952526) (y := 65521) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes139) (p := 149) (x := 10019470) (y := 66944) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes137) (p := 139) (x := 10091876) (y := 72406) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes131) (p := 137) (x := 10165966) (y := 74090) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes127) (p := 131) (x := 10244153) (y := 78187) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes113) (p := 127) (x := 10325533) (y := 81380) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes109) (p := 113) (x := 10417950) (y := 92417) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes107) (p := 109) (x := 10514717) (y := 96767) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes103) (p := 107) (x := 10614259) (y := 99542) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes101) (p := 103) (x := 10718719) (y := 104460) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes97) (p := 101) (x := 10826326) (y := 107607) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes89) (p := 97) (x := 10939531) (y := 113205) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes83) (p := 89) (x := 11064281) (y := 124750) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes79) (p := 83) (x := 11199602) (y := 135321) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes73) (p := 79) (x := 11343542) (y := 143940) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes71) (p := 73) (x := 11501390) (y := 157848) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes67) (p := 71) (x := 11665927) (y := 164537) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes61) (p := 67) (x := 11842855) (y := 176928) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes59) (p := 61) (x := 12040328) (y := 197473) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes53) (p := 59) (x := 12247956) (y := 207628) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes47) (p := 53) (x := 12483479) (y := 235523) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes43) (p := 47) (x := 12754822) (y := 271343) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes41) (p := 43) (x := 13058470) (y := 303648) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes37) (p := 41) (x := 13384903) (y := 326433) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes31) (p := 37) (x := 13756696) (y := 371793) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes29) (p := 31) (x := 14215248) (y := 458552) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes23) (p := 29) (x := 14722941) (y := 507693) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes19) (p := 23) (x := 15392164) (y := 669223) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes17) (p := 19) (x := 16247284) (y := 855120) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes13) (p := 17) (x := 17262739) (y := 1015455) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes11) (p := 13) (x := 18701300) (y := 1438561) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes7) (p := 11) (x := 20571429) (y := 1870129) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes5) (p := 7) (x := 24000000) (y := 3428571) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes3) (p := 5) (x := 30000000) (y := 6000000) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes2) (p := 3) (x := 45000000) (y := 15000000) (by decide) ?_ (by decide +kernel) rfl
  refine extend_count (ps := primes0) (p := 2) (x := 90000000) (y := 45000000) (by decide) ?_ (by decide +kernel) rfl
  rfl

lemma coverStep {k d : ℕ} {previous added full : List ℕ}
    (hp : primeList k = previous) (ha : extendPrimes k d = added)
    (hf : added ++ previous = full) : primeList (k+d) = full :=
  (primeList_extend k d).trans ((congrArg₂ List.append ha hp).trans hf)

/- The following blocks verify that the sieve visits every prime up to 9486. -/
lemma covered0 : primeList 0 = primes0 := rfl

lemma covered64 : primeList 64 = primes61 :=
  coverStep (d := 64) (added := [61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]) covered0 (by decide +kernel) rfl

lemma covered128 : primeList 128 = primes127 :=
  coverStep (d := 64) (added := [127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67]) covered64 (by decide +kernel) rfl

lemma covered192 : primeList 192 = primes191 :=
  coverStep (d := 64) (added := [191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131]) covered128 (by decide +kernel) rfl

lemma covered256 : primeList 256 = primes251 :=
  coverStep (d := 64) (added := [251, 241, 239, 233, 229, 227, 223, 211, 199, 197, 193]) covered192 (by decide +kernel) rfl

lemma covered320 : primeList 320 = primes317 :=
  coverStep (d := 64) (added := [317, 313, 311, 307, 293, 283, 281, 277, 271, 269, 263, 257]) covered256 (by decide +kernel) rfl

lemma covered384 : primeList 384 = primes383 :=
  coverStep (d := 64) (added := [383, 379, 373, 367, 359, 353, 349, 347, 337, 331]) covered320 (by decide +kernel) rfl

lemma covered448 : primeList 448 = primes443 :=
  coverStep (d := 64) (added := [443, 439, 433, 431, 421, 419, 409, 401, 397, 389]) covered384 (by decide +kernel) rfl

lemma covered512 : primeList 512 = primes509 :=
  coverStep (d := 64) (added := [509, 503, 499, 491, 487, 479, 467, 463, 461, 457, 449]) covered448 (by decide +kernel) rfl

lemma covered576 : primeList 576 = primes571 :=
  coverStep (d := 64) (added := [571, 569, 563, 557, 547, 541, 523, 521]) covered512 (by decide +kernel) rfl

lemma covered640 : primeList 640 = primes631 :=
  coverStep (d := 64) (added := [631, 619, 617, 613, 607, 601, 599, 593, 587, 577]) covered576 (by decide +kernel) rfl

lemma covered704 : primeList 704 = primes701 :=
  coverStep (d := 64) (added := [701, 691, 683, 677, 673, 661, 659, 653, 647, 643, 641]) covered640 (by decide +kernel) rfl

lemma covered768 : primeList 768 = primes761 :=
  coverStep (d := 64) (added := [761, 757, 751, 743, 739, 733, 727, 719, 709]) covered704 (by decide +kernel) rfl

lemma covered832 : primeList 832 = primes829 :=
  coverStep (d := 64) (added := [829, 827, 823, 821, 811, 809, 797, 787, 773, 769]) covered768 (by decide +kernel) rfl

lemma covered896 : primeList 896 = primes887 :=
  coverStep (d := 64) (added := [887, 883, 881, 877, 863, 859, 857, 853, 839]) covered832 (by decide +kernel) rfl

lemma covered960 : primeList 960 = primes953 :=
  coverStep (d := 64) (added := [953, 947, 941, 937, 929, 919, 911, 907]) covered896 (by decide +kernel) rfl

lemma covered1024 : primeList 1024 = primes1021 :=
  coverStep (d := 64) (added := [1021, 1019, 1013, 1009, 997, 991, 983, 977, 971, 967]) covered960 (by decide +kernel) rfl

lemma covered1088 : primeList 1088 = primes1087 :=
  coverStep (d := 64) (added := [1087, 1069, 1063, 1061, 1051, 1049, 1039, 1033, 1031]) covered1024 (by decide +kernel) rfl

lemma covered1152 : primeList 1152 = primes1151 :=
  coverStep (d := 64) (added := [1151, 1129, 1123, 1117, 1109, 1103, 1097, 1093, 1091]) covered1088 (by decide +kernel) rfl

lemma covered1216 : primeList 1216 = primes1213 :=
  coverStep (d := 64) (added := [1213, 1201, 1193, 1187, 1181, 1171, 1163, 1153]) covered1152 (by decide +kernel) rfl

lemma covered1280 : primeList 1280 = primes1279 :=
  coverStep (d := 64) (added := [1279, 1277, 1259, 1249, 1237, 1231, 1229, 1223, 1217]) covered1216 (by decide +kernel) rfl

lemma covered1344 : primeList 1344 = primes1327 :=
  coverStep (d := 64) (added := [1327, 1321, 1319, 1307, 1303, 1301, 1297, 1291, 1289, 1283]) covered1280 (by decide +kernel) rfl

lemma covered1408 : primeList 1408 = primes1399 :=
  coverStep (d := 64) (added := [1399, 1381, 1373, 1367, 1361]) covered1344 (by decide +kernel) rfl

lemma covered1472 : primeList 1472 = primes1471 :=
  coverStep (d := 64) (added := [1471, 1459, 1453, 1451, 1447, 1439, 1433, 1429, 1427, 1423, 1409]) covered1408 (by decide +kernel) rfl

lemma covered1536 : primeList 1536 = primes1531 :=
  coverStep (d := 64) (added := [1531, 1523, 1511, 1499, 1493, 1489, 1487, 1483, 1481]) covered1472 (by decide +kernel) rfl

lemma covered1600 : primeList 1600 = primes1597 :=
  coverStep (d := 64) (added := [1597, 1583, 1579, 1571, 1567, 1559, 1553, 1549, 1543]) covered1536 (by decide +kernel) rfl

lemma covered1664 : primeList 1664 = primes1663 :=
  coverStep (d := 64) (added := [1663, 1657, 1637, 1627, 1621, 1619, 1613, 1609, 1607, 1601]) covered1600 (by decide +kernel) rfl

lemma covered1728 : primeList 1728 = primes1723 :=
  coverStep (d := 64) (added := [1723, 1721, 1709, 1699, 1697, 1693, 1669, 1667]) covered1664 (by decide +kernel) rfl

lemma covered1792 : primeList 1792 = primes1789 :=
  coverStep (d := 64) (added := [1789, 1787, 1783, 1777, 1759, 1753, 1747, 1741, 1733]) covered1728 (by decide +kernel) rfl

lemma covered1856 : primeList 1856 = primes1847 :=
  coverStep (d := 64) (added := [1847, 1831, 1823, 1811, 1801]) covered1792 (by decide +kernel) rfl

lemma covered1920 : primeList 1920 = primes1913 :=
  coverStep (d := 64) (added := [1913, 1907, 1901, 1889, 1879, 1877, 1873, 1871, 1867, 1861]) covered1856 (by decide +kernel) rfl

lemma covered1984 : primeList 1984 = primes1979 :=
  coverStep (d := 64) (added := [1979, 1973, 1951, 1949, 1933, 1931]) covered1920 (by decide +kernel) rfl

lemma covered2048 : primeList 2048 = primes2039 :=
  coverStep (d := 64) (added := [2039, 2029, 2027, 2017, 2011, 2003, 1999, 1997, 1993, 1987]) covered1984 (by decide +kernel) rfl

lemma covered2112 : primeList 2112 = primes2111 :=
  coverStep (d := 64) (added := [2111, 2099, 2089, 2087, 2083, 2081, 2069, 2063, 2053]) covered2048 (by decide +kernel) rfl

lemma covered2176 : primeList 2176 = primes2161 :=
  coverStep (d := 64) (added := [2161, 2153, 2143, 2141, 2137, 2131, 2129, 2113]) covered2112 (by decide +kernel) rfl

lemma covered2240 : primeList 2240 = primes2239 :=
  coverStep (d := 64) (added := [2239, 2237, 2221, 2213, 2207, 2203, 2179]) covered2176 (by decide +kernel) rfl

lemma covered2304 : primeList 2304 = primes2297 :=
  coverStep (d := 64) (added := [2297, 2293, 2287, 2281, 2273, 2269, 2267, 2251, 2243]) covered2240 (by decide +kernel) rfl

lemma covered2368 : primeList 2368 = primes2357 :=
  coverStep (d := 64) (added := [2357, 2351, 2347, 2341, 2339, 2333, 2311, 2309]) covered2304 (by decide +kernel) rfl

lemma covered2432 : primeList 2432 = primes2423 :=
  coverStep (d := 64) (added := [2423, 2417, 2411, 2399, 2393, 2389, 2383, 2381, 2377, 2371]) covered2368 (by decide +kernel) rfl

lemma covered2496 : primeList 2496 = primes2477 :=
  coverStep (d := 64) (added := [2477, 2473, 2467, 2459, 2447, 2441, 2437]) covered2432 (by decide +kernel) rfl

lemma covered2560 : primeList 2560 = primes2557 :=
  coverStep (d := 64) (added := [2557, 2551, 2549, 2543, 2539, 2531, 2521, 2503]) covered2496 (by decide +kernel) rfl

lemma covered2624 : primeList 2624 = primes2621 :=
  coverStep (d := 64) (added := [2621, 2617, 2609, 2593, 2591, 2579]) covered2560 (by decide +kernel) rfl

lemma covered2688 : primeList 2688 = primes2687 :=
  coverStep (d := 64) (added := [2687, 2683, 2677, 2671, 2663, 2659, 2657, 2647, 2633]) covered2624 (by decide +kernel) rfl

lemma covered2752 : primeList 2752 = primes2749 :=
  coverStep (d := 64) (added := [2749, 2741, 2731, 2729, 2719, 2713, 2711, 2707, 2699, 2693, 2689]) covered2688 (by decide +kernel) rfl

lemma covered2816 : primeList 2816 = primes2803 :=
  coverStep (d := 64) (added := [2803, 2801, 2797, 2791, 2789, 2777, 2767, 2753]) covered2752 (by decide +kernel) rfl

lemma covered2880 : primeList 2880 = primes2879 :=
  coverStep (d := 64) (added := [2879, 2861, 2857, 2851, 2843, 2837, 2833, 2819]) covered2816 (by decide +kernel) rfl

lemma covered2944 : primeList 2944 = primes2939 :=
  coverStep (d := 64) (added := [2939, 2927, 2917, 2909, 2903, 2897, 2887]) covered2880 (by decide +kernel) rfl

lemma covered3008 : primeList 3008 = primes3001 :=
  coverStep (d := 64) (added := [3001, 2999, 2971, 2969, 2963, 2957, 2953]) covered2944 (by decide +kernel) rfl

lemma covered3072 : primeList 3072 = primes3067 :=
  coverStep (d := 64) (added := [3067, 3061, 3049, 3041, 3037, 3023, 3019, 3011]) covered3008 (by decide +kernel) rfl

lemma covered3136 : primeList 3136 = primes3121 :=
  coverStep (d := 64) (added := [3121, 3119, 3109, 3089, 3083, 3079]) covered3072 (by decide +kernel) rfl

lemma covered3200 : primeList 3200 = primes3191 :=
  coverStep (d := 64) (added := [3191, 3187, 3181, 3169, 3167, 3163, 3137]) covered3136 (by decide +kernel) rfl

lemma covered3264 : primeList 3264 = primes3259 :=
  coverStep (d := 64) (added := [3259, 3257, 3253, 3251, 3229, 3221, 3217, 3209, 3203]) covered3200 (by decide +kernel) rfl

lemma covered3328 : primeList 3328 = primes3323 :=
  coverStep (d := 64) (added := [3323, 3319, 3313, 3307, 3301, 3299, 3271]) covered3264 (by decide +kernel) rfl

lemma covered3392 : primeList 3392 = primes3391 :=
  coverStep (d := 64) (added := [3391, 3389, 3373, 3371, 3361, 3359, 3347, 3343, 3331, 3329]) covered3328 (by decide +kernel) rfl

lemma covered3456 : primeList 3456 = primes3449 :=
  coverStep (d := 64) (added := [3449, 3433, 3413, 3407]) covered3392 (by decide +kernel) rfl

lemma covered3520 : primeList 3520 = primes3517 :=
  coverStep (d := 64) (added := [3517, 3511, 3499, 3491, 3469, 3467, 3463, 3461, 3457]) covered3456 (by decide +kernel) rfl

lemma covered3584 : primeList 3584 = primes3583 :=
  coverStep (d := 64) (added := [3583, 3581, 3571, 3559, 3557, 3547, 3541, 3539, 3533, 3529, 3527]) covered3520 (by decide +kernel) rfl

lemma covered3648 : primeList 3648 = primes3643 :=
  coverStep (d := 64) (added := [3643, 3637, 3631, 3623, 3617, 3613, 3607, 3593]) covered3584 (by decide +kernel) rfl

lemma covered3712 : primeList 3712 = primes3709 :=
  coverStep (d := 64) (added := [3709, 3701, 3697, 3691, 3677, 3673, 3671, 3659]) covered3648 (by decide +kernel) rfl

lemma covered3776 : primeList 3776 = primes3769 :=
  coverStep (d := 64) (added := [3769, 3767, 3761, 3739, 3733, 3727, 3719]) covered3712 (by decide +kernel) rfl

lemma covered3840 : primeList 3840 = primes3833 :=
  coverStep (d := 64) (added := [3833, 3823, 3821, 3803, 3797, 3793, 3779]) covered3776 (by decide +kernel) rfl

lemma covered3904 : primeList 3904 = primes3889 :=
  coverStep (d := 64) (added := [3889, 3881, 3877, 3863, 3853, 3851, 3847]) covered3840 (by decide +kernel) rfl

lemma covered3968 : primeList 3968 = primes3967 :=
  coverStep (d := 64) (added := [3967, 3947, 3943, 3931, 3929, 3923, 3919, 3917, 3911, 3907]) covered3904 (by decide +kernel) rfl

lemma covered4032 : primeList 4032 = primes4027 :=
  coverStep (d := 64) (added := [4027, 4021, 4019, 4013, 4007, 4003, 4001, 3989]) covered3968 (by decide +kernel) rfl

lemma covered4096 : primeList 4096 = primes4093 :=
  coverStep (d := 64) (added := [4093, 4091, 4079, 4073, 4057, 4051, 4049]) covered4032 (by decide +kernel) rfl

lemma covered4160 : primeList 4160 = primes4159 :=
  coverStep (d := 64) (added := [4159, 4157, 4153, 4139, 4133, 4129, 4127, 4111, 4099]) covered4096 (by decide +kernel) rfl

lemma covered4224 : primeList 4224 = primes4219 :=
  coverStep (d := 64) (added := [4219, 4217, 4211, 4201, 4177]) covered4160 (by decide +kernel) rfl

lemma covered4288 : primeList 4288 = primes4283 :=
  coverStep (d := 64) (added := [4283, 4273, 4271, 4261, 4259, 4253, 4243, 4241, 4231, 4229]) covered4224 (by decide +kernel) rfl

lemma covered4352 : primeList 4352 = primes4349 :=
  coverStep (d := 64) (added := [4349, 4339, 4337, 4327, 4297, 4289]) covered4288 (by decide +kernel) rfl

lemma covered4416 : primeList 4416 = primes4409 :=
  coverStep (d := 64) (added := [4409, 4397, 4391, 4373, 4363, 4357]) covered4352 (by decide +kernel) rfl

lemma covered4480 : primeList 4480 = primes4463 :=
  coverStep (d := 64) (added := [4463, 4457, 4451, 4447, 4441, 4423, 4421]) covered4416 (by decide +kernel) rfl

lemma covered4544 : primeList 4544 = primes4523 :=
  coverStep (d := 64) (added := [4523, 4519, 4517, 4513, 4507, 4493, 4483, 4481]) covered4480 (by decide +kernel) rfl

lemma covered4608 : primeList 4608 = primes4603 :=
  coverStep (d := 64) (added := [4603, 4597, 4591, 4583, 4567, 4561, 4549, 4547]) covered4544 (by decide +kernel) rfl

lemma covered4672 : primeList 4672 = primes4663 :=
  coverStep (d := 64) (added := [4663, 4657, 4651, 4649, 4643, 4639, 4637, 4621]) covered4608 (by decide +kernel) rfl

lemma covered4736 : primeList 4736 = primes4733 :=
  coverStep (d := 64) (added := [4733, 4729, 4723, 4721, 4703, 4691, 4679, 4673]) covered4672 (by decide +kernel) rfl

lemma covered4800 : primeList 4800 = primes4799 :=
  coverStep (d := 64) (added := [4799, 4793, 4789, 4787, 4783, 4759, 4751]) covered4736 (by decide +kernel) rfl

lemma covered4864 : primeList 4864 = primes4861 :=
  coverStep (d := 64) (added := [4861, 4831, 4817, 4813, 4801]) covered4800 (by decide +kernel) rfl

lemma covered4928 : primeList 4928 = primes4919 :=
  coverStep (d := 64) (added := [4919, 4909, 4903, 4889, 4877, 4871]) covered4864 (by decide +kernel) rfl

lemma covered4992 : primeList 4992 = primes4987 :=
  coverStep (d := 64) (added := [4987, 4973, 4969, 4967, 4957, 4951, 4943, 4937, 4933, 4931]) covered4928 (by decide +kernel) rfl

lemma covered5056 : primeList 5056 = primes5051 :=
  coverStep (d := 64) (added := [5051, 5039, 5023, 5021, 5011, 5009, 5003, 4999, 4993]) covered4992 (by decide +kernel) rfl

lemma covered5120 : primeList 5120 = primes5119 :=
  coverStep (d := 64) (added := [5119, 5113, 5107, 5101, 5099, 5087, 5081, 5077, 5059]) covered5056 (by decide +kernel) rfl

lemma covered5184 : primeList 5184 = primes5179 :=
  coverStep (d := 64) (added := [5179, 5171, 5167, 5153, 5147]) covered5120 (by decide +kernel) rfl

lemma covered5248 : primeList 5248 = primes5237 :=
  coverStep (d := 64) (added := [5237, 5233, 5231, 5227, 5209, 5197, 5189]) covered5184 (by decide +kernel) rfl

lemma covered5312 : primeList 5312 = primes5309 :=
  coverStep (d := 64) (added := [5309, 5303, 5297, 5281, 5279, 5273, 5261]) covered5248 (by decide +kernel) rfl

lemma covered5376 : primeList 5376 = primes5351 :=
  coverStep (d := 64) (added := [5351, 5347, 5333, 5323]) covered5312 (by decide +kernel) rfl

lemma covered5440 : primeList 5440 = primes5437 :=
  coverStep (d := 64) (added := [5437, 5431, 5419, 5417, 5413, 5407, 5399, 5393, 5387, 5381]) covered5376 (by decide +kernel) rfl

lemma covered5504 : primeList 5504 = primes5503 :=
  coverStep (d := 64) (added := [5503, 5501, 5483, 5479, 5477, 5471, 5449, 5443, 5441]) covered5440 (by decide +kernel) rfl

lemma covered5568 : primeList 5568 = primes5563 :=
  coverStep (d := 64) (added := [5563, 5557, 5531, 5527, 5521, 5519, 5507]) covered5504 (by decide +kernel) rfl

lemma covered5632 : primeList 5632 = primes5623 :=
  coverStep (d := 64) (added := [5623, 5591, 5581, 5573, 5569]) covered5568 (by decide +kernel) rfl

lemma covered5696 : primeList 5696 = primes5693 :=
  coverStep (d := 64) (added := [5693, 5689, 5683, 5669, 5659, 5657, 5653, 5651, 5647, 5641, 5639]) covered5632 (by decide +kernel) rfl

lemma covered5760 : primeList 5760 = primes5749 :=
  coverStep (d := 64) (added := [5749, 5743, 5741, 5737, 5717, 5711, 5701]) covered5696 (by decide +kernel) rfl

lemma covered5824 : primeList 5824 = primes5821 :=
  coverStep (d := 64) (added := [5821, 5813, 5807, 5801, 5791, 5783, 5779]) covered5760 (by decide +kernel) rfl

lemma covered5888 : primeList 5888 = primes5881 :=
  coverStep (d := 64) (added := [5881, 5879, 5869, 5867, 5861, 5857, 5851, 5849, 5843, 5839, 5827]) covered5824 (by decide +kernel) rfl

lemma covered5952 : primeList 5952 = primes5939 :=
  coverStep (d := 64) (added := [5939, 5927, 5923, 5903, 5897]) covered5888 (by decide +kernel) rfl

lemma covered6016 : primeList 6016 = primes6011 :=
  coverStep (d := 64) (added := [6011, 6007, 5987, 5981, 5953]) covered5952 (by decide +kernel) rfl

lemma covered6080 : primeList 6080 = primes6079 :=
  coverStep (d := 64) (added := [6079, 6073, 6067, 6053, 6047, 6043, 6037, 6029]) covered6016 (by decide +kernel) rfl

lemma covered6144 : primeList 6144 = primes6143 :=
  coverStep (d := 64) (added := [6143, 6133, 6131, 6121, 6113, 6101, 6091, 6089]) covered6080 (by decide +kernel) rfl

lemma covered6208 : primeList 6208 = primes6203 :=
  coverStep (d := 64) (added := [6203, 6199, 6197, 6173, 6163, 6151]) covered6144 (by decide +kernel) rfl

lemma covered6272 : primeList 6272 = primes6271 :=
  coverStep (d := 64) (added := [6271, 6269, 6263, 6257, 6247, 6229, 6221, 6217, 6211]) covered6208 (by decide +kernel) rfl

lemma covered6336 : primeList 6336 = primes6329 :=
  coverStep (d := 64) (added := [6329, 6323, 6317, 6311, 6301, 6299, 6287, 6277]) covered6272 (by decide +kernel) rfl

lemma covered6400 : primeList 6400 = primes6397 :=
  coverStep (d := 64) (added := [6397, 6389, 6379, 6373, 6367, 6361, 6359, 6353, 6343, 6337]) covered6336 (by decide +kernel) rfl

lemma covered6464 : primeList 6464 = primes6451 :=
  coverStep (d := 64) (added := [6451, 6449, 6427, 6421]) covered6400 (by decide +kernel) rfl

lemma covered6528 : primeList 6528 = primes6521 :=
  coverStep (d := 64) (added := [6521, 6491, 6481, 6473, 6469]) covered6464 (by decide +kernel) rfl

lemma covered6592 : primeList 6592 = primes6581 :=
  coverStep (d := 64) (added := [6581, 6577, 6571, 6569, 6563, 6553, 6551, 6547, 6529]) covered6528 (by decide +kernel) rfl

lemma covered6656 : primeList 6656 = primes6653 :=
  coverStep (d := 64) (added := [6653, 6637, 6619, 6607, 6599]) covered6592 (by decide +kernel) rfl

lemma covered6720 : primeList 6720 = primes6719 :=
  coverStep (d := 64) (added := [6719, 6709, 6703, 6701, 6691, 6689, 6679, 6673, 6661, 6659]) covered6656 (by decide +kernel) rfl

lemma covered6784 : primeList 6784 = primes6781 :=
  coverStep (d := 64) (added := [6781, 6779, 6763, 6761, 6737, 6733]) covered6720 (by decide +kernel) rfl

lemma covered6848 : primeList 6848 = primes6841 :=
  coverStep (d := 64) (added := [6841, 6833, 6829, 6827, 6823, 6803, 6793, 6791]) covered6784 (by decide +kernel) rfl

lemma covered6912 : primeList 6912 = primes6911 :=
  coverStep (d := 64) (added := [6911, 6907, 6899, 6883, 6871, 6869, 6863, 6857]) covered6848 (by decide +kernel) rfl

lemma covered6976 : primeList 6976 = primes6971 :=
  coverStep (d := 64) (added := [6971, 6967, 6961, 6959, 6949, 6947, 6917]) covered6912 (by decide +kernel) rfl

lemma covered7040 : primeList 7040 = primes7039 :=
  coverStep (d := 64) (added := [7039, 7027, 7019, 7013, 7001, 6997, 6991, 6983, 6977]) covered6976 (by decide +kernel) rfl

lemma covered7104 : primeList 7104 = primes7103 :=
  coverStep (d := 64) (added := [7103, 7079, 7069, 7057, 7043]) covered7040 (by decide +kernel) rfl

lemma covered7168 : primeList 7168 = primes7159 :=
  coverStep (d := 64) (added := [7159, 7151, 7129, 7127, 7121, 7109]) covered7104 (by decide +kernel) rfl

lemma covered7232 : primeList 7232 = primes7229 :=
  coverStep (d := 64) (added := [7229, 7219, 7213, 7211, 7207, 7193, 7187, 7177]) covered7168 (by decide +kernel) rfl

lemma covered7296 : primeList 7296 = primes7283 :=
  coverStep (d := 64) (added := [7283, 7253, 7247, 7243, 7237]) covered7232 (by decide +kernel) rfl

lemma covered7360 : primeList 7360 = primes7351 :=
  coverStep (d := 64) (added := [7351, 7349, 7333, 7331, 7321, 7309, 7307, 7297]) covered7296 (by decide +kernel) rfl

lemma covered7424 : primeList 7424 = primes7417 :=
  coverStep (d := 64) (added := [7417, 7411, 7393, 7369]) covered7360 (by decide +kernel) rfl

lemma covered7488 : primeList 7488 = primes7487 :=
  coverStep (d := 64) (added := [7487, 7481, 7477, 7459, 7457, 7451, 7433]) covered7424 (by decide +kernel) rfl

lemma covered7552 : primeList 7552 = primes7549 :=
  coverStep (d := 64) (added := [7549, 7547, 7541, 7537, 7529, 7523, 7517, 7507, 7499, 7489]) covered7488 (by decide +kernel) rfl

lemma covered7616 : primeList 7616 = primes7607 :=
  coverStep (d := 64) (added := [7607, 7603, 7591, 7589, 7583, 7577, 7573, 7561, 7559]) covered7552 (by decide +kernel) rfl

lemma covered7680 : primeList 7680 = primes7673 :=
  coverStep (d := 64) (added := [7673, 7669, 7649, 7643, 7639, 7621]) covered7616 (by decide +kernel) rfl

lemma covered7744 : primeList 7744 = primes7741 :=
  coverStep (d := 64) (added := [7741, 7727, 7723, 7717, 7703, 7699, 7691, 7687, 7681]) covered7680 (by decide +kernel) rfl

lemma covered7808 : primeList 7808 = primes7793 :=
  coverStep (d := 64) (added := [7793, 7789, 7759, 7757, 7753]) covered7744 (by decide +kernel) rfl

lemma covered7872 : primeList 7872 = primes7867 :=
  coverStep (d := 64) (added := [7867, 7853, 7841, 7829, 7823, 7817]) covered7808 (by decide +kernel) rfl

lemma covered7936 : primeList 7936 = primes7933 :=
  coverStep (d := 64) (added := [7933, 7927, 7919, 7907, 7901, 7883, 7879, 7877, 7873]) covered7872 (by decide +kernel) rfl

lemma covered8000 : primeList 8000 = primes7993 :=
  coverStep (d := 64) (added := [7993, 7963, 7951, 7949, 7937]) covered7936 (by decide +kernel) rfl

lemma covered8064 : primeList 8064 = primes8059 :=
  coverStep (d := 64) (added := [8059, 8053, 8039, 8017, 8011, 8009]) covered8000 (by decide +kernel) rfl

lemma covered8128 : primeList 8128 = primes8123 :=
  coverStep (d := 64) (added := [8123, 8117, 8111, 8101, 8093, 8089, 8087, 8081, 8069]) covered8064 (by decide +kernel) rfl

lemma covered8192 : primeList 8192 = primes8191 :=
  coverStep (d := 64) (added := [8191, 8179, 8171, 8167, 8161, 8147]) covered8128 (by decide +kernel) rfl

lemma covered8256 : primeList 8256 = primes8243 :=
  coverStep (d := 64) (added := [8243, 8237, 8233, 8231, 8221, 8219, 8209]) covered8192 (by decide +kernel) rfl

lemma covered8320 : primeList 8320 = primes8317 :=
  coverStep (d := 64) (added := [8317, 8311, 8297, 8293, 8291, 8287, 8273, 8269, 8263]) covered8256 (by decide +kernel) rfl

lemma covered8384 : primeList 8384 = primes8377 :=
  coverStep (d := 64) (added := [8377, 8369, 8363, 8353, 8329]) covered8320 (by decide +kernel) rfl

lemma covered8448 : primeList 8448 = primes8447 :=
  coverStep (d := 64) (added := [8447, 8443, 8431, 8429, 8423, 8419, 8389, 8387]) covered8384 (by decide +kernel) rfl

lemma covered8512 : primeList 8512 = primes8501 :=
  coverStep (d := 64) (added := [8501, 8467, 8461]) covered8448 (by decide +kernel) rfl

lemma covered8576 : primeList 8576 = primes8573 :=
  coverStep (d := 64) (added := [8573, 8563, 8543, 8539, 8537, 8527, 8521, 8513]) covered8512 (by decide +kernel) rfl

lemma covered8640 : primeList 8640 = primes8629 :=
  coverStep (d := 64) (added := [8629, 8627, 8623, 8609, 8599, 8597, 8581]) covered8576 (by decide +kernel) rfl

lemma covered8704 : primeList 8704 = primes8699 :=
  coverStep (d := 64) (added := [8699, 8693, 8689, 8681, 8677, 8669, 8663, 8647, 8641]) covered8640 (by decide +kernel) rfl

lemma covered8768 : primeList 8768 = primes8761 :=
  coverStep (d := 64) (added := [8761, 8753, 8747, 8741, 8737, 8731, 8719, 8713, 8707]) covered8704 (by decide +kernel) rfl

lemma covered8832 : primeList 8832 = primes8831 :=
  coverStep (d := 64) (added := [8831, 8821, 8819, 8807, 8803, 8783, 8779]) covered8768 (by decide +kernel) rfl

lemma covered8896 : primeList 8896 = primes8893 :=
  coverStep (d := 64) (added := [8893, 8887, 8867, 8863, 8861, 8849, 8839, 8837]) covered8832 (by decide +kernel) rfl

lemma covered8960 : primeList 8960 = primes8951 :=
  coverStep (d := 64) (added := [8951, 8941, 8933, 8929, 8923]) covered8896 (by decide +kernel) rfl

lemma covered9024 : primeList 9024 = primes9013 :=
  coverStep (d := 64) (added := [9013, 9011, 9007, 9001, 8999, 8971, 8969, 8963]) covered8960 (by decide +kernel) rfl

lemma covered9088 : primeList 9088 = primes9067 :=
  coverStep (d := 64) (added := [9067, 9059, 9049, 9043, 9041, 9029]) covered9024 (by decide +kernel) rfl

lemma covered9152 : primeList 9152 = primes9151 :=
  coverStep (d := 64) (added := [9151, 9137, 9133, 9127, 9109, 9103, 9091]) covered9088 (by decide +kernel) rfl

lemma covered9216 : primeList 9216 = primes9209 :=
  coverStep (d := 64) (added := [9209, 9203, 9199, 9187, 9181, 9173, 9161, 9157]) covered9152 (by decide +kernel) rfl

lemma covered9280 : primeList 9280 = primes9277 :=
  coverStep (d := 64) (added := [9277, 9257, 9241, 9239, 9227, 9221]) covered9216 (by decide +kernel) rfl

lemma covered9344 : primeList 9344 = primes9343 :=
  coverStep (d := 64) (added := [9343, 9341, 9337, 9323, 9319, 9311, 9293, 9283, 9281]) covered9280 (by decide +kernel) rfl

lemma covered9408 : primeList 9408 = primes9403 :=
  coverStep (d := 64) (added := [9403, 9397, 9391, 9377, 9371, 9349]) covered9344 (by decide +kernel) rfl

lemma covered9472 : primeList 9472 = primes9467 :=
  coverStep (d := 64) (added := [9467, 9463, 9461, 9439, 9437, 9433, 9431, 9421, 9419, 9413]) covered9408 (by decide +kernel) rfl

lemma covered9486 : primeList 9486 = primes9479 :=
  coverStep (d := 14) (added := [9479, 9473]) covered9472 (by decide +kernel) rfl

end PrimeCountCertificate
open PrimeCountCertificate

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem OMA.solution : OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1.H3 := by
  change 5216100 ≤ Nat.primeCounting 90000000
  have h := certified_lower (k := 9486) (n := 90000000) (by decide) (by decide)
  rw [← length_primeList, covered9486, count9479] at h
  have hc : primes9479.length = 1175 := by rfl
  rw [hc] at h
  omega

