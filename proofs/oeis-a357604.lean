import OMAStatements.S_oeis_a357604

namespace OMA.A357604
open OMA.S_oeis_a357604

/-- The summand changes precisely when the denominator divides the new index. -/
private theorem drop_eq (m : ℕ) (hm : 0 < m) :
    a (m - 1) - a m =
      ∑ d ∈ m.divisors, (indicator (d - 1) - indicator d) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [Nat.add_one_sub_one]
  have hzero : indicator 0 = 0 := by simp [indicator, not_isPrimePow_zero]
  have extend : a t = ∑ k ∈ Finset.range (t + 1 + 1), indicator (t / k) := by
    simp [a, Finset.sum_range_succ, Nat.div_eq_of_lt (Nat.lt_succ_self t), hzero]
  rw [extend, a, ← Finset.sum_sub_distrib, ← Nat.sum_div_divisors (t+1)
    (fun d => indicator (d-1) - indicator d), ← Nat.filter_dvd_eq_divisors (by omega),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with h
  · rw [Nat.succ_div_of_dvd h]
    simp
  · rw [Nat.succ_div_of_not_dvd h, sub_self]

private def radius (m : ℕ) : ℕ := if m ≤ 327600 then 573 else m.sqrt

private theorem sqrt_bound (m : ℕ) : m.sqrt ≤ radius m := by
  unfold radius
  split <;> try rfl
  have hu := Nat.sqrt_le m
  by_contra! h
  have bound := Nat.mul_le_mul (show 574 ≤ m.sqrt by omega) (show 574 ≤ m.sqrt by omega)
  omega

/-- A loop with explicit fuel gives the usual least prime factor by kernel reduction. -/
private def trial (n k fuel : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => n)
    (fun _ prev d => if n < d*d then n else if d ∣ n then d else prev (d+2)) fuel k

private theorem trial_eq (n k fuel : ℕ) (hk : 3 ≤ k) (hc : n.sqrt < k+fuel) :
    trial n k fuel = Nat.minFacAux n k := by
  induction fuel generalizing k with
  | zero =>
    have hlt : n < k*k := (Nat.lt_succ_sqrt n).trans_le
      (Nat.mul_le_mul (by omega) (by omega))
    rw [Nat.minFacAux, if_pos hlt]
    rfl
  | succ fuel ih =>
    change (if n < k*k then n else if k ∣ n then k else trial n (k+2) fuel) = _
    rw [Nat.minFacAux]
    split
    · rfl
    · split
      · rfl
      · exact ih (k+2) (by omega) (by omega)

private def firstFactor (n : ℕ) : ℕ := if 2 ∣ n then 2 else trial n 3 (radius n)

private theorem firstFactor_eq (n : ℕ) : firstFactor n = n.minFac := by
  have h := sqrt_bound n
  rw [firstFactor, Nat.minFac_eq, trial_eq n 3 (radius n) (by decide) (by omega)]

private def powerTest (n : ℕ) : Bool :=
  (List.range (n.log2 + 1)).any (fun k => decide (0 < k ∧ n = (firstFactor n)^k))

private theorem powerTest_iff (n : ℕ) : powerTest n = true ↔ IsPrimePow n := by
  simp [powerTest, isPrimePow_nat_iff_bounded_log_minFac, firstFactor_eq,
    Nat.log2_eq_log_two]

private def weight (q : ℕ) : ℤ :=
  (if powerTest (q-1) then 1 else 0) - (if powerTest q then 1 else 0)


-- The repeated divisors share weights. Each cached value is separately
-- certified by the arithmetic test, and lookup defaults to direct evaluation.
private inductive WeightTree where
  | leaf
  | node (key : ℕ) (value : ℤ) (left right : WeightTree)

private def lookupWeight (d : ℕ) : WeightTree → ℤ
  | .leaf => weight d
  | .node key value left right =>
    if d = key then value else if d < key then lookupWeight d left else lookupWeight d right

private def treeOK : WeightTree → Bool
  | .leaf => true
  | .node key value left right => decide (weight key = value) && treeOK left && treeOK right

private theorem lookupWeight_eq (d : ℕ) (t : WeightTree) (h : treeOK t = true) :
    lookupWeight d t = weight d := by
  induction t with
  | leaf => rfl
  | node key value left right ihl ihr =>
    simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [lookupWeight]
    split
    · rename_i heq
      subst d
      exact h.1.1.symm
    · split
      · exact ihl h.1.2
      · exact ihr h.2

private def cache : WeightTree :=
  (.node 4725 0
    (.node 810 1
      (.node 220 0
        (.node 75 0
          (.node 28 1
            (.node 13 (-1)
              (.node 7 (-1)
                (.node 4 0 (.node 2 (-1) (.node 1 0 .leaf .leaf) (.node 3 0 .leaf .leaf)) (.node 6 1 (.node 5 0 .leaf .leaf) .leaf))
                (.node 10 1 (.node 9 0 (.node 8 0 .leaf .leaf) .leaf) (.node 12 1 (.node 11 (-1) .leaf .leaf) .leaf)))
              (.node 21 0
                (.node 16 (-1) (.node 15 0 (.node 14 1 .leaf .leaf) .leaf) (.node 20 1 (.node 18 1 .leaf .leaf) .leaf))
                (.node 25 (-1) (.node 24 1 (.node 22 0 .leaf .leaf) .leaf) (.node 27 (-1) (.node 26 1 .leaf .leaf) .leaf))))
            (.node 50 1
              (.node 40 0
                (.node 35 0 (.node 32 0 (.node 30 1 .leaf .leaf) (.node 33 1 .leaf .leaf)) (.node 39 0 (.node 36 0 .leaf .leaf) .leaf))
                (.node 45 0 (.node 44 1 (.node 42 1 .leaf .leaf) .leaf) (.node 49 (-1) (.node 48 1 .leaf .leaf) .leaf)))
              (.node 63 0
                (.node 55 0 (.node 54 1 (.node 52 0 .leaf .leaf) .leaf) (.node 60 1 (.node 56 0 .leaf .leaf) .leaf))
                (.node 66 0 (.node 65 1 (.node 64 (-1) .leaf .leaf) .leaf) (.node 72 1 (.node 70 0 .leaf .leaf) .leaf)))))
          (.node 135 0
            (.node 104 1
              (.node 90 1
                (.node 81 (-1) (.node 78 0 (.node 77 0 .leaf .leaf) (.node 80 1 .leaf .leaf)) (.node 88 0 (.node 84 1 .leaf .leaf) .leaf))
                (.node 98 1 (.node 96 0 (.node 91 0 .leaf .leaf) .leaf) (.node 100 0 (.node 99 0 .leaf .leaf) .leaf)))
              (.node 120 0
                (.node 110 1 (.node 108 1 (.node 105 0 .leaf .leaf) .leaf) (.node 117 0 (.node 112 0 .leaf .leaf) .leaf))
                (.node 128 0 (.node 126 1 (.node 125 (-1) .leaf .leaf) .leaf) (.node 132 1 (.node 130 0 .leaf .leaf) .leaf))))
            (.node 176 0
              (.node 156 0
                (.node 147 0 (.node 143 0 (.node 140 1 .leaf .leaf) (.node 144 0 .leaf .leaf)) (.node 154 0 (.node 150 1 .leaf .leaf) .leaf))
                (.node 165 0 (.node 162 0 (.node 160 0 .leaf .leaf) .leaf) (.node 175 0 (.node 168 1 .leaf .leaf) .leaf)))
              (.node 196 0
                (.node 189 0 (.node 182 1 (.node 180 1 .leaf .leaf) .leaf) (.node 195 0 (.node 192 1 .leaf .leaf) .leaf))
                (.node 208 0 (.node 200 1 (.node 198 1 .leaf .leaf) .leaf) (.node 216 0 (.node 210 0 .leaf .leaf) .leaf))))))
        (.node 455 0
          (.node 320 0
            (.node 270 1
              (.node 245 0
                (.node 234 1 (.node 225 0 (.node 224 1 .leaf .leaf) (.node 231 0 .leaf .leaf)) (.node 243 (-1) (.node 240 1 .leaf .leaf) .leaf))
                (.node 256 (-1) (.node 252 1 (.node 250 0 .leaf .leaf) .leaf) (.node 264 1 (.node 260 0 .leaf .leaf) .leaf)))
              (.node 294 1
                (.node 280 0 (.node 275 0 (.node 273 0 .leaf .leaf) .leaf) (.node 288 0 (.node 286 0 .leaf .leaf) .leaf))
                (.node 308 1 (.node 300 0 (.node 297 0 .leaf .leaf) .leaf) (.node 315 0 (.node 312 1 .leaf .leaf) .leaf))))
            (.node 390 1
              (.node 360 1
                (.node 336 0 (.node 325 0 (.node 324 0 .leaf .leaf) (.node 330 0 .leaf .leaf)) (.node 352 0 (.node 350 1 .leaf .leaf) .leaf))
                (.node 378 0 (.node 375 0 (.node 364 0 .leaf .leaf) .leaf) (.node 385 0 (.node 384 1 .leaf .leaf) .leaf)))
              (.node 429 0
                (.node 400 0 (.node 396 0 (.node 392 0 .leaf .leaf) .leaf) (.node 420 1 (.node 405 0 .leaf .leaf) .leaf))
                (.node 441 0 (.node 440 1 (.node 432 1 .leaf .leaf) .leaf) (.node 450 1 (.node 448 0 .leaf .leaf) .leaf)))))
          (.node 624 0
            (.node 540 0
              (.node 500 1
                (.node 486 0 (.node 468 1 (.node 462 1 .leaf .leaf) (.node 480 1 .leaf .leaf)) (.node 495 0 (.node 490 0 .leaf .leaf) .leaf))
                (.node 520 0 (.node 512 (-1) (.node 504 1 .leaf .leaf) .leaf) (.node 528 0 (.node 525 0 .leaf .leaf) .leaf)))
              (.node 576 0
                (.node 560 0 (.node 550 0 (.node 546 0 .leaf .leaf) .leaf) (.node 572 1 (.node 567 0 .leaf .leaf) .leaf))
                (.node 594 1 (.node 588 1 (.node 585 0 .leaf .leaf) .leaf) (.node 616 0 (.node 600 1 .leaf .leaf) .leaf))))
            (.node 720 1
              (.node 672 0
                (.node 648 1 (.node 640 0 (.node 630 0 .leaf .leaf) .leaf) (.node 660 1 (.node 650 0 .leaf .leaf) .leaf))
                (.node 700 0 (.node 693 0 (.node 675 0 .leaf .leaf) .leaf) (.node 715 0 (.node 704 0 .leaf .leaf) .leaf)))
              (.node 768 0
                (.node 735 0 (.node 729 (-1) (.node 728 1 .leaf .leaf) .leaf) (.node 756 0 (.node 750 0 .leaf .leaf) .leaf))
                (.node 784 0 (.node 780 0 (.node 770 1 .leaf .leaf) .leaf) (.node 800 0 (.node 792 0 .leaf .leaf) .leaf)))))))
      (.node 2112 1
        (.node 1344 0
          (.node 1050 1
            (.node 936 0
              (.node 880 0
                (.node 858 1 (.node 825 0 (.node 819 0 .leaf .leaf) (.node 840 1 .leaf .leaf)) (.node 875 0 (.node 864 1 .leaf .leaf) .leaf))
                (.node 900 0 (.node 896 0 (.node 882 1 .leaf .leaf) .leaf) (.node 924 0 (.node 910 0 .leaf .leaf) .leaf)))
              (.node 990 0
                (.node 972 1 (.node 960 0 (.node 945 0 .leaf .leaf) .leaf) (.node 980 0 (.node 975 0 .leaf .leaf) .leaf))
                (.node 1008 0 (.node 1001 0 (.node 1000 0 .leaf .leaf) .leaf) (.node 1040 1 (.node 1024 (-1) .leaf .leaf) .leaf))))
            (.node 1188 1
              (.node 1134 0
                (.node 1100 0 (.node 1080 0 (.node 1056 0 .leaf .leaf) (.node 1092 1 .leaf .leaf)) (.node 1125 0 (.node 1120 0 .leaf .leaf) .leaf))
                (.node 1155 0 (.node 1152 1 (.node 1144 0 .leaf .leaf) .leaf) (.node 1176 0 (.node 1170 0 .leaf .leaf) .leaf)))
              (.node 1280 1
                (.node 1225 0 (.node 1215 0 (.node 1200 0 .leaf .leaf) .leaf) (.node 1260 1 (.node 1232 1 .leaf .leaf) .leaf))
                (.node 1300 0 (.node 1296 0 (.node 1287 0 .leaf .leaf) .leaf) (.node 1323 0 (.node 1320 1 .leaf .leaf) .leaf)))))
          (.node 1716 0
            (.node 1512 1
              (.node 1440 1
                (.node 1400 1 (.node 1365 0 (.node 1350 0 .leaf .leaf) (.node 1386 0 .leaf .leaf)) (.node 1430 1 (.node 1408 0 .leaf .leaf) .leaf))
                (.node 1470 0 (.node 1458 0 (.node 1456 0 .leaf .leaf) .leaf) (.node 1500 1 (.node 1485 0 .leaf .leaf) .leaf)))
              (.node 1600 0
                (.node 1560 1 (.node 1540 0 (.node 1536 0 .leaf .leaf) .leaf) (.node 1584 1 (.node 1575 0 .leaf .leaf) .leaf))
                (.node 1650 0 (.node 1638 1 (.node 1620 1 .leaf .leaf) .leaf) (.node 1701 0 (.node 1680 0 .leaf .leaf) .leaf))))
            (.node 1925 0
              (.node 1800 0
                (.node 1760 1 (.node 1750 0 (.node 1728 0 .leaf .leaf) .leaf) (.node 1792 0 (.node 1764 0 .leaf .leaf) .leaf))
                (.node 1872 1 (.node 1848 1 (.node 1820 0 .leaf .leaf) .leaf) (.node 1920 0 (.node 1890 1 .leaf .leaf) .leaf)))
              (.node 2002 0
                (.node 1960 0 (.node 1950 1 (.node 1944 0 .leaf .leaf) .leaf) (.node 2000 1 (.node 1980 1 .leaf .leaf) .leaf))
                (.node 2048 (-1) (.node 2025 0 (.node 2016 0 .leaf .leaf) .leaf) (.node 2100 1 (.node 2079 0 .leaf .leaf) .leaf))))))
        (.node 3168 1
          (.node 2592 1
            (.node 2310 1
              (.node 2240 1
                (.node 2187 (-1) (.node 2160 0 (.node 2145 0 .leaf .leaf) (.node 2184 0 .leaf .leaf)) (.node 2205 0 (.node 2200 0 .leaf .leaf) .leaf))
                (.node 2275 0 (.node 2268 1 (.node 2250 0 .leaf .leaf) .leaf) (.node 2304 0 (.node 2288 1 .leaf .leaf) .leaf)))
              (.node 2450 0
                (.node 2376 0 (.node 2352 1 (.node 2340 1 .leaf .leaf) .leaf) (.node 2430 0 (.node 2400 1 .leaf .leaf) .leaf))
                (.node 2520 0 (.node 2475 0 (.node 2464 0 .leaf .leaf) .leaf) (.node 2574 0 (.node 2560 0 .leaf .leaf) .leaf))))
            (.node 2880 1
              (.node 2730 1
                (.node 2646 0 (.node 2625 0 (.node 2600 0 .leaf .leaf) (.node 2640 0 .leaf .leaf)) (.node 2700 1 (.node 2688 1 .leaf .leaf) .leaf))
                (.node 2816 0 (.node 2800 0 (.node 2772 0 .leaf .leaf) .leaf) (.node 2860 0 (.node 2835 0 .leaf .leaf) .leaf)))
              (.node 3003 0
                (.node 2940 1 (.node 2925 0 (.node 2916 0 .leaf .leaf) .leaf) (.node 3000 1 (.node 2970 1 .leaf .leaf) .leaf))
                (.node 3080 1 (.node 3072 0 (.node 3024 1 .leaf .leaf) .leaf) (.node 3150 0 (.node 3120 1 .leaf .leaf) .leaf)))))
          (.node 3920 1
            (.node 3528 1
              (.node 3402 0
                (.node 3300 1 (.node 3240 0 (.node 3200 0 .leaf .leaf) (.node 3276 0 .leaf .leaf)) (.node 3375 0 (.node 3360 1 .leaf .leaf) .leaf))
                (.node 3465 0 (.node 3456 0 (.node 3432 0 .leaf .leaf) .leaf) (.node 3520 0 (.node 3500 1 .leaf .leaf) .leaf)))
              (.node 3696 0
                (.node 3640 0 (.node 3600 0 (.node 3584 1 .leaf .leaf) .leaf) (.node 3675 0 (.node 3645 0 .leaf .leaf) .leaf))
                (.node 3850 0 (.node 3840 0 (.node 3780 1 .leaf .leaf) .leaf) (.node 3900 0 (.node 3888 0 .leaf .leaf) .leaf))))
            (.node 4320 0
              (.node 4095 0
                (.node 4004 1 (.node 4000 0 (.node 3960 0 .leaf .leaf) .leaf) (.node 4050 1 (.node 4032 0 .leaf .leaf) .leaf))
                (.node 4200 0 (.node 4158 1 (.node 4096 (-1) .leaf .leaf) .leaf) (.node 4290 1 (.node 4224 0 .leaf .leaf) .leaf)))
              (.node 4500 0
                (.node 4400 0 (.node 4374 1 (.node 4368 0 .leaf .leaf) .leaf) (.node 4480 0 (.node 4410 1 .leaf .leaf) .leaf))
                (.node 4608 0 (.node 4550 1 (.node 4536 0 .leaf .leaf) .leaf) (.node 4680 1 (.node 4620 0 .leaf .leaf) .leaf))))))))
    (.node 23760 0
      (.node 10395 0
        (.node 7000 0
          (.node 5832 0
            (.node 5250 0
              (.node 5005 0
                (.node 4900 0 (.node 4800 1 (.node 4752 1 .leaf .leaf) (.node 4860 0 .leaf .leaf)) (.node 4950 0 (.node 4928 0 .leaf .leaf) .leaf))
                (.node 5148 1 (.node 5120 1 (.node 5040 1 .leaf .leaf) .leaf) (.node 5200 0 (.node 5184 0 .leaf .leaf) .leaf)))
              (.node 5544 0
                (.node 5376 0 (.node 5292 0 (.node 5280 1 .leaf .leaf) .leaf) (.node 5460 0 (.node 5400 1 .leaf .leaf) .leaf))
                (.node 5720 0 (.node 5670 1 (.node 5600 0 .leaf .leaf) .leaf) (.node 5775 0 (.node 5760 0 .leaf .leaf) .leaf))))
            (.node 6435 0
              (.node 6075 0
                (.node 6000 0 (.node 5880 1 (.node 5850 1 .leaf .leaf) (.node 5940 1 .leaf .leaf)) (.node 6048 1 (.node 6006 0 .leaf .leaf) .leaf))
                (.node 6300 1 (.node 6160 0 (.node 6144 1 .leaf .leaf) .leaf) (.node 6400 0 (.node 6336 0 .leaf .leaf) .leaf)))
              (.node 6750 0
                (.node 6600 1 (.node 6552 1 (.node 6480 0 .leaf .leaf) .leaf) (.node 6720 1 (.node 6615 0 .leaf .leaf) .leaf))
                (.node 6864 1 (.node 6825 0 (.node 6804 1 .leaf .leaf) .leaf) (.node 6930 0 (.node 6912 1 .leaf .leaf) .leaf)))))
          (.node 8505 0
            (.node 7800 0
              (.node 7350 1
                (.node 7200 0 (.node 7056 0 (.node 7040 1 .leaf .leaf) (.node 7168 0 .leaf .leaf)) (.node 7290 0 (.node 7280 0 .leaf .leaf) .leaf))
                (.node 7680 0 (.node 7560 1 (.node 7392 0 .leaf .leaf) .leaf) (.node 7776 0 (.node 7700 1 .leaf .leaf) .leaf)))
              (.node 8100 0
                (.node 8000 0 (.node 7920 1 (.node 7875 0 .leaf .leaf) .leaf) (.node 8064 0 (.node 8008 0 .leaf .leaf) .leaf))
                (.node 8316 0 (.node 8192 0 (.node 8190 0 .leaf .leaf) .leaf) (.node 8448 1 (.node 8400 0 .leaf .leaf) .leaf))))
            (.node 9360 0
              (.node 9000 1
                (.node 8748 1 (.node 8640 0 (.node 8580 0 .leaf .leaf) .leaf) (.node 8960 0 (.node 8820 1 .leaf .leaf) .leaf))
                (.node 9100 0 (.node 9072 0 (.node 9009 0 .leaf .leaf) .leaf) (.node 9240 1 (.node 9216 0 .leaf .leaf) .leaf)))
              (.node 9900 0
                (.node 9720 1 (.node 9600 0 (.node 9450 0 .leaf .leaf) .leaf) (.node 9856 0 (.node 9800 0 .leaf .leaf) .leaf))
                (.node 10125 0 (.node 10080 1 (.node 10010 1 .leaf .leaf) .leaf) (.node 10368 0 (.node 10240 0 .leaf .leaf) .leaf))))))
        (.node 15750 1
          (.node 12800 1
            (.node 11550 1
              (.node 11025 0
                (.node 10752 0 (.node 10560 1 (.node 10500 1 .leaf .leaf) (.node 10584 0 .leaf .leaf)) (.node 10920 0 (.node 10800 1 .leaf .leaf) .leaf))
                (.node 11340 0 (.node 11200 0 (.node 11088 1 .leaf .leaf) .leaf) (.node 11520 1 (.node 11440 0 .leaf .leaf) .leaf)))
              (.node 12012 1
                (.node 11760 0 (.node 11700 1 (.node 11664 0 .leaf .leaf) .leaf) (.node 12000 0 (.node 11880 0 .leaf .leaf) .leaf))
                (.node 12288 0 (.node 12150 1 (.node 12096 0 .leaf .leaf) .leaf) (.node 12600 0 (.node 12320 0 .leaf .leaf) .leaf))))
            (.node 14175 0
              (.node 13500 1
                (.node 13200 0 (.node 12960 1 (.node 12870 0 .leaf .leaf) (.node 13104 1 .leaf .leaf)) (.node 13440 0 (.node 13230 1 .leaf .leaf) .leaf))
                (.node 13824 0 (.node 13650 1 (.node 13608 0 .leaf .leaf) .leaf) (.node 14080 0 (.node 13860 1 .leaf .leaf) .leaf)))
              (.node 15015 0
                (.node 14580 0 (.node 14400 0 (.node 14336 0 .leaf .leaf) .leaf) (.node 14784 1 (.node 14700 1 .leaf .leaf) .leaf))
                (.node 15400 0 (.node 15360 1 (.node 15120 0 .leaf .leaf) .leaf) (.node 15600 0 (.node 15552 1 .leaf .leaf) .leaf)))))
          (.node 19600 0
            (.node 17496 0
              (.node 16632 1
                (.node 16200 0 (.node 16016 0 (.node 15840 0 .leaf .leaf) (.node 16128 1 .leaf .leaf)) (.node 16384 (-1) (.node 16380 0 .leaf .leaf) .leaf))
                (.node 17160 1 (.node 17010 0 (.node 16800 0 .leaf .leaf) .leaf) (.node 17325 0 (.node 17280 0 .leaf .leaf) .leaf)))
              (.node 18200 1
                (.node 18000 0 (.node 17920 0 (.node 17640 0 .leaf .leaf) .leaf) (.node 18144 1 (.node 18018 0 .leaf .leaf) .leaf))
                (.node 18900 1 (.node 18480 0 (.node 18432 0 .leaf .leaf) .leaf) (.node 19440 0 (.node 19200 0 .leaf .leaf) .leaf))))
            (.node 21504 1
              (.node 20475 0
                (.node 20020 0 (.node 19800 0 (.node 19712 0 .leaf .leaf) .leaf) (.node 20250 1 (.node 20160 0 .leaf .leaf) .leaf))
                (.node 20790 1 (.node 20736 0 (.node 20480 1 .leaf .leaf) .leaf) (.node 21120 0 (.node 21000 0 .leaf .leaf) .leaf)))
              (.node 22680 1
                (.node 22050 0 (.node 21840 1 (.node 21600 1 .leaf .leaf) .leaf) (.node 22400 0 (.node 22176 0 .leaf .leaf) .leaf))
                (.node 23328 1 (.node 23100 1 (.node 23040 1 .leaf .leaf) .leaf) (.node 23625 0 (.node 23400 1 .leaf .leaf) .leaf)))))))
      (.node 65520 1
        (.node 37800 1
          (.node 30720 0
            (.node 27000 0
              (.node 25200 0
                (.node 24300 0 (.node 24024 1 (.node 24000 0 .leaf .leaf) (.node 24192 0 .leaf .leaf)) (.node 24640 0 (.node 24576 0 .leaf .leaf) .leaf))
                (.node 25920 1 (.node 25740 0 (.node 25600 0 .leaf .leaf) .leaf) (.node 26880 1 (.node 26460 1 .leaf .leaf) .leaf)))
              (.node 28800 0
                (.node 27648 1 (.node 27300 1 (.node 27216 0 .leaf .leaf) .leaf) (.node 28350 1 (.node 27720 0 .leaf .leaf) .leaf))
                (.node 29568 1 (.node 29400 1 (.node 29160 0 .leaf .leaf) .leaf) (.node 30240 0 (.node 30030 1 .leaf .leaf) .leaf))))
            (.node 34320 1
              (.node 32760 0
                (.node 31680 0 (.node 31104 0 (.node 30800 0 .leaf .leaf) (.node 31500 0 .leaf .leaf)) (.node 32400 0 (.node 32256 0 .leaf .leaf) .leaf))
                (.node 33264 0 (.node 33075 0 (.node 32768 (-1) .leaf .leaf) .leaf) (.node 34020 1 (.node 33600 1 .leaf .leaf) .leaf)))
              (.node 36000 1
                (.node 34992 0 (.node 34650 1 (.node 34560 0 .leaf .leaf) .leaf) (.node 35840 1 (.node 35280 1 .leaf .leaf) .leaf))
                (.node 36400 0 (.node 36288 0 (.node 36036 0 .leaf .leaf) .leaf) (.node 36960 0 (.node 36864 0 .leaf .leaf) .leaf)))))
          (.node 48600 0
            (.node 43200 0
              (.node 40950 1
                (.node 40040 1 (.node 38880 0 (.node 38400 0 .leaf .leaf) (.node 39600 0 .leaf .leaf)) (.node 40500 1 (.node 40320 0 .leaf .leaf) .leaf))
                (.node 41580 1 (.node 41472 0 (.node 40960 0 .leaf .leaf) .leaf) (.node 43008 0 (.node 42240 1 .leaf .leaf) .leaf)))
              (.node 46200 1
                (.node 45045 0 (.node 44352 1 (.node 44100 0 .leaf .leaf) .leaf) (.node 46080 0 (.node 45360 0 .leaf .leaf) .leaf))
                (.node 47250 0 (.node 46800 0 (.node 46656 0 .leaf .leaf) .leaf) (.node 48384 1 (.node 48048 0 .leaf .leaf) .leaf))))
            (.node 56700 0
              (.node 53760 1
                (.node 50400 0 (.node 49280 1 (.node 49152 0 .leaf .leaf) .leaf) (.node 52920 1 (.node 51840 1 .leaf .leaf) .leaf))
                (.node 54600 0 (.node 54432 0 (.node 54000 0 .leaf .leaf) .leaf) (.node 55440 1 (.node 55296 0 .leaf .leaf) .leaf)))
              (.node 60480 0
                (.node 58800 0 (.node 58320 0 (.node 57600 0 .leaf .leaf) .leaf) (.node 60060 0 (.node 59136 0 .leaf .leaf) .leaf))
                (.node 63000 0 (.node 62208 1 (.node 61440 0 .leaf .leaf) .leaf) (.node 64800 0 (.node 64512 0 .leaf .leaf) .leaf))))))
        (.node 136080 0
          (.node 90720 0
            (.node 76800 0
              (.node 69984 0
                (.node 68040 0 (.node 66150 0 (.node 65536 (-1) .leaf .leaf) (.node 67200 0 .leaf .leaf)) (.node 69300 0 (.node 69120 1 .leaf .leaf) .leaf))
                (.node 73728 1 (.node 72000 1 (.node 71680 0 .leaf .leaf) .leaf) (.node 75600 0 (.node 73920 0 .leaf .leaf) .leaf)))
              (.node 81920 1
                (.node 80640 0 (.node 80080 0 (.node 77760 0 .leaf .leaf) .leaf) (.node 81900 1 (.node 81000 0 .leaf .leaf) .leaf))
                (.node 86400 1 (.node 83160 0 (.node 82944 0 .leaf .leaf) .leaf) (.node 90090 1 (.node 88200 0 .leaf .leaf) .leaf))))
            (.node 110592 0
              (.node 98560 0
                (.node 94500 0 (.node 92400 1 (.node 92160 0 .leaf .leaf) (.node 93312 0 .leaf .leaf)) (.node 98304 0 (.node 97200 0 .leaf .leaf) .leaf))
                (.node 107520 0 (.node 103680 0 (.node 100800 1 .leaf .leaf) .leaf) (.node 109200 1 (.node 108000 1 .leaf .leaf) .leaf)))
              (.node 120960 0
                (.node 115200 0 (.node 113400 0 (.node 110880 1 .leaf .leaf) .leaf) (.node 120120 0 (.node 116640 1 .leaf .leaf) .leaf))
                (.node 129600 0 (.node 124416 0 (.node 122880 0 .leaf .leaf) .leaf) (.node 132300 1 (.node 131072 0 .leaf .leaf) .leaf)))))
          (.node 216000 0
            (.node 172800 0
              (.node 155520 0
                (.node 147456 0 (.node 138600 1 (.node 138240 1 .leaf .leaf) (.node 139968 1 .leaf .leaf)) (.node 151200 0 (.node 147840 0 .leaf .leaf) .leaf))
                (.node 163800 0 (.node 162000 1 (.node 161280 0 .leaf .leaf) .leaf) (.node 166320 1 (.node 165888 1 .leaf .leaf) .leaf)))
              (.node 189000 1
                (.node 181440 1 (.node 180180 1 (.node 176400 0 .leaf .leaf) .leaf) (.node 186624 0 (.node 184320 0 .leaf .leaf) .leaf))
                (.node 201600 1 (.node 196608 0 (.node 194400 0 .leaf .leaf) .leaf) (.node 215040 0 (.node 207360 0 .leaf .leaf) .leaf))))
            (.node 264600 1
              (.node 240240 0
                (.node 226800 1 (.node 221760 0 (.node 221184 0 .leaf .leaf) .leaf) (.node 233280 1 (.node 230400 0 .leaf .leaf) .leaf))
                (.node 248832 0 (.node 245760 1 (.node 241920 1 .leaf .leaf) .leaf) (.node 262144 (-1) (.node 259200 0 .leaf .leaf) .leaf)))
              (.node 295680 0
                (.node 277200 0 (.node 276480 0 (.node 272160 0 .leaf .leaf) .leaf) (.node 294912 1 (.node 279936 0 .leaf .leaf) .leaf))
                (.node 322560 1 (.node 311040 0 (.node 302400 1 .leaf .leaf) .leaf) (.node 327600 1 (.node 324000 0 .leaf .leaf) .leaf)))))))))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem cache_ok : treeOK cache = true := by decide +kernel

private def cachedWeight (d : ℕ) : ℤ := lookupWeight d cache
private theorem cachedWeight_eq (d : ℕ) : cachedWeight d = weight d :=
  lookupWeight_eq _ _ cache_ok

private def pairWeight (m d : ℕ) : ℤ :=
  cachedWeight d + (if d < m/d then cachedWeight (m/d) else 0)

private def pairedTerm (m d : ℕ) : ℤ :=
  if 0 < d ∧ d ∣ m ∧ d ≤ m/d then pairWeight m d else 0

private def pairSum (m k : ℕ) : ℤ :=
  Nat.rec 0 (fun d v => v + pairedTerm m d) k

private theorem pairSum_eq (m k : ℕ) : pairSum m k = ∑ d ∈ Finset.range k, pairedTerm m d := by
  induction k with
  | zero => simp [pairSum]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

private def dropValue (m : ℕ) : ℤ := pairSum m (radius m+1)

private theorem dropValue_eq (m : ℕ) (hm : 0 < m) :
    a (m-1) - a m = dropValue m := by
  rw [drop_eq m hm]
  let upper := fun d => if m/d < d then cachedWeight d else 0
  have splitSum : (∑ d ∈ m.divisors, (indicator (d-1)-indicator d)) =
      (∑ d ∈ m.divisors, if d ≤ m/d then cachedWeight d else 0) +
      ∑ d ∈ m.divisors, upper d := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [upper, cachedWeight_eq, weight, powerTest_iff, indicator]
    by_cases h : d ≤ m/d
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_ge h]
  rw [splitSum, ← Nat.sum_div_divisors m upper, ← Finset.sum_add_distrib]
  have rel : (∑ d ∈ m.divisors, ((if d ≤ m/d then cachedWeight d else 0) + upper (m/d))) =
      ∑ d ∈ m.divisors.filter (fun d => d ≤ m/d), pairWeight m d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    have dv := (Nat.mem_divisors.mp hd).1
    simp only [upper, Nat.div_div_self dv hm.ne', pairWeight]
    by_cases h : d ≤ m/d
    · simp [h]
    · simp [h, Nat.not_lt.mpr (by omega : m/d ≤ d)]
  rw [rel]
  have support : m.divisors.filter (fun d => d ≤ m/d) =
      (Finset.range (radius m+1)).filter (fun d => 0 < d ∧ d ∣ m ∧ d ≤ m/d) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_range]
    constructor
    · rintro ⟨⟨hd,_⟩,hle⟩
      have sq := (Nat.mul_le_mul_right d hle).trans (Nat.le_of_eq (Nat.div_mul_cancel hd))
      have hr := sqrt_bound m
      have hs := Nat.lt_succ_sqrt m
      have bound : d ≤ m.sqrt := by
        by_contra! hg
        have hh := Nat.mul_le_mul (show m.sqrt.succ ≤ d by omega) (show m.sqrt.succ ≤ d by omega)
        omega
      exact ⟨by omega, Nat.pos_of_dvd_of_pos hd hm, hd, hle⟩
    · rintro ⟨_,_,hd,hle⟩
      exact ⟨⟨hd,hm.ne'⟩,hle⟩
  rw [support, Finset.sum_filter, dropValue, pairSum_eq]
  rfl

-- Bounded certificate for the products of primorials. The closure check
-- proves exhaustiveness independently of how this list was generated.
private def candidates : List ℕ := [
  1, 2, 4, 6, 8, 12, 16, 24, 30, 32,
  36, 48, 60, 64, 72, 96, 120, 128, 144, 180,
  192, 210, 216, 240, 256, 288, 360, 384, 420, 432,
  480, 512, 576, 720, 768, 840, 864, 900, 960, 1024,
  1080, 1152, 1260, 1296, 1440, 1536, 1680, 1728, 1800, 1920,
  2048, 2160, 2304, 2310, 2520, 2592, 2880, 3072, 3360, 3456,
  3600, 3840, 4096, 4320, 4608, 4620, 5040, 5184, 5400, 5760,
  6144, 6300, 6480, 6720, 6912, 7200, 7560, 7680, 7776, 8192,
  8640, 9216, 9240, 10080, 10368, 10800, 11520, 12288, 12600, 12960,
  13440, 13824, 13860, 14400, 15120, 15360, 15552, 16384, 17280, 18432,
  18480, 20160, 20736, 21600, 23040, 24576, 25200, 25920, 26880, 27000,
  27648, 27720, 28800, 30030, 30240, 30720, 31104, 32400, 32768, 34560,
  36864, 36960, 37800, 38880, 40320, 41472, 43200, 44100, 45360, 46080,
  46656, 49152, 50400, 51840, 53760, 54000, 55296, 55440, 57600, 60060,
  60480, 61440, 62208, 64800, 65536, 69120, 69300, 73728, 73920, 75600,
  77760, 80640, 82944, 83160, 86400, 88200, 90720, 92160, 93312, 98304,
  100800, 103680, 107520, 108000, 110592, 110880, 115200, 120120, 120960, 122880,
  124416, 129600, 131072, 138240, 138600, 147456, 147840, 151200, 155520, 161280,
  162000, 165888, 166320, 172800, 176400, 180180, 181440, 184320, 186624, 189000,
  194400, 196608, 201600, 207360, 215040, 216000, 221184, 221760, 226800, 230400,
  233280, 240240, 241920, 245760, 248832, 259200, 262144, 264600, 272160, 276480,
  277200, 279936, 294912, 295680, 302400, 311040, 322560, 324000]

private def multipliers : List ℕ := [1, 2, 6, 30, 210, 2310, 30030]

private theorem primorial_small {k : ℕ} (h : primorial k ≤ 327600) :
    primorial k ∈ multipliers := by
  have hk : k < 17 := by
    by_contra! hlarge
    have mono := primorial_mono hlarge
    have big : primorial 17 = 510510 := by decide
    omega
  exact (show ∀ i : Fin 17, primorial i.val ∈ multipliers by decide) ⟨k, hk⟩

set_option maxRecDepth 8192 in
private theorem closed_check :
    candidates.all (fun m => multipliers.all (fun g =>
      decide (m*g > 327600) || candidates.contains (m*g))) = true := by decide

private theorem covers {m : ℕ} (h : leastSignature m) (hm : m ≤ 327600) : m ∈ candidates := by
  obtain ⟨l,rfl⟩ := h
  induction l with
  | nil => decide
  | cons k l ih =>
    simp only [List.map_cons, List.prod_cons] at hm ⊢
    have hp : 0 < (l.map primorial).prod := List.prod_pos (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact primorial_pos i)
    have hg := primorial_pos k
    have h1 := Nat.le_mul_of_pos_left (l.map primorial).prod hg
    have h2 := Nat.le_mul_of_pos_right (primorial k) hp
    have ht := ih (by omega)
    have hmem := primorial_small (k:=k) (by omega)
    have test := List.all_eq_true.mp (List.all_eq_true.mp closed_check _ ht) _ hmem
    simp [Nat.mul_comm (l.map primorial).prod] at test
    exact test.resolve_left (by omega)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem bounded_check :
    candidates.all (fun m => decide (dropValue m < 68)) = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem witness : dropValue 327600 = 68 := by decide +kernel

end OMA.A357604

open OMA.S_oeis_a357604 OMA.A357604 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a357604.main) := by
  intro h
  let hit (n : ℕ) : Prop := 1 ≤ n ∧ 68 ≤ a (n-1) - a n
  classical
  have hw : hit 327600 := ⟨by decide, by rw [dropValue_eq _ (by decide), witness]⟩
  have ex : ∃ n, hit n := ⟨_, hw⟩
  let m := Nat.find ex
  have hm : hit m := Nat.find_spec ex
  have low := hm.1
  have high : m ≤ 327600 := Nat.find_min' ex hw
  have hrec : recordAt (fun j => a (j-1) - a j) m := by
    refine ⟨low, ?_⟩
    intro j hj hjm
    have hj' : ¬ hit j := Nat.find_min ex hjm
    have hlt : a (j-1) - a j < 68 := by
      by_contra! bad
      exact hj' ⟨hj, bad⟩
    exact hlt.trans_le hm.2
  have mem := covers (h.2 m hrec) high
  have ht := List.all_eq_true.mp bounded_check m mem
  have lt : dropValue m < 68 := of_decide_eq_true ht
  have eqn := dropValue_eq m (by omega)
  have ge := hm.2
  omega
