import FormalConjectures.ErdosProblems.«366»

-- Reduction Erdos366.erdos_366.variants.weaker.R1 of Erdős Problem 366 — weaker
-- Original reduction credit: @maxime-fleury.
-- Correction: the old bounded-existence H1 is false. The kernel-checked finite
-- calculation below replaces it with bounded absence; H2 is unchanged.
-- The existence of any consecutive positive 3-full pair remains open here.


namespace Erdos366Finite

/- The finite-verification pattern is inspired by @nijv, open-math-agents PR #2725:
   https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2725.
   This certificate is independently written and verifies only the bounded statement.
   All finite calculations are checked with decide +kernel. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
set_option synthInstance.maxSize 4096 in
theorem no_consecutive_three_full_upto_100000 :
    ¬ ∃ n : ℕ, 0 < n ∧ n ≤ 100000 ∧ Nat.Full 3 n ∧ Nat.Full 3 (n + 1) := by
  let sievePair (n : ℕ) : Prop :=
    ((n % 2 ≠ 0 ∨ n % 8 = 0) ∧ ((n + 1) % 2 ≠ 0 ∨ (n + 1) % 8 = 0)) ∧
    ((n % 3 ≠ 0 ∨ n % 27 = 0) ∧ ((n + 1) % 3 ≠ 0 ∨ (n + 1) % 27 = 0)) ∧
    ((n % 5 ≠ 0 ∨ n % 125 = 0) ∧ ((n + 1) % 5 ≠ 0 ∨ (n + 1) % 125 = 0)) ∧
    ((n % 7 ≠ 0 ∨ n % 343 = 0) ∧ ((n + 1) % 7 ≠ 0 ∨ (n + 1) % 343 = 0)) ∧
    ((n % 11 ≠ 0 ∨ n % 1331 = 0) ∧ ((n + 1) % 11 ≠ 0 ∨ (n + 1) % 1331 = 0)) ∧
    ((n % 13 ≠ 0 ∨ n % 2197 = 0) ∧ ((n + 1) % 13 ≠ 0 ∨ (n + 1) % 2197 = 0)) ∧
    ((n % 17 ≠ 0 ∨ n % 4913 = 0) ∧ ((n + 1) % 17 ≠ 0 ∨ (n + 1) % 4913 = 0)) ∧
    ((n % 19 ≠ 0 ∨ n % 6859 = 0) ∧ ((n + 1) % 19 ≠ 0 ∨ (n + 1) % 6859 = 0)) ∧
    ((n % 23 ≠ 0 ∨ n % 12167 = 0) ∧ ((n + 1) % 23 ≠ 0 ∨ (n + 1) % 12167 = 0)) ∧
    ((n % 29 ≠ 0 ∨ n % 24389 = 0) ∧ ((n + 1) % 29 ≠ 0 ∨ (n + 1) % 24389 = 0)) ∧
    ((n % 31 ≠ 0 ∨ n % 29791 = 0) ∧ ((n + 1) % 31 ≠ 0 ∨ (n + 1) % 29791 = 0)) ∧
    ((n % 37 ≠ 0 ∨ n % 50653 = 0) ∧ ((n + 1) % 37 ≠ 0 ∨ (n + 1) % 50653 = 0)) ∧
    ((n % 41 ≠ 0 ∨ n % 68921 = 0) ∧ ((n + 1) % 41 ≠ 0 ∨ (n + 1) % 68921 = 0)) ∧
    ((n % 43 ≠ 0 ∨ n % 79507 = 0) ∧ ((n + 1) % 43 ≠ 0 ∨ (n + 1) % 79507 = 0))
  letI (n : ℕ) : Decidable (sievePair n) := by
    unfold sievePair
    infer_instance
  let cleared (n : ℕ) : Bool :=
    if sievePair n then decide (¬ (Nat.Full 3 n ∧ Nat.Full 3 (n + 1))) else true
  have full_mod_sieve {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
      (h : Nat.Full 3 n) : n % p ≠ 0 ∨ n % p ^ 3 = 0 := by
    by_cases hd : n % p = 0
    · exact Or.inr (Nat.dvd_iff_mod_eq_zero.mp
        (h p (Nat.mem_primeFactors.mpr ⟨hp, Nat.dvd_of_mod_eq_zero hd, hn⟩)))
    · exact Or.inl hd
  
  have full_pair_sieve {n : ℕ} (hn : 0 < n)
      (h : Nat.Full 3 n) (h' : Nat.Full 3 (n + 1)) : sievePair n := by
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    have hn1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
    exact ⟨
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 2) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 2) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 3) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 3) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 5) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 5) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 7) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 7) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 11) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 11) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 13) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 13) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 17) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 17) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 19) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 19) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 23) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 23) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 29) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 29) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 31) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 31) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 37) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 37) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 41) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 41) h'⟩,
      ⟨full_mod_sieve hn0 (by decide : Nat.Prime 43) h,
        full_mod_sieve hn1 (by decide : Nat.Prime 43) h'⟩⟩
  
  have checked_000 : (List.range' 1 1000).all cleared = true := by
    decide +kernel
  have checked_001 : (List.range' 1001 1000).all cleared = true := by
    decide +kernel
  have checked_002 : (List.range' 2001 1000).all cleared = true := by
    decide +kernel
  have checked_003 : (List.range' 3001 1000).all cleared = true := by
    decide +kernel
  have checked_004 : (List.range' 4001 1000).all cleared = true := by
    decide +kernel
  have checked_005 : (List.range' 5001 1000).all cleared = true := by
    decide +kernel
  have checked_006 : (List.range' 6001 1000).all cleared = true := by
    decide +kernel
  have checked_007 : (List.range' 7001 1000).all cleared = true := by
    decide +kernel
  have checked_008 : (List.range' 8001 1000).all cleared = true := by
    decide +kernel
  have checked_009 : (List.range' 9001 1000).all cleared = true := by
    decide +kernel
  have checked_010 : (List.range' 10001 1000).all cleared = true := by
    decide +kernel
  have checked_011 : (List.range' 11001 1000).all cleared = true := by
    decide +kernel
  have checked_012 : (List.range' 12001 1000).all cleared = true := by
    decide +kernel
  have checked_013 : (List.range' 13001 1000).all cleared = true := by
    decide +kernel
  have checked_014 : (List.range' 14001 1000).all cleared = true := by
    decide +kernel
  have checked_015 : (List.range' 15001 1000).all cleared = true := by
    decide +kernel
  have checked_016 : (List.range' 16001 1000).all cleared = true := by
    decide +kernel
  have checked_017 : (List.range' 17001 1000).all cleared = true := by
    decide +kernel
  have checked_018 : (List.range' 18001 1000).all cleared = true := by
    decide +kernel
  have checked_019 : (List.range' 19001 1000).all cleared = true := by
    decide +kernel
  have checked_020 : (List.range' 20001 1000).all cleared = true := by
    decide +kernel
  have checked_021 : (List.range' 21001 1000).all cleared = true := by
    decide +kernel
  have checked_022 : (List.range' 22001 1000).all cleared = true := by
    decide +kernel
  have checked_023 : (List.range' 23001 1000).all cleared = true := by
    decide +kernel
  have checked_024 : (List.range' 24001 1000).all cleared = true := by
    decide +kernel
  have checked_025 : (List.range' 25001 1000).all cleared = true := by
    decide +kernel
  have checked_026 : (List.range' 26001 1000).all cleared = true := by
    decide +kernel
  have checked_027 : (List.range' 27001 1000).all cleared = true := by
    decide +kernel
  have checked_028 : (List.range' 28001 1000).all cleared = true := by
    decide +kernel
  have checked_029 : (List.range' 29001 1000).all cleared = true := by
    decide +kernel
  have checked_030 : (List.range' 30001 1000).all cleared = true := by
    decide +kernel
  have checked_031 : (List.range' 31001 1000).all cleared = true := by
    decide +kernel
  have checked_032 : (List.range' 32001 1000).all cleared = true := by
    decide +kernel
  have checked_033 : (List.range' 33001 1000).all cleared = true := by
    decide +kernel
  have checked_034 : (List.range' 34001 1000).all cleared = true := by
    decide +kernel
  have checked_035 : (List.range' 35001 1000).all cleared = true := by
    decide +kernel
  have checked_036 : (List.range' 36001 1000).all cleared = true := by
    decide +kernel
  have checked_037 : (List.range' 37001 1000).all cleared = true := by
    decide +kernel
  have checked_038 : (List.range' 38001 1000).all cleared = true := by
    decide +kernel
  have checked_039 : (List.range' 39001 1000).all cleared = true := by
    decide +kernel
  have checked_040 : (List.range' 40001 1000).all cleared = true := by
    decide +kernel
  have checked_041 : (List.range' 41001 1000).all cleared = true := by
    decide +kernel
  have checked_042 : (List.range' 42001 1000).all cleared = true := by
    decide +kernel
  have checked_043 : (List.range' 43001 1000).all cleared = true := by
    decide +kernel
  have checked_044 : (List.range' 44001 1000).all cleared = true := by
    decide +kernel
  have checked_045 : (List.range' 45001 1000).all cleared = true := by
    decide +kernel
  have checked_046 : (List.range' 46001 1000).all cleared = true := by
    decide +kernel
  have checked_047 : (List.range' 47001 1000).all cleared = true := by
    decide +kernel
  have checked_048 : (List.range' 48001 1000).all cleared = true := by
    decide +kernel
  have checked_049 : (List.range' 49001 1000).all cleared = true := by
    decide +kernel
  have checked_050 : (List.range' 50001 1000).all cleared = true := by
    decide +kernel
  have checked_051 : (List.range' 51001 1000).all cleared = true := by
    decide +kernel
  have checked_052 : (List.range' 52001 1000).all cleared = true := by
    decide +kernel
  have checked_053 : (List.range' 53001 1000).all cleared = true := by
    decide +kernel
  have checked_054 : (List.range' 54001 1000).all cleared = true := by
    decide +kernel
  have checked_055 : (List.range' 55001 1000).all cleared = true := by
    decide +kernel
  have checked_056 : (List.range' 56001 1000).all cleared = true := by
    decide +kernel
  have checked_057 : (List.range' 57001 1000).all cleared = true := by
    decide +kernel
  have checked_058 : (List.range' 58001 1000).all cleared = true := by
    decide +kernel
  have checked_059 : (List.range' 59001 1000).all cleared = true := by
    decide +kernel
  have checked_060 : (List.range' 60001 1000).all cleared = true := by
    decide +kernel
  have checked_061 : (List.range' 61001 1000).all cleared = true := by
    decide +kernel
  have checked_062 : (List.range' 62001 1000).all cleared = true := by
    decide +kernel
  have checked_063 : (List.range' 63001 1000).all cleared = true := by
    decide +kernel
  have checked_064 : (List.range' 64001 1000).all cleared = true := by
    decide +kernel
  have checked_065 : (List.range' 65001 1000).all cleared = true := by
    decide +kernel
  have checked_066 : (List.range' 66001 1000).all cleared = true := by
    decide +kernel
  have checked_067 : (List.range' 67001 1000).all cleared = true := by
    decide +kernel
  have checked_068 : (List.range' 68001 1000).all cleared = true := by
    decide +kernel
  have checked_069 : (List.range' 69001 1000).all cleared = true := by
    decide +kernel
  have checked_070 : (List.range' 70001 1000).all cleared = true := by
    decide +kernel
  have checked_071 : (List.range' 71001 1000).all cleared = true := by
    decide +kernel
  have checked_072 : (List.range' 72001 1000).all cleared = true := by
    decide +kernel
  have checked_073 : (List.range' 73001 1000).all cleared = true := by
    decide +kernel
  have checked_074 : (List.range' 74001 1000).all cleared = true := by
    decide +kernel
  have checked_075 : (List.range' 75001 1000).all cleared = true := by
    decide +kernel
  have checked_076 : (List.range' 76001 1000).all cleared = true := by
    decide +kernel
  have checked_077 : (List.range' 77001 1000).all cleared = true := by
    decide +kernel
  have checked_078 : (List.range' 78001 1000).all cleared = true := by
    decide +kernel
  have checked_079 : (List.range' 79001 1000).all cleared = true := by
    decide +kernel
  have checked_080 : (List.range' 80001 1000).all cleared = true := by
    decide +kernel
  have checked_081 : (List.range' 81001 1000).all cleared = true := by
    decide +kernel
  have checked_082 : (List.range' 82001 1000).all cleared = true := by
    decide +kernel
  have checked_083 : (List.range' 83001 1000).all cleared = true := by
    decide +kernel
  have checked_084 : (List.range' 84001 1000).all cleared = true := by
    decide +kernel
  have checked_085 : (List.range' 85001 1000).all cleared = true := by
    decide +kernel
  have checked_086 : (List.range' 86001 1000).all cleared = true := by
    decide +kernel
  have checked_087 : (List.range' 87001 1000).all cleared = true := by
    decide +kernel
  have checked_088 : (List.range' 88001 1000).all cleared = true := by
    decide +kernel
  have checked_089 : (List.range' 89001 1000).all cleared = true := by
    decide +kernel
  have checked_090 : (List.range' 90001 1000).all cleared = true := by
    decide +kernel
  have checked_091 : (List.range' 91001 1000).all cleared = true := by
    decide +kernel
  have checked_092 : (List.range' 92001 1000).all cleared = true := by
    decide +kernel
  have checked_093 : (List.range' 93001 1000).all cleared = true := by
    decide +kernel
  have checked_094 : (List.range' 94001 1000).all cleared = true := by
    decide +kernel
  have checked_095 : (List.range' 95001 1000).all cleared = true := by
    decide +kernel
  have checked_096 : (List.range' 96001 1000).all cleared = true := by
    decide +kernel
  have checked_097 : (List.range' 97001 1000).all cleared = true := by
    decide +kernel
  have checked_098 : (List.range' 98001 1000).all cleared = true := by
    decide +kernel
  have checked_099 : (List.range' 99001 1000).all cleared = true := by
    decide +kernel

  have cleared_of_bounded {n : ℕ} (hn : 0 < n) (hb : n ≤ 100000) :
      cleared n = true := by
    by_cases h000 : n < 1001
    · exact (List.all_eq_true.mp checked_000) n
        (List.mem_range'_1.mpr ⟨Nat.succ_le_of_lt hn, h000⟩)
    by_cases h001 : n < 2001
    · exact (List.all_eq_true.mp checked_001) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h000, h001⟩)
    by_cases h002 : n < 3001
    · exact (List.all_eq_true.mp checked_002) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h001, h002⟩)
    by_cases h003 : n < 4001
    · exact (List.all_eq_true.mp checked_003) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h002, h003⟩)
    by_cases h004 : n < 5001
    · exact (List.all_eq_true.mp checked_004) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h003, h004⟩)
    by_cases h005 : n < 6001
    · exact (List.all_eq_true.mp checked_005) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h004, h005⟩)
    by_cases h006 : n < 7001
    · exact (List.all_eq_true.mp checked_006) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h005, h006⟩)
    by_cases h007 : n < 8001
    · exact (List.all_eq_true.mp checked_007) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h006, h007⟩)
    by_cases h008 : n < 9001
    · exact (List.all_eq_true.mp checked_008) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h007, h008⟩)
    by_cases h009 : n < 10001
    · exact (List.all_eq_true.mp checked_009) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h008, h009⟩)
    by_cases h010 : n < 11001
    · exact (List.all_eq_true.mp checked_010) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h009, h010⟩)
    by_cases h011 : n < 12001
    · exact (List.all_eq_true.mp checked_011) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h010, h011⟩)
    by_cases h012 : n < 13001
    · exact (List.all_eq_true.mp checked_012) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h011, h012⟩)
    by_cases h013 : n < 14001
    · exact (List.all_eq_true.mp checked_013) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h012, h013⟩)
    by_cases h014 : n < 15001
    · exact (List.all_eq_true.mp checked_014) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h013, h014⟩)
    by_cases h015 : n < 16001
    · exact (List.all_eq_true.mp checked_015) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h014, h015⟩)
    by_cases h016 : n < 17001
    · exact (List.all_eq_true.mp checked_016) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h015, h016⟩)
    by_cases h017 : n < 18001
    · exact (List.all_eq_true.mp checked_017) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h016, h017⟩)
    by_cases h018 : n < 19001
    · exact (List.all_eq_true.mp checked_018) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h017, h018⟩)
    by_cases h019 : n < 20001
    · exact (List.all_eq_true.mp checked_019) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h018, h019⟩)
    by_cases h020 : n < 21001
    · exact (List.all_eq_true.mp checked_020) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h019, h020⟩)
    by_cases h021 : n < 22001
    · exact (List.all_eq_true.mp checked_021) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h020, h021⟩)
    by_cases h022 : n < 23001
    · exact (List.all_eq_true.mp checked_022) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h021, h022⟩)
    by_cases h023 : n < 24001
    · exact (List.all_eq_true.mp checked_023) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h022, h023⟩)
    by_cases h024 : n < 25001
    · exact (List.all_eq_true.mp checked_024) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h023, h024⟩)
    by_cases h025 : n < 26001
    · exact (List.all_eq_true.mp checked_025) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h024, h025⟩)
    by_cases h026 : n < 27001
    · exact (List.all_eq_true.mp checked_026) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h025, h026⟩)
    by_cases h027 : n < 28001
    · exact (List.all_eq_true.mp checked_027) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h026, h027⟩)
    by_cases h028 : n < 29001
    · exact (List.all_eq_true.mp checked_028) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h027, h028⟩)
    by_cases h029 : n < 30001
    · exact (List.all_eq_true.mp checked_029) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h028, h029⟩)
    by_cases h030 : n < 31001
    · exact (List.all_eq_true.mp checked_030) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h029, h030⟩)
    by_cases h031 : n < 32001
    · exact (List.all_eq_true.mp checked_031) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h030, h031⟩)
    by_cases h032 : n < 33001
    · exact (List.all_eq_true.mp checked_032) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h031, h032⟩)
    by_cases h033 : n < 34001
    · exact (List.all_eq_true.mp checked_033) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h032, h033⟩)
    by_cases h034 : n < 35001
    · exact (List.all_eq_true.mp checked_034) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h033, h034⟩)
    by_cases h035 : n < 36001
    · exact (List.all_eq_true.mp checked_035) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h034, h035⟩)
    by_cases h036 : n < 37001
    · exact (List.all_eq_true.mp checked_036) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h035, h036⟩)
    by_cases h037 : n < 38001
    · exact (List.all_eq_true.mp checked_037) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h036, h037⟩)
    by_cases h038 : n < 39001
    · exact (List.all_eq_true.mp checked_038) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h037, h038⟩)
    by_cases h039 : n < 40001
    · exact (List.all_eq_true.mp checked_039) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h038, h039⟩)
    by_cases h040 : n < 41001
    · exact (List.all_eq_true.mp checked_040) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h039, h040⟩)
    by_cases h041 : n < 42001
    · exact (List.all_eq_true.mp checked_041) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h040, h041⟩)
    by_cases h042 : n < 43001
    · exact (List.all_eq_true.mp checked_042) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h041, h042⟩)
    by_cases h043 : n < 44001
    · exact (List.all_eq_true.mp checked_043) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h042, h043⟩)
    by_cases h044 : n < 45001
    · exact (List.all_eq_true.mp checked_044) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h043, h044⟩)
    by_cases h045 : n < 46001
    · exact (List.all_eq_true.mp checked_045) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h044, h045⟩)
    by_cases h046 : n < 47001
    · exact (List.all_eq_true.mp checked_046) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h045, h046⟩)
    by_cases h047 : n < 48001
    · exact (List.all_eq_true.mp checked_047) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h046, h047⟩)
    by_cases h048 : n < 49001
    · exact (List.all_eq_true.mp checked_048) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h047, h048⟩)
    by_cases h049 : n < 50001
    · exact (List.all_eq_true.mp checked_049) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h048, h049⟩)
    by_cases h050 : n < 51001
    · exact (List.all_eq_true.mp checked_050) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h049, h050⟩)
    by_cases h051 : n < 52001
    · exact (List.all_eq_true.mp checked_051) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h050, h051⟩)
    by_cases h052 : n < 53001
    · exact (List.all_eq_true.mp checked_052) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h051, h052⟩)
    by_cases h053 : n < 54001
    · exact (List.all_eq_true.mp checked_053) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h052, h053⟩)
    by_cases h054 : n < 55001
    · exact (List.all_eq_true.mp checked_054) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h053, h054⟩)
    by_cases h055 : n < 56001
    · exact (List.all_eq_true.mp checked_055) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h054, h055⟩)
    by_cases h056 : n < 57001
    · exact (List.all_eq_true.mp checked_056) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h055, h056⟩)
    by_cases h057 : n < 58001
    · exact (List.all_eq_true.mp checked_057) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h056, h057⟩)
    by_cases h058 : n < 59001
    · exact (List.all_eq_true.mp checked_058) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h057, h058⟩)
    by_cases h059 : n < 60001
    · exact (List.all_eq_true.mp checked_059) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h058, h059⟩)
    by_cases h060 : n < 61001
    · exact (List.all_eq_true.mp checked_060) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h059, h060⟩)
    by_cases h061 : n < 62001
    · exact (List.all_eq_true.mp checked_061) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h060, h061⟩)
    by_cases h062 : n < 63001
    · exact (List.all_eq_true.mp checked_062) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h061, h062⟩)
    by_cases h063 : n < 64001
    · exact (List.all_eq_true.mp checked_063) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h062, h063⟩)
    by_cases h064 : n < 65001
    · exact (List.all_eq_true.mp checked_064) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h063, h064⟩)
    by_cases h065 : n < 66001
    · exact (List.all_eq_true.mp checked_065) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h064, h065⟩)
    by_cases h066 : n < 67001
    · exact (List.all_eq_true.mp checked_066) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h065, h066⟩)
    by_cases h067 : n < 68001
    · exact (List.all_eq_true.mp checked_067) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h066, h067⟩)
    by_cases h068 : n < 69001
    · exact (List.all_eq_true.mp checked_068) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h067, h068⟩)
    by_cases h069 : n < 70001
    · exact (List.all_eq_true.mp checked_069) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h068, h069⟩)
    by_cases h070 : n < 71001
    · exact (List.all_eq_true.mp checked_070) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h069, h070⟩)
    by_cases h071 : n < 72001
    · exact (List.all_eq_true.mp checked_071) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h070, h071⟩)
    by_cases h072 : n < 73001
    · exact (List.all_eq_true.mp checked_072) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h071, h072⟩)
    by_cases h073 : n < 74001
    · exact (List.all_eq_true.mp checked_073) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h072, h073⟩)
    by_cases h074 : n < 75001
    · exact (List.all_eq_true.mp checked_074) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h073, h074⟩)
    by_cases h075 : n < 76001
    · exact (List.all_eq_true.mp checked_075) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h074, h075⟩)
    by_cases h076 : n < 77001
    · exact (List.all_eq_true.mp checked_076) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h075, h076⟩)
    by_cases h077 : n < 78001
    · exact (List.all_eq_true.mp checked_077) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h076, h077⟩)
    by_cases h078 : n < 79001
    · exact (List.all_eq_true.mp checked_078) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h077, h078⟩)
    by_cases h079 : n < 80001
    · exact (List.all_eq_true.mp checked_079) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h078, h079⟩)
    by_cases h080 : n < 81001
    · exact (List.all_eq_true.mp checked_080) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h079, h080⟩)
    by_cases h081 : n < 82001
    · exact (List.all_eq_true.mp checked_081) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h080, h081⟩)
    by_cases h082 : n < 83001
    · exact (List.all_eq_true.mp checked_082) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h081, h082⟩)
    by_cases h083 : n < 84001
    · exact (List.all_eq_true.mp checked_083) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h082, h083⟩)
    by_cases h084 : n < 85001
    · exact (List.all_eq_true.mp checked_084) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h083, h084⟩)
    by_cases h085 : n < 86001
    · exact (List.all_eq_true.mp checked_085) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h084, h085⟩)
    by_cases h086 : n < 87001
    · exact (List.all_eq_true.mp checked_086) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h085, h086⟩)
    by_cases h087 : n < 88001
    · exact (List.all_eq_true.mp checked_087) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h086, h087⟩)
    by_cases h088 : n < 89001
    · exact (List.all_eq_true.mp checked_088) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h087, h088⟩)
    by_cases h089 : n < 90001
    · exact (List.all_eq_true.mp checked_089) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h088, h089⟩)
    by_cases h090 : n < 91001
    · exact (List.all_eq_true.mp checked_090) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h089, h090⟩)
    by_cases h091 : n < 92001
    · exact (List.all_eq_true.mp checked_091) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h090, h091⟩)
    by_cases h092 : n < 93001
    · exact (List.all_eq_true.mp checked_092) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h091, h092⟩)
    by_cases h093 : n < 94001
    · exact (List.all_eq_true.mp checked_093) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h092, h093⟩)
    by_cases h094 : n < 95001
    · exact (List.all_eq_true.mp checked_094) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h093, h094⟩)
    by_cases h095 : n < 96001
    · exact (List.all_eq_true.mp checked_095) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h094, h095⟩)
    by_cases h096 : n < 97001
    · exact (List.all_eq_true.mp checked_096) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h095, h096⟩)
    by_cases h097 : n < 98001
    · exact (List.all_eq_true.mp checked_097) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h096, h097⟩)
    by_cases h098 : n < 99001
    · exact (List.all_eq_true.mp checked_098) n
        (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h097, h098⟩)
    exact (List.all_eq_true.mp checked_099) n
      (List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h098, Nat.lt_succ_of_le hb⟩)

  rintro ⟨n, hn, hb, hf, hf'⟩
  have hc := cleared_of_bounded hn hb
  have hs := full_pair_sieve hn hf hf'
  have hd : decide (¬ (Nat.Full 3 n ∧ Nat.Full 3 (n + 1))) = true := by
    simpa only [cleared, if_pos hs] using hc
  exact (of_decide_eq_true hd) ⟨hf, hf'⟩


end Erdos366Finite


namespace OMA.R_Erdos366_erdos_366_variants_weaker_R1

/-- No pair of consecutive `3`-full integers has first entry in `[1, 100000]`.
This replaces the previous bounded-existence obligation, which the finite
certificate above rules out. -/
def H1 : Prop := ¬ ∃ n : ℕ, 0 < n ∧ n ≤ 100000 ∧ Nat.Full 3 n ∧ Nat.Full 3 (n + 1)

/-- A pair of consecutive `3`-full integers beyond `100000`: the remaining
unbounded existence question. -/
def H2 : Prop := ∃ n : ℕ, 100000 < n ∧ Nat.Full 3 n ∧ Nat.Full 3 (n + 1)

/-- The corrected finite obligation is discharged by kernel computation. -/
theorem bounded_absence : H1 :=
  Erdos366Finite.no_consecutive_three_full_upto_100000

theorem main : H1 → H2 → type_of% @Erdos366.erdos_366.variants.weaker := by
  rintro _ ⟨n, hn, hf, hf'⟩
  exact ⟨n, Nat.lt_trans (by decide : 0 < 100000) hn, hf, hf'⟩

/-- The original existence problem is equivalent to the unchanged tail
obligation, because the entire positive range through `100000` is excluded. -/
theorem parent_iff_tail : (type_of% @Erdos366.erdos_366.variants.weaker) ↔ H2 := by
  constructor
  · rintro ⟨n, hn, hf, hf'⟩
    refine ⟨n, ?_, hf, hf'⟩
    exact lt_of_not_ge (fun hb => bounded_absence ⟨n, hn, hb, hf, hf'⟩)
  · exact main bounded_absence

end OMA.R_Erdos366_erdos_366_variants_weaker_R1
