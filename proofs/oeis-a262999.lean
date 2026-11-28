import OMAStatements.S_oeis_a262999
import Mathlib

/-!
# A disproof of Sun's conjecture on OEIS A262999

The conjecture says that `a(n) = 1` only for `n` in an explicit finite list. We show
`a(7872413) = 1`: the only pair is `(15015, 4749)`, with
`π(112732620) + π(22553001) = 6450605 + 1421808 = 7872413`.

Method. The values `π(k(k+1)/2)` for `k ≤ 16689` and `π(m^2)` for `m ≤ 11801` are certified
by a windowed bitmask sieve of Eratosthenes evaluated by the kernel (`decide +kernel`). Since
`π(T_16689) > 7872413` and `π(11801^2) > 7872413`, every pair has `k ≤ 16688` and `m ≤ 11800`.
A merge of the two sorted value lists `π(T_k)` and `7872413 - π(m^2)` finds the single common
value `6450605`, and monotonicity of `π` pins down `k = 15015` and `m = 4749`.

Attribution. The sieve (`multMask`, `stepW`, `sieveW`, ...), the SWAR population count
(`dsum`, `swar`, `pc`, ...) and the certified-table checker (`Good`, `chk`, ...) are adapted
from Neal Patel's refutation of A262995,
https://github.com/thatnealpatel/proofs, file
Proofs/Sorry/NumberComplexity/A262995Refutation.lean at commit
e0c9810910fd2faa896326257d0a7b95216756cc, used under the MIT License:

  MIT License

  Copyright (c) 2026 Neal Patel

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the 'Software'), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.

(Double quotes in the notice are written as single quotes, since this repository forbids the
double-quote character.) Changes: larger windows and sieving primes, a 32768-bit population
count with a closed-form mask, a two-sequence chunk checker, and a merge-based pair check.
-/

namespace OMA.A262999Disproof

open OMA.S_oeis_a262999

/-! ## Bitmask of the multiples of `d` -/

/-- `m ||| (m <<< s)`. -/
def dbl (s m : ℕ) : ℕ := m ||| (m <<< s)

/-- The bitmask of the multiples of `d` below `d * 2 ^ t`, built by doubling. -/
def multMask (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => dbl (d * 2 ^ t) (multMask d t)

theorem testBit_multMask {d : ℕ} (hd : 0 < d) (t i : ℕ) :
    (multMask d t).testBit i = true ↔ d ∣ i ∧ i < d * 2 ^ t := by
  induction t generalizing i with
  | zero =>
    rw [multMask, Nat.testBit_one_eq_true_iff_self_eq_zero, pow_zero, mul_one]
    constructor
    · rintro rfl
      exact ⟨dvd_zero d, hd⟩
    · rintro ⟨hdvd, hlt⟩
      exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
  | succ t ih =>
    rw [multMask, dbl, Nat.testBit_lor, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_iff, ih, ih]
    have hs : d ∣ d * 2 ^ t := dvd_mul_right d _
    have hpow : d * 2 ^ (t + 1) = d * 2 ^ t + d * 2 ^ t := by ring
    rw [hpow]
    constructor
    · rintro (⟨hdvd, hlt⟩ | ⟨hle, hdvd, hlt⟩)
      · exact ⟨hdvd, by omega⟩
      · refine ⟨?_, by omega⟩
        have h := Nat.dvd_add hdvd hs
        rwa [Nat.sub_add_cancel hle] at h
    · rintro ⟨hdvd, hlt⟩
      by_cases hle : d * 2 ^ t ≤ i
      · right
        exact ⟨hle, Nat.dvd_sub hdvd hs, by omega⟩
      · left
        exact ⟨hdvd, by omega⟩

/-- The bits of `B` not in `M`. -/
def clear (B M : ℕ) : ℕ := B ^^^ (B &&& M)

theorem testBit_clear (B M i : ℕ) :
    (clear B M).testBit i = (B.testBit i && !M.testBit i) := by
  rw [clear, Nat.testBit_xor, Nat.testBit_land]
  cases B.testBit i <;> cases M.testBit i <;> rfl

/-! ## A windowed sieve of Eratosthenes on bitmasks -/

/-- The number of doublings after which `d * 2 ^ t` exceeds `S`. -/
def tB (S d : ℕ) : ℕ := Nat.log2 (S / d) + 1

theorem lt_mul_two_pow_tB {S d : ℕ} (hd : 0 < d) : S < d * 2 ^ tB S d := by
  have h1 : S / d < 2 ^ tB S d := Nat.lt_log2_self
  have h2 : S < d * (S / d + 1) := Nat.lt_mul_div_succ S hd
  calc S < d * (S / d + 1) := h2
    _ ≤ d * 2 ^ tB S d := Nat.mul_le_mul_left d h1

/-- The least multiple of `d` that is at least `max lo (2 * d)`. -/
def firstMult (lo d : ℕ) : ℕ := (max lo (2 * d) + d - 1) / d * d

theorem dvd_firstMult (lo d : ℕ) : d ∣ firstMult lo d := Dvd.intro_left _ rfl

theorem le_firstMult {lo d : ℕ} (hd : 0 < d) : max lo (2 * d) ≤ firstMult lo d := by
  set m := max lo (2 * d)
  have hdm := Nat.div_add_mod (m + d - 1) d
  have hmod := Nat.mod_lt (m + d - 1) hd
  rw [firstMult, Nat.mul_comm]
  set q := (m + d - 1) / d
  set r := (m + d - 1) % d
  omega

theorem firstMult_le {lo d x : ℕ} (hd : 0 < d) (hdx : d ∣ x) (hx : max lo (2 * d) ≤ x) :
    firstMult lo d ≤ x := by
  obtain ⟨y, rfl⟩ := hdx
  rw [firstMult, Nat.mul_comm d y]
  apply Nat.mul_le_mul_right
  · rw [Nat.div_le_iff_le_mul_add_pred hd]
    set m := max lo (2 * d)
    set z := d * y
    omega

/-- One sieve step on the window `[lo, lo + S)`: clear the multiples `x` of `d` with
`2 * d ≤ x`. -/
def stepW (lo S d B : ℕ) : ℕ := clear B (multMask d (tB S d) <<< (firstMult lo d - lo))

theorem testBit_stepW {lo S d B i : ℕ} (hd : 0 < d) (hi : i < S) :
    (stepW lo S d B).testBit i = true ↔
      B.testBit i = true ∧ ¬ (2 * d ≤ lo + i ∧ d ∣ lo + i) := by
  rw [stepW, testBit_clear, Bool.and_eq_true, Bool.not_eq_true', Nat.testBit_shiftLeft,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.eq_false_iff, ne_eq,
    testBit_multMask hd]
  have hc := le_firstMult (lo := lo) hd
  have hcd := dvd_firstMult lo d
  have hS := lt_mul_two_pow_tB (S := S) hd
  rw [max_le_iff] at hc
  apply and_congr_right
  intro _
  constructor
  · rintro (hlt | hnot) ⟨h2d, hdvd⟩
    · have hle := firstMult_le (lo := lo) hd hdvd (max_le_iff.mpr ⟨by omega, h2d⟩)
      omega
    · apply hnot
      have hle := firstMult_le (lo := lo) hd hdvd (max_le_iff.mpr ⟨by omega, h2d⟩)
      refine ⟨?_, by omega⟩
      have h := Nat.dvd_sub hdvd hcd
      rwa [show lo + i - firstMult lo d = i - (firstMult lo d - lo) by omega] at h
  · intro hnot
    by_cases hlt : i < firstMult lo d - lo
    · left; omega
    · right
      rintro ⟨hdvd, _⟩
      apply hnot
      refine ⟨by omega, ?_⟩
      have h := Nat.dvd_add hdvd hcd
      rwa [show i - (firstMult lo d - lo) + firstMult lo d = lo + i by omega] at h

/-- The window `[lo, lo + S)` with the integers below `2` removed. -/
def initW (lo S : ℕ) : ℕ := (2 ^ S - 1) ^^^ (2 ^ (2 - lo) - 1)

theorem testBit_initW {lo S i : ℕ} (hi : i < S) :
    (initW lo S).testBit i = true ↔ 2 ≤ lo + i := by
  rw [initW, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one,
    decide_eq_true hi, Bool.true_xor, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

/-- The sieve of the window `[lo, lo + S)` by the list `ds`: bit `i` stands for `lo + i`. -/
def sieveW (lo S : ℕ) (ds : List ℕ) : ℕ := ds.foldl (fun B d => stepW lo S d B) (initW lo S)

theorem testBit_foldl_stepW {lo S i : ℕ} (hi : i < S) (ds : List ℕ) (hds : ∀ d ∈ ds, 0 < d) :
    ∀ B : ℕ, (ds.foldl (fun B d => stepW lo S d B) B).testBit i = true ↔
      B.testBit i = true ∧ ∀ d ∈ ds, ¬ (2 * d ≤ lo + i ∧ d ∣ lo + i) := by
  induction ds with
  | nil => intro B; simp
  | cons d ds ih =>
    intro B
    rw [List.foldl_cons, ih (fun e he => hds e (List.mem_cons_of_mem d he)),
      testBit_stepW (hds d List.mem_cons_self) hi, List.forall_mem_cons, and_assoc]

theorem testBit_sieveW {lo S i : ℕ} (hi : i < S) (ds : List ℕ) (hds : ∀ d ∈ ds, 0 < d) :
    (sieveW lo S ds).testBit i = true ↔
      2 ≤ lo + i ∧ ∀ d ∈ ds, ¬ (2 * d ≤ lo + i ∧ d ∣ lo + i) := by
  rw [sieveW, testBit_foldl_stepW hi ds hds, testBit_initW hi]

theorem sieve_cond_iff_prime {N x : ℕ} (hx : x < N) (ds : List ℕ)
    (hall : ∀ p : ℕ, p.Prime → p * p < N → p ∈ ds) (hds : ∀ d ∈ ds, 2 ≤ d) :
    (2 ≤ x ∧ ∀ d ∈ ds, ¬ (2 * d ≤ x ∧ d ∣ x)) ↔ x.Prime := by
  constructor
  · rintro ⟨h2, hnone⟩
    by_contra hnp
    have hx1 : x ≠ 1 := by omega
    have hq := Nat.minFac_prime hx1
    have hsq : x.minFac ^ 2 ≤ x := Nat.minFac_sq_le_self (by omega) hnp
    have hmem : x.minFac ∈ ds := hall _ hq (by nlinarith)
    apply hnone _ hmem
    refine ⟨?_, Nat.minFac_dvd x⟩
    obtain ⟨y, hy⟩ := Nat.minFac_dvd x
    have hy2 : 2 ≤ y := by
      by_contra hy2
      interval_cases y
      · omega
      · rw [mul_one] at hy
        exact hnp (hy ▸ hq)
    nlinarith
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    rintro d hd ⟨h2d, hdvd⟩
    rcases hp.eq_one_or_self_of_dvd d hdvd with h1 | hself
    · have := hds d hd
      omega
    · have := hp.two_le
      omega

/-! ## Population count by SWAR -/

/-- The sum of the first `L` base-`2 ^ w` digits of `x`. -/
def dsum (w : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L + 1, x => x % 2 ^ w + dsum w L (x / 2 ^ w)

/-- `(q ^ L - 1) / (q - 1) = 1 + q + ... + q ^ (L - 1)`. -/
theorem geo_succ {q : ℕ} (hq : 2 ≤ q) (L : ℕ) :
    (q ^ (L + 1) - 1) / (q - 1) = q * ((q ^ L - 1) / (q - 1)) + 1 := by
  obtain ⟨s, hs⟩ : q - 1 ∣ q ^ L - 1 := by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 L
  have h1 : 1 ≤ q ^ L := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ (L + 1) := Nat.one_le_pow _ _ (by omega)
  have hpos : 0 < q - 1 := by omega
  have key : q ^ (L + 1) - 1 = (q - 1) * (q * s + 1) := by
    zify [h1, h2, (by omega : 1 ≤ q)] at hs ⊢
    rw [pow_succ]
    linear_combination (q : ℤ) * hs
  rw [key, hs, Nat.mul_div_cancel_left _ hpos, Nat.mul_div_cancel_left _ hpos]

/-- The mask selecting the low `w` bits of each of `L` consecutive `2 * w`-bit fields,
in closed form. -/
def evenMask (w L : ℕ) : ℕ := (2 ^ w - 1) * (((2 ^ (2 * w)) ^ L - 1) / (2 ^ (2 * w) - 1))

theorem evenMask_succ (w L : ℕ) :
    evenMask w (L + 1) = 2 ^ (2 * w) * evenMask w L + (2 ^ w - 1) := by
  have hq : 2 ≤ 2 ^ (2 * w) ∨ w = 0 := by
    rcases Nat.eq_zero_or_pos w with h | h
    · exact Or.inr h
    · left
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases hq with hq | rfl
  · rw [evenMask, evenMask, geo_succ hq]
    ring
  · simp [evenMask]

/-- One SWAR step: add adjacent `w`-bit fields into `2 * w`-bit fields. -/
def swar (w L x : ℕ) : ℕ := (x &&& evenMask w L) + ((x >>> w) &&& evenMask w L)

theorem land_evenMask_succ (w L x : ℕ) :
    x &&& evenMask w (L + 1) = 2 ^ (2 * w) * ((x / 2 ^ (2 * w)) &&& evenMask w L) + x % 2 ^ w := by
  have hpow : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 2 ^ w - 1 < 2 ^ (2 * w) := by have := Nat.one_le_two_pow (n := w); omega
  have h2 : x % 2 ^ w < 2 ^ (2 * w) := lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hpow
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, evenMask_succ, Nat.testBit_two_pow_mul_add _ h1,
    Nat.testBit_two_pow_mul_add _ h2]
  split_ifs with hj
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Bool.and_comm]
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

theorem swar_succ (w L x : ℕ) :
    swar w (L + 1) x =
      2 ^ (2 * w) * swar w L (x / 2 ^ (2 * w)) + (x % 2 ^ w + x / 2 ^ w % 2 ^ w) := by
  have hshift : x >>> w / 2 ^ (2 * w) = (x / 2 ^ (2 * w)) >>> w := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [swar, swar, land_evenMask_succ, land_evenMask_succ, hshift, Nat.shiftRight_eq_div_pow x w]
  ring

theorem dsum_swar {w : ℕ} (hw : 0 < w) (L : ℕ) :
    ∀ x : ℕ, dsum (2 * w) L (swar w L x) = dsum w (2 * L) x := by
  induction L with
  | zero => intro x; rfl
  | succ L ih =>
    intro x
    have hd0 : x % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
    have hd1 : x / 2 ^ w % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
    have hpow : 2 ^ w + 2 ^ w ≤ 2 ^ (2 * w) := by
      rw [← two_mul, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hr : x % 2 ^ w + x / 2 ^ w % 2 ^ w < 2 ^ (2 * w) := by omega
    have hdiv : x / 2 ^ w / 2 ^ w = x / 2 ^ (2 * w) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, two_mul]
    rw [swar_succ, show 2 * (L + 1) = 2 * L + 1 + 1 by ring, dsum, dsum, dsum,
      Nat.add_comm (2 ^ (2 * w) * _), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hr, zero_add, ih, hdiv, add_assoc]

theorem dsum_swar' {w w2 L L2 : ℕ} (hw : 0 < w) (hw2 : w2 = 2 * w) (hL2 : L2 = 2 * L)
    (x : ℕ) : dsum w2 L (swar w L x) = dsum w L2 x := by
  rw [hw2, hL2, dsum_swar hw]

/-- Population count of the low `32768` bits, by fifteen SWAR steps. -/
def pc (x : ℕ) : ℕ :=
  swar 16384 1 (swar 8192 2 (swar 4096 4 (swar 2048 8 (swar 1024 16 (swar 512 32
    (swar 256 64 (swar 128 128 (swar 64 256 (swar 32 512 (swar 16 1024 (swar 8 2048
      (swar 4 4096 (swar 2 8192 (swar 1 16384 x)))))))))))))) % 2 ^ 32768

theorem pc_eq_dsum (x : ℕ) : pc x = dsum 1 32768 x := by
  have h : pc x = dsum 32768 1 (swar 16384 1 (swar 8192 2 (swar 4096 4 (swar 2048 8
      (swar 1024 16 (swar 512 32 (swar 256 64 (swar 128 128 (swar 64 256 (swar 32 512
        (swar 16 1024 (swar 8 2048 (swar 4 4096 (swar 2 8192 (swar 1 16384 x))))))))))))))) := by
    rw [pc, dsum, dsum, add_zero]
  rw [h, dsum_swar' (w := 16384) (w2 := 32768) (L := 1) (L2 := 2) (by norm_num) rfl rfl,
    dsum_swar' (w := 8192) (w2 := 16384) (L := 2) (L2 := 4) (by norm_num) rfl rfl,
    dsum_swar' (w := 4096) (w2 := 8192) (L := 4) (L2 := 8) (by norm_num) rfl rfl,
    dsum_swar' (w := 2048) (w2 := 4096) (L := 8) (L2 := 16) (by norm_num) rfl rfl,
    dsum_swar' (w := 1024) (w2 := 2048) (L := 16) (L2 := 32) (by norm_num) rfl rfl,
    dsum_swar' (w := 512) (w2 := 1024) (L := 32) (L2 := 64) (by norm_num) rfl rfl,
    dsum_swar' (w := 256) (w2 := 512) (L := 64) (L2 := 128) (by norm_num) rfl rfl,
    dsum_swar' (w := 128) (w2 := 256) (L := 128) (L2 := 256) (by norm_num) rfl rfl,
    dsum_swar' (w := 64) (w2 := 128) (L := 256) (L2 := 512) (by norm_num) rfl rfl,
    dsum_swar' (w := 32) (w2 := 64) (L := 512) (L2 := 1024) (by norm_num) rfl rfl,
    dsum_swar' (w := 16) (w2 := 32) (L := 1024) (L2 := 2048) (by norm_num) rfl rfl,
    dsum_swar' (w := 8) (w2 := 16) (L := 2048) (L2 := 4096) (by norm_num) rfl rfl,
    dsum_swar' (w := 4) (w2 := 8) (L := 4096) (L2 := 8192) (by norm_num) rfl rfl,
    dsum_swar' (w := 2) (w2 := 4) (L := 8192) (L2 := 16384) (by norm_num) rfl rfl,
    dsum_swar' (w := 1) (w2 := 2) (L := 16384) (L2 := 32768) (by norm_num) rfl rfl]

theorem dsum_one_eq_count (L : ℕ) :
    ∀ x : ℕ, dsum 1 L x = Nat.count (fun i => x.testBit i = true) L := by
  induction L with
  | zero => intro x; rfl
  | succ L ih =>
    intro x
    rw [dsum, Nat.count_succ', ih, pow_one]
    simp only [Nat.testBit_div_two]
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, add_comm]

theorem count_lt_and {len M : ℕ} (q : ℕ → Prop) [DecidablePred q] (h : len ≤ M) :
    Nat.count (fun i => i < len ∧ q i) M = Nat.count q len := by
  induction M, h using Nat.le_induction with
  | base =>
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro i hi
    rw [Finset.mem_range] at hi
    simp [hi]
  | succ M hM ih =>
    rw [Nat.count_succ, ih]
    simp only [show ¬ M < len by omega, false_and, if_false, add_zero]

/-- The number of set bits of `B` at positions `a, ..., a + len - 1`, for `len ≤ 32768`. -/
def segCount (B a len : ℕ) : ℕ := pc ((B >>> a) % 2 ^ len)

theorem segCount_eq {len : ℕ} (B a : ℕ) (hlen : len ≤ 32768) :
    segCount B a len = Nat.count (fun i => B.testBit (a + i) = true) len := by
  rw [segCount, pc_eq_dsum, dsum_one_eq_count, ← count_lt_and _ hlen]
  congr 1
  funext i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Bool.and_eq_true, decide_eq_true_iff]

/-! ## Certified tables of prime counts -/

theorem count_congr_lt {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {n : ℕ}
    (h : ∀ i < n, p i ↔ q i) : Nat.count p n = Nat.count q n := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact h i (Finset.mem_range.mp hi)

/-- The list `L` records the number of primes below `f (j + i)` at its index `i`. -/
def Good (f : ℕ → ℕ) (j : ℕ) (L : List ℕ) : Prop :=
  ∀ i < L.length, Nat.count Nat.Prime (f (j + i)) = L.getD i 0

theorem Good.append {f : ℕ → ℕ} {j j' : ℕ} {L1 L2 : List ℕ} (h1 : Good f j L1)
    (h2 : Good f j' L2) (hj : j + L1.length = j') : Good f j (L1 ++ L2) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hlt : i < L1.length
  · rw [List.getD_append _ _ _ _ hlt]
    exact h1 i hlt
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have h := h2 (i - L1.length) (by omega)
    rwa [show j' + (i - L1.length) = j + i by omega] at h

theorem Good.count_eq {f : ℕ → ℕ} {j : ℕ} {L : List ℕ} (h : Good f j L) {i c : ℕ}
    (hi : i < L.length) (hc : L.getD i 0 = c) : Nat.count Nat.Prime (f (j + i)) = c :=
  (h i hi).trans hc

/-- Checker for claimed prime counts along `f j, f (j + 1), ...`, starting from the count `c`
below `f j`, using the bitmask `B` of the primes in the window `[lo, lo + S)`. -/
def chk (f : ℕ → ℕ) (B lo S : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | j, c, v :: l =>
      (lo ≤ f j && f j ≤ f (j + 1) && f (j + 1) - f j ≤ 32768 && f (j + 1) ≤ lo + S &&
        v == c + segCount B (f j - lo) (f (j + 1) - f j)) && chk f B lo S (j + 1) v l

theorem chk_sound (f : ℕ → ℕ) (B lo S : ℕ)
    (hB : ∀ i < S, B.testBit i = true ↔ (lo + i).Prime) (l : List ℕ) :
    ∀ j c : ℕ, chk f B lo S j c l = true → Nat.count Nat.Prime (f j) = c →
      Good f (j + 1) l := by
  induction l with
  | nil => intro j c _ _ i hi; simp at hi
  | cons v l ih =>
    intro j c hchk hc
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
    obtain ⟨⟨⟨⟨⟨hlo, hmono⟩, hgap⟩, hS⟩, hv⟩, hrest⟩ := hchk
    have hcount : Nat.count Nat.Prime (f (j + 1)) = v := by
      have hsplit : f (j + 1) = f j + (f (j + 1) - f j) := by omega
      rw [hsplit, Nat.count_add, hc, hv, segCount_eq _ _ hgap]
      congr 1
      apply count_congr_lt
      intro i hi
      rw [hB _ (by omega), show lo + (f j - lo + i) = f j + i by omega]
    have hgood := ih (j + 1) v hrest hcount
    intro i hi
    rcases i with _ | i
    · simpa using hcount
    · have h := hgood i (by simpa using hi)
      rw [List.getD_cons_succ, ← h, show j + 1 + (i + 1) = j + 1 + 1 + i by omega]

/-! ## The sieving primes: the primes below `11833` -/

/-- The prime bitmask of `[0, 11833)`, sieved by `2, ..., 108`. -/
def smallSieve : ℕ := sieveW 0 11833 (List.range' 2 107)

theorem testBit_smallSieve {i : ℕ} (hi : i < 11833) : smallSieve.testBit i = true ↔ i.Prime := by
  have hpos : ∀ d ∈ List.range' 2 107, 0 < d := by
    intro d hd
    rw [List.mem_range'_1] at hd
    omega
  have hall : ∀ p : ℕ, p.Prime → p * p < 11833 → p ∈ List.range' 2 107 := by
    intro p hp hpp
    have h2 := hp.two_le
    rw [List.mem_range'_1]
    constructor
    · exact h2
    · nlinarith
  have h2 : ∀ d ∈ List.range' 2 107, 2 ≤ d := by
    intro d hd
    rw [List.mem_range'_1] at hd
    omega
  rw [smallSieve, testBit_sieveW hi _ hpos,
    sieve_cond_iff_prime (by omega : 0 + i < 11833) _ hall h2, zero_add]


/-- The primes below `11833`. -/
def ds : List ℕ := [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
    193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
    307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
    421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
    547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653,
    659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
    797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919,
    929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033,
    1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129,
    1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249,
    1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367,
    1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481,
    1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579,
    1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693,
    1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801,
    1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931,
    1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039,
    2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143,
    2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281,
    2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383,
    2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521,
    2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657,
    2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731,
    2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851,
    2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971,
    2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119,
    3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253,
    3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361,
    3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499,
    3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607,
    3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719,
    3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851,
    3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967,
    3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093,
    4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229,
    4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349,
    4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483,
    4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621,
    4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733,
    4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889,
    4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999,
    5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113,
    5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273,
    5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413,
    5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519,
    5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653,
    5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783,
    5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879,
    5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047,
    6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173,
    6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299,
    6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397,
    6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569,
    6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701,
    6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829,
    6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961,
    6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079,
    7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229,
    7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393,
    7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529,
    7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639,
    7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757,
    7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907,
    7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069,
    8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209,
    8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317,
    8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467,
    8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627,
    8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737,
    8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861,
    8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007,
    9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151,
    9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281,
    9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413,
    9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521,
    9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677,
    9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803,
    9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929,
    9931, 9941, 9949, 9967, 9973, 10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079, 10091,
    10093, 10099, 10103, 10111, 10133, 10139, 10141, 10151, 10159, 10163, 10169, 10177, 10181,
    10193, 10211, 10223, 10243, 10247, 10253, 10259, 10267, 10271, 10273, 10289, 10301, 10303,
    10313, 10321, 10331, 10333, 10337, 10343, 10357, 10369, 10391, 10399, 10427, 10429, 10433,
    10453, 10457, 10459, 10463, 10477, 10487, 10499, 10501, 10513, 10529, 10531, 10559, 10567,
    10589, 10597, 10601, 10607, 10613, 10627, 10631, 10639, 10651, 10657, 10663, 10667, 10687,
    10691, 10709, 10711, 10723, 10729, 10733, 10739, 10753, 10771, 10781, 10789, 10799, 10831,
    10837, 10847, 10853, 10859, 10861, 10867, 10883, 10889, 10891, 10903, 10909, 10937, 10939,
    10949, 10957, 10973, 10979, 10987, 10993, 11003, 11027, 11047, 11057, 11059, 11069, 11071,
    11083, 11087, 11093, 11113, 11117, 11119, 11131, 11149, 11159, 11161, 11171, 11173, 11177,
    11197, 11213, 11239, 11243, 11251, 11257, 11261, 11273, 11279, 11287, 11299, 11311, 11317,
    11321, 11329, 11351, 11353, 11369, 11383, 11393, 11399, 11411, 11423, 11437, 11443, 11447,
    11467, 11471, 11483, 11489, 11491, 11497, 11503, 11519, 11527, 11549, 11551, 11579, 11587,
    11593, 11597, 11617, 11621, 11633, 11657, 11677, 11681, 11689, 11699, 11701, 11717, 11719,
    11731, 11743, 11777, 11779, 11783, 11789, 11801, 11807, 11813, 11821, 11827, 11831]

theorem ds_eq : ds = (List.range 11833).filter (fun p => smallSieve.testBit p) := by
  decide +kernel

theorem mem_ds {p : ℕ} : p ∈ ds ↔ p < 11833 ∧ p.Prime := by
  rw [ds_eq, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hp, hbit⟩
    exact ⟨hp, (testBit_smallSieve hp).mp hbit⟩
  · rintro ⟨hp, hprime⟩
    exact ⟨hp, (testBit_smallSieve hp).mpr hprime⟩

/-- Sieving by `ds` is exact below `11833 ^ 2`. -/
def NMax : ℕ := 11833 * 11833

theorem testBit_sieveW_ds {lo S : ℕ} (hN : lo + S ≤ NMax) :
    ∀ i < S, (sieveW lo S ds).testBit i = true ↔ (lo + i).Prime := by
  intro i hi
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => (mem_ds.mp hd).2.pos
  have h2 : ∀ d ∈ ds, 2 ≤ d := fun d hd => (mem_ds.mp hd).2.two_le
  have hall : ∀ p : ℕ, p.Prime → p * p < NMax → p ∈ ds := by
    intro p hp hpp
    refine mem_ds.mpr ⟨?_, hp⟩
    by_contra hbig
    unfold NMax at hpp
    nlinarith
  rw [testBit_sieveW hi _ hpos, sieve_cond_iff_prime (by omega : lo + i < NMax) _ hall h2]

/-! ## The two point sequences -/

/-- The number of primes below `fA k` is `π(k(k+1)/2)`. -/
def fA (k : ℕ) : ℕ := k * (k + 1) / 2 + 1

/-- The number of primes below `fB m` is `π(m ^ 2)`. -/
def fB (m : ℕ) : ℕ := m ^ 2 + 1

theorem count_fA (k : ℕ) : Nat.count Nat.Prime (fA k) = Nat.primeCounting (k * (k + 1) / 2) := rfl

theorem count_fB (m : ℕ) : Nat.count Nat.Prime (fB m) = Nat.primeCounting (m ^ 2) := rfl

/-- One window `[lo, lo + S)`, sieved once, checks a run of each sequence. -/
def chk2 (lo S jA cA : ℕ) (LA : List ℕ) (jB cB : ℕ) (LB : List ℕ) : Bool :=
  chk fA (sieveW lo S ds) lo S jA cA LA && chk fB (sieveW lo S ds) lo S jB cB LB

theorem chk2_sound {lo S jA cA : ℕ} {LA : List ℕ} {jB cB : ℕ} {LB : List ℕ}
    (hN : lo + S ≤ NMax) (h : chk2 lo S jA cA LA jB cB LB = true)
    (hA : Nat.count Nat.Prime (fA jA) = cA) (hB : Nat.count Nat.Prime (fB jB) = cB) :
    Good fA (jA + 1) LA ∧ Good fB (jB + 1) LB := by
  rw [chk2, Bool.and_eq_true] at h
  exact ⟨chk_sound fA _ lo S (testBit_sieveW_ds hN) LA jA cA h.1 hA,
    chk_sound fB _ lo S (testBit_sieveW_ds hN) LB jB cB h.2 hB⟩

theorem hc0A : Nat.count Nat.Prime (fA 0) = 0 := by decide

theorem hc0B : Nat.count Nat.Prime (fB 0) = 0 := by decide

/-! ## The windows

Window `w` is `[w * 2 ^ 20, w * 2 ^ 20 + 2 ^ 20 + 2 ^ 15)`. `LA_w` lists `π(T_k)` and `LB_w`
lists `π(m ^ 2)` for the points whose previous point lies in `[w * 2 ^ 20, (w + 1) * 2 ^ 20)`.
-/

def LA_0 : List ℕ := [
    0, 2, 3, 4, 6, 8, 9, 11, 14, 16, 18, 21, 24, 27, 30, 32, 36, 39, 42, 46, 50, 54, 58, 62, 66,
    70, 74, 79, 84, 90, 94, 99, 102, 108, 114, 121, 126, 131, 137, 141, 149, 154, 160, 166, 174,
    180, 188, 193, 200, 205, 216, 220, 226, 235, 242, 250, 259, 267, 274, 281, 290, 297, 305, 312,
    324, 329, 338, 347, 358, 367, 374, 381, 393, 403, 413, 422, 431, 440, 446, 457, 467, 478, 487,
    499, 510, 522, 531, 541, 552, 564, 574, 587, 596, 607, 617, 629, 640, 650, 661, 675, 686, 697,
    708, 721, 734, 747, 757, 775, 783, 796, 808, 823, 836, 847, 859, 873, 887, 903, 914, 928, 938,
    950, 968, 982, 994, 1007, 1022, 1035, 1049, 1061, 1076, 1093, 1108, 1124, 1137, 1152, 1170,
    1184, 1199, 1217, 1231, 1246, 1262, 1277, 1290, 1308, 1322, 1336, 1354, 1369, 1383, 1398,
    1411, 1430, 1446, 1463, 1480, 1500, 1518, 1532, 1553, 1570, 1585, 1602, 1619, 1637, 1654,
    1669, 1683, 1701, 1720, 1742, 1757, 1776, 1799, 1816, 1837, 1857, 1875, 1891, 1908, 1926,
    1943, 1961, 1981, 2000, 2020, 2039, 2057, 2080, 2101, 2122, 2137, 2152, 2169, 2188, 2213,
    2230, 2250, 2271, 2293, 2313, 2330, 2352, 2373, 2394, 2416, 2437, 2460, 2484, 2502, 2524,
    2547, 2565, 2591, 2609, 2631, 2654, 2679, 2700, 2721, 2738, 2759, 2781, 2803, 2825, 2847,
    2868, 2893, 2915, 2939, 2963, 2984, 3004, 3022, 3052, 3074, 3095, 3124, 3147, 3169, 3195,
    3217, 3238, 3259, 3282, 3302, 3330, 3352, 3380, 3401, 3424, 3447, 3476, 3503, 3525, 3553,
    3578, 3607, 3632, 3653, 3679, 3707, 3731, 3754, 3780, 3801, 3829, 3854, 3879, 3907, 3935,
    3960, 3990, 4009, 4034, 4059, 4086, 4112, 4140, 4166, 4196, 4221, 4241, 4266, 4295, 4324,
    4352, 4381, 4411, 4444, 4473, 4502, 4522, 4549, 4572, 4604, 4632, 4660, 4687, 4714, 4739,
    4765, 4794, 4822, 4849, 4873, 4905, 4935, 4963, 4990, 5022, 5051, 5081, 5110, 5141, 5172,
    5197, 5224, 5254, 5289, 5319, 5349, 5375, 5406, 5437, 5465, 5497, 5521, 5557, 5585, 5615,
    5641, 5679, 5709, 5741, 5776, 5811, 5836, 5870, 5903, 5933, 5962, 5996, 6033, 6060, 6091,
    6120, 6152, 6179, 6214, 6243, 6273, 6304, 6333, 6369, 6407, 6434, 6462, 6492, 6526, 6563,
    6595, 6623, 6656, 6691, 6727, 6762, 6794, 6822, 6855, 6885, 6914, 6949, 6985, 7016, 7053,
    7091, 7128, 7164, 7197, 7232, 7260, 7295, 7330, 7363, 7399, 7434, 7472, 7503, 7537, 7570,
    7606, 7649, 7681, 7713, 7746, 7782, 7813, 7852, 7885, 7926, 7965, 8000, 8038, 8078, 8109,
    8145, 8178, 8214, 8250, 8283, 8321, 8357, 8393, 8429, 8464, 8502, 8542, 8569, 8605, 8644,
    8686, 8726, 8763, 8798, 8835, 8869, 8908, 8949, 8991, 9032, 9065, 9102, 9143, 9184, 9222,
    9261, 9299, 9339, 9373, 9410, 9443, 9482, 9526, 9563, 9600, 9641, 9675, 9716, 9759, 9804,
    9841, 9872, 9911, 9952, 9989, 10031, 10073, 10108, 10151, 10193, 10229, 10264, 10306, 10344,
    10388, 10430, 10465, 10508, 10549, 10586, 10627, 10668, 10708, 10752, 10790, 10828, 10868,
    10909, 10958, 10995, 11033, 11076, 11121, 11159, 11200, 11243, 11282, 11326, 11367, 11411,
    11458, 11501, 11543, 11583, 11630, 11671, 11712, 11756, 11800, 11843, 11885, 11920, 11969,
    12007, 12055, 12100, 12146, 12186, 12232, 12271, 12314, 12355, 12403, 12448, 12488, 12535,
    12572, 12617, 12665, 12714, 12761, 12805, 12846, 12896, 12934, 12978, 13022, 13071, 13117,
    13166, 13210, 13252, 13289, 13337, 13378, 13422, 13466, 13516, 13559, 13603, 13651, 13693,
    13738, 13789, 13838, 13886, 13930, 13979, 14030, 14076, 14123, 14168, 14214, 14260, 14307,
    14357, 14395, 14441, 14493, 14535, 14582, 14623, 14677, 14721, 14770, 14817, 14862, 14909,
    14955, 15005, 15057, 15094, 15143, 15185, 15233, 15287, 15332, 15373, 15418, 15465, 15517,
    15570, 15615, 15665, 15716, 15765, 15812, 15864, 15912, 15952, 16002, 16062, 16108, 16150,
    16202, 16257, 16313, 16366, 16410, 16451, 16503, 16558, 16604, 16656, 16706, 16757, 16810,
    16869, 16915, 16970, 17014, 17064, 17115, 17172, 17216, 17267, 17318, 17369, 17424, 17475,
    17525, 17573, 17625, 17678, 17726, 17778, 17832, 17884, 17932, 17988, 18035, 18084, 18141,
    18188, 18236, 18289, 18341, 18391, 18446, 18502, 18552, 18611, 18664, 18716, 18774, 18834,
    18887, 18940, 18992, 19036, 19090, 19145, 19202, 19249, 19299, 19349, 19406, 19454, 19508,
    19563, 19624, 19675, 19729, 19787, 19835, 19899, 19947, 20003, 20057, 20113, 20167, 20220,
    20271, 20330, 20389, 20452, 20509, 20563, 20618, 20669, 20715, 20769, 20827, 20880, 20928,
    20983, 21032, 21093, 21148, 21202, 21258, 21314, 21375, 21435, 21488, 21542, 21605, 21659,
    21716, 21773, 21830, 21890, 21953, 22011, 22064, 22114, 22179, 22235, 22288, 22347, 22400,
    22466, 22521, 22577, 22630, 22685, 22749, 22801, 22858, 22914, 22970, 23024, 23080, 23141,
    23197, 23259, 23319, 23375, 23442, 23508, 23564, 23626, 23683, 23743, 23801, 23862, 23918,
    23972, 24031, 24093, 24156, 24213, 24270, 24330, 24384, 24443, 24504, 24567, 24631, 24693,
    24747, 24809, 24871, 24930, 24986, 25039, 25093, 25159, 25218, 25286, 25346, 25401, 25463,
    25516, 25579, 25639, 25696, 25762, 25814, 25877, 25932, 25990, 26054, 26120, 26178, 26242,
    26308, 26373, 26438, 26500, 26566, 26630, 26682, 26747, 26805, 26869, 26924, 26990, 27051,
    27122, 27185, 27245, 27307, 27373, 27442, 27506, 27576, 27644, 27703, 27768, 27833, 27894,
    27951, 28026, 28092, 28150, 28219, 28286, 28343, 28412, 28478, 28542, 28607, 28665, 28729,
    28792, 28858, 28922, 28991, 29056, 29118, 29178, 29241, 29307, 29376, 29435, 29502, 29568,
    29630, 29701, 29770, 29831, 29896, 29964, 30024, 30098, 30164, 30232, 30299, 30369, 30436,
    30496, 30555, 30623, 30694, 30755, 30810, 30877, 30949, 31011, 31079, 31147, 31215, 31284,
    31356, 31421, 31483, 31542, 31599, 31664, 31733, 31801, 31864, 31943, 32009, 32078, 32141,
    32207, 32280, 32345, 32412, 32473, 32542, 32613, 32682, 32752, 32826, 32883, 32949, 33016,
    33089, 33163, 33230, 33308, 33385, 33449, 33522, 33585, 33653, 33722, 33794, 33864, 33928,
    33988, 34057, 34125, 34200, 34257, 34328, 34389, 34463, 34537, 34610, 34681, 34753, 34826,
    34885, 34956, 35031, 35101, 35169, 35242, 35320, 35389, 35459, 35529, 35593, 35672, 35746,
    35819, 35881, 35950, 36025, 36086, 36172, 36243, 36316, 36394, 36470, 36541, 36625, 36694,
    36764, 36825, 36894, 36971, 37047, 37118, 37197, 37278, 37355, 37417, 37483, 37552, 37617,
    37694, 37773, 37851, 37918, 37979, 38053, 38129, 38196, 38278, 38343, 38418, 38483, 38555,
    38620, 38686, 38769, 38853, 38925, 38987, 39069, 39151, 39220, 39304, 39380, 39453, 39523,
    39604, 39686, 39765, 39829, 39907, 39983, 40060, 40135, 40212, 40288, 40363, 40422, 40494,
    40570, 40652, 40731, 40808, 40885, 40955, 41031, 41107, 41191, 41273, 41343, 41418, 41497,
    41579, 41658, 41724, 41795, 41871, 41957, 42029, 42106, 42181, 42251, 42334, 42413, 42478,
    42562, 42640, 42707, 42794, 42885, 42956, 43037, 43114, 43194, 43276, 43350, 43419, 43507,
    43592, 43667, 43740, 43817, 43901, 43972, 44055, 44134, 44203, 44279, 44371, 44441, 44521,
    44592, 44668, 44753, 44835, 44908, 44980, 45058, 45136, 45214, 45298, 45379, 45461, 45535,
    45618, 45700, 45765, 45857, 45928, 46004, 46093, 46177, 46241, 46329, 46409, 46489, 46566,
    46636, 46720, 46801, 46891, 46972, 47060, 47137, 47212, 47296, 47379, 47458, 47538, 47620,
    47708, 47785, 47872, 47948, 48037, 48123, 48215, 48291, 48368, 48445, 48522, 48613, 48694,
    48778, 48859, 48946, 49020, 49101, 49185, 49268, 49352, 49437, 49520, 49599, 49684, 49767,
    49857, 49938, 50022, 50104, 50184, 50268, 50360, 50449, 50525, 50607, 50695, 50775, 50850,
    50940, 51022, 51098, 51179, 51258, 51341, 51413, 51507, 51589, 51676, 51766, 51850, 51939,
    52004, 52088, 52168, 52250, 52326, 52419, 52508, 52590, 52683, 52764, 52852, 52933, 53020,
    53103, 53195, 53275, 53358, 53443, 53526, 53621, 53702, 53790, 53879, 53972, 54052, 54139,
    54216, 54301, 54389, 54480, 54564, 54649, 54738, 54820, 54899, 54994, 55092, 55181, 55265,
    55350, 55435, 55527, 55612, 55702, 55789, 55871, 55960, 56047, 56139, 56229, 56313, 56405,
    56483, 56569, 56657, 56748, 56833, 56935, 57020, 57107, 57206, 57290, 57388, 57474, 57567,
    57642, 57732, 57824, 57901, 57985, 58073, 58172, 58257, 58355, 58448, 58533, 58627, 58716,
    58801, 58889, 58980, 59067, 59161, 59257, 59340, 59428, 59526, 59614, 59701, 59784, 59863,
    59945, 60032, 60121, 60214, 60301, 60402, 60487, 60588, 60679, 60757, 60846, 60938, 61036,
    61135, 61220, 61316, 61411, 61510, 61596, 61689, 61786, 61878, 61966, 62061, 62146, 62232,
    62329, 62423, 62507, 62608, 62697, 62793, 62891, 62974, 63070, 63165, 63258, 63348, 63445,
    63544, 63634, 63734, 63828, 63910, 64019, 64103, 64189, 64282, 64386, 64471, 64558, 64654,
    64752, 64844, 64940, 65030, 65121, 65219, 65307, 65407, 65503, 65599, 65697, 65793, 65894,
    65989, 66079, 66167, 66263, 66371, 66465, 66550, 66645, 66734, 66828, 66919, 67015, 67113,
    67208, 67300, 67391, 67489, 67585, 67679, 67775, 67865, 67959, 68054, 68156, 68247, 68344,
    68443, 68551, 68634, 68739, 68834, 68937, 69036, 69138, 69222, 69321, 69410, 69518, 69613,
    69707, 69810, 69912, 70006, 70106, 70194, 70296, 70396, 70496, 70584, 70683, 70783, 70885,
    70983, 71073, 71176, 71262, 71359, 71454, 71545, 71649, 71748, 71856, 71962, 72061, 72164,
    72254, 72339, 72436, 72538, 72641, 72737, 72835, 72940, 73043, 73148, 73249, 73339, 73441,
    73538, 73633, 73730, 73840, 73931, 74028, 74128, 74223, 74330, 74433, 74535, 74627, 74717,
    74816, 74916, 75023, 75121, 75218, 75315, 75404, 75504, 75603, 75709, 75812, 75917, 76019,
    76118, 76213, 76316, 76417, 76530, 76625, 76733, 76832, 76919, 77026, 77113, 77217, 77316,
    77412, 77517, 77617, 77712, 77817, 77918, 78018, 78118, 78218, 78326, 78433, 78531, 78638,
    78747, 78844, 78944, 79055, 79167, 79268, 79372, 79478, 79581, 79685, 79791, 79883, 79995,
    80105, 80206, 80306, 80413, 80518, 80619, 80726, 80826, 80923, 81032, 81133, 81237, 81339,
    81433, 81542, 81643, 81752, 81856, 81958, 82061]

def LB_0 : List ℕ := [
    0, 2, 4, 6, 9, 11, 15, 18, 22, 25, 30, 34, 39, 44, 48, 54, 61, 66, 72, 78, 85, 92, 99, 105,
    114, 122, 129, 137, 146, 154, 162, 172, 181, 191, 200, 210, 219, 228, 240, 251, 263, 274, 283,
    295, 306, 319, 329, 342, 357, 367, 378, 393, 409, 421, 434, 445, 457, 474, 487, 503, 519, 532,
    549, 564, 578, 594, 609, 624, 641, 654, 675, 690, 705, 722, 739, 757, 779, 793, 811, 834, 847,
    867, 886, 906, 923, 939, 960, 982, 1000, 1018, 1038, 1058, 1077, 1100, 1121, 1142, 1163, 1185,
    1208, 1229, 1252, 1274, 1294, 1315, 1336, 1357, 1381, 1400, 1423, 1447, 1471, 1498, 1523,
    1547, 1572, 1594, 1617, 1646, 1667, 1686, 1715, 1743, 1766, 1796, 1821, 1848, 1877, 1900,
    1924, 1948, 1976, 2004, 2032, 2057, 2088, 2118, 2141, 2163, 2190, 2223, 2248, 2281, 2310,
    2334, 2366, 2392, 2426, 2456, 2489, 2515, 2547, 2580, 2607, 2637, 2672, 2702, 2729, 2757,
    2788, 2818, 2851, 2883, 2915, 2951, 2980, 3010, 3043, 3076, 3107, 3145, 3178, 3211, 3241,
    3274, 3302, 3338, 3377, 3407, 3436, 3476, 3512, 3551, 3585, 3625, 3656, 3695, 3731, 3765,
    3795, 3834, 3868, 3908, 3945, 3986, 4018, 4052, 4089, 4127, 4164, 4203, 4236, 4271, 4313,
    4352, 4396, 4436, 4480, 4515, 4551, 4589, 4627, 4669, 4707, 4743, 4781, 4821, 4857, 4899,
    4942, 4978, 5022, 5065, 5106, 5152, 5191, 5229, 5274, 5318, 5356, 5397, 5442, 5483, 5522,
    5570, 5611, 5652, 5698, 5743, 5792, 5835, 5882, 5926, 5968, 6018, 6059, 6101, 6147, 6186,
    6232, 6275, 6320, 6365, 6414, 6454, 6495, 6542, 6595, 6636, 6684, 6735, 6783, 6823, 6869,
    6910, 6960, 7007, 7057, 7108, 7161, 7206, 7252, 7300, 7351, 7399, 7450, 7499, 7544, 7594,
    7650, 7694, 7743, 7789, 7842, 7891, 7950, 7999, 8053, 8103, 8152, 8198, 8251, 8303, 8354,
    8405, 8452, 8506, 8555, 8600, 8657, 8713, 8769, 8821, 8870, 8928, 8985, 9041, 9089, 9147,
    9205, 9260, 9309, 9361, 9416, 9466, 9525, 9580, 9631, 9685, 9745, 9805, 9855, 9907, 9964,
    10022, 10077, 10127, 10191, 10238, 10298, 10353, 10415, 10466, 10523, 10580, 10639, 10690,
    10756, 10811, 10867, 10921, 10987, 11041, 11098, 11159, 11214, 11274, 11335, 11399, 11460,
    11522, 11578, 11641, 11701, 11762, 11823, 11882, 11936, 11998, 12064, 12131, 12187, 12248,
    12307, 12366, 12433, 12490, 12553, 12613, 12677, 12751, 12813, 12873, 12934, 12997, 13062,
    13129, 13196, 13255, 13314, 13372, 13435, 13499, 13566, 13631, 13692, 13756, 13829, 13895,
    13960, 14034, 14100, 14164, 14228, 14293, 14360, 14420, 14490, 14552, 14615, 14683, 14752,
    14818, 14877, 14951, 15018, 15084, 15146, 15209, 15283, 15346, 15406, 15473, 15548, 15613,
    15687, 15758, 15823, 15894, 15953, 16030, 16104, 16165, 16242, 16318, 16393, 16449, 16522,
    16594, 16667, 16735, 16813, 16886, 16964, 17027, 17097, 17175, 17243, 17317, 17388, 17463,
    17531, 17607, 17678, 17746, 17823, 17897, 17969, 18038, 18108, 18185, 18259, 18324, 18399,
    18475, 18549, 18627, 18707, 18784, 18866, 18942, 19012, 19084, 19157, 19231, 19304, 19373,
    19451, 19530, 19614, 19688, 19765, 19836, 19918, 19993, 20074, 20148, 20224, 20301, 20385,
    20476, 20548, 20621, 20694, 20768, 20851, 20919, 20997, 21068, 21150, 21231, 21310, 21395,
    21470, 21549, 21634, 21714, 21799, 21876, 21964, 22044, 22115, 22204, 22282, 22363, 22441,
    22529, 22599, 22679, 22765, 22845, 22925, 23000, 23079, 23168, 23247, 23332, 23415, 23511,
    23594, 23676, 23760, 23849, 23925, 24000, 24091, 24179, 24258, 24341, 24421, 24507, 24601,
    24684, 24760, 24856, 24933, 25018, 25089, 25182, 25267, 25356, 25438, 25516, 25602, 25684,
    25775, 25855, 25936, 26020, 26112, 26193, 26290, 26380, 26476, 26565, 26646, 26734, 26820,
    26906, 26992, 27082, 27177, 27261, 27356, 27445, 27543, 27641, 27729, 27820, 27903, 27996,
    28092, 28176, 28274, 28361, 28453, 28546, 28632, 28725, 28818, 28904, 29001, 29096, 29178,
    29269, 29361, 29454, 29544, 29636, 29731, 29827, 29914, 30010, 30103, 30201, 30294, 30397,
    30482, 30568, 30667, 30757, 30835, 30940, 31033, 31126, 31221, 31324, 31417, 31497, 31587,
    31675, 31774, 31864, 31973, 32069, 32157, 32255, 32349, 32442, 32538, 32637, 32736, 32830,
    32917, 33013, 33118, 33216, 33326, 33427, 33525, 33613, 33713, 33813, 33910, 33996, 34094,
    34193, 34286, 34373, 34478, 34579, 34681, 34786, 34875, 34978, 35083, 35174, 35278, 35383,
    35483, 35578, 35684, 35787, 35880, 35977, 36075, 36183, 36287, 36398, 36503, 36615, 36714,
    36806, 36903, 37011, 37115, 37227, 37339, 37430, 37525, 37619, 37728, 37837, 37933, 38030,
    38136, 38236, 38337, 38442, 38538, 38629, 38734, 38853, 38950, 39053, 39164, 39275, 39387,
    39485, 39596, 39715, 39809, 39921, 40026, 40132, 40243, 40348, 40433, 40542, 40654, 40766,
    40874, 40978, 41084, 41202, 41306, 41412, 41527, 41643, 41737, 41840, 41957, 42065, 42169,
    42275, 42385, 42486, 42602, 42701, 42820, 42938, 43048, 43157, 43274, 43378, 43491, 43610,
    43715, 43823, 43934, 44045, 44155, 44256, 44381, 44483, 44588, 44699, 44813, 44921, 45030,
    45137, 45251, 45364, 45481, 45589, 45704, 45805, 45922, 46029, 46158, 46257, 46369, 46487,
    46596, 46706, 46821, 46940, 47064, 47173, 47287, 47406, 47520, 47631, 47753, 47869, 47982,
    48100, 48233, 48340, 48446, 48561, 48680, 48801, 48916, 49030, 49145, 49262, 49377, 49501,
    49613, 49733, 49857, 49968, 50086, 50203, 50327, 50458, 50568, 50685, 50799, 50916, 51035,
    51145, 51256, 51367, 51489, 51609, 51730, 51854, 51967, 52074, 52192, 52306, 52431, 52553,
    52676, 52798, 52913, 53037, 53156, 53275, 53397, 53514, 53645, 53761, 53886, 54013, 54129,
    54244, 54367, 54495, 54614, 54738, 54858, 54979, 55114, 55234, 55356, 55477, 55602, 55729,
    55851, 55969, 56100, 56222, 56350, 56465, 56585, 56707, 56836, 56969, 57097, 57225, 57356,
    57482, 57605, 57726, 57848, 57963, 58090, 58225, 58355, 58479, 58608, 58733, 58858, 58986,
    59113, 59248, 59372, 59502, 59622, 59746, 59862, 59981, 60105, 60236, 60364, 60490, 60629,
    60749, 60872, 61008, 61145, 61269, 61408, 61539, 61670, 61802, 61929, 62061, 62182, 62313,
    62444, 62578, 62705, 62838, 62968, 63105, 63229, 63363, 63498, 63632, 63768, 63894, 64040,
    64162, 64288, 64432, 64547, 64683, 64820, 64950, 65077, 65215, 65335, 65479, 65616, 65755,
    65895, 66032, 66156, 66296, 66436, 66557, 66692, 66824, 66950, 67090, 67230, 67353, 67488,
    67626, 67761, 67886, 68018, 68163, 68294, 68436, 68578, 68707, 68848, 68991, 69134, 69264,
    69389, 69537, 69669, 69813, 69957, 70089, 70221, 70361, 70503, 70633, 70774, 70913, 71052,
    71194, 71319, 71454, 71583, 71727, 71879, 72035, 72170, 72291, 72426, 72568, 72709, 72848,
    72992, 73146, 73284, 73421, 73558, 73696, 73843, 73979, 74114, 74253, 74399, 74547, 74676,
    74812, 74953, 75096, 75236, 75374, 75506, 75647, 75795, 75943, 76082, 76223, 76366, 76520,
    76656, 76806, 76938, 77072, 77214, 77354, 77497, 77637, 77780, 77928, 78060, 78208, 78359,
    78498, 78650, 78803, 78941, 79099, 79252, 79390, 79540, 79689, 79830, 79981, 80131, 80273,
    80426, 80573, 80721, 80848, 81006, 81154, 81298, 81433, 81588, 81737, 81880, 82025]

def LA_1 : List ℕ := [
    82171, 82266, 82364, 82469, 82573, 82672, 82781, 82886, 82980, 83080, 83194, 83293, 83398,
    83504, 83616, 83717, 83820, 83932, 84045, 84142, 84246, 84366, 84472, 84573, 84672, 84780,
    84885, 84979, 85095, 85202, 85319, 85432, 85535, 85633, 85746, 85848, 85962, 86071, 86181,
    86288, 86401, 86506, 86623, 86731, 86838, 86944, 87055, 87151, 87268, 87365, 87468, 87573,
    87679, 87793, 87898, 88011, 88125, 88233, 88343, 88447, 88553, 88654, 88765, 88868, 88979,
    89079, 89186, 89291, 89412, 89514, 89624, 89731, 89849, 89963, 90071, 90183, 90307, 90419,
    90529, 90635, 90747, 90856, 90961, 91065, 91177, 91288, 91404, 91524, 91638, 91751, 91865,
    91972, 92089, 92201, 92311, 92420, 92533, 92642, 92755, 92857, 92968, 93073, 93180, 93286,
    93391, 93495, 93601, 93712, 93832, 93951, 94061, 94181, 94285, 94394, 94504, 94612, 94724,
    94842, 94944, 95056, 95173, 95275, 95376, 95477, 95594, 95711, 95821, 95930, 96045, 96152,
    96272, 96391, 96510, 96615, 96715, 96843, 96951, 97075, 97188, 97296, 97413, 97519, 97651,
    97763, 97878, 97996, 98104, 98225, 98325, 98436, 98551, 98661, 98778, 98892, 99004, 99125,
    99244, 99358, 99464, 99579, 99687, 99803, 99915, 100026, 100144, 100261, 100373, 100489,
    100595, 100712, 100836, 100949, 101058, 101165, 101286, 101403, 101504, 101643, 101756,
    101868, 101984, 102095, 102204, 102324, 102442, 102546, 102667, 102784, 102904, 103028,
    103145, 103253, 103364, 103479, 103587, 103705, 103819, 103938, 104066, 104171, 104291,
    104407, 104522, 104647, 104758, 104877, 104993, 105108, 105222, 105339, 105457, 105586,
    105710, 105830, 105934, 106051, 106175, 106289, 106402, 106524, 106632, 106756, 106885,
    107021, 107146, 107254, 107368, 107484, 107591, 107713, 107831, 107951, 108081, 108179,
    108288, 108401, 108518, 108638, 108757, 108879, 109007, 109121, 109235, 109366, 109492,
    109625, 109741, 109864, 109978, 110097, 110213, 110334, 110464, 110573, 110702, 110817,
    110934, 111073, 111180, 111298, 111418, 111553, 111669, 111799, 111913, 112028, 112139,
    112267, 112386, 112491, 112627, 112756, 112873, 113001, 113120, 113236, 113355, 113491,
    113612, 113742, 113863, 113987, 114097, 114216, 114340, 114464, 114602, 114725, 114848,
    114975, 115094, 115225, 115340, 115465, 115582, 115698, 115813, 115947, 116061, 116180,
    116304, 116416, 116530, 116654, 116780, 116905, 117033, 117152, 117261, 117386, 117514,
    117643, 117759, 117888, 118002, 118139, 118260, 118398, 118505, 118628, 118757, 118885,
    118994, 119119, 119255, 119378, 119498, 119623, 119741, 119866, 119984, 120111, 120228,
    120343, 120482, 120591, 120709, 120846, 120965, 121088, 121208, 121352, 121492, 121607,
    121732, 121854, 121987, 122099, 122224, 122347, 122476, 122602, 122728, 122854, 122986,
    123118, 123245, 123367, 123499, 123640, 123765, 123872, 123995, 124113, 124247, 124374,
    124501, 124625, 124752, 124882, 125017, 125151, 125263, 125391, 125510, 125631, 125759,
    125907, 126041, 126165, 126284, 126421, 126547, 126685, 126814, 126941, 127049, 127188,
    127315, 127430, 127564, 127693, 127817, 127946, 128084, 128218, 128357, 128470, 128598,
    128728, 128860, 128987, 129106, 129240, 129366, 129490, 129619, 129744, 129874, 130005,
    130130, 130257, 130385, 130514, 130640, 130764, 130903, 131034, 131158, 131281, 131425,
    131567, 131698, 131838, 131965, 132088, 132215, 132329, 132447, 132583, 132711, 132840,
    132972, 133099, 133232, 133367, 133498, 133634, 133768, 133902, 134036, 134161, 134290,
    134419, 134556, 134683, 134821, 134949, 135089, 135222, 135344, 135480, 135618, 135754,
    135888, 136013, 136152, 136278, 136399, 136538, 136664, 136814, 136951, 137087, 137222,
    137361, 137489, 137614, 137735, 137860, 137991, 138135, 138266, 138406, 138540, 138669,
    138805, 138948, 139083, 139221, 139351, 139484, 139624, 139772, 139907, 140033, 140165,
    140293, 140431, 140573, 140696, 140838, 140967, 141104, 141238, 141381, 141513, 141657,
    141789, 141920, 142049, 142177, 142311, 142438, 142580, 142720, 142857, 142995, 143137,
    143280, 143404, 143541, 143670, 143804, 143958, 144098, 144233, 144363, 144496, 144629,
    144767, 144910, 145048, 145183, 145329, 145459, 145591, 145720, 145872, 146003, 146130,
    146269, 146411, 146537, 146676, 146804, 146930, 147063, 147189, 147327, 147460, 147609,
    147755, 147890, 148019, 148162, 148296, 148436, 148573, 148719, 148867, 149002, 149139,
    149277, 149414, 149569, 149699, 149835, 149988, 150131, 150266, 150404, 150544, 150672,
    150810, 150958, 151092, 151242, 151389, 151524, 151652, 151793, 151935, 152067, 152210,
    152335, 152478, 152609, 152754, 152891, 153035, 153176, 153309, 153459, 153599, 153737,
    153879, 154020, 154149, 154279, 154431, 154564, 154704, 154839, 154989, 155131, 155270,
    155411, 155546, 155681]

def LB_1 : List ℕ := [
    82174, 82314, 82462, 82606, 82755, 82896, 83030, 83190, 83334, 83483, 83637, 83782, 83936,
    84084, 84231, 84391, 84540, 84683, 84835, 84972, 85131, 85295, 85450, 85597, 85747, 85897,
    86047, 86208, 86370, 86514, 86683, 86831, 86976, 87128, 87286, 87419, 87572, 87724, 87883,
    88038, 88195, 88349, 88494, 88644, 88792, 88943, 89093, 89241, 89405, 89559, 89705, 89873,
    90025, 90187, 90359, 90508, 90665, 90823, 90970, 91124, 91282, 91446, 91613, 91767, 91932,
    92089, 92243, 92404, 92557, 92707, 92864, 93022, 93168, 93313, 93468, 93614, 93779, 93944,
    94102, 94264, 94419, 94573, 94726, 94883, 95042, 95206, 95344, 95490, 95655, 95812, 95966,
    96126, 96295, 96466, 96616, 96768, 96927, 97104, 97262, 97424, 97585, 97750, 97911, 98085,
    98238, 98389, 98544, 98703, 98869, 99033, 99206, 99366, 99519, 99670, 99839, 99992, 100157,
    100325, 100482, 100640, 100805, 100964, 101122, 101288, 101450, 101621, 101789, 101953,
    102107, 102268, 102431, 102588, 102752, 102926, 103092, 103253, 103411, 103561, 103733,
    103893, 104071, 104226, 104394, 104563, 104719, 104891, 105060, 105218, 105383, 105562,
    105733, 105893, 106056, 106224, 106388, 106549, 106722, 106903, 107083, 107249, 107407,
    107564, 107733, 107904, 108081, 108227, 108386, 108547, 108709, 108887, 109066, 109228,
    109408, 109588, 109757, 109928, 110094, 110257, 110433, 110602, 110769, 110940, 111122,
    111285, 111458, 111631, 111810, 111970, 112130, 112309, 112468, 112648, 112829, 113003,
    113166, 113335, 113521, 113692, 113872, 114040, 114204, 114382, 114572, 114739, 114924,
    115093, 115265, 115440, 115605, 115771, 115954, 116114, 116292, 116447, 116616, 116795,
    116972, 117148, 117302, 117484, 117663, 117833, 118004, 118198, 118376, 118539, 118711,
    118898, 119058, 119242, 119415, 119593, 119762, 119932, 120111, 120270, 120461, 120616,
    120799, 120973, 121144, 121334, 121526, 121702, 121871, 122047, 122218, 122393, 122577,
    122756, 122927, 123125, 123301, 123488, 123673, 123841, 124009, 124180, 124364, 124540,
    124723, 124907, 125096, 125264, 125436, 125621, 125796, 125995, 126172, 126345, 126536,
    126726, 126905, 127069, 127258, 127428, 127612, 127791, 127978, 128169, 128362, 128530,
    128713, 128900, 129068, 129253, 129439, 129614, 129785, 129973, 130157, 130329, 130515,
    130699, 130884, 131060, 131240, 131436, 131632, 131827, 132005, 132183, 132352, 132521,
    132709, 132898, 133083, 133268, 133453, 133642, 133831, 134018, 134206, 134375, 134570,
    134761, 134944, 135145, 135325, 135510, 135698, 135891, 136073, 136262, 136435, 136623,
    136826, 137019, 137212, 137398, 137585, 137754, 137938, 138135, 138325, 138517, 138709,
    138901, 139094, 139283, 139468, 139672, 139871, 140049, 140235, 140429, 140619, 140816,
    140994, 141191, 141389, 141582, 141767, 141961, 142136, 142321, 142509, 142711, 142910,
    143102, 143305, 143487, 143673, 143872, 144074, 144270, 144455, 144640, 144840, 145032,
    145236, 145435, 145611, 145812, 146003, 146186, 146382, 146570, 146762, 146939, 147127,
    147311, 147509, 147705, 147905, 148096, 148288, 148492, 148688, 148895, 149081, 149283,
    149486, 149687, 149877, 150086, 150280, 150480, 150667, 150862, 151063, 151270, 151463,
    151652, 151844, 152045, 152239, 152430, 152618, 152810, 153019, 153217, 153427, 153616,
    153820, 154013, 154206, 154402, 154592, 154787, 154994, 155193, 155394, 155577, 155778]

def LA_2 : List ℕ := [
    155821, 155968, 156112, 156257, 156396, 156539, 156673, 156814, 156962, 157109, 157238,
    157380, 157516, 157667, 157808, 157948, 158094, 158225, 158376, 158512, 158655, 158802,
    158961, 159094, 159233, 159370, 159513, 159659, 159814, 159967, 160103, 160249, 160382,
    160517, 160664, 160806, 160953, 161099, 161248, 161381, 161516, 161662, 161802, 161949,
    162094, 162239, 162378, 162524, 162647, 162792, 162933, 163076, 163234, 163383, 163529,
    163653, 163798, 163938, 164073, 164215, 164360, 164509, 164663, 164802, 164946, 165099,
    165246, 165387, 165529, 165668, 165816, 165964, 166098, 166236, 166385, 166546, 166701,
    166849, 166983, 167134, 167287, 167438, 167594, 167748, 167899, 168037, 168177, 168314,
    168447, 168590, 168737, 168886, 169034, 169178, 169316, 169468, 169630, 169773, 169907,
    170057, 170210, 170356, 170492, 170640, 170778, 170919, 171064, 171204, 171356, 171505,
    171641, 171796, 171946, 172091, 172231, 172386, 172530, 172663, 172815, 172963, 173098,
    173258, 173395, 173555, 173697, 173858, 174006, 174158, 174308, 174449, 174585, 174738,
    174882, 175040, 175189, 175331, 175492, 175649, 175798, 175936, 176076, 176243, 176386,
    176537, 176684, 176833, 176965, 177113, 177272, 177422, 177581, 177726, 177882, 178024,
    178175, 178321, 178466, 178613, 178762, 178906, 179058, 179206, 179362, 179510, 179661,
    179817, 179977, 180123, 180274, 180433, 180578, 180740, 180882, 181021, 181176, 181320,
    181473, 181621, 181769, 181922, 182068, 182230, 182382, 182531, 182673, 182829, 182983,
    183133, 183289, 183450, 183591, 183742, 183899, 184057, 184203, 184341, 184498, 184653,
    184827, 184968, 185134, 185290, 185434, 185588, 185738, 185878, 186031, 186189, 186326,
    186487, 186640, 186798, 186942, 187094, 187253, 187415, 187558, 187720, 187871, 188025,
    188181, 188346, 188503, 188671, 188826, 188975, 189128, 189282, 189430, 189594, 189747,
    189901, 190051, 190200, 190348, 190501, 190654, 190806, 190975, 191131, 191274, 191427,
    191585, 191735, 191887, 192060, 192220, 192367, 192514, 192676, 192832, 193003, 193155,
    193308, 193464, 193620, 193795, 193950, 194100, 194256, 194414, 194560, 194697, 194857,
    195015, 195170, 195328, 195481, 195643, 195799, 195962, 196118, 196283, 196436, 196595,
    196757, 196903, 197073, 197231, 197389, 197547, 197707, 197868, 198035, 198177, 198337,
    198483, 198642, 198798, 198954, 199095, 199246, 199414, 199579, 199731, 199894, 200038,
    200202, 200351, 200510, 200670, 200839, 200992, 201155, 201320, 201472, 201629, 201782,
    201943, 202099, 202255, 202424, 202577, 202724, 202887, 203046, 203196, 203373, 203527,
    203701, 203859, 204024, 204197, 204365, 204519, 204683, 204851, 205022, 205177, 205316,
    205485, 205652, 205827, 205999, 206155, 206313, 206464, 206625, 206794, 206950, 207112,
    207261, 207419, 207583, 207744, 207913, 208069, 208218, 208392, 208534, 208690, 208852,
    209016, 209175, 209341, 209504, 209656, 209817, 209971, 210142, 210300, 210464, 210626,
    210795, 210949, 211103, 211267, 211438, 211600, 211768, 211931, 212080, 212247, 212399,
    212568, 212741, 212895, 213047, 213214, 213366, 213539, 213700, 213862, 214009, 214179,
    214346, 214516, 214679, 214851, 215006, 215169, 215326, 215490, 215666, 215834, 215995,
    216146, 216313, 216478, 216643, 216817, 216979, 217150, 217312, 217473, 217650, 217810,
    217963, 218121, 218293, 218443, 218619, 218781, 218939, 219105, 219258, 219430, 219588,
    219766, 219924, 220085, 220242, 220415, 220574, 220741, 220908, 221063, 221212, 221387,
    221562, 221729, 221918, 222083, 222254, 222411, 222580, 222757, 222927, 223097, 223262,
    223422, 223562, 223744, 223916, 224085, 224252, 224409, 224582, 224766, 224932, 225096,
    225256, 225422, 225600, 225761, 225926, 226082, 226256, 226419, 226586]

def LB_2 : List ℕ := [
    155984, 156185, 156387, 156589, 156783, 156992, 157183, 157382, 157576, 157786, 157985,
    158182, 158389, 158586, 158789, 158999, 159200, 159390, 159597, 159813, 160018, 160224,
    160409, 160613, 160814, 161012, 161227, 161423, 161618, 161819, 162029, 162231, 162431,
    162622, 162814, 163026, 163234, 163451, 163638, 163840, 164030, 164228, 164434, 164653,
    164854, 165060, 165266, 165468, 165668, 165873, 166081, 166268, 166485, 166708, 166913,
    167125, 167331, 167548, 167767, 167969, 168172, 168364, 168561, 168769, 168977, 169181,
    169392, 169610, 169815, 170006, 170225, 170426, 170629, 170833, 171030, 171226, 171449,
    171641, 171858, 172067, 172273, 172482, 172672, 172881, 173089, 173295, 173514, 173723,
    173943, 174155, 174352, 174565, 174770, 174979, 175198, 175405, 175632, 175836, 176029,
    176260, 176460, 176678, 176876, 177081, 177299, 177521, 177728, 177941, 178151, 178355,
    178562, 178779, 178972, 179194, 179417, 179625, 179840, 180057, 180272, 180492, 180710,
    180914, 181124, 181330, 181544, 181754, 181962, 182185, 182401, 182605, 182821, 183037,
    183260, 183477, 183684, 183904, 184125, 184325, 184536, 184773, 184984, 185217, 185423,
    185629, 185848, 186054, 186271, 186487, 186706, 186921, 187134, 187359, 187567, 187789,
    188016, 188232, 188462, 188693, 188910, 189124, 189339, 189561, 189778, 189991, 190204,
    190414, 190628, 190859, 191087, 191292, 191516, 191725, 191949, 192185, 192396, 192603,
    192834, 193060, 193284, 193501, 193734, 193962, 194166, 194401, 194610, 194811, 195044,
    195264, 195477, 195706, 195930, 196156, 196383, 196607, 196823, 197052, 197281, 197502,
    197726, 197967, 198171, 198387, 198602, 198829, 199038, 199248, 199486, 199710, 199931,
    200154, 200363, 200587, 200825, 201049, 201277, 201501, 201723, 201942, 202168, 202392,
    202611, 202833, 203061, 203277, 203511, 203750, 203974, 204220, 204450, 204679, 204915,
    205143, 205349, 205583, 205831, 206066, 206287, 206508, 206742, 206965, 207198, 207411,
    207636, 207872, 208091, 208315, 208535, 208757, 208991, 209219, 209447, 209672, 209896,
    210126, 210349, 210581, 210818, 211039, 211263, 211507, 211730, 211956, 212192, 212407,
    212653, 212878, 213095, 213316, 213557, 213784, 214000, 214235, 214475, 214712, 214938,
    215170, 215394, 215635, 215880, 216103, 216330, 216563, 216801, 217039, 217266, 217500,
    217742, 217961, 218191, 218417, 218659, 218885, 219119, 219343, 219569, 219812, 220038,
    220264, 220501, 220731, 220971, 221186, 221424, 221668, 221920, 222153, 222390, 222620,
    222877, 223119, 223345, 223549, 223801, 224040, 224283, 224511, 224766, 224997, 225228,
    225464, 225705, 225942, 226175, 226403, 226635]

def LA_3 : List ℕ := [
    226755, 226918, 227102, 227272, 227434, 227602, 227762, 227946, 228102, 228276, 228457,
    228617, 228788, 228944, 229131, 229292, 229465, 229638, 229809, 229979, 230156, 230331,
    230509, 230669, 230852, 231030, 231186, 231368, 231538, 231705, 231875, 232042, 232219,
    232381, 232554, 232740, 232918, 233073, 233235, 233410, 233574, 233747, 233907, 234081,
    234259, 234428, 234595, 234774, 234940, 235108, 235278, 235466, 235628, 235794, 235963,
    236133, 236320, 236484, 236645, 236819, 236975, 237142, 237316, 237487, 237665, 237844,
    238016, 238180, 238346, 238519, 238701, 238872, 239036, 239199, 239366, 239541, 239728,
    239898, 240061, 240239, 240399, 240569, 240734, 240888, 241051, 241239, 241424, 241602,
    241769, 241936, 242129, 242294, 242463, 242635, 242820, 242995, 243155, 243334, 243506,
    243683, 243879, 244044, 244214, 244403, 244573, 244742, 244913, 245084, 245264, 245443,
    245606, 245792, 245961, 246155, 246328, 246509, 246684, 246854, 247036, 247198, 247374,
    247542, 247713, 247872, 248048, 248235, 248393, 248569, 248732, 248903, 249063, 249231,
    249402, 249579, 249759, 249930, 250099, 250263, 250454, 250619, 250796, 250977, 251160,
    251314, 251496, 251667, 251832, 252003, 252173, 252355, 252536, 252700, 252872, 253041,
    253226, 253400, 253570, 253747, 253926, 254107, 254281, 254464, 254647, 254825, 254995,
    255173, 255341, 255514, 255698, 255875, 256050, 256213, 256404, 256586, 256767, 256945,
    257131, 257315, 257503, 257694, 257871, 258048, 258233, 258427, 258605, 258782, 258964,
    259137, 259311, 259487, 259663, 259838, 260008, 260166, 260335, 260527, 260708, 260871,
    261063, 261236, 261419, 261613, 261791, 261988, 262168, 262340, 262517, 262696, 262884,
    263062, 263246, 263435, 263617, 263796, 263972, 264138, 264331, 264507, 264690, 264880,
    265062, 265251, 265445, 265632, 265807, 265990, 266157, 266335, 266513, 266698, 266886,
    267070, 267251, 267426, 267578, 267761, 267942, 268113, 268292, 268474, 268668, 268852,
    269029, 269214, 269380, 269568, 269736, 269934, 270116, 270299, 270474, 270657, 270846,
    271038, 271231, 271412, 271606, 271778, 271962, 272151, 272319, 272502, 272688, 272883,
    273060, 273251, 273422, 273608, 273788, 273975, 274158, 274337, 274522, 274695, 274875,
    275055, 275231, 275418, 275599, 275794, 275980, 276175, 276366, 276543, 276723, 276894,
    277085, 277283, 277461, 277640, 277820, 278009, 278196, 278382, 278583, 278759, 278939,
    279129, 279323, 279506, 279690, 279892, 280073, 280240, 280429, 280605, 280781, 280961,
    281140, 281331, 281526, 281720, 281900, 282079, 282246, 282433, 282612, 282799, 282974,
    283159, 283357, 283520, 283727, 283912, 284095, 284283, 284466, 284657, 284846, 285035,
    285226, 285416, 285611, 285805, 286000, 286191, 286385, 286573, 286760, 286927, 287124,
    287310, 287491, 287680, 287863, 288064, 288247, 288446, 288623, 288803, 289010, 289189,
    289384, 289575, 289764, 289937, 290125, 290321, 290521, 290699, 290886, 291055, 291243,
    291432, 291619, 291802, 291970, 292160, 292350, 292535, 292728, 292912, 293115, 293295,
    293495, 293684, 293895, 294081, 294269, 294450, 294640, 294822, 295017, 295214, 295414,
    295602, 295797, 295984]

def LB_3 : List ℕ := [
    226878, 227129, 227374, 227593, 227826, 228079, 228319, 228555, 228793, 229026, 229271,
    229520, 229759, 230001, 230253, 230503, 230738, 230984, 231223, 231472, 231706, 231947,
    232191, 232429, 232677, 232928, 233151, 233394, 233635, 233868, 234105, 234362, 234595,
    234845, 235076, 235322, 235569, 235804, 236045, 236296, 236527, 236773, 236993, 237235,
    237481, 237736, 237974, 238213, 238457, 238704, 238945, 239179, 239415, 239672, 239913,
    240153, 240390, 240627, 240846, 241077, 241349, 241602, 241836, 242094, 242330, 242578,
    242828, 243065, 243318, 243563, 243821, 244061, 244320, 244570, 244810, 245052, 245300,
    245550, 245801, 246053, 246303, 246560, 246796, 247051, 247294, 247533, 247769, 248010,
    248257, 248505, 248732, 248974, 249205, 249444, 249701, 249946, 250184, 250437, 250677,
    250927, 251185, 251417, 251663, 251891, 252135, 252395, 252646, 252881, 253124, 253379,
    253621, 253878, 254129, 254373, 254640, 254890, 255124, 255370, 255622, 255879, 256133,
    256371, 256635, 256891, 257144, 257418, 257679, 257935, 258184, 258456, 258703, 258964,
    259209, 259452, 259704, 259948, 260175, 260425, 260691, 260938, 261193, 261446, 261705,
    261980, 262229, 262479, 262731, 262986, 263256, 263517, 263774, 264023, 264275, 264526,
    264789, 265046, 265317, 265588, 265841, 266089, 266336, 266578, 266856, 267113, 267363,
    267591, 267848, 268100, 268354, 268612, 268872, 269137, 269380, 269622, 269893, 270149,
    270415, 270667, 270923, 271205, 271468, 271736, 271987, 272242, 272494, 272759, 273023,
    273287, 273531, 273790, 274050, 274311, 274566, 274810, 275069, 275331, 275584, 275850,
    276116, 276396, 276645, 276891, 277162, 277427, 277688, 277948, 278211, 278477, 278744,
    278997, 279259, 279530, 279793, 280066, 280313, 280569, 280817, 281071, 281338, 281604,
    281872, 282126, 282376, 282627, 282898, 283146, 283413, 283680, 283945, 284209, 284466,
    284740, 285004, 285269, 285544, 285817, 286090, 286366, 286627, 286883, 287148, 287415,
    287671, 287932, 288209, 288485, 288740, 289018, 289277, 289548, 289812, 290068, 290343,
    290617, 290875, 291122, 291388, 291656, 291905, 292161, 292429, 292700, 292962, 293234,
    293511, 293782, 294071, 294332, 294590, 294848, 295123, 295410, 295685, 295947]

def LA_4 : List ℕ := [
    296172, 296361, 296552, 296754, 296940, 297136, 297318, 297506, 297697, 297895, 298086,
    298266, 298450, 298645, 298821, 299014, 299210, 299391, 299590, 299787, 299979, 300168,
    300359, 300551, 300735, 300919, 301118, 301304, 301490, 301691, 301862, 302058, 302236,
    302432, 302617, 302810, 303002, 303202, 303393, 303580, 303780, 303966, 304168, 304338,
    304534, 304741, 304927, 305111, 305313, 305508, 305693, 305878, 306073, 306255, 306453,
    306638, 306828, 307021, 307212, 307400, 307621, 307808, 307990, 308194, 308395, 308585,
    308773, 308962, 309156, 309339, 309535, 309728, 309911, 310108, 310313, 310507, 310713,
    310912, 311110, 311320, 311509, 311698, 311907, 312114, 312310, 312505, 312706, 312901,
    313096, 313291, 313494, 313685, 313881, 314075, 314270, 314473, 314664, 314859, 315076,
    315278, 315473, 315660, 315854, 316050, 316250, 316450, 316633, 316818, 317015, 317207,
    317405, 317588, 317787, 317982, 318172, 318360, 318558, 318753, 318957, 319138, 319342,
    319559, 319740, 319933, 320147, 320345, 320546, 320726, 320930, 321133, 321327, 321526,
    321717, 321925, 322132, 322321, 322511, 322705, 322903, 323115, 323317, 323501, 323715,
    323897, 324110, 324293, 324496, 324694, 324893, 325095, 325283, 325481, 325689, 325873,
    326064, 326254, 326452, 326659, 326850, 327057, 327258, 327460, 327665, 327880, 328084,
    328290, 328472, 328675, 328891, 329084, 329286, 329469, 329670, 329868, 330071, 330277,
    330479, 330677, 330866, 331079, 331291, 331499, 331681, 331888, 332080, 332281, 332462,
    332665, 332874, 333074, 333277, 333480, 333667, 333873, 334065, 334266, 334465, 334668,
    334859, 335050, 335258, 335462, 335673, 335880, 336074, 336274, 336471, 336681, 336884,
    337084, 337274, 337465, 337669, 337903, 338103, 338295, 338493, 338699, 338910, 339102,
    339301, 339507, 339707, 339929, 340129, 340323, 340524, 340734, 340934, 341142, 341359,
    341575, 341785, 341994, 342207, 342399, 342616, 342806, 343007, 343200, 343414, 343617,
    343818, 344020, 344226, 344425, 344634, 344835, 345054, 345246, 345455, 345665, 345861,
    346078, 346299, 346503, 346694, 346896, 347122, 347318, 347526, 347743, 347952, 348161,
    348349, 348554, 348758, 348959, 349162, 349367, 349567, 349771, 349969, 350188, 350396,
    350601, 350807, 350995, 351211, 351416, 351610, 351812, 352023, 352242, 352448, 352644,
    352846, 353057, 353256, 353469, 353679, 353885, 354097, 354303, 354508, 354711, 354925,
    355125, 355322, 355527, 355731, 355938, 356144, 356347, 356571, 356775, 356976, 357198,
    357399, 357614, 357821, 358023, 358228, 358435, 358640, 358848, 359057, 359262, 359470,
    359686, 359881, 360084, 360285, 360490, 360696, 360905, 361108, 361325, 361535, 361756,
    361966, 362165, 362377, 362591, 362805, 363002, 363220, 363431, 363637, 363836, 364058,
    364278]

def LB_4 : List ℕ := [
    296212, 296489, 296766, 297033, 297297, 297563, 297837, 298105, 298364, 298635, 298885,
    299170, 299426, 299710, 299985, 300251, 300525, 300786, 301055, 301321, 301593, 301850,
    302112, 302387, 302646, 302927, 303201, 303473, 303755, 304018, 304280, 304545, 304827,
    305093, 305370, 305641, 305902, 306174, 306446, 306709, 306985, 307247, 307530, 307812,
    308088, 308364, 308627, 308907, 309174, 309435, 309719, 309976, 310270, 310544, 310832,
    311111, 311402, 311665, 311958, 312252, 312523, 312802, 313074, 313359, 313630, 313914,
    314184, 314467, 314745, 315032, 315319, 315587, 315862, 316136, 316425, 316691, 316954,
    317229, 317500, 317777, 318048, 318321, 318600, 318871, 319142, 319437, 319714, 319983,
    320277, 320563, 320832, 321115, 321398, 321671, 321953, 322245, 322509, 322787, 323083,
    323365, 323629, 323909, 324204, 324478, 324753, 325032, 325310, 325596, 325863, 326125,
    326409, 326694, 326983, 327266, 327547, 327844, 328146, 328412, 328695, 328984, 329272,
    329545, 329821, 330112, 330399, 330677, 330950, 331257, 331543, 331816, 332098, 332372,
    332648, 332938, 333218, 333502, 333767, 334061, 334349, 334626, 334896, 335183, 335470,
    335773, 336049, 336333, 336618, 336912, 337175, 337455, 337751, 338060, 338332, 338616,
    338913, 339186, 339477, 339765, 340059, 340347, 340621, 340917, 341211, 341511, 341812,
    342125, 342391, 342684, 342969, 343247, 343545, 343829, 344122, 344405, 344693, 344994,
    345279, 345568, 345852, 346155, 346458, 346738, 347032, 347326, 347624, 347926, 348208,
    348492, 348785, 349065, 349348, 349635, 349931, 350222, 350515, 350805, 351087, 351379,
    351658, 351947, 352255, 352541, 352828, 353126, 353410, 353704, 354003, 354293, 354594,
    354881, 355162, 355442, 355743, 356028, 356314, 356627, 356911, 357218, 357505, 357808,
    358094, 358390, 358672, 358974, 359263, 359555, 359853, 360132, 360420, 360712, 361004,
    361300, 361605, 361918, 362197, 362502, 362802, 363098, 363390, 363685, 363985, 364290]

def LA_5 : List ℕ := [
    364487, 364711, 364925, 365125, 365324, 365534, 365754, 365962, 366180, 366384, 366596,
    366797, 366985, 367203, 367426, 367645, 367848, 368068, 368277, 368488, 368677, 368891,
    369105, 369303, 369525, 369740, 369949, 370167, 370374, 370586, 370803, 371012, 371208,
    371424, 371638, 371857, 372061, 372261, 372472, 372686, 372913, 373117, 373354, 373558,
    373770, 373975, 374184, 374393, 374598, 374807, 375017, 375234, 375446, 375655, 375871,
    376091, 376303, 376512, 376718, 376944, 377140, 377354, 377572, 377792, 378002, 378219,
    378448, 378656, 378858, 379072, 379278, 379478, 379701, 379916, 380124, 380330, 380550,
    380768, 380982, 381203, 381415, 381616, 381838, 382035, 382241, 382457, 382658, 382871,
    383109, 383325, 383533, 383735, 383948, 384152, 384360, 384575, 384797, 385005, 385237,
    385465, 385669, 385862, 386086, 386313, 386512, 386731, 386951, 387164, 387382, 387581,
    387807, 388031, 388236, 388454, 388657, 388867, 389085, 389312, 389532, 389740, 389944,
    390150, 390366, 390587, 390801, 391013, 391237, 391444, 391654, 391875, 392089, 392302,
    392512, 392736, 392942, 393177, 393402, 393633, 393857, 394065, 394270, 394499, 394722,
    394946, 395160, 395384, 395596, 395808, 396014, 396237, 396464, 396671, 396895, 397121,
    397333, 397543, 397757, 397966, 398178, 398402, 398612, 398826, 399046, 399258, 399471,
    399696, 399912, 400129, 400353, 400580, 400798, 401015, 401226, 401448, 401657, 401874,
    402103, 402312, 402526, 402746, 402967, 403197, 403426, 403642, 403840, 404053, 404277,
    404498, 404725, 404942, 405156, 405401, 405635, 405840, 406073, 406297, 406512, 406736,
    406960, 407186, 407419, 407656, 407867, 408103, 408318, 408537, 408767, 408991, 409211,
    409429, 409650, 409867, 410087, 410304, 410525, 410751, 410963, 411175, 411380, 411618,
    411827, 412064, 412289, 412500, 412707, 412938, 413166, 413398, 413631, 413845, 414069,
    414286, 414522, 414762, 414975, 415167, 415380, 415615, 415828, 416038, 416274, 416507,
    416728, 416936, 417160, 417377, 417604, 417833, 418058, 418266, 418489, 418716, 418930,
    419159, 419402, 419624, 419847, 420074, 420299, 420526, 420740, 420961, 421189, 421404,
    421626, 421860, 422079, 422294, 422538, 422768, 422989, 423210, 423433, 423671, 423892,
    424118, 424341, 424554, 424769, 424993, 425203, 425440, 425684, 425910, 426130, 426361,
    426571, 426787, 427005, 427231, 427460, 427677, 427921, 428133, 428360, 428588, 428803,
    429032, 429268, 429499, 429730, 429951, 430186, 430405, 430635, 430879, 431107, 431342,
    431563]

def LB_5 : List ℕ := [
    364591, 364903, 365180, 365476, 365776, 366077, 366374, 366670, 366947, 367246, 367558,
    367852, 368155, 368456, 368738, 369038, 369327, 369629, 369931, 370236, 370534, 370833,
    371127, 371422, 371721, 372025, 372323, 372603, 372924, 373231, 373528, 373833, 374118,
    374422, 374708, 375004, 375314, 375603, 375918, 376223, 376518, 376824, 377116, 377414,
    377734, 378027, 378337, 378640, 378924, 379228, 379519, 379825, 380124, 380427, 380730,
    381036, 381346, 381628, 381940, 382228, 382516, 382812, 383144, 383443, 383727, 384028,
    384320, 384627, 384925, 385247, 385558, 385832, 386150, 386460, 386755, 387062, 387369,
    387661, 387980, 388276, 388573, 388874, 389187, 389501, 389792, 390092, 390388, 390695,
    390994, 391305, 391595, 391906, 392210, 392506, 392817, 393137, 393453, 393773, 394077,
    394372, 394698, 395013, 395315, 395621, 395922, 396229, 396538, 396852, 397167, 397462,
    397764, 398056, 398375, 398669, 398971, 399276, 399591, 399898, 400195, 400523, 400831,
    401137, 401447, 401741, 402060, 402361, 402668, 402986, 403306, 403615, 403920, 404221,
    404528, 404840, 405149, 405492, 405802, 406123, 406429, 406741, 407058, 407392, 407708,
    408031, 408341, 408661, 408975, 409292, 409604, 409903, 410213, 410527, 410841, 411134,
    411448, 411752, 412089, 412395, 412685, 413008, 413329, 413657, 413971, 414280, 414619,
    414939, 415207, 415529, 415837, 416156, 416479, 416790, 417092, 417405, 417731, 418044,
    418333, 418669, 418980, 419308, 419631, 419947, 420264, 420577, 420887, 421209, 421519,
    421844, 422151, 422480, 422798, 423113, 423432, 423764, 424075, 424394, 424691, 425010,
    425321, 425654, 425976, 426296, 426597, 426896, 427227, 427547, 427868, 428180, 428497,
    428816, 429144, 429466, 429799, 430115, 430436, 430753, 431096, 431417, 431738]

def LA_6 : List ℕ := [
    431796, 432039, 432280, 432512, 432727, 432946, 433173, 433402, 433635, 433871, 434104,
    434320, 434554, 434766, 434995, 435217, 435441, 435670, 435899, 436116, 436356, 436569,
    436786, 437002, 437223, 437457, 437665, 437894, 438125, 438361, 438582, 438812, 439040,
    439267, 439499, 439719, 439955, 440188, 440407, 440628, 440850, 441080, 441307, 441530,
    441772, 442010, 442232, 442458, 442693, 442916, 443138, 443371, 443593, 443830, 444051,
    444290, 444511, 444747, 444993, 445208, 445445, 445681, 445911, 446137, 446367, 446592,
    446834, 447049, 447286, 447514, 447751, 447984, 448200, 448427, 448683, 448906, 449136,
    449365, 449599, 449829, 450074, 450315, 450546, 450769, 450998, 451230, 451465, 451703,
    451934, 452182, 452424, 452636, 452860, 453097, 453321, 453543, 453781, 454013, 454252,
    454464, 454702, 454920, 455155, 455385, 455622, 455852, 456083, 456307, 456535, 456760,
    457003, 457233, 457472, 457710, 457947, 458188, 458426, 458666, 458899, 459141, 459366,
    459598, 459839, 460061, 460289, 460533, 460771, 461007, 461254, 461490, 461722, 461947,
    462176, 462409, 462645, 462878, 463107, 463320, 463556, 463791, 464034, 464270, 464498,
    464743, 464975, 465222, 465446, 465688, 465921, 466157, 466389, 466633, 466873, 467089,
    467337, 467583, 467824, 468075, 468323, 468536, 468784, 469015, 469261, 469497, 469738,
    469977, 470203, 470440, 470671, 470912, 471143, 471371, 471624, 471851, 472078, 472314,
    472565, 472810, 473041, 473273, 473521, 473786, 474004, 474240, 474488, 474718, 474953,
    475191, 475431, 475655, 475891, 476127, 476369, 476613, 476843, 477077, 477317, 477541,
    477786, 478027, 478269, 478524, 478759, 479003, 479245, 479492, 479750, 479983, 480223,
    480458, 480673, 480905, 481137, 481389, 481633, 481868, 482104, 482352, 482589, 482824,
    483075, 483332, 483565, 483805, 484047, 484267, 484511, 484740, 484960, 485191, 485432,
    485676, 485917, 486160, 486400, 486639, 486876, 487115, 487357, 487597, 487829, 488061,
    488295, 488536, 488783, 489016, 489262, 489505, 489744, 489980, 490228, 490462, 490704,
    490949, 491187, 491419, 491657, 491908, 492156, 492399, 492636, 492878, 493106, 493363,
    493612, 493840, 494087, 494337, 494576, 494808, 495064, 495312, 495554, 495784, 496030,
    496271, 496491, 496761, 496996, 497240, 497477, 497715, 497964, 498188]

def LB_6 : List ℕ := [
    432080, 432416, 432728, 433032, 433368, 433692, 434024, 434335, 434652, 434977, 435295,
    435608, 435936, 436250, 436565, 436873, 437185, 437500, 437812, 438137, 438459, 438791,
    439115, 439422, 439753, 440079, 440393, 440710, 441027, 441352, 441681, 442014, 442334,
    442663, 442976, 443296, 443620, 443943, 444269, 444592, 444928, 445249, 445582, 445909,
    446226, 446542, 446884, 447203, 447529, 447861, 448182, 448501, 448845, 449169, 449496,
    449818, 450172, 450499, 450818, 451144, 451473, 451800, 452146, 452479, 452791, 453120,
    453435, 453765, 454098, 454411, 454735, 455056, 455385, 455715, 456041, 456372, 456684,
    457023, 457357, 457688, 458025, 458358, 458696, 459034, 459362, 459692, 460019, 460346,
    460685, 461019, 461368, 461691, 462013, 462339, 462667, 462995, 463309, 463628, 463970,
    464313, 464653, 464980, 465322, 465651, 465985, 466318, 466651, 466980, 467313, 467659,
    468015, 468352, 468681, 469011, 469360, 469690, 470032, 470358, 470683, 471020, 471342,
    471690, 472012, 472342, 472694, 473031, 473374, 473731, 474045, 474388, 474721, 475064,
    475389, 475717, 476057, 476394, 476725, 477055, 477386, 477721, 478066, 478403, 478758,
    479107, 479452, 479799, 480133, 480474, 480787, 481112, 481458, 481801, 482139, 482494,
    482817, 483171, 483519, 483852, 484192, 484521, 484836, 485166, 485494, 485842, 486182,
    486520, 486861, 487196, 487549, 487859, 488207, 488538, 488887, 489219, 489569, 489900,
    490245, 490579, 490926, 491253, 491594, 491943, 492285, 492633, 492967, 493310, 493660,
    494002, 494347, 494685, 495034, 495377, 495714, 496055, 496389, 496741, 497080, 497422,
    497760, 498095, 498421]

def LA_7 : List ℕ := [
    498420, 498653, 498901, 499156, 499397, 499644, 499895, 500131, 500380, 500631, 500870,
    501119, 501353, 501585, 501825, 502069, 502295, 502539, 502786, 503038, 503288, 503521,
    503770, 504018, 504266, 504501, 504746, 505003, 505255, 505485, 505731, 505956, 506197,
    506436, 506679, 506944, 507177, 507430, 507673, 507906, 508138, 508383, 508640, 508880,
    509108, 509365, 509603, 509838, 510067, 510324, 510571, 510814, 511069, 511324, 511576,
    511817, 512072, 512317, 512537, 512802, 513021, 513269, 513503, 513751, 514004, 514263,
    514511, 514766, 515021, 515277, 515518, 515755, 515980, 516249, 516516, 516742, 516986,
    517231, 517473, 517735, 517983, 518221, 518475, 518719, 518967, 519224, 519465, 519701,
    519956, 520207, 520463, 520714, 520962, 521203, 521440, 521697, 521941, 522203, 522450,
    522688, 522932, 523184, 523414, 523660, 523896, 524141, 524407, 524639, 524888, 525137,
    525380, 525647, 525882, 526139, 526362, 526603, 526852, 527110, 527349, 527614, 527862,
    528131, 528360, 528615, 528858, 529100, 529344, 529608, 529869, 530130, 530380, 530638,
    530879, 531134, 531383, 531630, 531894, 532138, 532396, 532646, 532902, 533152, 533396,
    533641, 533879, 534148, 534395, 534646, 534887, 535135, 535394, 535645, 535895, 536145,
    536409, 536653, 536906, 537142, 537393, 537646, 537892, 538147, 538410, 538650, 538912,
    539163, 539407, 539660, 539906, 540156, 540414, 540656, 540904, 541153, 541409, 541655,
    541894, 542142, 542398, 542668, 542902, 543162, 543432, 543687, 543944, 544184, 544444,
    544685, 544926, 545173, 545433, 545671, 545915, 546164, 546411, 546662, 546919, 547178,
    547434, 547715, 547949, 548202, 548443, 548692, 548938, 549200, 549460, 549727, 549980,
    550238, 550483, 550725, 550984, 551256, 551512, 551764, 552007, 552258, 552521, 552786,
    553043, 553308, 553559, 553809, 554057, 554320, 554576, 554835, 555100, 555345, 555610,
    555853, 556106, 556347, 556592, 556856, 557116, 557371, 557643, 557893, 558141, 558398,
    558650, 558912, 559161, 559432, 559679, 559942, 560190, 560451, 560694, 560950, 561211,
    561476, 561749, 562005, 562254, 562502, 562749, 563008, 563255, 563526, 563774, 564046,
    564294]

def LB_7 : List ℕ := [
    498771, 499118, 499460, 499804, 500152, 500510, 500853, 501186, 501520, 501862, 502207,
    502534, 502888, 503237, 503580, 503927, 504282, 504620, 504976, 505330, 505660, 505994,
    506326, 506667, 507034, 507376, 507717, 508041, 508390, 508734, 509067, 509434, 509763,
    510092, 510453, 510799, 511157, 511517, 511864, 512214, 512537, 512889, 513227, 513568,
    513924, 514281, 514635, 515000, 515355, 515693, 516015, 516405, 516739, 517080, 517424,
    517786, 518134, 518486, 518831, 519189, 519531, 519878, 520234, 520591, 520949, 521287,
    521637, 521992, 522353, 522695, 523033, 523376, 523727, 524063, 524422, 524768, 525114,
    525463, 525815, 526176, 526500, 526849, 527205, 527569, 527917, 528285, 528632, 528971,
    529315, 529688, 530059, 530410, 530763, 531123, 531466, 531832, 532189, 532553, 532908,
    533262, 533605, 533953, 534315, 534667, 535025, 535375, 535732, 536082, 536452, 536799,
    537141, 537503, 537841, 538204, 538569, 538934, 539280, 539637, 539982, 540345, 540690,
    541032, 541404, 541743, 542095, 542456, 542811, 543171, 543543, 543908, 544268, 544609,
    544954, 545311, 545655, 546004, 546349, 546712, 547074, 547434, 547827, 548164, 548509,
    548863, 549221, 549592, 549953, 550319, 550667, 551025, 551405, 551760, 552113, 552473,
    552846, 553211, 553569, 553917, 554280, 554654, 555023, 555382, 555736, 556093, 556436,
    556800, 557165, 557532, 557900, 558250, 558607, 558980, 559341, 559702, 560069, 560430,
    560779, 561142, 561517, 561900, 562253, 562596, 562965, 563316, 563687, 564058, 564420]

def LA_8 : List ℕ := [
    564558, 564802, 565072, 565306, 565569, 565837, 566094, 566353, 566595, 566840, 567102,
    567358, 567597, 567855, 568105, 568371, 568632, 568885, 569133, 569387, 569653, 569925,
    570188, 570443, 570707, 570972, 571224, 571488, 571749, 572017, 572273, 572532, 572807,
    573058, 573330, 573579, 573842, 574107, 574352, 574638, 574890, 575141, 575379, 575665,
    575930, 576203, 576465, 576713, 576975, 577236, 577493, 577760, 578021, 578292, 578558,
    578805, 579066, 579325, 579573, 579846, 580109, 580352, 580616, 580894, 581159, 581431,
    581669, 581946, 582183, 582427, 582701, 582974, 583237, 583497, 583758, 584014, 584279,
    584550, 584816, 585088, 585349, 585609, 585881, 586131, 586394, 586640, 586906, 587158,
    587436, 587711, 587972, 588244, 588505, 588746, 589038, 589309, 589551, 589818, 590072,
    590343, 590592, 590846, 591119, 591366, 591644, 591903, 592154, 592413, 592672, 592935,
    593199, 593475, 593714, 593978, 594228, 594497, 594762, 595035, 595279, 595561, 595819,
    596086, 596338, 596585, 596872, 597134, 597402, 597678, 597951, 598207, 598476, 598749,
    599006, 599277, 599543, 599803, 600050, 600314, 600568, 600831, 601094, 601367, 601634,
    601907, 602177, 602452, 602685, 602955, 603201, 603460, 603731, 603994, 604244, 604511,
    604770, 605041, 605318, 605579, 605826, 606085, 606358, 606620, 606896, 607153, 607417,
    607698, 607969, 608236, 608502, 608769, 609041, 609300, 609555, 609812, 610078, 610341,
    610602, 610875, 611157, 611433, 611695, 611964, 612215, 612481, 612741, 613021, 613279,
    613556, 613827, 614098, 614368, 614634, 614910, 615161, 615432, 615707, 615975, 616255,
    616528, 616805, 617072, 617340, 617615, 617868, 618155, 618415, 618695, 618946, 619213,
    619489, 619757, 620027, 620296, 620554, 620822, 621101, 621383, 621637, 621912, 622191,
    622441, 622706, 622975, 623244, 623517, 623772, 624056, 624334, 624605, 624885, 625155,
    625418, 625693, 625961, 626212, 626489, 626770, 627016, 627289, 627558, 627838, 628093,
    628372, 628642, 628908, 629176, 629430, 629694]

def LB_8 : List ℕ := [
    564779, 565137, 565494, 565877, 566228, 566584, 566951, 567307, 567649, 568007, 568379,
    568752, 569095, 569469, 569833, 570221, 570584, 570955, 571314, 571684, 572061, 572425,
    572808, 573165, 573536, 573914, 574262, 574654, 575010, 575360, 575743, 576136, 576502,
    576866, 577228, 577598, 577964, 578347, 578711, 579077, 579434, 579814, 580180, 580532,
    580921, 581303, 581656, 582037, 582381, 582753, 583128, 583500, 583876, 584245, 584623,
    584998, 585373, 585749, 586109, 586482, 586836, 587199, 587592, 587966, 588346, 588704,
    589107, 589462, 589830, 590193, 590558, 590938, 591293, 591684, 592051, 592404, 592768,
    593151, 593520, 593883, 594237, 594625, 594995, 595357, 595729, 596116, 596466, 596848,
    597229, 597601, 597997, 598365, 598749, 599114, 599492, 599859, 600216, 600585, 600955,
    601334, 601728, 602108, 602489, 602829, 603191, 603557, 603947, 604304, 604678, 605053,
    605448, 605795, 606168, 606539, 606927, 607298, 607683, 608071, 608444, 608823, 609197,
    609559, 609934, 610299, 610671, 611067, 611459, 611827, 612197, 612565, 612947, 613322,
    613712, 614093, 614476, 614866, 615224, 615604, 615989, 616384, 616774, 617149, 617533,
    617900, 618302, 618684, 619046, 619436, 619806, 620190, 620562, 620943, 621344, 621707,
    622096, 622464, 622845, 623220, 623611, 623982, 624386, 624763, 625155, 625534, 625912,
    626273, 626662, 627038, 627423, 627804, 628179, 628558, 628942, 629312, 629686]

def LA_9 : List ℕ := [
    629968, 630232, 630521, 630781, 631031, 631311, 631574, 631861, 632131, 632393, 632655,
    632936, 633203, 633475, 633748, 634030, 634307, 634578, 634831, 635112, 635369, 635649,
    635919, 636199, 636468, 636738, 637008, 637293, 637554, 637813, 638096, 638374, 638653,
    638955, 639231, 639503, 639777, 640042, 640306, 640567, 640855, 641125, 641404, 641675,
    641942, 642214, 642479, 642772, 643041, 643323, 643587, 643859, 644150, 644418, 644684,
    644979, 645245, 645511, 645779, 646039, 646305, 646586, 646869, 647123, 647396, 647675,
    647965, 648237, 648522, 648796, 649072, 649341, 649607, 649899, 650152, 650419, 650691,
    650960, 651233, 651504, 651784, 652065, 652349, 652639, 652902, 653171, 653461, 653744,
    654005, 654301, 654564, 654831, 655079, 655361, 655621, 655905, 656193, 656465, 656738,
    657000, 657275, 657551, 657829, 658104, 658389, 658661, 658927, 659197, 659477, 659750,
    660015, 660295, 660582, 660859, 661143, 661402, 661687, 661953, 662221, 662501, 662783,
    663054, 663329, 663589, 663861, 664121, 664405, 664678, 664961, 665234, 665519, 665787,
    666081, 666363, 666631, 666912, 667197, 667491, 667765, 668053, 668328, 668616, 668882,
    669153, 669438, 669720, 670001, 670274, 670559, 670839, 671105, 671383, 671667, 671945,
    672222, 672510, 672783, 673053, 673346, 673641, 673919, 674192, 674465, 674744, 675016,
    675283, 675571, 675849, 676129, 676393, 676650, 676936, 677232, 677501, 677770, 678041,
    678317, 678612, 678905, 679196, 679464, 679733, 680014, 680299, 680578, 680876, 681156,
    681443, 681731, 682003, 682279, 682557, 682844, 683124, 683384, 683681, 683937, 684220,
    684503, 684793, 685082, 685362, 685653, 685935, 686197, 686482, 686754, 687048, 687323,
    687632, 687891, 688172, 688463, 688741, 689037, 689328, 689620, 689889, 690173, 690462,
    690745, 691023, 691322, 691599, 691887, 692154, 692443, 692721, 693017, 693292, 693590,
    693878, 694161, 694437, 694725]

def LB_9 : List ℕ := [
    630074, 630460, 630833, 631205, 631578, 631982, 632357, 632734, 633120, 633501, 633894,
    634290, 634663, 635048, 635414, 635819, 636202, 636587, 636965, 637362, 637722, 638117,
    638508, 638924, 639317, 639706, 640078, 640461, 640847, 641223, 641620, 641997, 642382,
    642783, 643170, 643553, 643942, 644342, 644721, 645111, 645503, 645882, 646244, 646642,
    647023, 647404, 647796, 648199, 648591, 648987, 649370, 649750, 650133, 650511, 650899,
    651277, 651674, 652061, 652462, 652857, 653237, 653650, 654026, 654416, 654804, 655175,
    655550, 655943, 656342, 656722, 657108, 657495, 657883, 658289, 658666, 659051, 659436,
    659821, 660201, 660615, 661004, 661386, 661774, 662160, 662552, 662929, 663329, 663710,
    664078, 664477, 664861, 665254, 665645, 666054, 666444, 666841, 667233, 667641, 668044,
    668437, 668828, 669211, 669616, 670017, 670401, 670797, 671174, 671582, 671978, 672377,
    672769, 673158, 673582, 673971, 674356, 674751, 675136, 675533, 675919, 676310, 676679,
    677076, 677478, 677862, 678240, 678657, 679062, 679461, 679843, 680240, 680641, 681049,
    681458, 681865, 682251, 682649, 683042, 683421, 683826, 684206, 684614, 685019, 685419,
    685837, 686207, 686602, 687014, 687404, 687811, 688197, 688610, 689010, 689422, 689819,
    690221, 690631, 691023, 691435, 691828, 692236, 692622, 693036, 693432, 693848, 694251,
    694646, 695064]

def LA_10 : List ℕ := [
    695017, 695296, 695588, 695873, 696170, 696439, 696728, 697001, 697290, 697552, 697839,
    698126, 698404, 698707, 698988, 699281, 699570, 699868, 700140, 700409, 700690, 700982,
    701260, 701558, 701831, 702118, 702392, 702678, 702954, 703243, 703538, 703822, 704102,
    704392, 704686, 704984, 705258, 705537, 705822, 706111, 706419, 706710, 706994, 707295,
    707572, 707861, 708152, 708442, 708734, 709039, 709324, 709598, 709885, 710156, 710443,
    710740, 711011, 711302, 711582, 711863, 712151, 712415, 712699, 712995, 713278, 713549,
    713841, 714135, 714423, 714704, 715010, 715290, 715558, 715848, 716119, 716424, 716727,
    717017, 717309, 717591, 717879, 718174, 718465, 718739, 719024, 719302, 719595, 719880,
    720172, 720472, 720767, 721056, 721323, 721616, 721913, 722215, 722496, 722785, 723082,
    723379, 723665, 723952, 724250, 724532, 724805, 725108, 725389, 725685, 725955, 726262,
    726541, 726841, 727111, 727396, 727673, 727964, 728258, 728547, 728825, 729118, 729419,
    729706, 730002, 730313, 730603, 730885, 731185, 731485, 731767, 732056, 732364, 732650,
    732938, 733233, 733543, 733821, 734104, 734368, 734656, 734939, 735231, 735520, 735828,
    736119, 736411, 736719, 737003, 737300, 737607, 737902, 738182, 738483, 738770, 739067,
    739348, 739640, 739926, 740222, 740503, 740780, 741080, 741370, 741669, 741966, 742265,
    742541, 742844, 743124, 743412, 743694, 743983, 744285, 744592, 744882, 745152, 745449,
    745752, 746037, 746333, 746637, 746918, 747205, 747495, 747787, 748085, 748385, 748673,
    748965, 749250, 749545, 749827, 750124, 750408, 750697, 751004, 751307, 751586, 751880,
    752169, 752478, 752767, 753055, 753331, 753629, 753933, 754215, 754528, 754837, 755128,
    755430, 755739, 756026, 756317, 756597, 756888, 757197, 757485, 757774, 758056, 758349,
    758639, 758961, 759255, 759550]

def LB_10 : List ℕ := [
    695460, 695864, 696268, 696673, 697061, 697446, 697851, 698251, 698674, 699075, 699477,
    699893, 700277, 700677, 701079, 701491, 701882, 702278, 702679, 703076, 703496, 703894,
    704296, 704709, 705109, 705514, 705914, 706343, 706756, 707163, 707567, 707972, 708387,
    708796, 709220, 709610, 710013, 710409, 710816, 711225, 711620, 712017, 712404, 712812,
    713218, 713606, 714010, 714428, 714831, 715245, 715634, 716031, 716452, 716882, 717293,
    717691, 718100, 718518, 718913, 719300, 719710, 720110, 720541, 720944, 721338, 721762,
    722181, 722575, 722990, 723420, 723819, 724236, 724649, 725036, 725452, 725851, 726267,
    726677, 727074, 727471, 727878, 728281, 728690, 729101, 729522, 729939, 730362, 730771,
    731186, 731607, 732001, 732426, 732850, 733254, 733681, 734077, 734459, 734861, 735267,
    735701, 736110, 736525, 736943, 737363, 737785, 738191, 738613, 739028, 739431, 739834,
    740255, 740655, 741063, 741479, 741899, 742327, 742729, 743129, 743545, 743941, 744355,
    744790, 745176, 745584, 746009, 746425, 746856, 747256, 747655, 748081, 748493, 748902,
    749311, 749730, 750137, 750533, 750971, 751388, 751795, 752207, 752637, 753042, 753438,
    753869, 754271, 754714, 755138, 755563, 755985, 756382, 756801, 757219, 757647, 758043,
    758453, 758882, 759316, 759732]

def LA_11 : List ℕ := [
    759868, 760173, 760468, 760763, 761052, 761354, 761644, 761938, 762242, 762544, 762830,
    763129, 763422, 763717, 764034, 764346, 764661, 764961, 765263, 765539, 765819, 766099,
    766405, 766718, 767015, 767317, 767608, 767905, 768193, 768463, 768777, 769073, 769366,
    769690, 769977, 770267, 770565, 770867, 771156, 771445, 771753, 772044, 772342, 772643,
    772943, 773241, 773525, 773826, 774114, 774394, 774718, 775033, 775329, 775627, 775933,
    776236, 776526, 776829, 777126, 777421, 777715, 778007, 778302, 778578, 778886, 779174,
    779491, 779811, 780103, 780393, 780712, 781002, 781299, 781591, 781897, 782203, 782491,
    782795, 783101, 783391, 783729, 784007, 784300, 784604, 784909, 785230, 785536, 785837,
    786130, 786409, 786716, 787013, 787323, 787624, 787931, 788212, 788501, 788812, 789126,
    789412, 789703, 790007, 790303, 790610, 790899, 791208, 791511, 791833, 792132, 792418,
    792726, 793020, 793312, 793617, 793900, 794200, 794507, 794809, 795121, 795422, 795720,
    796013, 796320, 796628, 796946, 797260, 797545, 797842, 798137, 798443, 798749, 799033,
    799342, 799642, 799945, 800245, 800537, 800850, 801167, 801464, 801768, 802079, 802406,
    802689, 802987, 803273, 803576, 803882, 804189, 804493, 804806, 805107, 805392, 805707,
    806026, 806322, 806626, 806946, 807277, 807576, 807884, 808177, 808472, 808771, 809051,
    809359, 809664, 809989, 810307, 810637, 810939, 811240, 811560, 811844, 812147, 812457,
    812763, 813071, 813392, 813695, 814011, 814317, 814609, 814913, 815214, 815523, 815832,
    816125, 816452, 816740, 817037, 817353, 817661, 817963, 818276, 818557, 818849, 819137,
    819448, 819775, 820095, 820403, 820705, 820987, 821295, 821608, 821911, 822219, 822520,
    822811, 823124, 823428, 823732, 824042]

def LB_11 : List ℕ := [
    760172, 760592, 761001, 761428, 761841, 762256, 762681, 763096, 763503, 763943, 764386,
    764828, 765255, 765654, 766037, 766473, 766907, 767329, 767742, 768157, 768558, 768980,
    769407, 769851, 770250, 770667, 771090, 771503, 771938, 772345, 772781, 773193, 773608,
    774020, 774418, 774881, 775306, 775727, 776164, 776568, 777001, 777419, 777837, 778248,
    778646, 779066, 779504, 779942, 780352, 780802, 781215, 781626, 782057, 782476, 782899,
    783327, 783784, 784182, 784612, 785045, 785483, 785915, 786319, 786744, 787185, 787601,
    788020, 788432, 788858, 789299, 789701, 790120, 790554, 790979, 791402, 791854, 792268,
    792697, 793116, 793535, 793940, 794361, 794799, 795236, 795661, 796071, 796510, 796957,
    797383, 797807, 798223, 798654, 799066, 799510, 799924, 800346, 800770, 801219, 801644,
    802081, 802523, 802939, 803358, 803775, 804212, 804639, 805080, 805495, 805934, 806368,
    806807, 807269, 807698, 808117, 808539, 808951, 809372, 809811, 810257, 810743, 811147,
    811590, 811999, 812443, 812876, 813331, 813755, 814187, 814610, 815037, 815479, 815910,
    816341, 816763, 817197, 817634, 818068, 818480, 818887, 819324, 819772, 820230, 820658,
    821055, 821497, 821930, 822356, 822778, 823203, 823647, 824086]

def LA_12 : List ℕ := [
    824353, 824662, 824973, 825291, 825605, 825911, 826215, 826517, 826835, 827137, 827457,
    827754, 828055, 828361, 828659, 828961, 829269, 829587, 829897, 830205, 830521, 830820,
    831132, 831425, 831743, 832079, 832390, 832699, 833014, 833329, 833647, 833953, 834246,
    834566, 834885, 835187, 835503, 835822, 836125, 836420, 836740, 837052, 837355, 837660,
    837971, 838276, 838592, 838909, 839219, 839537, 839834, 840163, 840468, 840769, 841097,
    841408, 841713, 842018, 842306, 842622, 842938, 843233, 843533, 843840, 844142, 844457,
    844752, 845068, 845381, 845678, 845991, 846299, 846608, 846922, 847225, 847542, 847836,
    848143, 848445, 848759, 849081, 849400, 849724, 850021, 850339, 850668, 850958, 851259,
    851581, 851879, 852191, 852514, 852802, 853099, 853400, 853719, 854040, 854338, 854647,
    854934, 855256, 855564, 855891, 856191, 856487, 856813, 857133, 857446, 857765, 858086,
    858380, 858691, 859002, 859304, 859608, 859933, 860261, 860578, 860886, 861209, 861529,
    861838, 862150, 862476, 862789, 863092, 863415, 863725, 864027, 864356, 864660, 864960,
    865262, 865576, 865903, 866234, 866539, 866853, 867140, 867473, 867791, 868109, 868428,
    868759, 869051, 869362, 869687, 870001, 870316, 870624, 870945, 871254, 871592, 871898,
    872218, 872536, 872844, 873159, 873483, 873799, 874099, 874412, 874716, 875028, 875346,
    875672, 876002, 876291, 876609, 876915, 877233, 877527, 877848, 878159, 878482, 878808,
    879101, 879438, 879750, 880061, 880364, 880681, 881000, 881319, 881627, 881953, 882258,
    882561, 882898, 883207, 883525, 883829, 884152, 884477, 884788, 885133, 885439, 885744,
    886080, 886413, 886735, 887047, 887336, 887676]

def LB_12 : List ℕ := [
    824519, 824955, 825403, 825834, 826269, 826719, 827150, 827576, 828018, 828439, 828862,
    829291, 829756, 830181, 830611, 831057, 831478, 831936, 832390, 832815, 833271, 833719,
    834147, 834586, 835031, 835472, 835915, 836342, 836780, 837222, 837654, 838091, 838525,
    838978, 839415, 839845, 840298, 840732, 841182, 841628, 842048, 842464, 842918, 843334,
    843766, 844194, 844641, 845071, 845507, 845932, 846381, 846817, 847253, 847689, 848112,
    848535, 848992, 849445, 849887, 850333, 850784, 851203, 851644, 852076, 852530, 852946,
    853371, 853815, 854248, 854684, 855106, 855553, 856004, 856424, 856875, 857325, 857775,
    858213, 858643, 859082, 859514, 859969, 860413, 860865, 861316, 861765, 862202, 862646,
    863092, 863536, 863975, 864424, 864856, 865285, 865737, 866187, 866639, 867056, 867515,
    867967, 868419, 868874, 869293, 869755, 870195, 870634, 871087, 871542, 871981, 872441,
    872880, 873321, 873777, 874205, 874649, 875092, 875534, 876003, 876416, 876858, 877314,
    877745, 878184, 878635, 879073, 879531, 879979, 880413, 880870, 881310, 881757, 882204,
    882639, 883086, 883540, 883992, 884438, 884886, 885345, 885785, 886262, 886715, 887157,
    887607, 888061]

def LA_13 : List ℕ := [
    888000, 888320, 888629, 888950, 889270, 889591, 889927, 890263, 890581, 890887, 891212,
    891518, 891831, 892159, 892480, 892792, 893127, 893436, 893760, 894063, 894378, 894697,
    895028, 895361, 895658, 895979, 896280, 896596, 896932, 897283, 897608, 897921, 898225,
    898549, 898872, 899197, 899508, 899828, 900137, 900458, 900799, 901125, 901439, 901777,
    902071, 902403, 902727, 903049, 903380, 903697, 904033, 904364, 904687, 905002, 905336,
    905654, 905969, 906287, 906607, 906916, 907238, 907546, 907861, 908180, 908498, 908800,
    909131, 909438, 909748, 910077, 910388, 910716, 911033, 911342, 911682, 912013, 912335,
    912651, 912965, 913287, 913583, 913922, 914233, 914570, 914886, 915232, 915546, 915869,
    916190, 916502, 916854, 917173, 917495, 917813, 918138, 918466, 918810, 919113, 919430,
    919761, 920079, 920399, 920719, 921043, 921359, 921668, 921985, 922294, 922623, 922942,
    923274, 923595, 923910, 924237, 924578, 924903, 925222, 925548, 925871, 926214, 926526,
    926860, 927193, 927517, 927848, 928168, 928482, 928803, 929134, 929480, 929779, 930112,
    930436, 930765, 931093, 931430, 931786, 932113, 932438, 932753, 933086, 933411, 933758,
    934089, 934419, 934731, 935058, 935382, 935691, 936030, 936346, 936665, 937000, 937330,
    937650, 937971, 938299, 938613, 938937, 939293, 939616, 939932, 940253, 940571, 940897,
    941225, 941536, 941864, 942198, 942522, 942853, 943181, 943503, 943833, 944165, 944484,
    944812, 945147, 945491, 945812, 946141, 946487, 946810, 947122, 947439, 947765, 948077,
    948403, 948729, 949060, 949370, 949706, 950022, 950354, 950688, 951019, 951352]

def LB_13 : List ℕ := [
    888510, 888954, 889423, 889875, 890336, 890785, 891247, 891684, 892135, 892580, 893042,
    893484, 893932, 894377, 894829, 895311, 895731, 896180, 896615, 897095, 897571, 898001,
    898458, 898910, 899366, 899817, 900247, 900727, 901194, 901640, 902083, 902552, 903006,
    903470, 903927, 904397, 904854, 905320, 905768, 906214, 906665, 907113, 907546, 907994,
    908445, 908885, 909339, 909767, 910227, 910688, 911128, 911593, 912063, 912501, 912959,
    913404, 913866, 914298, 914767, 915247, 915698, 916147, 916602, 917082, 917533, 917998,
    918447, 918911, 919359, 919820, 920270, 920726, 921172, 921624, 922061, 922510, 922973,
    923444, 923891, 924357, 924819, 925281, 925742, 926208, 926651, 927137, 927599, 928051,
    928499, 928962, 929442, 929873, 930345, 930808, 931262, 931770, 932229, 932681, 933152,
    933630, 934096, 934560, 935009, 935469, 935922, 936385, 936836, 937299, 937761, 938232,
    938676, 939139, 939614, 940070, 940511, 940968, 941426, 941885, 942360, 942819, 943285,
    943740, 944210, 944666, 945141, 945623, 946080, 946552, 947006, 947452, 947898, 948362,
    948823, 949283, 949741, 950194, 950671, 951136, 951630]

def LA_14 : List ℕ := [
    951695, 952019, 952358, 952658, 952995, 953330, 953656, 953991, 954314, 954646, 954987,
    955304, 955643, 955977, 956301, 956628, 956970, 957321, 957640, 957972, 958298, 958624,
    958968, 959290, 959613, 959945, 960272, 960606, 960932, 961282, 961610, 961920, 962260,
    962590, 962922, 963244, 963571, 963882, 964216, 964549, 964882, 965200, 965525, 965848,
    966181, 966507, 966835, 967176, 967511, 967857, 968189, 968483, 968808, 969143, 969470,
    969797, 970134, 970470, 970794, 971130, 971458, 971784, 972119, 972459, 972790, 973123,
    973458, 973788, 974123, 974449, 974780, 975109, 975446, 975757, 976104, 976433, 976776,
    977101, 977430, 977761, 978089, 978425, 978752, 979095, 979411, 979749, 980077, 980410,
    980774, 981112, 981438, 981755, 982075, 982406, 982730, 983052, 983396, 983732, 984063,
    984388, 984739, 985067, 985412, 985753, 986087, 986421, 986766, 987096, 987433, 987786,
    988113, 988445, 988775, 989111, 989440, 989781, 990123, 990454, 990782, 991112, 991445,
    991788, 992121, 992469, 992806, 993107, 993442, 993765, 994099, 994430, 994754, 995076,
    995409, 995746, 996091, 996419, 996748, 997067, 997405, 997733, 998078, 998408, 998758,
    999077, 999427, 999763, 1000095, 1000431, 1000770, 1001121, 1001463, 1001810, 1002158,
    1002494, 1002829, 1003175, 1003502, 1003833, 1004187, 1004535, 1004877, 1005216, 1005544,
    1005884, 1006222, 1006584, 1006908, 1007240, 1007580, 1007920, 1008254, 1008590, 1008935,
    1009274, 1009605, 1009945, 1010275, 1010612, 1010979, 1011315, 1011648, 1011974, 1012309,
    1012658, 1012986, 1013328, 1013668, 1014023, 1014349, 1014679, 1015011]

def LB_14 : List ℕ := [
    952083, 952531, 953002, 953469, 953932, 954408, 954871, 955332, 955801, 956272, 956740,
    957239, 957695, 958170, 958620, 959101, 959551, 960015, 960484, 960950, 961452, 961886,
    962356, 962815, 963286, 963730, 964201, 964671, 965124, 965590, 966059, 966517, 966978,
    967463, 967957, 968384, 968838, 969306, 969770, 970244, 970710, 971182, 971635, 972115,
    972599, 973061, 973537, 974013, 974471, 974945, 975410, 975866, 976346, 976820, 977275,
    977750, 978221, 978685, 979162, 979619, 980085, 980569, 981071, 981529, 981982, 982445,
    982899, 983375, 983849, 984310, 984800, 985271, 985754, 986225, 986711, 987188, 987666,
    988139, 988607, 989083, 989544, 990035, 990503, 990959, 991435, 991916, 992397, 992872,
    993327, 993779, 994254, 994713, 995176, 995643, 996133, 996590, 997052, 997532, 997991,
    998476, 998953, 999435, 999898, 1000380, 1000860, 1001350, 1001841, 1002321, 1002797, 1003288,
    1003755, 1004238, 1004735, 1005211, 1005680, 1006151, 1006655, 1007118, 1007604, 1008086,
    1008547, 1009038, 1009509, 1009983, 1010467, 1010959, 1011434, 1011906, 1012383, 1012853,
    1013336, 1013822, 1014299, 1014761]

def LA_15 : List ℕ := [
    1015359, 1015697, 1016031, 1016364, 1016709, 1017055, 1017379, 1017695, 1018043, 1018393,
    1018718, 1019046, 1019379, 1019723, 1020059, 1020397, 1020752, 1021086, 1021433, 1021780,
    1022131, 1022491, 1022832, 1023176, 1023520, 1023866, 1024204, 1024549, 1024869, 1025215,
    1025555, 1025886, 1026217, 1026583, 1026917, 1027270, 1027604, 1027925, 1028271, 1028616,
    1028954, 1029297, 1029637, 1029975, 1030320, 1030662, 1031000, 1031334, 1031670, 1032011,
    1032356, 1032697, 1033051, 1033380, 1033708, 1034053, 1034387, 1034705, 1035056, 1035415,
    1035774, 1036095, 1036444, 1036774, 1037117, 1037459, 1037788, 1038138, 1038487, 1038829,
    1039167, 1039504, 1039862, 1040199, 1040525, 1040860, 1041196, 1041548, 1041870, 1042219,
    1042558, 1042913, 1043259, 1043613, 1043961, 1044318, 1044646, 1044987, 1045337, 1045693,
    1046031, 1046359, 1046703, 1047059, 1047425, 1047761, 1048083, 1048426, 1048776, 1049128,
    1049477, 1049835, 1050158, 1050487, 1050820, 1051155, 1051484, 1051821, 1052180, 1052512,
    1052849, 1053207, 1053552, 1053887, 1054233, 1054585, 1054930, 1055265, 1055617, 1055967,
    1056301, 1056679, 1057018, 1057364, 1057708, 1058066, 1058392, 1058713, 1059069, 1059414,
    1059772, 1060114, 1060458, 1060833, 1061174, 1061516, 1061872, 1062196, 1062548, 1062886,
    1063228, 1063573, 1063919, 1064243, 1064584, 1064934, 1065278, 1065609, 1065953, 1066305,
    1066672, 1067026, 1067377, 1067739, 1068076, 1068436, 1068770, 1069112, 1069458, 1069810,
    1070162, 1070520, 1070868, 1071205, 1071556, 1071907, 1072257, 1072603, 1072952, 1073273,
    1073620, 1073976, 1074320, 1074672, 1075029, 1075377, 1075732, 1076075, 1076428, 1076784,
    1077134, 1077477, 1077829, 1078185]

def LB_15 : List ℕ := [
    1015242, 1015728, 1016202, 1016680, 1017165, 1017628, 1018115, 1018572, 1019046, 1019529,
    1020004, 1020481, 1020970, 1021457, 1021943, 1022455, 1022946, 1023424, 1023920, 1024399,
    1024857, 1025342, 1025816, 1026294, 1026796, 1027286, 1027752, 1028220, 1028700, 1029195,
    1029678, 1030153, 1030640, 1031130, 1031595, 1032068, 1032559, 1033055, 1033519, 1034000,
    1034458, 1034932, 1035440, 1035941, 1036413, 1036884, 1037374, 1037846, 1038330, 1038824,
    1039300, 1039803, 1040269, 1040739, 1041218, 1041694, 1042173, 1042660, 1043151, 1043655,
    1044151, 1044632, 1045111, 1045614, 1046091, 1046575, 1047069, 1047564, 1048034, 1048525,
    1049021, 1049514, 1049999, 1050462, 1050932, 1051413, 1051884, 1052381, 1052848, 1053339,
    1053828, 1054318, 1054805, 1055297, 1055774, 1056266, 1056782, 1057271, 1057754, 1058227,
    1058702, 1059203, 1059694, 1060185, 1060693, 1061188, 1061676, 1062158, 1062650, 1063114,
    1063615, 1064079, 1064560, 1065049, 1065531, 1066020, 1066526, 1067028, 1067525, 1068022,
    1068527, 1068986, 1069486, 1069984, 1070486, 1070972, 1071465, 1071955, 1072445, 1072943,
    1073412, 1073907, 1074399, 1074894, 1075400, 1075902, 1076379, 1076885, 1077371, 1077871]

def LA_16 : List ℕ := [
    1078516, 1078891, 1079248, 1079584, 1079934, 1080302, 1080652, 1080994, 1081328, 1081680,
    1082039, 1082367, 1082709, 1083073, 1083409, 1083771, 1084105, 1084438, 1084796, 1085144,
    1085506, 1085856, 1086195, 1086551, 1086902, 1087249, 1087595, 1087959, 1088304, 1088695,
    1089058, 1089389, 1089752, 1090120, 1090465, 1090802, 1091172, 1091508, 1091876, 1092228,
    1092577, 1092931, 1093294, 1093642, 1093978, 1094325, 1094648, 1095021, 1095375, 1095742,
    1096100, 1096438, 1096790, 1097152, 1097498, 1097842, 1098187, 1098553, 1098893, 1099252,
    1099594, 1099929, 1100290, 1100636, 1100979, 1101311, 1101659, 1101996, 1102345, 1102688,
    1103038, 1103388, 1103739, 1104073, 1104429, 1104789, 1105151, 1105510, 1105875, 1106204,
    1106552, 1106909, 1107258, 1107609, 1107966, 1108321, 1108669, 1109038, 1109407, 1109762,
    1110105, 1110484, 1110860, 1111229, 1111580, 1111938, 1112268, 1112620, 1112979, 1113313,
    1113664, 1114024, 1114378, 1114734, 1115083, 1115452, 1115815, 1116195, 1116548, 1116895,
    1117242, 1117597, 1117955, 1118320, 1118662, 1119006, 1119349, 1119720, 1120093, 1120462,
    1120809, 1121181, 1121560, 1121917, 1122262, 1122601, 1122952, 1123313, 1123662, 1124028,
    1124393, 1124748, 1125095, 1125457, 1125819, 1126177, 1126541, 1126897, 1127251, 1127575,
    1127937, 1128297, 1128641, 1129020, 1129374, 1129734, 1130093, 1130430, 1130780, 1131131,
    1131475, 1131821, 1132178, 1132549, 1132904, 1133268, 1133622, 1133974, 1134320, 1134682,
    1135028, 1135395, 1135748, 1136094, 1136424, 1136780, 1137138, 1137487, 1137854, 1138220,
    1138582, 1138969, 1139320, 1139669, 1140044, 1140391, 1140741, 1141085]

def LB_16 : List ℕ := [
    1078362, 1078872, 1079376, 1079854, 1080368, 1080858, 1081334, 1081831, 1082314, 1082794,
    1083296, 1083801, 1084280, 1084763, 1085262, 1085771, 1086257, 1086745, 1087243, 1087737,
    1088248, 1088777, 1089275, 1089769, 1090278, 1090760, 1091269, 1091766, 1092272, 1092771,
    1093279, 1093766, 1094255, 1094727, 1095243, 1095748, 1096249, 1096735, 1097243, 1097730,
    1098223, 1098728, 1099221, 1099714, 1100204, 1100692, 1101178, 1101659, 1102147, 1102628,
    1103129, 1103619, 1104097, 1104607, 1105112, 1105626, 1106119, 1106599, 1107107, 1107599,
    1108099, 1108605, 1109119, 1109629, 1110126, 1110659, 1111179, 1111659, 1112172, 1112665,
    1113154, 1113643, 1114152, 1114651, 1115152, 1115678, 1116200, 1116691, 1117183, 1117684,
    1118197, 1118687, 1119174, 1119690, 1120219, 1120722, 1121235, 1121768, 1122254, 1122742,
    1123248, 1123742, 1124257, 1124772, 1125256, 1125781, 1126281, 1126791, 1127293, 1127773,
    1128277, 1128780, 1129292, 1129814, 1130310, 1130787, 1131272, 1131780, 1132273, 1132787,
    1133302, 1133811, 1134290, 1134803, 1135307, 1135801, 1136286, 1136780, 1137280, 1137784,
    1138306, 1138845, 1139342, 1139850, 1140346, 1140849, 1141346]

def LA_17 : List ℕ := [
    1141438, 1141785, 1142141, 1142494, 1142845, 1143233, 1143591, 1143952, 1144304, 1144656,
    1145019, 1145380, 1145729, 1146084, 1146429, 1146791, 1147161, 1147519, 1147898, 1148256,
    1148642, 1149008, 1149377, 1149734, 1150110, 1150478, 1150835, 1151186, 1151549, 1151892,
    1152245, 1152605, 1152960, 1153302, 1153673, 1154024, 1154372, 1154746, 1155108, 1155441,
    1155793, 1156152, 1156486, 1156851, 1157226, 1157594, 1157956, 1158299, 1158659, 1159019,
    1159378, 1159756, 1160112, 1160469, 1160813, 1161164, 1161524, 1161897, 1162246, 1162581,
    1162947, 1163302, 1163658, 1164021, 1164385, 1164757, 1165116, 1165504, 1165888, 1166246,
    1166609, 1166961, 1167352, 1167700, 1168076, 1168444, 1168800, 1169163, 1169509, 1169899,
    1170264, 1170624, 1171006, 1171359, 1171716, 1172076, 1172434, 1172769, 1173118, 1173484,
    1173844, 1174210, 1174567, 1174925, 1175288, 1175661, 1176033, 1176411, 1176754, 1177103,
    1177469, 1177851, 1178208, 1178561, 1178934, 1179288, 1179628, 1179987, 1180345, 1180711,
    1181069, 1181416, 1181790, 1182140, 1182500, 1182858, 1183234, 1183598, 1183961, 1184325,
    1184697, 1185049, 1185425, 1185791, 1186143, 1186535, 1186905, 1187262, 1187641, 1188003,
    1188356, 1188734, 1189098, 1189464, 1189827, 1190215, 1190588, 1190959, 1191329, 1191686,
    1192038, 1192377, 1192735, 1193106, 1193461, 1193838, 1194199, 1194546, 1194930, 1195313,
    1195700, 1196048, 1196423, 1196783, 1197164, 1197528, 1197891, 1198249, 1198627, 1198969,
    1199331, 1199694, 1200049, 1200415, 1200794, 1201148, 1201537, 1201882, 1202275, 1202632,
    1203005, 1203384, 1203747]

def LB_17 : List ℕ := [
    1141837, 1142338, 1142831, 1143373, 1143882, 1144378, 1144878, 1145393, 1145884, 1146377,
    1146898, 1147397, 1147934, 1148457, 1148976, 1149503, 1150015, 1150537, 1151039, 1151552,
    1152043, 1152547, 1153043, 1153552, 1154045, 1154548, 1155075, 1155551, 1156060, 1156534,
    1157058, 1157584, 1158089, 1158590, 1159101, 1159607, 1160128, 1160620, 1161121, 1161631,
    1162141, 1162621, 1163135, 1163642, 1164152, 1164677, 1165200, 1165747, 1166250, 1166760,
    1167294, 1167791, 1168318, 1168830, 1169336, 1169869, 1170387, 1170909, 1171412, 1171921,
    1172429, 1172906, 1173424, 1173927, 1174443, 1174943, 1175470, 1175993, 1176515, 1176999,
    1177523, 1178053, 1178552, 1179075, 1179561, 1180057, 1180566, 1181077, 1181578, 1182091,
    1182594, 1183123, 1183639, 1184144, 1184670, 1185174, 1185706, 1186222, 1186751, 1187263,
    1187780, 1188298, 1188824, 1189341, 1189856, 1190401, 1190921, 1191445, 1191948, 1192422,
    1192946, 1193444, 1193975, 1194474, 1195011, 1195555, 1196065, 1196590, 1197116, 1197641,
    1198138, 1198670, 1199164, 1199677, 1200176, 1200712, 1201230, 1201740, 1202282, 1202796,
    1203330, 1203838]

def LA_18 : List ℕ := [
    1204113, 1204457, 1204820, 1205181, 1205518, 1205895, 1206260, 1206638, 1207032, 1207397,
    1207779, 1208160, 1208507, 1208872, 1209231, 1209592, 1209949, 1210346, 1210706, 1211079,
    1211430, 1211804, 1212183, 1212520, 1212896, 1213271, 1213653, 1214019, 1214387, 1214746,
    1215094, 1215478, 1215846, 1216218, 1216593, 1216947, 1217305, 1217657, 1218026, 1218418,
    1218771, 1219163, 1219519, 1219886, 1220256, 1220647, 1221005, 1221370, 1221717, 1222095,
    1222472, 1222844, 1223229, 1223564, 1223929, 1224297, 1224668, 1225041, 1225394, 1225778,
    1226152, 1226532, 1226896, 1227267, 1227629, 1227993, 1228359, 1228731, 1229116, 1229483,
    1229866, 1230239, 1230615, 1230992, 1231349, 1231702, 1232097, 1232469, 1232845, 1233205,
    1233571, 1233958, 1234351, 1234718, 1235075, 1235456, 1235831, 1236223, 1236583, 1236952,
    1237339, 1237722, 1238077, 1238475, 1238817, 1239181, 1239565, 1239936, 1240282, 1240641,
    1241036, 1241395, 1241778, 1242137, 1242502, 1242868, 1243250, 1243603, 1243973, 1244323,
    1244697, 1245071, 1245427, 1245786, 1246143, 1246536, 1246909, 1247302, 1247660, 1248051,
    1248435, 1248807, 1249177, 1249531, 1249895, 1250269, 1250636, 1251026, 1251394, 1251758,
    1252142, 1252526, 1252910, 1253287, 1253664, 1254021, 1254386, 1254757, 1255139, 1255525,
    1255905, 1256276, 1256659, 1257029, 1257406, 1257773, 1258162, 1258541, 1258932, 1259313,
    1259674, 1260051, 1260434, 1260792, 1261158, 1261551, 1261942, 1262306, 1262666, 1263048,
    1263427, 1263813, 1264191, 1264533, 1264902, 1265287, 1265665, 1266059]

def LB_18 : List ℕ := [
    1204335, 1204845, 1205352, 1205865, 1206385, 1206925, 1207463, 1207983, 1208504, 1209028,
    1209526, 1210040, 1210587, 1211099, 1211604, 1212136, 1212632, 1213178, 1213698, 1214221,
    1214730, 1215236, 1215760, 1216297, 1216810, 1217315, 1217823, 1218369, 1218874, 1219403,
    1219930, 1220463, 1220973, 1221488, 1222009, 1222534, 1223074, 1223563, 1224083, 1224605,
    1225129, 1225651, 1226179, 1226708, 1227220, 1227746, 1228254, 1228783, 1229329, 1229856,
    1230391, 1230910, 1231428, 1231935, 1232483, 1233013, 1233526, 1234074, 1234609, 1235113,
    1235657, 1236201, 1236709, 1237249, 1237787, 1238311, 1238821, 1239342, 1239885, 1240376,
    1240905, 1241429, 1241958, 1242471, 1242993, 1243513, 1244028, 1244534, 1245064, 1245561,
    1246082, 1246623, 1247168, 1247680, 1248227, 1248759, 1249281, 1249789, 1250314, 1250858,
    1251375, 1251896, 1252439, 1252977, 1253517, 1254032, 1254549, 1255081, 1255627, 1256156,
    1256689, 1257225, 1257740, 1258298, 1258834, 1259375, 1259890, 1260430, 1260946, 1261483,
    1262024, 1262554, 1263077, 1263601, 1264150, 1264643, 1265180, 1265724, 1266272]

def LA_19 : List ℕ := [
    1266437, 1266814, 1267180, 1267573, 1267947, 1268346, 1268709, 1269073, 1269451, 1269828,
    1270206, 1270591, 1270968, 1271335, 1271718, 1272084, 1272482, 1272869, 1273250, 1273620,
    1273995, 1274365, 1274747, 1275136, 1275506, 1275881, 1276261, 1276640, 1277023, 1277399,
    1277763, 1278136, 1278508, 1278866, 1279244, 1279626, 1280002, 1280382, 1280785, 1281170,
    1281570, 1281933, 1282285, 1282672, 1283039, 1283398, 1283764, 1284133, 1284521, 1284912,
    1285295, 1285663, 1286040, 1286417, 1286776, 1287160, 1287545, 1287918, 1288284, 1288664,
    1289058, 1289444, 1289819, 1290177, 1290555, 1290930, 1291312, 1291690, 1292080, 1292471,
    1292842, 1293232, 1293622, 1293989, 1294361, 1294740, 1295098, 1295476, 1295847, 1296235,
    1296601, 1296958, 1297346, 1297734, 1298105, 1298508, 1298882, 1299242, 1299611, 1300006,
    1300393, 1300774, 1301160, 1301559, 1301942, 1302295, 1302680, 1303051, 1303438, 1303811,
    1304197, 1304613, 1304971, 1305348, 1305754, 1306140, 1306503, 1306871, 1307248, 1307638,
    1308044, 1308404, 1308786, 1309147, 1309541, 1309920, 1310301, 1310697, 1311094, 1311495,
    1311875, 1312266, 1312660, 1313054, 1313429, 1313817, 1314183, 1314574, 1314948, 1315340,
    1315716, 1316103, 1316472, 1316870, 1317233, 1317625, 1317998, 1318372, 1318760, 1319138,
    1319502, 1319881, 1320254, 1320649, 1321044, 1321433, 1321814, 1322200, 1322582, 1322979,
    1323371, 1323750, 1324127, 1324497, 1324871, 1325263, 1325639, 1326027, 1326411, 1326773,
    1327166, 1327556, 1327930, 1328294]

def LB_19 : List ℕ := [
    1266802, 1267335, 1267862, 1268416, 1268928, 1269464, 1270003, 1270542, 1271068, 1271598,
    1272131, 1272686, 1273222, 1273759, 1274275, 1274812, 1275358, 1275882, 1276424, 1276965,
    1277480, 1278000, 1278537, 1279042, 1279591, 1280122, 1280671, 1281224, 1281762, 1282278,
    1282821, 1283321, 1283847, 1284373, 1284926, 1285456, 1285986, 1286527, 1287048, 1287597,
    1288114, 1288643, 1289193, 1289739, 1290251, 1290771, 1291318, 1291859, 1292414, 1292948,
    1293484, 1294018, 1294554, 1295075, 1295594, 1296135, 1296650, 1297184, 1297730, 1298262,
    1298811, 1299326, 1299872, 1300408, 1300947, 1301516, 1302044, 1302561, 1303105, 1303646,
    1304187, 1304738, 1305264, 1305828, 1306364, 1306885, 1307416, 1307986, 1308515, 1309021,
    1309575, 1310100, 1310668, 1311235, 1311785, 1312342, 1312893, 1313429, 1313979, 1314510,
    1315039, 1315594, 1316132, 1316661, 1317191, 1317747, 1318284, 1318817, 1319341, 1319870,
    1320401, 1320971, 1321493, 1322056, 1322599, 1323152, 1323691, 1324226, 1324752, 1325303,
    1325849, 1326386, 1326913, 1327462, 1327995, 1328530]

def LA_20 : List ℕ := [
    1328691, 1329093, 1329474, 1329859, 1330248, 1330644, 1331047, 1331429, 1331795, 1332189,
    1332589, 1332956, 1333357, 1333760, 1334119, 1334505, 1334883, 1335257, 1335626, 1336020,
    1336409, 1336789, 1337199, 1337572, 1337945, 1338336, 1338734, 1339102, 1339458, 1339841,
    1340250, 1340638, 1341008, 1341388, 1341783, 1342163, 1342536, 1342922, 1343302, 1343676,
    1344065, 1344435, 1344824, 1345218, 1345626, 1346020, 1346423, 1346815, 1347211, 1347598,
    1347991, 1348369, 1348761, 1349136, 1349524, 1349903, 1350300, 1350681, 1351056, 1351444,
    1351834, 1352220, 1352612, 1353010, 1353398, 1353791, 1354161, 1354562, 1354934, 1355322,
    1355702, 1356093, 1356492, 1356893, 1357299, 1357694, 1358086, 1358488, 1358886, 1359254,
    1359648, 1360000, 1360392, 1360769, 1361151, 1361542, 1361932, 1362316, 1362710, 1363095,
    1363478, 1363865, 1364260, 1364652, 1365049, 1365447, 1365830, 1366242, 1366611, 1367007,
    1367401, 1367779, 1368166, 1368538, 1368936, 1369317, 1369714, 1370119, 1370507, 1370900,
    1371296, 1371680, 1372083, 1372474, 1372862, 1373245, 1373631, 1374042, 1374446, 1374814,
    1375210, 1375605, 1375975, 1376400, 1376791, 1377182, 1377549, 1377945, 1378337, 1378732,
    1379129, 1379514, 1379900, 1380307, 1380698, 1381082, 1381478, 1381868, 1382262, 1382675,
    1383056, 1383426, 1383830, 1384230, 1384623, 1385020, 1385429, 1385830, 1386249, 1386628,
    1387029, 1387406, 1387796, 1388179, 1388577, 1388966, 1389360, 1389745, 1390153, 1390529]

def LB_20 : List ℕ := [
    1329098, 1329648, 1330186, 1330746, 1331304, 1331834, 1332386, 1332924, 1333481, 1334033,
    1334564, 1335101, 1335618, 1336175, 1336706, 1337278, 1337806, 1338359, 1338909, 1339418,
    1339957, 1340525, 1341053, 1341607, 1342150, 1342683, 1343211, 1343756, 1344296, 1344832,
    1345398, 1345957, 1346527, 1347091, 1347640, 1348180, 1348734, 1349268, 1349801, 1350367,
    1350902, 1351440, 1351996, 1352549, 1353111, 1353653, 1354187, 1354745, 1355277, 1355822,
    1356384, 1356947, 1357523, 1358073, 1358638, 1359179, 1359728, 1360243, 1360783, 1361322,
    1361874, 1362429, 1362968, 1363527, 1364064, 1364630, 1365188, 1365729, 1366311, 1366842,
    1367402, 1367943, 1368473, 1369032, 1369576, 1370149, 1370688, 1371250, 1371814, 1372365,
    1372920, 1373470, 1374032, 1374595, 1375123, 1375688, 1376253, 1376810, 1377361, 1377896,
    1378445, 1379021, 1379563, 1380117, 1380677, 1381221, 1381789, 1382337, 1382898, 1383433,
    1383993, 1384563, 1385121, 1385709, 1386285, 1386832, 1387372, 1387920, 1388471, 1389017,
    1389585, 1390149, 1390706]

def LA_21 : List ℕ := [
    1390933, 1391354, 1391747, 1392163, 1392548, 1392931, 1393311, 1393707, 1394072, 1394449,
    1394835, 1395225, 1395605, 1395996, 1396386, 1396781, 1397177, 1397561, 1397963, 1398350,
    1398731, 1399135, 1399532, 1399919, 1400315, 1400695, 1401068, 1401471, 1401860, 1402235,
    1402628, 1402998, 1403403, 1403791, 1404198, 1404581, 1404981, 1405373, 1405771, 1406143,
    1406546, 1406948, 1407344, 1407740, 1408150, 1408557, 1408933, 1409322, 1409702, 1410093,
    1410485, 1410874, 1411289, 1411669, 1412059, 1412437, 1412850, 1413234, 1413631, 1414041,
    1414426, 1414809, 1415186, 1415587, 1415977, 1416383, 1416772, 1417166, 1417570, 1417977,
    1418358, 1418759, 1419153, 1419553, 1419954, 1420353, 1420766, 1421159, 1421559, 1421966,
    1422362, 1422773, 1423171, 1423560, 1423971, 1424365, 1424757, 1425147, 1425550, 1425967,
    1426371, 1426773, 1427135, 1427525, 1427916, 1428319, 1428718, 1429115, 1429521, 1429923,
    1430341, 1430736, 1431146, 1431544, 1431936, 1432333, 1432746, 1433142, 1433544, 1433930,
    1434336, 1434718, 1435111, 1435510, 1435914, 1436296, 1436692, 1437096, 1437473, 1437880,
    1438262, 1438664, 1439088, 1439497, 1439901, 1440296, 1440699, 1441087, 1441497, 1441897,
    1442302, 1442705, 1443094, 1443523, 1443912, 1444305, 1444697, 1445099, 1445503, 1445898,
    1446294, 1446688, 1447089, 1447492, 1447884, 1448285, 1448720, 1449119, 1449531, 1449940,
    1450341, 1450733, 1451135, 1451546, 1451938, 1452337]

def LB_21 : List ℕ := [
    1391277, 1391836, 1392421, 1392955, 1393498, 1394027, 1394565, 1395116, 1395649, 1396215,
    1396767, 1397326, 1397887, 1398429, 1398983, 1399546, 1400109, 1400652, 1401176, 1401732,
    1402275, 1402829, 1403375, 1403927, 1404482, 1405045, 1405610, 1406144, 1406708, 1407278,
    1407839, 1408425, 1408958, 1409503, 1410063, 1410609, 1411169, 1411725, 1412273, 1412842,
    1413395, 1413956, 1414501, 1415055, 1415608, 1416166, 1416729, 1417274, 1417858, 1418407,
    1418969, 1419531, 1420098, 1420663, 1421226, 1421808, 1422368, 1422950, 1423491, 1424070,
    1424629, 1425191, 1425746, 1426343, 1426890, 1427418, 1427978, 1428554, 1429109, 1429675,
    1430264, 1430836, 1431401, 1431956, 1432526, 1433095, 1433657, 1434225, 1434775, 1435340,
    1435894, 1436437, 1436999, 1437557, 1438110, 1438675, 1439272, 1439841, 1440408, 1440970,
    1441531, 1442110, 1442669, 1443243, 1443811, 1444373, 1444937, 1445503, 1446055, 1446626,
    1447188, 1447742, 1448314, 1448916, 1449486, 1450061, 1450624, 1451190, 1451765, 1452323]

def LA_22 : List ℕ := [
    1452748, 1453147, 1453533, 1453906, 1454317, 1454725, 1455124, 1455514, 1455903, 1456307,
    1456709, 1457104, 1457514, 1457936, 1458368, 1458748, 1459144, 1459526, 1459914, 1460318,
    1460705, 1461118, 1461528, 1461911, 1462310, 1462710, 1463118, 1463521, 1463936, 1464357,
    1464763, 1465169, 1465551, 1465970, 1466381, 1466803, 1467197, 1467605, 1467998, 1468392,
    1468788, 1469223, 1469633, 1470031, 1470450, 1470827, 1471215, 1471602, 1471998, 1472399,
    1472793, 1473193, 1473587, 1473995, 1474416, 1474806, 1475243, 1475638, 1476060, 1476470,
    1476876, 1477255, 1477669, 1478052, 1478457, 1478850, 1479254, 1479668, 1480079, 1480483,
    1480899, 1481294, 1481691, 1482103, 1482509, 1482883, 1483303, 1483723, 1484114, 1484523,
    1484929, 1485345, 1485750, 1486141, 1486532, 1486951, 1487365, 1487777, 1488188, 1488587,
    1488990, 1489399, 1489793, 1490192, 1490587, 1490987, 1491389, 1491786, 1492195, 1492589,
    1493010, 1493421, 1493820, 1494234, 1494638, 1495040, 1495440, 1495847, 1496245, 1496669,
    1497077, 1497458, 1497873, 1498245, 1498647, 1499055, 1499473, 1499873, 1500288, 1500716,
    1501117, 1501526, 1501959, 1502371, 1502767, 1503180, 1503583, 1503985, 1504375, 1504781,
    1505188, 1505597, 1505993, 1506403, 1506837, 1507238, 1507662, 1508065, 1508478, 1508879,
    1509273, 1509711, 1510097, 1510521, 1510931, 1511341, 1511760, 1512156, 1512557, 1512944,
    1513357, 1513763, 1514172]

def LB_22 : List ℕ := [
    1452907, 1453445, 1453997, 1454561, 1455140, 1455683, 1456251, 1456825, 1457390, 1457980,
    1458573, 1459125, 1459662, 1460236, 1460774, 1461359, 1461914, 1462482, 1463049, 1463627,
    1464202, 1464800, 1465367, 1465933, 1466522, 1467090, 1467668, 1468220, 1468780, 1469381,
    1469947, 1470535, 1471074, 1471623, 1472180, 1472748, 1473320, 1473884, 1474473, 1475032,
    1475618, 1476207, 1476785, 1477331, 1477902, 1478467, 1479029, 1479614, 1480200, 1480773,
    1481333, 1481907, 1482483, 1483015, 1483617, 1484179, 1484754, 1485341, 1485899, 1486462,
    1487042, 1487637, 1488218, 1488779, 1489351, 1489924, 1490477, 1491046, 1491606, 1492179,
    1492755, 1493329, 1493906, 1494494, 1495049, 1495624, 1496195, 1496796, 1497339, 1497910,
    1498457, 1499029, 1499617, 1500183, 1500776, 1501354, 1501961, 1502529, 1503111, 1503689,
    1504258, 1504814, 1505385, 1505959, 1506541, 1507132, 1507732, 1508295, 1508867, 1509454,
    1510020, 1510614, 1511191, 1511778, 1512352, 1512895, 1513470, 1514061]

def LA_23 : List ℕ := [
    1514557, 1514971, 1515370, 1515802, 1516213, 1516648, 1517060, 1517453, 1517872, 1518276,
    1518700, 1519098, 1519501, 1519916, 1520320, 1520752, 1521174, 1521572, 1521978, 1522407,
    1522797, 1523216, 1523638, 1524063, 1524473, 1524889, 1525307, 1525716, 1526118, 1526522,
    1526933, 1527343, 1527751, 1528176, 1528584, 1528974, 1529388, 1529818, 1530232, 1530641,
    1531060, 1531476, 1531892, 1532291, 1532708, 1533105, 1533508, 1533913, 1534292, 1534723,
    1535116, 1535542, 1535964, 1536368, 1536777, 1537201, 1537604, 1538022, 1538434, 1538848,
    1539266, 1539696, 1540086, 1540501, 1540910, 1541326, 1541737, 1542142, 1542551, 1542941,
    1543361, 1543769, 1544198, 1544591, 1545015, 1545406, 1545838, 1546238, 1546671, 1547099,
    1547529, 1547946, 1548362, 1548768, 1549201, 1549617, 1550043, 1550442, 1550830, 1551254,
    1551676, 1552065, 1552495, 1552934, 1553343, 1553757, 1554159, 1554549, 1554986, 1555398,
    1555782, 1556189, 1556601, 1557004, 1557417, 1557853, 1558266, 1558699, 1559093, 1559507,
    1559921, 1560327, 1560751, 1561148, 1561547, 1561956, 1562364, 1562785, 1563197, 1563620,
    1564043, 1564471, 1564890, 1565296, 1565708, 1566120, 1566544, 1566969, 1567387, 1567788,
    1568183, 1568583, 1568998, 1569425, 1569853, 1570264, 1570693, 1571123, 1571525, 1571950,
    1572378, 1572809, 1573234, 1573640, 1574054, 1574433, 1574840, 1575237, 1575667]

def LB_23 : List ℕ := [
    1514595, 1515195, 1515779, 1516377, 1516976, 1517530, 1518120, 1518707, 1519268, 1519850,
    1520437, 1521038, 1521612, 1522202, 1522765, 1523346, 1523958, 1524538, 1525125, 1525710,
    1526279, 1526859, 1527437, 1528022, 1528610, 1529184, 1529769, 1530356, 1530944, 1531529,
    1532109, 1532689, 1533258, 1533828, 1534382, 1534954, 1535552, 1536145, 1536724, 1537316,
    1537887, 1538477, 1539061, 1539663, 1540227, 1540805, 1541401, 1541969, 1542551, 1543118,
    1543695, 1544307, 1544866, 1545435, 1546027, 1546627, 1547226, 1547843, 1548418, 1549013,
    1549596, 1550200, 1550753, 1551346, 1551914, 1552512, 1553120, 1553703, 1554274, 1554854,
    1555439, 1556000, 1556578, 1557143, 1557763, 1558341, 1558937, 1559513, 1560097, 1560683,
    1561230, 1561828, 1562408, 1562977, 1563579, 1564178, 1564794, 1565356, 1565927, 1566540,
    1567138, 1567707, 1568270, 1568847, 1569453, 1570045, 1570637, 1571238, 1571818, 1572425,
    1573044, 1573618, 1574194, 1574762, 1575310, 1575914]

def LA_24 : List ℕ := [
    1576093, 1576497, 1576914, 1577336, 1577737, 1578126, 1578551, 1578949, 1579357, 1579759,
    1580172, 1580572, 1580991, 1581421, 1581848, 1582272, 1582663, 1583076, 1583497, 1583932,
    1584347, 1584766, 1585187, 1585617, 1586036, 1586431, 1586837, 1587252, 1587656, 1588083,
    1588506, 1588938, 1589359, 1589773, 1590174, 1590591, 1590983, 1591405, 1591820, 1592253,
    1592680, 1593113, 1593551, 1593986, 1594392, 1594793, 1595209, 1595610, 1596017, 1596434,
    1596868, 1597292, 1597730, 1598151, 1598558, 1598970, 1599381, 1599818, 1600248, 1600663,
    1601088, 1601498, 1601918, 1602315, 1602740, 1603182, 1603610, 1604031, 1604437, 1604829,
    1605244, 1605650, 1606102, 1606498, 1606929, 1607352, 1607787, 1608232, 1608628, 1609033,
    1609468, 1609891, 1610322, 1610739, 1611172, 1611574, 1612014, 1612433, 1612844, 1613285,
    1613718, 1614124, 1614563, 1614989, 1615423, 1615840, 1616257, 1616670, 1617095, 1617504,
    1617939, 1618369, 1618788, 1619182, 1619625, 1620031, 1620471, 1620907, 1621324, 1621726,
    1622130, 1622558, 1622992, 1623424, 1623850, 1624290, 1624704, 1625113, 1625533, 1625945,
    1626372, 1626789, 1627232, 1627642, 1628071, 1628505, 1628924, 1629316, 1629767, 1630191,
    1630603, 1631012, 1631441, 1631876, 1632313, 1632738, 1633150, 1633574, 1634000, 1634425,
    1634836, 1635254, 1635677, 1636076, 1636501, 1636939, 1637378]

def LB_24 : List ℕ := [
    1576501, 1577102, 1577678, 1578248, 1578824, 1579405, 1579962, 1580542, 1581138, 1581729,
    1582333, 1582911, 1583493, 1584092, 1584700, 1585286, 1585892, 1586465, 1587036, 1587606,
    1588214, 1588819, 1589418, 1589996, 1590576, 1591158, 1591731, 1592343, 1592955, 1593565,
    1594157, 1594740, 1595313, 1595892, 1596477, 1597091, 1597699, 1598288, 1598868, 1599456,
    1600072, 1600664, 1601253, 1601845, 1602427, 1603014, 1603646, 1604253, 1604800, 1605363,
    1605981, 1606567, 1607172, 1607781, 1608380, 1608944, 1609552, 1610164, 1610762, 1611360,
    1611951, 1612557, 1613153, 1613772, 1614373, 1614964, 1615585, 1616162, 1616757, 1617337,
    1617948, 1618550, 1619121, 1619718, 1620328, 1620942, 1621527, 1622103, 1622696, 1623311,
    1623925, 1624517, 1625107, 1625695, 1626292, 1626908, 1627499, 1628095, 1628689, 1629273,
    1629890, 1630501, 1631069, 1631680, 1632299, 1632890, 1633480, 1634088, 1634672, 1635267,
    1635860, 1636443, 1637054]

def LA_25 : List ℕ := [
    1637804, 1638222, 1638654, 1639026, 1639449, 1639856, 1640293, 1640745, 1641154, 1641576,
    1642010, 1642435, 1642841, 1643272, 1643721, 1644150, 1644557, 1644972, 1645393, 1645830,
    1646259, 1646689, 1647104, 1647535, 1647975, 1648424, 1648862, 1649308, 1649720, 1650132,
    1650525, 1650953, 1651379, 1651813, 1652253, 1652663, 1653100, 1653524, 1653976, 1654425,
    1654831, 1655247, 1655684, 1656113, 1656538, 1656974, 1657424, 1657842, 1658259, 1658677,
    1659112, 1659550, 1659956, 1660377, 1660807, 1661232, 1661664, 1662094, 1662526, 1662948,
    1663376, 1663822, 1664236, 1664675, 1665084, 1665505, 1665930, 1666395, 1666809, 1667213,
    1667632, 1668043, 1668474, 1668884, 1669309, 1669750, 1670158, 1670592, 1671034, 1671457,
    1671875, 1672320, 1672740, 1673144, 1673588, 1674018, 1674448, 1674881, 1675307, 1675746,
    1676183, 1676611, 1677042, 1677466, 1677905, 1678334, 1678763, 1679205, 1679630, 1680058,
    1680471, 1680928, 1681363, 1681783, 1682211, 1682632, 1683084, 1683515, 1683933, 1684361,
    1684799, 1685214, 1685626, 1686059, 1686499, 1686931, 1687361, 1687810, 1688245, 1688704,
    1689137, 1689547, 1689980, 1690406, 1690845, 1691281, 1691717, 1692161, 1692595, 1693001,
    1693439, 1693878, 1694299, 1694702, 1695147, 1695555, 1696003, 1696427, 1696858, 1697278,
    1697706, 1698139, 1698572]

def LB_25 : List ℕ := [
    1637669, 1638266, 1638840, 1639411, 1640008, 1640627, 1641230, 1641822, 1642436, 1643038,
    1643648, 1644258, 1644825, 1645419, 1646033, 1646636, 1647240, 1647857, 1648483, 1649114,
    1649709, 1650281, 1650862, 1651474, 1652092, 1652681, 1653302, 1653919, 1654540, 1655128,
    1655724, 1656347, 1656951, 1657570, 1658165, 1658770, 1659380, 1659960, 1660556, 1661163,
    1661778, 1662393, 1662991, 1663599, 1664195, 1664823, 1665404, 1666002, 1666638, 1667202,
    1667806, 1668390, 1668972, 1669602, 1670179, 1670801, 1671404, 1672016, 1672617, 1673203,
    1673818, 1674437, 1675039, 1675649, 1676276, 1676867, 1677475, 1678096, 1678700, 1679311,
    1679905, 1680518, 1681153, 1681753, 1682350, 1682966, 1683586, 1684189, 1684797, 1685381,
    1685983, 1686605, 1687211, 1687841, 1688475, 1689092, 1689677, 1690283, 1690906, 1691510,
    1692144, 1692747, 1693349, 1693958, 1694540, 1695164, 1695756, 1696379, 1696979, 1697575,
    1698190, 1698785]

def LA_26 : List ℕ := [
    1698979, 1699398, 1699841, 1700275, 1700700, 1701123, 1701555, 1701973, 1702405, 1702855,
    1703282, 1703707, 1704147, 1704565, 1704978, 1705423, 1705852, 1706310, 1706733, 1707167,
    1707606, 1708035, 1708485, 1708939, 1709355, 1709769, 1710212, 1710645, 1711067, 1711492,
    1711921, 1712333, 1712786, 1713224, 1713662, 1714097, 1714526, 1714967, 1715398, 1715834,
    1716278, 1716697, 1717159, 1717604, 1718051, 1718516, 1718929, 1719340, 1719784, 1720218,
    1720663, 1721075, 1721505, 1721952, 1722360, 1722797, 1723217, 1723649, 1724094, 1724524,
    1724946, 1725386, 1725855, 1726319, 1726752, 1727190, 1727601, 1728041, 1728456, 1728910,
    1729319, 1729746, 1730201, 1730629, 1731054, 1731476, 1731912, 1732325, 1732762, 1733178,
    1733616, 1734071, 1734517, 1734944, 1735386, 1735833, 1736281, 1736730, 1737162, 1737609,
    1738023, 1738471, 1738898, 1739340, 1739792, 1740232, 1740659, 1741081, 1741505, 1741952,
    1742409, 1742862, 1743302, 1743749, 1744160, 1744590, 1745013, 1745440, 1745884, 1746335,
    1746770, 1747223, 1747642, 1748072, 1748502, 1748931, 1749373, 1749815, 1750279, 1750706,
    1751129, 1751574, 1751997, 1752419, 1752839, 1753278, 1753747, 1754177, 1754620, 1755072,
    1755514, 1755963, 1756395, 1756827, 1757281, 1757740, 1758155, 1758618, 1759058, 1759503,
    1759946]

def LB_26 : List ℕ := [
    1699371, 1699992, 1700599, 1701207, 1701809, 1702407, 1703035, 1703637, 1704257, 1704835,
    1705462, 1706071, 1706694, 1707305, 1707923, 1708553, 1709181, 1709761, 1710384, 1710991,
    1711586, 1712184, 1712804, 1713427, 1714047, 1714656, 1715279, 1715892, 1716507, 1717130,
    1717756, 1718416, 1718995, 1719594, 1720230, 1720832, 1721439, 1722058, 1722662, 1723257,
    1723856, 1724489, 1725086, 1725722, 1726397, 1727014, 1727599, 1728209, 1728827, 1729418,
    1730033, 1730652, 1731247, 1731868, 1732448, 1733050, 1733679, 1734317, 1734929, 1735558,
    1736190, 1736818, 1737439, 1738038, 1738666, 1739280, 1739913, 1740519, 1741125, 1741740,
    1742375, 1743016, 1743649, 1744249, 1744825, 1745441, 1746064, 1746699, 1747329, 1747920,
    1748527, 1749150, 1749779, 1750407, 1751020, 1751645, 1752240, 1752828, 1753469, 1754091,
    1754727, 1755348, 1755982, 1756593, 1757229, 1757850, 1758477, 1759114, 1759738]

def LA_27 : List ℕ := [
    1760393, 1760826, 1761277, 1761687, 1762109, 1762541, 1762978, 1763424, 1763844, 1764282,
    1764731, 1765169, 1765598, 1766021, 1766477, 1766912, 1767378, 1767813, 1768250, 1768684,
    1769110, 1769536, 1769979, 1770456, 1770919, 1771356, 1771800, 1772239, 1772664, 1773102,
    1773543, 1773990, 1774419, 1774860, 1775290, 1775752, 1776209, 1776611, 1777065, 1777502,
    1777950, 1778407, 1778837, 1779289, 1779731, 1780167, 1780602, 1781053, 1781496, 1781926,
    1782345, 1782782, 1783217, 1783656, 1784113, 1784561, 1785017, 1785451, 1785868, 1786298,
    1786745, 1787182, 1787624, 1788080, 1788494, 1788914, 1789360, 1789822, 1790251, 1790696,
    1791129, 1791596, 1792028, 1792485, 1792925, 1793353, 1793799, 1794251, 1794679, 1795151,
    1795596, 1796032, 1796440, 1796902, 1797338, 1797762, 1798200, 1798653, 1799108, 1799544,
    1799999, 1800433, 1800877, 1801330, 1801766, 1802213, 1802660, 1803077, 1803520, 1803964,
    1804408, 1804847, 1805298, 1805737, 1806189, 1806630, 1807077, 1807512, 1807950, 1808399,
    1808829, 1809267, 1809706, 1810146, 1810596, 1811057, 1811486, 1811942, 1812390, 1812815,
    1813234, 1813670, 1814096, 1814571, 1815019, 1815466, 1815908, 1816379, 1816838, 1817292,
    1817748, 1818183, 1818633, 1819093, 1819518, 1819976, 1820451, 1820905]

def LB_27 : List ℕ := [
    1760370, 1760990, 1761596, 1762203, 1762809, 1763428, 1764038, 1764665, 1765281, 1765871,
    1766520, 1767140, 1767777, 1768390, 1769009, 1769601, 1770246, 1770914, 1771538, 1772159,
    1772760, 1773383, 1774017, 1774628, 1775245, 1775889, 1776494, 1777116, 1777749, 1778387,
    1779003, 1779634, 1780249, 1780873, 1781516, 1782115, 1782726, 1783344, 1783970, 1784611,
    1785227, 1785842, 1786443, 1787073, 1787703, 1788321, 1788914, 1789547, 1790170, 1790797,
    1791434, 1792062, 1792683, 1793305, 1793943, 1794562, 1795225, 1795840, 1796430, 1797079,
    1797678, 1798306, 1798937, 1799569, 1800199, 1800818, 1801453, 1802090, 1802695, 1803319,
    1803933, 1804579, 1805195, 1805820, 1806465, 1807083, 1807697, 1808325, 1808956, 1809557,
    1810181, 1810801, 1811456, 1812091, 1812682, 1813301, 1813915, 1814563, 1815202, 1815825,
    1816485, 1817134, 1817767, 1818406, 1819034, 1819656, 1820322, 1820960]

def LA_28 : List ℕ := [
    1821340, 1821812, 1822227, 1822667, 1823112, 1823558, 1823988, 1824419, 1824842, 1825297,
    1825735, 1826175, 1826623, 1827059, 1827507, 1827970, 1828420, 1828859, 1829289, 1829754,
    1830198, 1830654, 1831117, 1831555, 1832001, 1832427, 1832865, 1833323, 1833760, 1834229,
    1834678, 1835106, 1835559, 1836026, 1836450, 1836908, 1837342, 1837808, 1838255, 1838719,
    1839158, 1839598, 1840067, 1840525, 1840956, 1841441, 1841905, 1842353, 1842796, 1843224,
    1843654, 1844087, 1844517, 1844971, 1845407, 1845857, 1846308, 1846744, 1847178, 1847630,
    1848088, 1848529, 1848989, 1849456, 1849923, 1850389, 1850839, 1851310, 1851755, 1852201,
    1852633, 1853093, 1853541, 1853997, 1854469, 1854938, 1855387, 1855816, 1856284, 1856727,
    1857198, 1857647, 1858092, 1858564, 1859028, 1859474, 1859929, 1860380, 1860819, 1861271,
    1861727, 1862175, 1862647, 1863120, 1863557, 1864001, 1864443, 1864895, 1865344, 1865806,
    1866273, 1866729, 1867172, 1867601, 1868057, 1868510, 1868967, 1869422, 1869873, 1870330,
    1870785, 1871244, 1871697, 1872152, 1872584, 1873042, 1873485, 1873937, 1874411, 1874844,
    1875316, 1875766, 1876222, 1876678, 1877140, 1877613, 1878056, 1878511, 1878962, 1879410,
    1879834, 1880308, 1880759, 1881230, 1881696, 1882143]

def LB_28 : List ℕ := [
    1821605, 1822206, 1822838, 1823462, 1824064, 1824665, 1825307, 1825918, 1826555, 1827178,
    1827818, 1828461, 1829078, 1829708, 1830359, 1830997, 1831621, 1832243, 1832863, 1833499,
    1834135, 1834776, 1835400, 1836053, 1836662, 1837299, 1837939, 1838575, 1839214, 1839855,
    1840505, 1841138, 1841804, 1842449, 1843064, 1843672, 1844285, 1844910, 1845532, 1846156,
    1846789, 1847417, 1848051, 1848691, 1849354, 1850001, 1850652, 1851313, 1851951, 1852561,
    1853211, 1853837, 1854506, 1855168, 1855769, 1856433, 1857075, 1857718, 1858362, 1859018,
    1859652, 1860295, 1860914, 1861571, 1862198, 1862871, 1863515, 1864125, 1864750, 1865401,
    1866045, 1866704, 1867324, 1867951, 1868595, 1869229, 1869881, 1870532, 1871174, 1871805,
    1872441, 1873083, 1873718, 1874374, 1875010, 1875657, 1876296, 1876941, 1877607, 1878238,
    1878881, 1879520, 1880143, 1880796, 1881436, 1882095]

def LA_29 : List ℕ := [
    1882581, 1883003, 1883440, 1883876, 1884306, 1884777, 1885229, 1885685, 1886125, 1886590,
    1887026, 1887481, 1887939, 1888399, 1888842, 1889338, 1889790, 1890222, 1890687, 1891136,
    1891598, 1892060, 1892533, 1892983, 1893438, 1893902, 1894361, 1894799, 1895279, 1895740,
    1896214, 1896680, 1897141, 1897585, 1898042, 1898484, 1898946, 1899404, 1899850, 1900307,
    1900759, 1901218, 1901657, 1902107, 1902557, 1903004, 1903472, 1903902, 1904374, 1904826,
    1905290, 1905727, 1906217, 1906660, 1907113, 1907577, 1908050, 1908499, 1908962, 1909427,
    1909880, 1910338, 1910819, 1911267, 1911697, 1912157, 1912606, 1913072, 1913512, 1913965,
    1914408, 1914865, 1915299, 1915740, 1916211, 1916670, 1917136, 1917598, 1918046, 1918504,
    1918921, 1919361, 1919818, 1920278, 1920735, 1921162, 1921625, 1922052, 1922533, 1922994,
    1923466, 1923927, 1924390, 1924844, 1925298, 1925742, 1926194, 1926641, 1927091, 1927538,
    1928016, 1928462, 1928918, 1929386, 1929858, 1930310, 1930749, 1931198, 1931649, 1932134,
    1932616, 1933074, 1933532, 1934005, 1934454, 1934892, 1935375, 1935843, 1936295, 1936754,
    1937196, 1937658, 1938116, 1938576, 1939033, 1939489, 1939950, 1940406, 1940858, 1941311,
    1941773, 1942226, 1942672]

def LB_29 : List ℕ := [
    1882696, 1883325, 1883932, 1884567, 1885210, 1885848, 1886498, 1887119, 1887761, 1888414,
    1889069, 1889725, 1890340, 1890999, 1891643, 1892294, 1892954, 1893599, 1894253, 1894879,
    1895538, 1896215, 1896878, 1897507, 1898153, 1898792, 1899425, 1900066, 1900718, 1901354,
    1901987, 1902629, 1903266, 1903890, 1904548, 1905209, 1905842, 1906492, 1907128, 1907780,
    1908436, 1909101, 1909744, 1910398, 1911046, 1911671, 1912314, 1912964, 1913596, 1914240,
    1914870, 1915489, 1916138, 1916785, 1917442, 1918089, 1918709, 1919323, 1919957, 1920618,
    1921240, 1921878, 1922528, 1923177, 1923841, 1924504, 1925140, 1925768, 1926394, 1927034,
    1927691, 1928334, 1928979, 1929639, 1930290, 1930914, 1931552, 1932217, 1932899, 1933545,
    1934211, 1934824, 1935507, 1936145, 1936801, 1937434, 1938079, 1938736, 1939378, 1940020,
    1940675, 1941309, 1941963, 1942592]

def LA_30 : List ℕ := [
    1943132, 1943584, 1944033, 1944481, 1944943, 1945390, 1945846, 1946301, 1946749, 1947204,
    1947659, 1948123, 1948626, 1949093, 1949551, 1950017, 1950487, 1950921, 1951386, 1951862,
    1952319, 1952784, 1953231, 1953688, 1954159, 1954606, 1955106, 1955563, 1956013, 1956486,
    1956934, 1957380, 1957830, 1958300, 1958753, 1959230, 1959665, 1960123, 1960595, 1961059,
    1961520, 1961965, 1962433, 1962915, 1963379, 1963841, 1964304, 1964775, 1965248, 1965724,
    1966188, 1966648, 1967124, 1967557, 1968017, 1968482, 1968943, 1969428, 1969854, 1970330,
    1970780, 1971257, 1971715, 1972181, 1972655, 1973100, 1973576, 1974047, 1974513, 1974951,
    1975403, 1975861, 1976325, 1976787, 1977254, 1977714, 1978184, 1978650, 1979097, 1979568,
    1980063, 1980545, 1980992, 1981456, 1981912, 1982403, 1982880, 1983329, 1983784, 1984238,
    1984700, 1985148, 1985618, 1986062, 1986530, 1986963, 1987437, 1987935, 1988385, 1988855,
    1989310, 1989785, 1990242, 1990714, 1991208, 1991669, 1992130, 1992589, 1993047, 1993522,
    1993986, 1994456, 1994931, 1995392, 1995834, 1996314, 1996809, 1997258, 1997710, 1998188,
    1998667, 1999099, 1999561, 2000047, 2000508, 2000982, 2001475, 2001936, 2002400, 2002862,
    2003327]

def LB_30 : List ℕ := [
    1943240, 1943874, 1944511, 1945150, 1945806, 1946453, 1947078, 1947733, 1948397, 1949079,
    1949733, 1950384, 1951021, 1951683, 1952337, 1952976, 1953631, 1954275, 1954950, 1955608,
    1956267, 1956909, 1957543, 1958186, 1958830, 1959481, 1960126, 1960794, 1961445, 1962076,
    1962756, 1963416, 1964066, 1964732, 1965404, 1966064, 1966730, 1967374, 1968010, 1968665,
    1969318, 1969957, 1970616, 1971274, 1971931, 1972601, 1973239, 1973915, 1974566, 1975194,
    1975837, 1976493, 1977136, 1977793, 1978471, 1979104, 1979770, 1980477, 1981112, 1981758,
    1982439, 1983108, 1983744, 1984402, 1985040, 1985685, 1986337, 1986958, 1987644, 1988307,
    1988957, 1989619, 1990270, 1990949, 1991620, 1992267, 1992923, 1993586, 1994236, 1994913,
    1995563, 1996214, 1996893, 1997536, 1998203, 1998852, 1999494, 2000174, 2000822, 2001527,
    2002168, 2002827, 2003492]

def LA_31 : List ℕ := [
    2003787, 2004261, 2004728, 2005203, 2005654, 2006116, 2006593, 2007070, 2007535, 2008021,
    2008490, 2008943, 2009427, 2009882, 2010361, 2010821, 2011279, 2011728, 2012188, 2012691,
    2013142, 2013608, 2014083, 2014560, 2015017, 2015484, 2015959, 2016428, 2016891, 2017366,
    2017810, 2018288, 2018738, 2019210, 2019688, 2020155, 2020619, 2021089, 2021534, 2021991,
    2022470, 2022927, 2023402, 2023859, 2024326, 2024795, 2025281, 2025755, 2026217, 2026668,
    2027139, 2027636, 2028107, 2028582, 2029070, 2029543, 2030018, 2030479, 2030957, 2031425,
    2031883, 2032355, 2032817, 2033290, 2033728, 2034195, 2034658, 2035126, 2035596, 2036073,
    2036534, 2037000, 2037460, 2037946, 2038420, 2038888, 2039362, 2039831, 2040305, 2040781,
    2041259, 2041729, 2042201, 2042675, 2043137, 2043594, 2044079, 2044540, 2045011, 2045473,
    2045965, 2046454, 2046932, 2047380, 2047855, 2048341, 2048797, 2049298, 2049760, 2050229,
    2050713, 2051178, 2051668, 2052131, 2052595, 2053075, 2053556, 2054046, 2054520, 2054982,
    2055468, 2055925, 2056403, 2056877, 2057353, 2057817, 2058282, 2058765, 2059257, 2059705,
    2060192, 2060657, 2061108, 2061586, 2062026, 2062499, 2062974, 2063449, 2063947]

def LB_31 : List ℕ := [
    2004146, 2004810, 2005474, 2006117, 2006781, 2007454, 2008127, 2008787, 2009463, 2010120,
    2010775, 2011413, 2012065, 2012751, 2013395, 2014062, 2014743, 2015403, 2016054, 2016710,
    2017386, 2018027, 2018674, 2019348, 2020019, 2020669, 2021329, 2021961, 2022631, 2023297,
    2023941, 2024603, 2025287, 2025957, 2026605, 2027268, 2027948, 2028619, 2029305, 2029983,
    2030637, 2031302, 2031963, 2032617, 2033282, 2033914, 2034587, 2035238, 2035899, 2036559,
    2037209, 2037896, 2038551, 2039235, 2039881, 2040567, 2041237, 2041901, 2042577, 2043226,
    2043895, 2044551, 2045216, 2045892, 2046583, 2047239, 2047898, 2048590, 2049255, 2049923,
    2050594, 2051258, 2051930, 2052592, 2053274, 2053958, 2054628, 2055293, 2055958, 2056634,
    2057296, 2057971, 2058637, 2059315, 2059983, 2060639, 2061294, 2061933, 2062592, 2063275,
    2063961]

def LA_32 : List ℕ := [
    2064419, 2064897, 2065348, 2065814, 2066293, 2066767, 2067233, 2067705, 2068161, 2068631,
    2069123, 2069584, 2070077, 2070542, 2071005, 2071480, 2071959, 2072433, 2072923, 2073382,
    2073863, 2074327, 2074802, 2075284, 2075782, 2076260, 2076736, 2077209, 2077664, 2078128,
    2078614, 2079125, 2079595, 2080059, 2080540, 2081011, 2081502, 2081981, 2082443, 2082933,
    2083412, 2083873, 2084344, 2084823, 2085297, 2085757, 2086208, 2086672, 2087138, 2087607,
    2088097, 2088544, 2089030, 2089520, 2089991, 2090451, 2090921, 2091394, 2091888, 2092348,
    2092799, 2093278, 2093746, 2094226, 2094708, 2095176, 2095660, 2096130, 2096603, 2097065,
    2097548, 2098022, 2098488, 2098952, 2099409, 2099878, 2100338, 2100822, 2101304, 2101783,
    2102262, 2102726, 2103205, 2103654, 2104140, 2104628, 2105099, 2105580, 2106054, 2106541,
    2107003, 2107472, 2107938, 2108412, 2108885, 2109337, 2109814, 2110282, 2110745, 2111226,
    2111719, 2112178, 2112673, 2113164, 2113620, 2114111, 2114567, 2115035, 2115541, 2116018,
    2116509, 2116982, 2117464, 2117943, 2118427, 2118913, 2119401, 2119897, 2120367, 2120833,
    2121310, 2121794, 2122272, 2122756, 2123232, 2123716, 2124206]

def LB_32 : List ℕ := [
    2064638, 2065300, 2065954, 2066613, 2067285, 2067945, 2068600, 2069280, 2069956, 2070630,
    2071295, 2071960, 2072640, 2073298, 2073980, 2074638, 2075326, 2076005, 2076695, 2077355,
    2078002, 2078679, 2079401, 2080048, 2080721, 2081402, 2082070, 2082764, 2083434, 2084077,
    2084757, 2085434, 2086082, 2086730, 2087396, 2088066, 2088736, 2089407, 2090093, 2090743,
    2091403, 2092083, 2092730, 2093401, 2094072, 2094748, 2095425, 2096091, 2096761, 2097430,
    2098099, 2098757, 2099407, 2100065, 2100737, 2101424, 2102098, 2102753, 2103427, 2104085,
    2104772, 2105450, 2106120, 2106797, 2107457, 2108122, 2108796, 2109439, 2110110, 2110762,
    2111436, 2112120, 2112811, 2113474, 2114155, 2114809, 2115508, 2116188, 2116870, 2117553,
    2118227, 2118916, 2119609, 2120288, 2120942, 2121632, 2122304, 2122991, 2123674, 2124357]

def LA_33 : List ℕ := [
    2124663, 2125153, 2125615, 2126113, 2126573, 2127031, 2127472, 2127953, 2128435, 2128918,
    2129394, 2129870, 2130360, 2130845, 2131324, 2131788, 2132262, 2132715, 2133183, 2133693,
    2134170, 2134659, 2135149, 2135644, 2136115, 2136589, 2137044, 2137526, 2137987, 2138493,
    2138989, 2139489, 2139984, 2140462, 2140952, 2141419, 2141907, 2142411, 2142896, 2143368,
    2143833, 2144338, 2144811, 2145298, 2145783, 2146241, 2146721, 2147187, 2147666, 2148159,
    2148644, 2149109, 2149598, 2150058, 2150532, 2151018, 2151491, 2151981, 2152451, 2152956,
    2153441, 2153916, 2154379, 2154862, 2155356, 2155851, 2156348, 2156816, 2157289, 2157758,
    2158249, 2158737, 2159221, 2159708, 2160206, 2160689, 2161186, 2161667, 2162159, 2162617,
    2163096, 2163575, 2164053, 2164545, 2165040, 2165523, 2166024, 2166500, 2166984, 2167440,
    2167918, 2168400, 2168903, 2169408, 2169900, 2170385, 2170898, 2171366, 2171844, 2172316,
    2172826, 2173301, 2173770, 2174235, 2174723, 2175210, 2175696, 2176177, 2176655, 2177144,
    2177640, 2178138, 2178614, 2179111, 2179595, 2180060, 2180543, 2181021, 2181500, 2181991,
    2182477, 2182952, 2183454, 2183953, 2184437]

def LB_33 : List ℕ := [
    2125032, 2125697, 2126379, 2127021, 2127667, 2128333, 2129026, 2129695, 2130381, 2131063,
    2131723, 2132375, 2133032, 2133745, 2134423, 2135125, 2135800, 2136477, 2137141, 2137803,
    2138503, 2139209, 2139913, 2140582, 2141269, 2141951, 2142670, 2143320, 2143990, 2144689,
    2145375, 2146046, 2146715, 2147396, 2148068, 2148749, 2149414, 2150080, 2150767, 2151434,
    2152122, 2152813, 2153492, 2154173, 2154846, 2155548, 2156236, 2156901, 2157579, 2158265,
    2158948, 2159649, 2160328, 2161019, 2161709, 2162401, 2163062, 2163731, 2164428, 2165126,
    2165818, 2166500, 2167172, 2167847, 2168526, 2169240, 2169939, 2170632, 2171308, 2171984,
    2172674, 2173366, 2174036, 2174705, 2175391, 2176084, 2176758, 2177466, 2178159, 2178857,
    2179532, 2180207, 2180882, 2181562, 2182251, 2182926, 2183627, 2184335]

def LA_34 : List ℕ := [
    2184933, 2185422, 2185898, 2186379, 2186867, 2187329, 2187808, 2188293, 2188790, 2189282,
    2189792, 2190272, 2190760, 2191241, 2191732, 2192234, 2192722, 2193212, 2193664, 2194152,
    2194637, 2195146, 2195628, 2196121, 2196592, 2197072, 2197550, 2198025, 2198511, 2198986,
    2199469, 2199960, 2200452, 2200947, 2201411, 2201904, 2202394, 2202883, 2203356, 2203866,
    2204352, 2204858, 2205360, 2205869, 2206352, 2206839, 2207300, 2207785, 2208261, 2208753,
    2209239, 2209745, 2210231, 2210743, 2211219, 2211713, 2212189, 2212675, 2213175, 2213646,
    2214130, 2214618, 2215076, 2215571, 2216051, 2216532, 2217028, 2217535, 2218018, 2218517,
    2219022, 2219520, 2220010, 2220502, 2221023, 2221517, 2222005, 2222458, 2222961, 2223487,
    2223979, 2224462, 2224958, 2225445, 2225951, 2226427, 2226898, 2227376, 2227874, 2228352,
    2228839, 2229325, 2229814, 2230302, 2230803, 2231311, 2231806, 2232304, 2232801, 2233265,
    2233765, 2234257, 2234735, 2235236, 2235719, 2236218, 2236691, 2237167, 2237681, 2238189,
    2238685, 2239150, 2239669, 2240159, 2240639, 2241112, 2241602, 2242109, 2242594, 2243076,
    2243549, 2244040, 2244526]

def LB_34 : List ℕ := [
    2185014, 2185702, 2186386, 2187071, 2187726, 2188414, 2189112, 2189831, 2190506, 2191194,
    2191899, 2192611, 2193274, 2193953, 2194627, 2195336, 2196028, 2196690, 2197376, 2198051,
    2198715, 2199413, 2200111, 2200796, 2201484, 2202171, 2202850, 2203539, 2204262, 2204960,
    2205675, 2206363, 2207038, 2207712, 2208382, 2209089, 2209795, 2210503, 2211177, 2211879,
    2212553, 2213248, 2213913, 2214616, 2215282, 2215968, 2216661, 2217361, 2218046, 2218750,
    2219477, 2220151, 2220881, 2221576, 2222249, 2222942, 2223679, 2224374, 2225060, 2225771,
    2226440, 2227112, 2227812, 2228471, 2229176, 2229863, 2230561, 2231269, 2231974, 2232682,
    2233357, 2234067, 2234739, 2235432, 2236140, 2236809, 2237499, 2238227, 2238929, 2239618,
    2240308, 2240978, 2241678, 2242394, 2243064, 2243728, 2244438, 2245115]

def LA_35 : List ℕ := [
    2245011, 2245485, 2245967, 2246475, 2246942, 2247455, 2247970, 2248477, 2248965, 2249472,
    2249945, 2250442, 2250944, 2251459, 2251932, 2252375, 2252873, 2253367, 2253868, 2254360,
    2254853, 2255327, 2255796, 2256260, 2256723, 2257236, 2257732, 2258232, 2258726, 2259215,
    2259710, 2260221, 2260720, 2261234, 2261715, 2262214, 2262721, 2263201, 2263715, 2264198,
    2264695, 2265200, 2265681, 2266176, 2266658, 2267180, 2267691, 2268188, 2268715, 2269222,
    2269735, 2270225, 2270712, 2271189, 2271683, 2272171, 2272669, 2273162, 2273673, 2274174,
    2274655, 2275124, 2275619, 2276117, 2276573, 2277077, 2277573, 2278078, 2278553, 2279044,
    2279548, 2280044, 2280530, 2281037, 2281513, 2282023, 2282537, 2283020, 2283513, 2284024,
    2284532, 2285039, 2285539, 2285993, 2286515, 2286978, 2287455, 2287966, 2288460, 2288967,
    2289471, 2289984, 2290475, 2290986, 2291522, 2291985, 2292501, 2293006, 2293493, 2293985,
    2294473, 2294955, 2295431, 2295948, 2296447, 2296946, 2297452, 2297938, 2298442, 2298952,
    2299422, 2299948, 2300466, 2300932, 2301443, 2301924, 2302430, 2302931, 2303438, 2303931,
    2304423, 2304935]

def LB_35 : List ℕ := [
    2245796, 2246493, 2247179, 2247917, 2248623, 2249325, 2249999, 2250704, 2251429, 2252079,
    2252768, 2253476, 2254171, 2254863, 2255522, 2256190, 2256855, 2257566, 2258276, 2258977,
    2259663, 2260389, 2261100, 2261793, 2262507, 2263194, 2263907, 2264608, 2265310, 2265992,
    2266684, 2267409, 2268139, 2268869, 2269582, 2270289, 2270971, 2271669, 2272372, 2273066,
    2273770, 2274458, 2275142, 2275845, 2276515, 2277213, 2277926, 2278609, 2279304, 2280009,
    2280705, 2281407, 2282123, 2282824, 2283514, 2284245, 2284955, 2285652, 2286335, 2287014,
    2287703, 2288410, 2289128, 2289847, 2290557, 2291282, 2291969, 2292697, 2293413, 2294091,
    2294775, 2295455, 2296176, 2296879, 2297595, 2298291, 2299007, 2299704, 2300442, 2301102,
    2301814, 2302518, 2303229, 2303938, 2304655]

def LA_36 : List ℕ := [
    2305398, 2305910, 2306400, 2306897, 2307400, 2307878, 2308374, 2308864, 2309383, 2309909,
    2310381, 2310875, 2311366, 2311859, 2312346, 2312836, 2313338, 2313858, 2314342, 2314847,
    2315357, 2315837, 2316311, 2316837, 2317336, 2317824, 2318316, 2318822, 2319320, 2319832,
    2320344, 2320803, 2321315, 2321821, 2322336, 2322842, 2323357, 2323881, 2324351, 2324860,
    2325346, 2325872, 2326367, 2326864, 2327372, 2327865, 2328360, 2328889, 2329393, 2329920,
    2330412, 2330898, 2331412, 2331897, 2332404, 2332906, 2333404, 2333932, 2334432, 2334943,
    2335443, 2335962, 2336477, 2336990, 2337479, 2337998, 2338487, 2338984, 2339475, 2339964,
    2340470, 2340991, 2341472, 2341971, 2342444, 2342956, 2343482, 2343990, 2344502, 2345000,
    2345491, 2346007, 2346502, 2346988, 2347492, 2348002, 2348527, 2349047, 2349543, 2350013,
    2350515, 2351007, 2351501, 2352000, 2352485, 2353005, 2353514, 2354004, 2354507, 2355001,
    2355495, 2355998, 2356504, 2357009, 2357509, 2357998, 2358515, 2359022, 2359542, 2360080,
    2360579, 2361066, 2361602, 2362103, 2362600, 2363099, 2363627, 2364123, 2364637, 2365153]

def LB_36 : List ℕ := [
    2305333, 2306039, 2306743, 2307444, 2308121, 2308820, 2309538, 2310256, 2310958, 2311644,
    2312340, 2313038, 2313761, 2314456, 2315174, 2315863, 2316568, 2317283, 2317974, 2318671,
    2319375, 2320100, 2320784, 2321495, 2322229, 2322942, 2323681, 2324367, 2325083, 2325794,
    2326500, 2327207, 2327916, 2328617, 2329352, 2330079, 2330781, 2331492, 2332208, 2332903,
    2333620, 2334346, 2335056, 2335783, 2336513, 2337209, 2337939, 2338639, 2339333, 2340023,
    2340759, 2341456, 2342160, 2342858, 2343590, 2344297, 2345017, 2345722, 2346430, 2347138,
    2347849, 2348587, 2349292, 2349986, 2350688, 2351386, 2352081, 2352793, 2353515, 2354208,
    2354923, 2355619, 2356339, 2357047, 2357748, 2358471, 2359188, 2359930, 2360648, 2361365,
    2362092, 2362802, 2363525, 2364236, 2364973]

def LA_37 : List ℕ := [
    2365658, 2366135, 2366649, 2367151, 2367664, 2368195, 2368716, 2369217, 2369716, 2370242,
    2370735, 2371221, 2371730, 2372257, 2372792, 2373289, 2373792, 2374284, 2374773, 2375267,
    2375775, 2376278, 2376756, 2377278, 2377780, 2378272, 2378798, 2379306, 2379788, 2380290,
    2380794, 2381312, 2381845, 2382337, 2382829, 2383343, 2383844, 2384364, 2384879, 2385392,
    2385905, 2386389, 2386896, 2387400, 2387893, 2388404, 2388912, 2389435, 2389942, 2390456,
    2390968, 2391452, 2391956, 2392485, 2393025, 2393544, 2394066, 2394585, 2395099, 2395618,
    2396106, 2396632, 2397121, 2397620, 2398136, 2398636, 2399140, 2399654, 2400182, 2400699,
    2401199, 2401688, 2402207, 2402724, 2403203, 2403715, 2404230, 2404739, 2405253, 2405781,
    2406321, 2406804, 2407298, 2407826, 2408338, 2408837, 2409322, 2409842, 2410350, 2410860,
    2411391, 2411931, 2412448, 2412958, 2413462, 2413986, 2414475, 2415004, 2415520, 2416020,
    2416529, 2417039, 2417530, 2418026, 2418530, 2419030, 2419540, 2420067, 2420566, 2421095,
    2421609, 2422121, 2422623, 2423131, 2423602, 2424125, 2424638, 2425155]

def LB_37 : List ℕ := [
    2365675, 2366390, 2367094, 2367831, 2368563, 2369271, 2369997, 2370710, 2371417, 2372139,
    2372875, 2373596, 2374297, 2374983, 2375696, 2376403, 2377117, 2377830, 2378532, 2379261,
    2379963, 2380674, 2381401, 2382122, 2382823, 2383557, 2384270, 2384993, 2385721, 2386421,
    2387143, 2387834, 2388550, 2389283, 2390015, 2390746, 2391431, 2392133, 2392906, 2393649,
    2394386, 2395117, 2395832, 2396560, 2397275, 2397965, 2398688, 2399398, 2400144, 2400863,
    2401564, 2402300, 2403005, 2403716, 2404463, 2405174, 2405912, 2406643, 2407331, 2408073,
    2408776, 2409490, 2410218, 2410936, 2411692, 2412437, 2413159, 2413879, 2414584, 2415322,
    2416043, 2416772, 2417464, 2418164, 2418877, 2419595, 2420332, 2421059, 2421786, 2422503,
    2423219, 2423932, 2424644, 2425368]

def LA_38 : List ℕ := [
    2425667, 2426175, 2426669, 2427174, 2427675, 2428203, 2428720, 2429224, 2429731, 2430215,
    2430708, 2431210, 2431722, 2432258, 2432745, 2433250, 2433773, 2434294, 2434794, 2435292,
    2435793, 2436295, 2436814, 2437311, 2437825, 2438348, 2438848, 2439394, 2439901, 2440424,
    2440941, 2441449, 2441969, 2442470, 2442977, 2443515, 2444000, 2444514, 2445022, 2445524,
    2446026, 2446546, 2447042, 2447567, 2448068, 2448568, 2449115, 2449635, 2450175, 2450687,
    2451208, 2451714, 2452253, 2452764, 2453270, 2453794, 2454313, 2454823, 2455353, 2455863,
    2456390, 2456887, 2457373, 2457892, 2458395, 2458902, 2459415, 2459935, 2460453, 2460963,
    2461479, 2461999, 2462512, 2463010, 2463541, 2464048, 2464564, 2465079, 2465574, 2466082,
    2466581, 2467080, 2467604, 2468111, 2468623, 2469139, 2469638, 2470142, 2470661, 2471183,
    2471700, 2472207, 2472709, 2473222, 2473758, 2474276, 2474813, 2475342, 2475878, 2476393,
    2476913, 2477426, 2477946, 2478481, 2479011, 2479514, 2480020, 2480539, 2481059, 2481596,
    2482122, 2482628, 2483155, 2483667, 2484180, 2484666, 2485158]

def LB_38 : List ℕ := [
    2426086, 2426798, 2427520, 2428239, 2428977, 2429685, 2430383, 2431093, 2431801, 2432536,
    2433244, 2433981, 2434698, 2435410, 2436127, 2436839, 2437552, 2438292, 2439012, 2439750,
    2440483, 2441222, 2441954, 2442661, 2443393, 2444099, 2444834, 2445539, 2446261, 2446967,
    2447702, 2448397, 2449172, 2449915, 2450642, 2451386, 2452131, 2452870, 2453571, 2454313,
    2455044, 2455770, 2456508, 2457211, 2457931, 2458650, 2459360, 2460085, 2460824, 2461557,
    2462302, 2462998, 2463739, 2464472, 2465179, 2465884, 2466603, 2467312, 2468047, 2468759,
    2469490, 2470197, 2470940, 2471667, 2472396, 2473104, 2473861, 2474602, 2475350, 2476090,
    2476831, 2477560, 2478296, 2479053, 2479772, 2480497, 2481249, 2481984, 2482701, 2483451,
    2484171, 2484861]

def LA_39 : List ℕ := [
    2485660, 2486174, 2486678, 2487198, 2487706, 2488224, 2488735, 2489247, 2489778, 2490314,
    2490817, 2491330, 2491850, 2492383, 2492883, 2493398, 2493893, 2494413, 2494934, 2495459,
    2495990, 2496520, 2497028, 2497559, 2498058, 2498583, 2499108, 2499639, 2500127, 2500663,
    2501173, 2501718, 2502229, 2502726, 2503240, 2503780, 2504286, 2504795, 2505301, 2505812,
    2506328, 2506836, 2507363, 2507869, 2508382, 2508907, 2509437, 2509964, 2510490, 2511001,
    2511508, 2512016, 2512536, 2513066, 2513561, 2514084, 2514587, 2515095, 2515632, 2516160,
    2516686, 2517230, 2517734, 2518232, 2518761, 2519286, 2519809, 2520309, 2520823, 2521339,
    2521879, 2522406, 2522923, 2523403, 2523916, 2524430, 2524951, 2525452, 2525948, 2526474,
    2526973, 2527493, 2528026, 2528543, 2529072, 2529595, 2530126, 2530657, 2531175, 2531696,
    2532205, 2532710, 2533244, 2533762, 2534291, 2534828, 2535347, 2535862, 2536378, 2536911,
    2537437, 2537969, 2538519, 2539045, 2539562, 2540083, 2540583, 2541100, 2541633, 2542144,
    2542667, 2543178, 2543676, 2544185, 2544710]

def LB_39 : List ℕ := [
    2485568, 2486282, 2487005, 2487729, 2488465, 2489189, 2489938, 2490673, 2491389, 2492133,
    2492861, 2493578, 2494308, 2495043, 2495777, 2496531, 2497257, 2497984, 2498714, 2499471,
    2500177, 2500928, 2501680, 2502407, 2503114, 2503867, 2504578, 2505297, 2506023, 2506745,
    2507491, 2508202, 2508938, 2509688, 2510428, 2511159, 2511877, 2512603, 2513332, 2514061,
    2514771, 2515514, 2516276, 2517020, 2517750, 2518468, 2519213, 2519945, 2520672, 2521395,
    2522147, 2522892, 2523590, 2524305, 2525047, 2525737, 2526478, 2527187, 2527933, 2528669,
    2529419, 2530163, 2530911, 2531640, 2532371, 2533103, 2533849, 2534595, 2535335, 2536081,
    2536814, 2537560, 2538326, 2539067, 2539799, 2540512, 2541252, 2542010, 2542723, 2543450,
    2544161, 2544902]

def LA_40 : List ℕ := [
    2545238, 2545759, 2546257, 2546767, 2547280, 2547797, 2548324, 2548850, 2549345, 2549875,
    2550413, 2550920, 2551419, 2551953, 2552486, 2553024, 2553551, 2554048, 2554573, 2555086,
    2555634, 2556173, 2556710, 2557227, 2557747, 2558278, 2558782, 2559324, 2559848, 2560373,
    2560894, 2561419, 2561980, 2562483, 2563019, 2563549, 2564070, 2564609, 2565167, 2565702,
    2566203, 2566727, 2567248, 2567772, 2568289, 2568813, 2569360, 2569878, 2570388, 2570892,
    2571422, 2571932, 2572463, 2572981, 2573523, 2574039, 2574582, 2575115, 2575654, 2576172,
    2576689, 2577226, 2577752, 2578263, 2578775, 2579323, 2579835, 2580338, 2580857, 2581370,
    2581905, 2582439, 2582963, 2583480, 2583999, 2584521, 2585094, 2585611, 2586122, 2586650,
    2587167, 2587692, 2588232, 2588743, 2589260, 2589793, 2590321, 2590829, 2591376, 2591880,
    2592429, 2592948, 2593496, 2594032, 2594554, 2595066, 2595587, 2596128, 2596658, 2597160,
    2597674, 2598198, 2598701, 2599221, 2599740, 2600267, 2600789, 2601335, 2601860, 2602373,
    2602882, 2603401, 2603937, 2604472]

def LB_40 : List ℕ := [
    2545643, 2546358, 2547076, 2547806, 2548553, 2549264, 2550008, 2550755, 2551471, 2552225,
    2552982, 2553718, 2554441, 2555174, 2555939, 2556701, 2557434, 2558182, 2558910, 2559677,
    2560407, 2561132, 2561921, 2562646, 2563405, 2564146, 2564923, 2565678, 2566389, 2567141,
    2567868, 2568616, 2569378, 2570098, 2570818, 2571567, 2572294, 2573043, 2573783, 2574545,
    2575298, 2576046, 2576785, 2577532, 2578263, 2578995, 2579746, 2580472, 2581199, 2581947,
    2582689, 2583431, 2584168, 2584937, 2585685, 2586416, 2587152, 2587919, 2588645, 2589366,
    2590128, 2590851, 2591609, 2592357, 2593107, 2593889, 2594611, 2595347, 2596101, 2596843,
    2597556, 2598293, 2599010, 2599747, 2600499, 2601257, 2601987, 2602723, 2603446, 2604212]

def LA_41 : List ℕ := [
    2604979, 2605489, 2606021, 2606566, 2607082, 2607598, 2608122, 2608653, 2609202, 2609751,
    2610287, 2610814, 2611325, 2611861, 2612391, 2612916, 2613425, 2614000, 2614520, 2615054,
    2615568, 2616091, 2616639, 2617158, 2617681, 2618204, 2618734, 2619252, 2619771, 2620298,
    2620819, 2621352, 2621884, 2622417, 2622938, 2623465, 2624007, 2624553, 2625106, 2625598,
    2626143, 2626665, 2627199, 2627728, 2628255, 2628803, 2629308, 2629867, 2630403, 2630933,
    2631456, 2631983, 2632523, 2633072, 2633612, 2634118, 2634658, 2635188, 2635735, 2636275,
    2636818, 2637362, 2637888, 2638391, 2638925, 2639439, 2639959, 2640493, 2641004, 2641540,
    2642056, 2642563, 2643098, 2643636, 2644153, 2644667, 2645216, 2645740, 2646276, 2646805,
    2647321, 2647876, 2648405, 2648926, 2649479, 2649990, 2650506, 2651031, 2651579, 2652121,
    2652650, 2653161, 2653737, 2654233, 2654782, 2655286, 2655796, 2656335, 2656864, 2657389,
    2657942, 2658487, 2659044, 2659605, 2660141, 2660693, 2661223, 2661734, 2662271, 2662794,
    2663316, 2663878]

def LB_41 : List ℕ := [
    2604939, 2605671, 2606410, 2607165, 2607883, 2608645, 2609414, 2610178, 2610929, 2611669,
    2612419, 2613152, 2613928, 2614665, 2615418, 2616163, 2616915, 2617658, 2618406, 2619138,
    2619871, 2620616, 2621360, 2622127, 2622866, 2623606, 2624377, 2625146, 2625880, 2626631,
    2627377, 2628124, 2628880, 2629623, 2630401, 2631138, 2631879, 2632655, 2633424, 2634153,
    2634913, 2635676, 2636440, 2637217, 2637959, 2638687, 2639420, 2640160, 2640897, 2641653,
    2642377, 2643111, 2643864, 2644597, 2645355, 2646111, 2646869, 2647601, 2648369, 2649113,
    2649870, 2650601, 2651348, 2652125, 2652878, 2653643, 2654366, 2655127, 2655846, 2656612,
    2657340, 2658126, 2658894, 2659685, 2660448, 2661212, 2661958, 2662692, 2663434, 2664215]

def LA_42 : List ℕ := [
    2664412, 2664935, 2665468, 2666013, 2666527, 2667046, 2667573, 2668104, 2668620, 2669157,
    2669684, 2670214, 2670762, 2671284, 2671829, 2672358, 2672908, 2673458, 2673974, 2674499,
    2675033, 2675557, 2676093, 2676632, 2677190, 2677757, 2678290, 2678826, 2679331, 2679857,
    2680404, 2680934, 2681458, 2682002, 2682532, 2683055, 2683588, 2684116, 2684652, 2685223,
    2685744, 2686275, 2686814, 2687349, 2687886, 2688432, 2688956, 2689469, 2690001, 2690529,
    2691083, 2691611, 2692162, 2692698, 2693220, 2693770, 2694320, 2694865, 2695400, 2695962,
    2696515, 2697042, 2697551, 2698104, 2698648, 2699159, 2699686, 2700243, 2700784, 2701336,
    2701888, 2702412, 2702947, 2703502, 2704027, 2704581, 2705142, 2705669, 2706205, 2706737,
    2707263, 2707785, 2708336, 2708831, 2709386, 2709904, 2710472, 2711012, 2711548, 2712066,
    2712605, 2713151, 2713681, 2714220, 2714750, 2715294, 2715848, 2716392, 2716921, 2717452,
    2717987, 2718542, 2719073, 2719616, 2720131, 2720682, 2721217, 2721810, 2722353, 2722915,
    2723423]

def LB_42 : List ℕ := [
    2664971, 2665727, 2666468, 2667199, 2667950, 2668681, 2669441, 2670189, 2670942, 2671714,
    2672457, 2673231, 2673987, 2674734, 2675468, 2676219, 2677013, 2677802, 2678553, 2679293,
    2680033, 2680799, 2681544, 2682302, 2683052, 2683793, 2684557, 2685345, 2686074, 2686847,
    2687613, 2688369, 2689123, 2689859, 2690606, 2691382, 2692143, 2692890, 2693662, 2694426,
    2695210, 2695976, 2696749, 2697473, 2698244, 2699015, 2699735, 2700520, 2701296, 2702066,
    2702821, 2703582, 2704360, 2705145, 2705878, 2706648, 2707390, 2708157, 2708873, 2709634,
    2710416, 2711185, 2711927, 2712686, 2713450, 2714204, 2714961, 2715745, 2716509, 2717247,
    2718010, 2718775, 2719544, 2720280, 2721065, 2721878, 2722653, 2723396]

def LA_43 : List ℕ := [
    2723955, 2724493, 2725037, 2725587, 2726109, 2726645, 2727169, 2727683, 2728232, 2728775,
    2729297, 2729833, 2730370, 2730940, 2731500, 2732047, 2732584, 2733126, 2733661, 2734217,
    2734768, 2735306, 2735845, 2736409, 2736989, 2737494, 2738063, 2738620, 2739164, 2739709,
    2740222, 2740752, 2741311, 2741830, 2742365, 2742919, 2743470, 2744035, 2744585, 2745153,
    2745677, 2746193, 2746729, 2747276, 2747823, 2748364, 2748928, 2749458, 2749982, 2750536,
    2751069, 2751628, 2752192, 2752718, 2753273, 2753818, 2754363, 2754889, 2755432, 2755960,
    2756521, 2757057, 2757597, 2758142, 2758683, 2759221, 2759750, 2760295, 2760862, 2761420,
    2761958, 2762516, 2763035, 2763557, 2764081, 2764628, 2765157, 2765683, 2766251, 2766790,
    2767345, 2767897, 2768431, 2768980, 2769548, 2770098, 2770645, 2771198, 2771739, 2772278,
    2772834, 2773343, 2773868, 2774415, 2774971, 2775510, 2776074, 2776597, 2777123, 2777679,
    2778243, 2778794, 2779325, 2779873, 2780416, 2780943, 2781493, 2782024, 2782548, 2783089]

def LB_43 : List ℕ := [
    2724148, 2724919, 2725692, 2726431, 2727178, 2727920, 2728687, 2729438, 2730195, 2730986,
    2731760, 2732543, 2733297, 2734078, 2734861, 2735612, 2736404, 2737189, 2737951, 2738748,
    2739503, 2740254, 2741026, 2741765, 2742508, 2743314, 2744103, 2744889, 2745646, 2746398,
    2747165, 2747934, 2748706, 2749474, 2750227, 2750983, 2751790, 2752544, 2753337, 2754084,
    2754855, 2755622, 2756375, 2757150, 2757911, 2758683, 2759450, 2760198, 2760997, 2761784,
    2762550, 2763296, 2764015, 2764801, 2765536, 2766325, 2767092, 2767873, 2768645, 2769442,
    2770217, 2771006, 2771765, 2772530, 2773281, 2774010, 2774795, 2775571, 2776350, 2777096,
    2777886, 2778659, 2779433, 2780189, 2780948, 2781705, 2782458, 2783224]

def LA_44 : List ℕ := [
    2783637, 2784172, 2784716, 2785283, 2785808, 2786358, 2786928, 2787459, 2788010, 2788561,
    2789082, 2789631, 2790168, 2790700, 2791222, 2791762, 2792316, 2792876, 2793419, 2793970,
    2794513, 2795071, 2795589, 2796159, 2796705, 2797236, 2797778, 2798325, 2798888, 2799434,
    2799968, 2800499, 2801038, 2801576, 2802150, 2802691, 2803241, 2803803, 2804361, 2804890,
    2805450, 2806001, 2806505, 2807066, 2807596, 2808158, 2808690, 2809273, 2809821, 2810379,
    2810924, 2811485, 2812016, 2812568, 2813116, 2813675, 2814215, 2814774, 2815329, 2815851,
    2816381, 2816928, 2817496, 2818037, 2818567, 2819137, 2819685, 2820238, 2820796, 2821336,
    2821893, 2822440, 2822976, 2823523, 2824059, 2824615, 2825158, 2825734, 2826298, 2826837,
    2827373, 2827911, 2828479, 2829028, 2829558, 2830097, 2830649, 2831202, 2831781, 2832322,
    2832859, 2833406, 2833963, 2834480, 2835020, 2835550, 2836084, 2836625, 2837176, 2837750,
    2838299, 2838848, 2839412, 2839977, 2840525, 2841061, 2841619, 2842183, 2842742]

def LB_44 : List ℕ := [
    2783992, 2784764, 2785548, 2786320, 2787104, 2787863, 2788630, 2789393, 2790159, 2790917,
    2791656, 2792433, 2793208, 2793997, 2794766, 2795521, 2796313, 2797079, 2797846, 2798622,
    2799411, 2800169, 2800920, 2801686, 2802475, 2803250, 2804062, 2804807, 2805582, 2806343,
    2807116, 2807888, 2808643, 2809459, 2810241, 2811017, 2811798, 2812565, 2813342, 2814114,
    2814905, 2815679, 2816421, 2817188, 2817979, 2818745, 2819535, 2820323, 2821093, 2821868,
    2822648, 2823410, 2824172, 2824957, 2825747, 2826550, 2827296, 2828065, 2828848, 2829613,
    2830392, 2831165, 2831967, 2832731, 2833501, 2834273, 2835023, 2835775, 2836533, 2837308,
    2838117, 2838892, 2839688, 2840471, 2841237, 2842022, 2842819]

def LA_45 : List ℕ := [
    2843292, 2843843, 2844375, 2844912, 2845465, 2846007, 2846546, 2847125, 2847667, 2848224,
    2848773, 2849340, 2849889, 2850462, 2850985, 2851514, 2852052, 2852614, 2853182, 2853748,
    2854277, 2854824, 2855366, 2855927, 2856463, 2857005, 2857553, 2858091, 2858669, 2859229,
    2859797, 2860341, 2860894, 2861435, 2862015, 2862555, 2863101, 2863654, 2864201, 2864747,
    2865304, 2865844, 2866388, 2866935, 2867501, 2868044, 2868573, 2869113, 2869657, 2870209,
    2870760, 2871317, 2871847, 2872409, 2872986, 2873529, 2874063, 2874612, 2875185, 2875740,
    2876269, 2876812, 2877383, 2877934, 2878503, 2879045, 2879607, 2880180, 2880730, 2881317,
    2881862, 2882412, 2882960, 2883504, 2884047, 2884597, 2885144, 2885688, 2886253, 2886807,
    2887330, 2887892, 2888428, 2888981, 2889551, 2890111, 2890641, 2891194, 2891717, 2892265,
    2892813, 2893384, 2893954, 2894514, 2895061, 2895632, 2896188, 2896728, 2897264, 2897833,
    2898389, 2898923, 2899497, 2900037, 2900594, 2901110, 2901667]

def LB_45 : List ℕ := [
    2843615, 2844363, 2845127, 2845897, 2846660, 2847480, 2848244, 2849031, 2849818, 2850597,
    2851373, 2852126, 2852927, 2853715, 2854491, 2855256, 2856041, 2856800, 2857563, 2858324,
    2859128, 2859941, 2860712, 2861475, 2862282, 2863060, 2863830, 2864609, 2865387, 2866174,
    2866933, 2867712, 2868479, 2869234, 2870004, 2870803, 2871594, 2872360, 2873144, 2873905,
    2874684, 2875460, 2876244, 2877021, 2877823, 2878601, 2879395, 2880200, 2880994, 2881782,
    2882561, 2883332, 2884105, 2884884, 2885648, 2886445, 2887206, 2887993, 2888764, 2889551,
    2890336, 2891095, 2891848, 2892619, 2893420, 2894230, 2895008, 2895800, 2896582, 2897355,
    2898155, 2898909, 2899715, 2900485, 2901225, 2902019]

def LA_46 : List ℕ := [
    2902225, 2902773, 2903348, 2903895, 2904461, 2905010, 2905569, 2906147, 2906690, 2907253,
    2907828, 2908381, 2908907, 2909466, 2910041, 2910594, 2911167, 2911703, 2912247, 2912784,
    2913341, 2913875, 2914451, 2915010, 2915564, 2916142, 2916703, 2917272, 2917862, 2918384,
    2918939, 2919463, 2920018, 2920563, 2921129, 2921725, 2922276, 2922830, 2923392, 2923922,
    2924460, 2925007, 2925608, 2926150, 2926708, 2927266, 2927818, 2928374, 2928906, 2929466,
    2930017, 2930560, 2931100, 2931644, 2932212, 2932779, 2933337, 2933918, 2934507, 2935070,
    2935627, 2936164, 2936716, 2937278, 2937849, 2938408, 2938963, 2939505, 2940061, 2940618,
    2941194, 2941758, 2942318, 2942884, 2943415, 2943992, 2944533, 2945100, 2945652, 2946179,
    2946763, 2947327, 2947899, 2948446, 2948988, 2949566, 2950132, 2950690, 2951245, 2951794,
    2952356, 2952907, 2953483, 2954038, 2954584, 2955150, 2955730, 2956310, 2956895, 2957449,
    2958018, 2958559, 2959113, 2959675, 2960235, 2960786]

def LB_46 : List ℕ := [
    2902799, 2903597, 2904391, 2905180, 2905974, 2906752, 2907550, 2908350, 2909104, 2909903,
    2910701, 2911478, 2912252, 2913011, 2913803, 2914599, 2915372, 2916187, 2916986, 2917814,
    2918568, 2919344, 2920102, 2920892, 2921712, 2922501, 2923286, 2924052, 2924799, 2925633,
    2926395, 2927201, 2927973, 2928754, 2929527, 2930310, 2931074, 2931852, 2932665, 2933443,
    2934274, 2935095, 2935854, 2936629, 2937435, 2938246, 2939014, 2939799, 2940579, 2941386,
    2942171, 2942967, 2943758, 2944531, 2945318, 2946086, 2946883, 2947701, 2948485, 2949258,
    2950072, 2950864, 2951644, 2952428, 2953215, 2954017, 2954799, 2955619, 2956446, 2957237,
    2958033, 2958809, 2959613, 2960392, 2961184]

def LA_47 : List ℕ := [
    2961357, 2961893, 2962459, 2963033, 2963585, 2964144, 2964733, 2965289, 2965846, 2966415,
    2966986, 2967536, 2968114, 2968686, 2969255, 2969787, 2970354, 2970918, 2971483, 2972071,
    2972655, 2973208, 2973789, 2974346, 2974895, 2975459, 2976010, 2976592, 2977157, 2977748,
    2978314, 2978873, 2979446, 2980015, 2980574, 2981123, 2981684, 2982256, 2982797, 2983374,
    2983922, 2984476, 2985049, 2985605, 2986165, 2986718, 2987321, 2987871, 2988425, 2988987,
    2989563, 2990110, 2990687, 2991209, 2991789, 2992361, 2992951, 2993498, 2994056, 2994630,
    2995219, 2995779, 2996342, 2996897, 2997469, 2998026, 2998581, 2999141, 2999725, 3000308,
    3000847, 3001412, 3001945, 3002523, 3003091, 3003623, 3004217, 3004743, 3005331, 3005904,
    3006451, 3007023, 3007601, 3008169, 3008756, 3009308, 3009863, 3010419, 3010982, 3011529,
    3012090, 3012658, 3013225, 3013801, 3014375, 3014950, 3015463, 3016036, 3016610, 3017186,
    3017751, 3018315, 3018896, 3019467, 3020048]

def LB_47 : List ℕ := [
    2961951, 2962749, 2963549, 2964359, 2965140, 2965943, 2966744, 2967539, 2968366, 2969146,
    2969945, 2970729, 2971532, 2972360, 2973150, 2973962, 2974755, 2975545, 2976337, 2977151,
    2977962, 2978767, 2979568, 2980368, 2981149, 2981954, 2982726, 2983531, 2984320, 2985110,
    2985897, 2986686, 2987518, 2988302, 2989094, 2989892, 2990703, 2991466, 2992254, 2993096,
    2993884, 2994680, 2995515, 2996296, 2997084, 2997893, 2998677, 2999480, 3000301, 3001073,
    3001848, 3002660, 3003427, 3004250, 3005024, 3005834, 3006627, 3007425, 3008245, 3009057,
    3009838, 3010629, 3011416, 3012201, 3013015, 3013821, 3014620, 3015396, 3016192, 3017000,
    3017800, 3018625, 3019429, 3020247]

def LA_48 : List ℕ := [
    3020610, 3021168, 3021722, 3022286, 3022841, 3023418, 3023960, 3024523, 3025091, 3025671,
    3026236, 3026804, 3027373, 3027947, 3028516, 3029079, 3029644, 3030216, 3030798, 3031363,
    3031921, 3032519, 3033088, 3033647, 3034228, 3034783, 3035347, 3035916, 3036480, 3037032,
    3037616, 3038171, 3038735, 3039303, 3039869, 3040443, 3041014, 3041558, 3042130, 3042704,
    3043297, 3043880, 3044453, 3045011, 3045590, 3046151, 3046705, 3047273, 3047854, 3048440,
    3049016, 3049598, 3050170, 3050708, 3051276, 3051818, 3052402, 3052978, 3053519, 3054093,
    3054653, 3055206, 3055776, 3056317, 3056893, 3057491, 3058063, 3058605, 3059166, 3059734,
    3060283, 3060847, 3061422, 3062001, 3062555, 3063135, 3063727, 3064307, 3064875, 3065426,
    3065985, 3066555, 3067105, 3067677, 3068252, 3068833, 3069398, 3069960, 3070535, 3071117,
    3071684, 3072266, 3072834, 3073410, 3073959, 3074514, 3075091, 3075669, 3076232, 3076799,
    3077386, 3077978, 3078547, 3079149]

def LB_48 : List ℕ := [
    3021046, 3021824, 3022623, 3023421, 3024191, 3024982, 3025806, 3026604, 3027412, 3028220,
    3029022, 3029823, 3030633, 3031444, 3032241, 3033073, 3033870, 3034682, 3035460, 3036276,
    3037056, 3037874, 3038665, 3039479, 3040281, 3041074, 3041843, 3042674, 3043509, 3044322,
    3045106, 3045927, 3046713, 3047533, 3048364, 3049161, 3049971, 3050766, 3051547, 3052354,
    3053147, 3053951, 3054722, 3055539, 3056310, 3057135, 3057949, 3058730, 3059535, 3060317,
    3061108, 3061934, 3062738, 3063553, 3064383, 3065176, 3065960, 3066763, 3067561, 3068360,
    3069176, 3069975, 3070794, 3071601, 3072416, 3073221, 3074020, 3074801, 3075626, 3076412,
    3077251, 3078068, 3078902]

def LA_49 : List ℕ := [
    3079734, 3080305, 3080869, 3081450, 3082014, 3082547, 3083133, 3083675, 3084236, 3084809,
    3085398, 3085971, 3086558, 3087135, 3087714, 3088278, 3088842, 3089434, 3090016, 3090604,
    3091161, 3091748, 3092318, 3092889, 3093426, 3094005, 3094560, 3095134, 3095697, 3096241,
    3096840, 3097406, 3097966, 3098538, 3099130, 3099721, 3100290, 3100863, 3101437, 3102023,
    3102618, 3103197, 3103786, 3104376, 3104976, 3105526, 3106087, 3106643, 3107242, 3107796,
    3108365, 3108929, 3109523, 3110088, 3110666, 3111246, 3111814, 3112393, 3112962, 3113535,
    3114098, 3114678, 3115240, 3115821, 3116390, 3116975, 3117577, 3118158, 3118715, 3119302,
    3119851, 3120428, 3121006, 3121564, 3122145, 3122712, 3123258, 3123861, 3124444, 3125007,
    3125583, 3126144, 3126730, 3127308, 3127873, 3128439, 3129026, 3129588, 3130144, 3130700,
    3131276, 3131858, 3132448, 3132997, 3133595, 3134192, 3134765, 3135343, 3135925, 3136490,
    3137075, 3137645, 3138200]

def LB_49 : List ℕ := [
    3079733, 3080539, 3081343, 3082139, 3082934, 3083709, 3084521, 3085330, 3086157, 3086977,
    3087789, 3088581, 3089413, 3090254, 3091037, 3091865, 3092679, 3093449, 3094264, 3095062,
    3095857, 3096654, 3097473, 3098273, 3099091, 3099922, 3100717, 3101547, 3102369, 3103203,
    3104028, 3104870, 3105661, 3106456, 3107292, 3108081, 3108881, 3109716, 3110517, 3111332,
    3112141, 3112953, 3113769, 3114550, 3115368, 3116175, 3117001, 3117850, 3118651, 3119479,
    3120257, 3121086, 3121877, 3122690, 3123470, 3124317, 3125119, 3125919, 3126745, 3127545,
    3128349, 3129170, 3129950, 3130746, 3131575, 3132403, 3133201, 3134035, 3134860, 3135683,
    3136488, 3137326, 3138091]

def LA_50 : List ℕ := [
    3138799, 3139377, 3139937, 3140507, 3141077, 3141678, 3142240, 3142806, 3143371, 3143947,
    3144523, 3145123, 3145680, 3146244, 3146835, 3147410, 3147981, 3148570, 3149163, 3149773,
    3150350, 3150911, 3151483, 3152048, 3152626, 3153205, 3153775, 3154375, 3154941, 3155507,
    3156089, 3156646, 3157256, 3157851, 3158410, 3158979, 3159571, 3160160, 3160739, 3161292,
    3161864, 3162469, 3163057, 3163626, 3164191, 3164784, 3165365, 3165932, 3166527, 3167069,
    3167650, 3168230, 3168811, 3169410, 3169985, 3170542, 3171128, 3171702, 3172285, 3172868,
    3173447, 3174012, 3174616, 3175197, 3175790, 3176342, 3176919, 3177501, 3178078, 3178682,
    3179276, 3179867, 3180430, 3180983, 3181549, 3182136, 3182762, 3183311, 3183875, 3184493,
    3185062, 3185653, 3186229, 3186827, 3187430, 3188008, 3188576, 3189165, 3189758, 3190331,
    3190893, 3191446, 3192019, 3192606, 3193191, 3193769, 3194363, 3194925, 3195523, 3196084,
    3196655, 3197208]

def LB_50 : List ℕ := [
    3138934, 3139747, 3140551, 3141357, 3142182, 3142977, 3143783, 3144600, 3145440, 3146222,
    3147049, 3147853, 3148696, 3149536, 3150364, 3151171, 3151972, 3152775, 3153592, 3154425,
    3155228, 3156047, 3156857, 3157713, 3158523, 3159331, 3160162, 3160970, 3161780, 3162619,
    3163431, 3164241, 3165063, 3165887, 3166697, 3167496, 3168309, 3169138, 3169971, 3170771,
    3171587, 3172414, 3173249, 3174039, 3174876, 3175720, 3176510, 3177321, 3178141, 3179008,
    3179830, 3180643, 3181420, 3182249, 3183096, 3183884, 3184737, 3185563, 3186390, 3187235,
    3188055, 3188860, 3189703, 3190524, 3191296, 3192116, 3192948, 3193761, 3194591, 3195402,
    3196199, 3197012]

def LA_51 : List ℕ := [
    3197788, 3198362, 3198947, 3199536, 3200108, 3200699, 3201262, 3201841, 3202402, 3202972,
    3203562, 3204140, 3204705, 3205270, 3205855, 3206464, 3207056, 3207657, 3208252, 3208808,
    3209379, 3209951, 3210551, 3211150, 3211740, 3212309, 3212887, 3213469, 3214050, 3214635,
    3215206, 3215809, 3216367, 3216926, 3217496, 3218096, 3218663, 3219262, 3219872, 3220454,
    3221050, 3221647, 3222195, 3222770, 3223364, 3223965, 3224555, 3225159, 3225749, 3226308,
    3226879, 3227482, 3228031, 3228636, 3229227, 3229793, 3230377, 3230973, 3231577, 3232145,
    3232731, 3233319, 3233913, 3234505, 3235085, 3235638, 3236209, 3236785, 3237387, 3237941,
    3238509, 3239090, 3239672, 3240256, 3240850, 3241438, 3242022, 3242615, 3243195, 3243766,
    3244369, 3244972, 3245548, 3246113, 3246706, 3247287, 3247839, 3248427, 3249002, 3249579,
    3250164, 3250772, 3251349, 3251912, 3252501, 3253094, 3253665, 3254238, 3254844, 3255448,
    3256051]

def LB_51 : List ℕ := [
    3197828, 3198648, 3199462, 3200269, 3201100, 3201910, 3202711, 3203542, 3204352, 3205150,
    3205985, 3206814, 3207677, 3208489, 3209296, 3210112, 3210963, 3211794, 3212612, 3213431,
    3214258, 3215057, 3215908, 3216700, 3217496, 3218333, 3219151, 3219997, 3220855, 3221696,
    3222490, 3223312, 3224163, 3224991, 3225818, 3226636, 3227465, 3228264, 3229104, 3229913,
    3230743, 3231600, 3232410, 3233243, 3234071, 3234908, 3235707, 3236532, 3237353, 3238160,
    3238956, 3239783, 3240600, 3241447, 3242270, 3243103, 3243916, 3244760, 3245599, 3246409,
    3247234, 3248027, 3248848, 3249667, 3250516, 3251340, 3252143, 3252981, 3253799, 3254621,
    3255475, 3256332]

def LA_52 : List ℕ := [
    3256623, 3257216, 3257790, 3258358, 3258962, 3259571, 3260158, 3260751, 3261346, 3261958,
    3262541, 3263146, 3263720, 3264302, 3264874, 3265451, 3266030, 3266602, 3267190, 3267781,
    3268354, 3268936, 3269536, 3270142, 3270705, 3271302, 3271891, 3272462, 3273060, 3273628,
    3274213, 3274808, 3275373, 3275931, 3276499, 3277095, 3277685, 3278251, 3278859, 3279478,
    3280077, 3280651, 3281255, 3281835, 3282427, 3283022, 3283628, 3284221, 3284800, 3285405,
    3286017, 3286609, 3287205, 3287807, 3288399, 3288971, 3289551, 3290153, 3290727, 3291317,
    3291888, 3292476, 3293069, 3293658, 3294256, 3294854, 3295457, 3296047, 3296619, 3297197,
    3297790, 3298367, 3298937, 3299541, 3300143, 3300750, 3301309, 3301911, 3302506, 3303074,
    3303672, 3304267, 3304859, 3305444, 3306042, 3306639, 3307238, 3307827, 3308401, 3308992,
    3309598, 3310184, 3310743, 3311343, 3311902, 3312509, 3313074, 3313656, 3314279, 3314869]

def LB_52 : List ℕ := [
    3257152, 3257950, 3258783, 3259657, 3260460, 3261311, 3262176, 3263005, 3263838, 3264661,
    3265466, 3266290, 3267088, 3267925, 3268756, 3269599, 3270434, 3271260, 3272095, 3272909,
    3273725, 3274563, 3275366, 3276162, 3276983, 3277819, 3278636, 3279517, 3280354, 3281192,
    3282029, 3282859, 3283704, 3284543, 3285386, 3286245, 3287090, 3287937, 3288764, 3289571,
    3290404, 3291246, 3292058, 3292899, 3293730, 3294562, 3295416, 3296254, 3297057, 3297881,
    3298708, 3299544, 3300395, 3301210, 3302057, 3302891, 3303715, 3304574, 3305395, 3306232,
    3307084, 3307919, 3308746, 3309583, 3310408, 3311227, 3312045, 3312883, 3313687, 3314554]

def LA_53 : List ℕ := [
    3315440, 3316033, 3316642, 3317232, 3317838, 3318439, 3319011, 3319604, 3320227, 3320818,
    3321406, 3322015, 3322607, 3323218, 3323810, 3324403, 3325015, 3325621, 3326230, 3326765,
    3327361, 3327957, 3328575, 3329144, 3329761, 3330351, 3330928, 3331523, 3332095, 3332693,
    3333276, 3333873, 3334457, 3335028, 3335622, 3336201, 3336816, 3337411, 3338029, 3338617,
    3339198, 3339816, 3340388, 3340973, 3341568, 3342184, 3342792, 3343394, 3343995, 3344593,
    3345200, 3345805, 3346407, 3346992, 3347597, 3348214, 3348825, 3349424, 3350002, 3350587,
    3351185, 3351777, 3352340, 3352922, 3353553, 3354142, 3354748, 3355332, 3355921, 3356505,
    3357093, 3357693, 3358288, 3358878, 3359475, 3360061, 3360643, 3361231, 3361809, 3362394,
    3362980, 3363555, 3364143, 3364757, 3365340, 3365955, 3366535, 3367117, 3367734, 3368332,
    3368910, 3369513, 3370129, 3370704, 3371309, 3371922, 3372529, 3373115, 3373692]

def LB_53 : List ℕ := [
    3315370, 3316206, 3317055, 3317913, 3318739, 3319573, 3320436, 3321277, 3322124, 3322958,
    3323819, 3324672, 3325533, 3326375, 3327163, 3328006, 3328862, 3329708, 3330545, 3331361,
    3332193, 3333026, 3333869, 3334688, 3335527, 3336348, 3337205, 3338064, 3338892, 3339739,
    3340556, 3341400, 3342257, 3343112, 3343963, 3344820, 3345672, 3346523, 3347364, 3348232,
    3349092, 3349923, 3350747, 3351596, 3352392, 3353252, 3354100, 3354928, 3355786, 3356592,
    3357440, 3358289, 3359121, 3359955, 3360788, 3361614, 3362432, 3363266, 3364084, 3364928,
    3365788, 3366620, 3367444, 3368315, 3369150, 3370017, 3370841, 3371669, 3372558, 3373381]

def LA_54 : List ℕ := [
    3374291, 3374909, 3375517, 3376121, 3376741, 3377364, 3377978, 3378586, 3379164, 3379800,
    3380365, 3380959, 3381578, 3382186, 3382782, 3383379, 3383977, 3384591, 3385181, 3385776,
    3386338, 3386929, 3387513, 3388094, 3388722, 3389321, 3389919, 3390511, 3391140, 3391732,
    3392309, 3392895, 3393466, 3394089, 3394696, 3395288, 3395877, 3396477, 3397062, 3397657,
    3398274, 3398882, 3399489, 3400072, 3400675, 3401286, 3401884, 3402481, 3403077, 3403667,
    3404281, 3404855, 3405467, 3406059, 3406647, 3407268, 3407847, 3408468, 3409073, 3409670,
    3410257, 3410895, 3411521, 3412102, 3412717, 3413319, 3413935, 3414552, 3415137, 3415732,
    3416337, 3416934, 3417534, 3418121, 3418710, 3419320, 3419894, 3420480, 3421076, 3421672,
    3422280, 3422883, 3423496, 3424094, 3424707, 3425302, 3425898, 3426501, 3427111, 3427707,
    3428297, 3428889, 3429484, 3430083, 3430682, 3431282, 3431894, 3432481]

def LB_54 : List ℕ := [
    3374226, 3375081, 3375938, 3376807, 3377680, 3378549, 3379386, 3380234, 3381068, 3381939,
    3382787, 3383644, 3384493, 3385330, 3386150, 3386970, 3387799, 3388673, 3389520, 3390363,
    3391239, 3392056, 3392888, 3393712, 3394579, 3395423, 3396263, 3397093, 3397938, 3398803,
    3399673, 3400484, 3401367, 3402207, 3403043, 3403896, 3404736, 3405573, 3406415, 3407282,
    3408105, 3408982, 3409824, 3410690, 3411578, 3412425, 3413271, 3414158, 3414980, 3415832,
    3416698, 3417533, 3418359, 3419225, 3420052, 3420877, 3421713, 3422577, 3423439, 3424282,
    3425140, 3425985, 3426844, 3427691, 3428513, 3429356, 3430207, 3431048, 3431911, 3432759]

def LA_55 : List ℕ := [
    3433059, 3433666, 3434280, 3434876, 3435455, 3436055, 3436666, 3437251, 3437855, 3438476,
    3439061, 3439660, 3440256, 3440860, 3441444, 3442033, 3442634, 3443254, 3443868, 3444462,
    3445065, 3445661, 3446264, 3446864, 3447470, 3448067, 3448671, 3449256, 3449845, 3450428,
    3451046, 3451636, 3452255, 3452862, 3453476, 3454092, 3454703, 3455302, 3455901, 3456499,
    3457082, 3457682, 3458310, 3458921, 3459520, 3460103, 3460709, 3461298, 3461923, 3462527,
    3463110, 3463714, 3464330, 3464953, 3465550, 3466171, 3466759, 3467333, 3467935, 3468542,
    3469162, 3469747, 3470380, 3471002, 3471598, 3472194, 3472813, 3473397, 3473997, 3474592,
    3475192, 3475808, 3476399, 3476993, 3477596, 3478200, 3478822, 3479470, 3480049, 3480630,
    3481261, 3481871, 3482486, 3483079, 3483699, 3484305, 3484922, 3485530, 3486149, 3486753,
    3487346, 3487928, 3488526, 3489157, 3489739, 3490341, 3490964]

def LB_55 : List ℕ := [
    3433588, 3434433, 3435277, 3436107, 3436965, 3437814, 3438674, 3439521, 3440361, 3441206,
    3442038, 3442904, 3443768, 3444619, 3445454, 3446312, 3447169, 3448014, 3448866, 3449690,
    3450524, 3451367, 3452242, 3453106, 3453973, 3454834, 3455681, 3456523, 3457364, 3458247,
    3459111, 3459932, 3460781, 3461638, 3462497, 3463330, 3464192, 3465057, 3465933, 3466768,
    3467591, 3468462, 3469309, 3470169, 3471056, 3471899, 3472768, 3473602, 3474454, 3475288,
    3476147, 3476986, 3477843, 3478712, 3479604, 3480434, 3481299, 3482176, 3483016, 3483894,
    3484741, 3485610, 3486501, 3487328, 3488153, 3489031, 3489853, 3490734]

def LA_56 : List ℕ := [
    3491563, 3492187, 3492812, 3493391, 3494026, 3494618, 3495244, 3495877, 3496499, 3497124,
    3497700, 3498314, 3498922, 3499535, 3500134, 3500751, 3501341, 3501963, 3502571, 3503185,
    3503747, 3504342, 3504935, 3505551, 3506155, 3506745, 3507359, 3507984, 3508606, 3509210,
    3509796, 3510393, 3511005, 3511607, 3512240, 3512809, 3513432, 3514014, 3514614, 3515215,
    3515841, 3516463, 3517086, 3517667, 3518266, 3518869, 3519456, 3520070, 3520659, 3521242,
    3521874, 3522501, 3523125, 3523692, 3524319, 3524938, 3525561, 3526150, 3526760, 3527349,
    3527944, 3528529, 3529133, 3529785, 3530383, 3530994, 3531613, 3532188, 3532811, 3533429,
    3534041, 3534648, 3535277, 3535880, 3536496, 3537116, 3537715, 3538296, 3538901, 3539518,
    3540145, 3540775, 3541400, 3541985, 3542596, 3543211, 3543800, 3544427, 3545025, 3545635,
    3546245, 3546862, 3547444, 3548043, 3548660, 3549300]

def LB_56 : List ℕ := [
    3491584, 3492470, 3493315, 3494198, 3495056, 3495941, 3496834, 3497667, 3498513, 3499392,
    3500236, 3501108, 3501965, 3502821, 3503656, 3504482, 3505349, 3506201, 3507044, 3507912,
    3508812, 3509644, 3510475, 3511347, 3512226, 3513060, 3513903, 3514749, 3515624, 3516496,
    3517338, 3518182, 3519040, 3519884, 3520726, 3521584, 3522470, 3523329, 3524182, 3525053,
    3525908, 3526772, 3527601, 3528442, 3529295, 3530188, 3531048, 3531914, 3532749, 3533620,
    3534483, 3535363, 3536247, 3537104, 3537947, 3538793, 3539663, 3540559, 3541435, 3542273,
    3543128, 3543985, 3544857, 3545716, 3546581, 3547419, 3548288, 3549155, 3550044]

def LA_57 : List ℕ := [
    3549921, 3550533, 3551142, 3551759, 3552368, 3552986, 3553626, 3554247, 3554837, 3555438,
    3556047, 3556655, 3557277, 3557874, 3558462, 3559089, 3559687, 3560296, 3560885, 3561499,
    3562143, 3562751, 3563366, 3563963, 3564576, 3565183, 3565810, 3566416, 3567015, 3567626,
    3568230, 3568823, 3569447, 3570052, 3570673, 3571292, 3571913, 3572513, 3573123, 3573724,
    3574354, 3574991, 3575622, 3576231, 3576826, 3577427, 3578038, 3578635, 3579254, 3579895,
    3580515, 3581135, 3581729, 3582355, 3582995, 3583587, 3584204, 3584854, 3585446, 3586079,
    3586683, 3587257, 3587871, 3588493, 3589126, 3589744, 3590349, 3590942, 3591549, 3592156,
    3592773, 3593394, 3593992, 3594609, 3595230, 3595826, 3596465, 3597118, 3597736, 3598378,
    3598965, 3599584, 3600202, 3600824, 3601416, 3602031, 3602625, 3603251, 3603899, 3604527,
    3605144, 3605755, 3606360, 3606974, 3607595, 3608240]

def LB_57 : List ℕ := [
    3550917, 3551781, 3552647, 3553534, 3554390, 3555238, 3556106, 3556965, 3557830, 3558683,
    3559536, 3560404, 3561246, 3562143, 3563012, 3563863, 3564720, 3565580, 3566453, 3567314,
    3568171, 3569025, 3569877, 3570758, 3571653, 3572493, 3573342, 3574225, 3575124, 3576010,
    3576856, 3577695, 3578560, 3579446, 3580326, 3581200, 3582049, 3582954, 3583800, 3584696,
    3585557, 3586453, 3587263, 3588148, 3589021, 3589896, 3590745, 3591599, 3592475, 3593333,
    3594192, 3595081, 3595922, 3596830, 3597724, 3598602, 3599465, 3600340, 3601191, 3602067,
    3602922, 3603823, 3604708, 3605576, 3606434, 3607318, 3608211]

def LA_58 : List ℕ := [
    3608849, 3609492, 3610135, 3610722, 3611339, 3611935, 3612569, 3613178, 3613799, 3614412,
    3615010, 3615632, 3616261, 3616872, 3617493, 3618120, 3618736, 3619369, 3619990, 3620583,
    3621201, 3621823, 3622432, 3623042, 3623617, 3624243, 3624860, 3625471, 3626091, 3626697,
    3627275, 3627902, 3628510, 3629115, 3629740, 3630372, 3630986, 3631591, 3632220, 3632828,
    3633479, 3634065, 3634655, 3635270, 3635877, 3636464, 3637086, 3637702, 3638322, 3638953,
    3639571, 3640191, 3640802, 3641395, 3642023, 3642639, 3643266, 3643904, 3644520, 3645157,
    3645772, 3646363, 3646988, 3647609, 3648217, 3648829, 3649428, 3650059, 3650651, 3651281,
    3651901, 3652517, 3653135, 3653742, 3654351, 3654987, 3655619, 3656227, 3656836, 3657454,
    3658059, 3658713, 3659323, 3659958, 3660562, 3661168, 3661789, 3662394, 3663005, 3663643,
    3664268, 3664881, 3665516, 3666139]

def LB_58 : List ℕ := [
    3609093, 3609992, 3610839, 3611704, 3612580, 3613442, 3614324, 3615161, 3616062, 3616927,
    3617805, 3618689, 3619569, 3620427, 3621297, 3622162, 3623032, 3623866, 3624764, 3625623,
    3626494, 3627323, 3628177, 3629048, 3629937, 3630807, 3631677, 3632570, 3633455, 3634299,
    3635137, 3635995, 3636860, 3637726, 3638599, 3639483, 3640355, 3641202, 3642084, 3642982,
    3643863, 3644754, 3645625, 3646466, 3647367, 3648220, 3649095, 3649961, 3650812, 3651680,
    3652566, 3653431, 3654298, 3655191, 3656064, 3656938, 3657791, 3658699, 3659564, 3660446,
    3661299, 3662156, 3663035, 3663932, 3664798, 3665693, 3666576]

def LA_59 : List ℕ := [
    3666769, 3667391, 3667990, 3668608, 3669229, 3669862, 3670490, 3671100, 3671725, 3672336,
    3672960, 3673588, 3674220, 3674824, 3675470, 3676070, 3676686, 3677309, 3677932, 3678580,
    3679202, 3679843, 3680462, 3681105, 3681746, 3682340, 3682952, 3683555, 3684173, 3684808,
    3685406, 3686023, 3686666, 3687269, 3687872, 3688489, 3689112, 3689740, 3690358, 3691010,
    3691645, 3692269, 3692927, 3693547, 3694152, 3694767, 3695381, 3695990, 3696627, 3697249,
    3697876, 3698503, 3699111, 3699733, 3700366, 3700971, 3701600, 3702224, 3702851, 3703459,
    3704074, 3704695, 3705278, 3705888, 3706503, 3707150, 3707779, 3708392, 3709003, 3709619,
    3710229, 3710882, 3711496, 3712109, 3712743, 3713375, 3713999, 3714625, 3715266, 3715875,
    3716523, 3717159, 3717794, 3718421, 3719027, 3719664, 3720293, 3720893, 3721509, 3722130,
    3722759, 3723375, 3724027, 3724673]

def LB_59 : List ℕ := [
    3667462, 3668314, 3669193, 3670086, 3670970, 3671848, 3672702, 3673597, 3674475, 3675383,
    3676217, 3677099, 3677988, 3678887, 3679791, 3680664, 3681588, 3682435, 3683298, 3684165,
    3685046, 3685914, 3686791, 3687667, 3688533, 3689414, 3690287, 3691201, 3692095, 3693013,
    3693892, 3694735, 3695589, 3696484, 3697365, 3698260, 3699127, 3700009, 3700887, 3701771,
    3702651, 3703527, 3704394, 3705229, 3706110, 3706996, 3707883, 3708739, 3709619, 3710496,
    3711386, 3712253, 3713160, 3714047, 3714932, 3715811, 3716723, 3717622, 3718494, 3719390,
    3720273, 3721134, 3722024, 3722898, 3723779, 3724694]

def LA_60 : List ℕ := [
    3725288, 3725902, 3726538, 3727160, 3727789, 3728403, 3729023, 3729637, 3730275, 3730895,
    3731501, 3732097, 3732731, 3733411, 3734013, 3734656, 3735267, 3735880, 3736504, 3737126,
    3737738, 3738357, 3739005, 3739633, 3740249, 3740895, 3741535, 3742151, 3742777, 3743409,
    3744035, 3744651, 3745298, 3745917, 3746550, 3747144, 3747769, 3748366, 3748999, 3749640,
    3750276, 3750919, 3751548, 3752169, 3752800, 3753438, 3754086, 3754713, 3755334, 3755975,
    3756602, 3757231, 3757828, 3758423, 3759100, 3759729, 3760353, 3760986, 3761632, 3762245,
    3762863, 3763504, 3764112, 3764744, 3765374, 3766002, 3766618, 3767269, 3767893, 3768502,
    3769105, 3769744, 3770377, 3771028, 3771654, 3772296, 3772904, 3773573, 3774225, 3774863,
    3775466, 3776129, 3776753, 3777357, 3778007, 3778659, 3779280, 3779913, 3780543, 3781181,
    3781816, 3782427, 3783069]

def LB_60 : List ℕ := [
    3725573, 3726459, 3727336, 3728212, 3729091, 3729981, 3730861, 3731717, 3732587, 3733521,
    3734405, 3735272, 3736149, 3737024, 3737894, 3738779, 3739686, 3740576, 3741483, 3742355,
    3743250, 3744134, 3745013, 3745907, 3746788, 3747649, 3748512, 3749418, 3750315, 3751221,
    3752098, 3752986, 3753900, 3754786, 3755691, 3756573, 3757452, 3758292, 3759229, 3760127,
    3761002, 3761901, 3762776, 3763668, 3764541, 3765436, 3766319, 3767215, 3768081, 3768955,
    3769848, 3770760, 3771650, 3772558, 3773465, 3774381, 3775256, 3776172, 3777037, 3777933,
    3778862, 3779734, 3780634, 3781544, 3782404, 3783314]

def LA_61 : List ℕ := [
    3783705, 3784315, 3784941, 3785560, 3786189, 3786821, 3787444, 3788072, 3788707, 3789351,
    3789984, 3790622, 3791262, 3791870, 3792513, 3793154, 3793787, 3794402, 3794991, 3795639,
    3796284, 3796923, 3797551, 3798157, 3798786, 3799418, 3800043, 3800695, 3801358, 3802007,
    3802601, 3803228, 3803861, 3804497, 3805116, 3805742, 3806387, 3807022, 3807668, 3808313,
    3808930, 3809556, 3810182, 3810816, 3811444, 3812059, 3812693, 3813317, 3813959, 3814604,
    3815216, 3815852, 3816466, 3817077, 3817695, 3818321, 3818954, 3819551, 3820195, 3820815,
    3821436, 3822089, 3822727, 3823359, 3823992, 3824610, 3825252, 3825875, 3826477, 3827121,
    3827720, 3828345, 3829009, 3829623, 3830256, 3830888, 3831542, 3832162, 3832758, 3833381,
    3834026, 3834677, 3835326, 3835964, 3836579, 3837216, 3837847, 3838473, 3839129, 3839761,
    3840387, 3841025, 3841668]

def LB_61 : List ℕ := [
    3784189, 3785086, 3785960, 3786839, 3787734, 3788615, 3789526, 3790414, 3791322, 3792206,
    3793117, 3794007, 3794855, 3795745, 3796665, 3797556, 3798420, 3799305, 3800209, 3801145,
    3802045, 3802907, 3803805, 3804700, 3805576, 3806480, 3807380, 3808299, 3809175, 3810052,
    3810956, 3811824, 3812728, 3813627, 3814522, 3815395, 3816296, 3817150, 3818035, 3818918,
    3819769, 3820670, 3821568, 3822476, 3823373, 3824269, 3825160, 3826018, 3826915, 3827778,
    3828669, 3829568, 3830462, 3831366, 3832252, 3833127, 3834019, 3834952, 3835847, 3836725,
    3837636, 3838510, 3839427, 3840313, 3841215]

def LA_62 : List ℕ := [
    3842324, 3842986, 3843585, 3844229, 3844869, 3845478, 3846113, 3846744, 3847358, 3848010,
    3848609, 3849251, 3849885, 3850492, 3851136, 3851769, 3852383, 3853029, 3853688, 3854306,
    3854923, 3855561, 3856213, 3856855, 3857500, 3858135, 3858760, 3859401, 3860059, 3860674,
    3861263, 3861914, 3862512, 3863167, 3863840, 3864495, 3865135, 3865780, 3866432, 3867098,
    3867742, 3868384, 3869001, 3869639, 3870256, 3870891, 3871523, 3872151, 3872786, 3873425,
    3874028, 3874671, 3875293, 3875956, 3876576, 3877193, 3877813, 3878468, 3879096, 3879762,
    3880376, 3881011, 3881648, 3882291, 3882913, 3883542, 3884186, 3884815, 3885454, 3886111,
    3886755, 3887378, 3888033, 3888668, 3889318, 3889937, 3890566, 3891218, 3891857, 3892501,
    3893136, 3893772, 3894423, 3895079, 3895729, 3896380, 3897010, 3897639, 3898299, 3898941,
    3899607]

def LB_62 : List ℕ := [
    3842139, 3843072, 3843931, 3844841, 3845734, 3846611, 3847484, 3848379, 3849269, 3850164,
    3851038, 3851945, 3852806, 3853746, 3854608, 3855516, 3856434, 3857344, 3858244, 3859139,
    3860059, 3860926, 3861803, 3862672, 3863614, 3864541, 3865443, 3866368, 3867312, 3868205,
    3869090, 3869986, 3870869, 3871760, 3872667, 3873554, 3874451, 3875324, 3876232, 3877117,
    3878005, 3878911, 3879835, 3880715, 3881611, 3882507, 3883406, 3884291, 3885200, 3886120,
    3887014, 3887936, 3888846, 3889709, 3890621, 3891551, 3892448, 3893329, 3894262, 3895173,
    3896089, 3897002, 3897885, 3898824, 3899761]

def LA_63 : List ℕ := [
    3900227, 3900857, 3901516, 3902157, 3902786, 3903430, 3904045, 3904660, 3905307, 3905991,
    3906625, 3907288, 3907922, 3908554, 3909207, 3909878, 3910500, 3911110, 3911752, 3912383,
    3913044, 3913727, 3914371, 3915023, 3915649, 3916288, 3916930, 3917579, 3918250, 3918874,
    3919511, 3920143, 3920789, 3921411, 3922046, 3922687, 3923329, 3923965, 3924643, 3925270,
    3925919, 3926552, 3927177, 3927816, 3928448, 3929085, 3929756, 3930408, 3931054, 3931685,
    3932324, 3932974, 3933621, 3934270, 3934926, 3935555, 3936194, 3936818, 3937459, 3938094,
    3938727, 3939381, 3940029, 3940657, 3941293, 3941931, 3942546, 3943184, 3943839, 3944499,
    3945157, 3945809, 3946436, 3947051, 3947693, 3948338, 3948988, 3949618, 3950248, 3950905,
    3951561, 3952191, 3952828, 3953460, 3954100, 3954769, 3955391, 3956024, 3956671, 3957314,
    3957973]

def LB_63 : List ℕ := [
    3900643, 3901552, 3902439, 3903346, 3904235, 3905127, 3906057, 3906986, 3907890, 3908798,
    3909731, 3910620, 3911493, 3912397, 3913359, 3914277, 3915190, 3916079, 3916990, 3917934,
    3918829, 3919728, 3920629, 3921530, 3922427, 3923327, 3924256, 3925160, 3926062, 3926958,
    3927860, 3928750, 3929691, 3930611, 3931509, 3932403, 3933347, 3934246, 3935168, 3936067,
    3936956, 3937860, 3938754, 3939674, 3940573, 3941469, 3942359, 3943249, 3944184, 3945115,
    3946036, 3946897, 3947819, 3948726, 3949627, 3950518, 3951441, 3952350, 3953254, 3954161,
    3955055, 3955972, 3956871, 3957809]

def LA_64 : List ℕ := [
    3958591, 3959241, 3959861, 3960497, 3961138, 3961801, 3962448, 3963106, 3963758, 3964380,
    3965031, 3965681, 3966324, 3966956, 3967641, 3968270, 3968940, 3969599, 3970251, 3970885,
    3971514, 3972164, 3972797, 3973443, 3974096, 3974759, 3975391, 3976043, 3976687, 3977356,
    3978015, 3978652, 3979301, 3979936, 3980578, 3981230, 3981890, 3982515, 3983157, 3983829,
    3984480, 3985126, 3985764, 3986382, 3987010, 3987686, 3988313, 3988961, 3989615, 3990251,
    3990894, 3991548, 3992206, 3992862, 3993530, 3994152, 3994781, 3995417, 3996061, 3996709,
    3997357, 3997992, 3998625, 3999304, 3999944, 4000581, 4001244, 4001875, 4002542, 4003187,
    4003837, 4004487, 4005158, 4005811, 4006433, 4007082, 4007718, 4008365, 4009013, 4009658,
    4010302, 4010976, 4011589, 4012252, 4012871, 4013520, 4014177, 4014834, 4015461, 4016108]

def LB_64 : List ℕ := [
    3958678, 3959593, 3960485, 3961402, 3962322, 3963255, 3964147, 3965053, 3965992, 3966886,
    3967837, 3968737, 3969672, 3970596, 3971478, 3972393, 3973303, 3974221, 3975147, 3976061,
    3976981, 3977921, 3978821, 3979734, 3980643, 3981546, 3982461, 3983365, 3984309, 3985221,
    3986140, 3987002, 3987932, 3988853, 3989768, 3990671, 3991593, 3992523, 3993456, 3994360,
    3995232, 3996152, 3997073, 3997966, 3998892, 3999825, 4000716, 4001638, 4002564, 4003497,
    4004410, 4005339, 4006233, 4007143, 4008066, 4008970, 4009875, 4010814, 4011718, 4012628,
    4013525, 4014456, 4015357, 4016265]

def LA_65 : List ℕ := [
    4016754, 4017388, 4018049, 4018691, 4019344, 4019997, 4020648, 4021313, 4021956, 4022585,
    4023243, 4023899, 4024544, 4025173, 4025818, 4026456, 4027105, 4027739, 4028376, 4029019,
    4029691, 4030351, 4030991, 4031627, 4032248, 4032928, 4033584, 4034249, 4034908, 4035553,
    4036184, 4036831, 4037452, 4038100, 4038765, 4039421, 4040068, 4040711, 4041352, 4041998,
    4042652, 4043285, 4043946, 4044612, 4045252, 4045884, 4046532, 4047206, 4047857, 4048483,
    4049124, 4049785, 4050434, 4051072, 4051723, 4052348, 4052986, 4053643, 4054300, 4054946,
    4055613, 4056271, 4056929, 4057560, 4058206, 4058860, 4059486, 4060139, 4060783, 4061451,
    4062101, 4062788, 4063458, 4064083, 4064716, 4065361, 4066022, 4066683, 4067324, 4067964,
    4068602, 4069265, 4069942, 4070589, 4071213, 4071850, 4072530, 4073155, 4073813, 4074480]

def LB_65 : List ℕ := [
    4017184, 4018102, 4019014, 4019934, 4020856, 4021776, 4022685, 4023603, 4024524, 4025417,
    4026332, 4027249, 4028142, 4029057, 4029983, 4030909, 4031807, 4032727, 4033660, 4034591,
    4035519, 4036426, 4037313, 4038218, 4039155, 4040077, 4040995, 4041886, 4042824, 4043735,
    4044664, 4045548, 4046476, 4047414, 4048330, 4049217, 4050163, 4051063, 4051983, 4052864,
    4053804, 4054716, 4055653, 4056595, 4057498, 4058398, 4059297, 4060225, 4061142, 4062079,
    4063024, 4063961, 4064837, 4065772, 4066698, 4067617, 4068527, 4069448, 4070391, 4071275,
    4072197, 4073116, 4074029, 4074960]

def LA_66 : List ℕ := [
    4075111, 4075734, 4076364, 4077015, 4077651, 4078319, 4078970, 4079636, 4080283, 4080941,
    4081600, 4082271, 4082940, 4083576, 4084244, 4084934, 4085594, 4086231, 4086881, 4087559,
    4088211, 4088875, 4089508, 4090166, 4090834, 4091478, 4092140, 4092792, 4093454, 4094134,
    4094796, 4095436, 4096072, 4096723, 4097383, 4098030, 4098687, 4099344, 4100021, 4100689,
    4101326, 4102000, 4102643, 4103297, 4103941, 4104637, 4105288, 4105929, 4106590, 4107234,
    4107860, 4108534, 4109215, 4109867, 4110485, 4111152, 4111789, 4112436, 4113084, 4113739,
    4114390, 4115062, 4115705, 4116336, 4116976, 4117612, 4118276, 4118939, 4119590, 4120252,
    4120903, 4121546, 4122192, 4122847, 4123522, 4124172, 4124834, 4125483, 4126137, 4126768,
    4127433, 4128122, 4128770, 4129419, 4130033, 4130708, 4131371, 4132061, 4132716]

def LB_66 : List ℕ := [
    4075844, 4076762, 4077651, 4078586, 4079521, 4080440, 4081382, 4082316, 4083243, 4084175,
    4085143, 4086057, 4086977, 4087919, 4088863, 4089772, 4090701, 4091625, 4092555, 4093483,
    4094437, 4095356, 4096254, 4097172, 4098105, 4099039, 4099983, 4100901, 4101855, 4102761,
    4103672, 4104643, 4105557, 4106479, 4107398, 4108307, 4109259, 4110178, 4111099, 4112006,
    4112911, 4113838, 4114763, 4115695, 4116596, 4117501, 4118420, 4119356, 4120279, 4121212,
    4122118, 4123039, 4123991, 4124901, 4125824, 4126738, 4127692, 4128629, 4129545, 4130457,
    4131387, 4132346]

def LA_67 : List ℕ := [
    4133359, 4134009, 4134705, 4135363, 4136014, 4136665, 4137320, 4137982, 4138635, 4139266,
    4139933, 4140614, 4141286, 4141946, 4142620, 4143268, 4143895, 4144588, 4145263, 4145945,
    4146572, 4147215, 4147872, 4148547, 4149201, 4149857, 4150523, 4151171, 4151874, 4152509,
    4153135, 4153743, 4154410, 4155063, 4155736, 4156384, 4157027, 4157687, 4158362, 4159031,
    4159700, 4160350, 4160973, 4161612, 4162257, 4162912, 4163566, 4164238, 4164872, 4165541,
    4166215, 4166869, 4167513, 4168173, 4168848, 4169482, 4170169, 4170828, 4171496, 4172156,
    4172814, 4173459, 4174124, 4174795, 4175438, 4176062, 4176731, 4177398, 4178069, 4178733,
    4179392, 4180034, 4180721, 4181406, 4182056, 4182699, 4183322, 4183990, 4184662, 4185314,
    4185991, 4186668, 4187310, 4187973, 4188641, 4189297, 4189954, 4190616]

def LB_67 : List ℕ := [
    4133276, 4134205, 4135143, 4136074, 4136987, 4137938, 4138853, 4139780, 4140732, 4141663,
    4142619, 4143522, 4144466, 4145426, 4146369, 4147258, 4148191, 4149138, 4150076, 4150988,
    4151961, 4152858, 4153722, 4154665, 4155600, 4156513, 4157432, 4158383, 4159316, 4160269,
    4161135, 4162067, 4162997, 4163917, 4164832, 4165779, 4166724, 4167638, 4168548, 4169485,
    4170452, 4171383, 4172318, 4173236, 4174176, 4175113, 4176004, 4176950, 4177881, 4178834,
    4179750, 4180708, 4181670, 4182561, 4183467, 4184408, 4185350, 4186299, 4187222, 4188157,
    4189107, 4190034, 4190971]

def LA_68 : List ℕ := [
    4191272, 4191906, 4192571, 4193245, 4193911, 4194568, 4195218, 4195901, 4196573, 4197252,
    4197927, 4198616, 4199271, 4199932, 4200598, 4201228, 4201919, 4202588, 4203243, 4203907,
    4204580, 4205224, 4205888, 4206575, 4207240, 4207919, 4208557, 4209215, 4209890, 4210536,
    4211203, 4211871, 4212509, 4213150, 4213814, 4214477, 4215161, 4215785, 4216391, 4217053,
    4217727, 4218387, 4219066, 4219703, 4220398, 4221050, 4221738, 4222397, 4223044, 4223717,
    4224387, 4225066, 4225700, 4226372, 4227017, 4227681, 4228316, 4228988, 4229660, 4230307,
    4230988, 4231682, 4232327, 4232995, 4233675, 4234342, 4235012, 4235688, 4236348, 4237023,
    4237670, 4238356, 4239035, 4239701, 4240406, 4241091, 4241749, 4242396, 4243057, 4243737,
    4244406, 4245083, 4245763, 4246438, 4247098, 4247759, 4248408]

def LB_68 : List ℕ := [
    4191876, 4192820, 4193757, 4194695, 4195618, 4196586, 4197552, 4198512, 4199459, 4200402,
    4201278, 4202250, 4203195, 4204134, 4205062, 4206005, 4206961, 4207911, 4208819, 4209758,
    4210691, 4211638, 4212550, 4213455, 4214395, 4215338, 4216217, 4217137, 4218081, 4219039,
    4219968, 4220926, 4221871, 4222798, 4223736, 4224691, 4225601, 4226540, 4227476, 4228388,
    4229334, 4230257, 4231234, 4232158, 4233113, 4234084, 4235013, 4235967, 4236900, 4237842,
    4238793, 4239758, 4240741, 4241685, 4242612, 4243554, 4244502, 4245482, 4246417, 4247359,
    4248286]

def LA_69 : List ℕ := [
    4249085, 4249738, 4250397, 4251073, 4251731, 4252387, 4253059, 4253727, 4254358, 4255034,
    4255694, 4256346, 4257004, 4257670, 4258370, 4259034, 4259737, 4260377, 4261051, 4261695,
    4262342, 4263005, 4263681, 4264317, 4264983, 4265647, 4266315, 4267003, 4267639, 4268355,
    4269015, 4269663, 4270343, 4270964, 4271631, 4272280, 4272954, 4273653, 4274338, 4274992,
    4275676, 4276354, 4277005, 4277687, 4278338, 4279022, 4279686, 4280353, 4281027, 4281686,
    4282362, 4283030, 4283698, 4284375, 4285027, 4285705, 4286396, 4287069, 4287719, 4288384,
    4289050, 4289721, 4290390, 4291031, 4291701, 4292382, 4293028, 4293658, 4294326, 4295002,
    4295663, 4296330, 4297008, 4297660, 4298339, 4299023, 4299670, 4300337, 4301026, 4301700,
    4302362, 4303044, 4303706, 4304381, 4305035, 4305729, 4306379]

def LB_69 : List ℕ := [
    4249224, 4250162, 4251102, 4252051, 4252970, 4253908, 4254846, 4255777, 4256707, 4257636,
    4258615, 4259557, 4260510, 4261435, 4262348, 4263301, 4264208, 4265154, 4266088, 4267063,
    4267998, 4268960, 4269885, 4270812, 4271731, 4272661, 4273642, 4274590, 4275542, 4276492,
    4277434, 4278381, 4279338, 4280279, 4281230, 4282170, 4283110, 4284085, 4285001, 4285960,
    4286920, 4287848, 4288803, 4289744, 4290674, 4291605, 4292546, 4293461, 4294389, 4295337,
    4296285, 4297234, 4298177, 4299133, 4300061, 4301024, 4301970, 4302919, 4303853, 4304817,
    4305771, 4306691]

def LA_70 : List ℕ := [
    4307022, 4307679, 4308346, 4309018, 4309661, 4310341, 4311019, 4311676, 4312359, 4313028,
    4313718, 4314380, 4315074, 4315766, 4316442, 4317112, 4317775, 4318415, 4319092, 4319762,
    4320445, 4321131, 4321804, 4322476, 4323169, 4323842, 4324494, 4325153, 4325824, 4326478,
    4327158, 4327837, 4328495, 4329159, 4329836, 4330496, 4331165, 4331848, 4332522, 4333203,
    4333885, 4334554, 4335231, 4335876, 4336547, 4337249, 4337893, 4338570, 4339238, 4339897,
    4340575, 4341227, 4341893, 4342560, 4343194, 4343847, 4344501, 4345196, 4345885, 4346538,
    4347216, 4347891, 4348524, 4349210, 4349883, 4350565, 4351256, 4351908, 4352578, 4353240,
    4353893, 4354590, 4355251, 4355912, 4356569, 4357256, 4357942, 4358612, 4359285, 4359982,
    4360636, 4361334, 4362005, 4362657, 4363330, 4364029]

def LB_70 : List ℕ := [
    4307606, 4308561, 4309476, 4310438, 4311386, 4312337, 4313289, 4314238, 4315212, 4316178,
    4317135, 4318049, 4319003, 4319951, 4320919, 4321876, 4322842, 4323799, 4324720, 4325663,
    4326599, 4327549, 4328498, 4329446, 4330388, 4331349, 4332291, 4333257, 4334210, 4335165,
    4336095, 4337078, 4338003, 4338952, 4339886, 4340827, 4341778, 4342700, 4343601, 4344533,
    4345527, 4346455, 4347403, 4348347, 4349286, 4350244, 4351226, 4352159, 4353096, 4354037,
    4354987, 4355930, 4356885, 4357835, 4358793, 4359766, 4360706, 4361669, 4362604, 4363573,
    4364533]

def LA_71 : List ℕ := [
    4364698, 4365360, 4366013, 4366671, 4367351, 4368024, 4368703, 4369368, 4370028, 4370682,
    4371368, 4372063, 4372773, 4373440, 4374094, 4374752, 4375441, 4376102, 4376758, 4377441,
    4378123, 4378794, 4379477, 4380138, 4380814, 4381523, 4382182, 4382879, 4383540, 4384217,
    4384900, 4385580, 4386222, 4386882, 4387560, 4388244, 4388967, 4389624, 4390313, 4390984,
    4391661, 4392310, 4392987, 4393668, 4394343, 4395008, 4395647, 4396329, 4397002, 4397676,
    4398356, 4399056, 4399741, 4400411, 4401101, 4401752, 4402420, 4403113, 4403796, 4404475,
    4405158, 4405839, 4406557, 4407217, 4407898, 4408580, 4409251, 4409934, 4410607, 4411293,
    4411974, 4412655, 4413329, 4413999, 4414679, 4415342, 4416050, 4416753, 4417418, 4418106,
    4418804, 4419464, 4420147, 4420819, 4421485, 4422178]

def LB_71 : List ℕ := [
    4365468, 4366381, 4367342, 4368290, 4369250, 4370166, 4371131, 4372099, 4373097, 4374013,
    4374965, 4375917, 4376853, 4377817, 4378775, 4379739, 4380678, 4381654, 4382618, 4383573,
    4384525, 4385478, 4386415, 4387336, 4388320, 4389308, 4390264, 4391226, 4392153, 4393108,
    4394055, 4395010, 4395921, 4396870, 4397828, 4398817, 4399782, 4400745, 4401686, 4402637,
    4403615, 4404564, 4405541, 4406539, 4407481, 4408442, 4409406, 4410354, 4411320, 4412284,
    4413243, 4414205, 4415143, 4416125, 4417105, 4418064, 4419035, 4419997, 4420934, 4421893]

def LA_72 : List ℕ := [
    4422865, 4423534, 4424185, 4424868, 4425529, 4426214, 4426899, 4427547, 4428217, 4428906,
    4429599, 4430292, 4430966, 4431646, 4432311, 4433002, 4433684, 4434359, 4435006, 4435710,
    4436404, 4437062, 4437741, 4438437, 4439140, 4439791, 4440492, 4441184, 4441856, 4442549,
    4443232, 4443923, 4444599, 4445290, 4445942, 4446606, 4447323, 4448017, 4448700, 4449388,
    4450075, 4450763, 4451430, 4452102, 4452768, 4453445, 4454126, 4454796, 4455464, 4456157,
    4456837, 4457526, 4458210, 4458882, 4459556, 4460237, 4460913, 4461601, 4462258, 4462915,
    4463603, 4464294, 4464957, 4465620, 4466301, 4466983, 4467643, 4468323, 4468999, 4469687,
    4470404, 4471079, 4471735, 4472432, 4473121, 4473811, 4474485, 4475136, 4475819, 4476485,
    4477136, 4477814, 4478505, 4479204, 4479895]

def LB_72 : List ℕ := [
    4422871, 4423815, 4424755, 4425709, 4426673, 4427603, 4428571, 4429541, 4430510, 4431475,
    4432422, 4433384, 4434350, 4435269, 4436262, 4437226, 4438206, 4439185, 4440118, 4441111,
    4442051, 4443042, 4444008, 4444972, 4445914, 4446856, 4447858, 4448840, 4449800, 4450780,
    4451712, 4452678, 4453632, 4454587, 4455533, 4456501, 4457475, 4458434, 4459392, 4460345,
    4461315, 4462257, 4463205, 4464182, 4465118, 4466062, 4467032, 4467964, 4468933, 4469919,
    4470903, 4471838, 4472817, 4473791, 4474730, 4475692, 4476630, 4477550, 4478532, 4479520,
    4480501]

def LA_73 : List ℕ := [
    4480587, 4481273, 4481915, 4482592, 4483255, 4483947, 4484645, 4485318, 4485998, 4486637,
    4487320, 4488011, 4488694, 4489364, 4490027, 4490705, 4491386, 4492061, 4492766, 4493435,
    4494113, 4494832, 4495520, 4496192, 4496862, 4497544, 4498241, 4498926, 4499602, 4500286,
    4500955, 4501645, 4502354, 4503037, 4503712, 4504406, 4505135, 4505817, 4506488, 4507151,
    4507836, 4508508, 4509199, 4509886, 4510571, 4511256, 4511952, 4512632, 4513313, 4514026,
    4514698, 4515386, 4516065, 4516753, 4517445, 4518135, 4518794, 4519457, 4520162, 4520827,
    4521525, 4522187, 4522871, 4523580, 4524278, 4524965, 4525631, 4526325, 4527001, 4527665,
    4528362, 4529055, 4529727, 4530390, 4531076, 4531761, 4532461, 4533136, 4533829, 4534518,
    4535195, 4535885, 4536567, 4537277]

def LB_73 : List ℕ := [
    4481452, 4482388, 4483338, 4484326, 4485270, 4486220, 4487172, 4488130, 4489092, 4490034,
    4490986, 4491947, 4492938, 4493884, 4494892, 4495848, 4496804, 4497764, 4498744, 4499706,
    4500660, 4501633, 4502628, 4503591, 4504577, 4505567, 4506526, 4507492, 4508431, 4509406,
    4510380, 4511338, 4512315, 4513276, 4514278, 4515240, 4516211, 4517175, 4518153, 4519091,
    4520067, 4521001, 4521969, 4522935, 4523934, 4524908, 4525858, 4526834, 4527793, 4528766,
    4529725, 4530679, 4531660, 4532611, 4533592, 4534562, 4535513, 4536500, 4537472]

def LA_74 : List ℕ := [
    4537931, 4538630, 4539293, 4539986, 4540633, 4541334, 4542005, 4542693, 4543374, 4544075,
    4544786, 4545475, 4546153, 4546826, 4547517, 4548197, 4548893, 4549573, 4550245, 4550926,
    4551623, 4552331, 4553015, 4553701, 4554398, 4555107, 4555809, 4556467, 4557166, 4557845,
    4558528, 4559203, 4559897, 4560592, 4561258, 4561961, 4562663, 4563341, 4564020, 4564698,
    4565397, 4566101, 4566803, 4567477, 4568146, 4568854, 4569565, 4570229, 4570917, 4571601,
    4572298, 4572973, 4573646, 4574327, 4575008, 4575675, 4576379, 4577051, 4577714, 4578404,
    4579104, 4579791, 4580487, 4581185, 4581859, 4582522, 4583191, 4583889, 4584571, 4585243,
    4585934, 4586600, 4587318, 4588005, 4588699, 4589406, 4590100, 4590785, 4591504, 4592193,
    4592860, 4593564, 4594227, 4594913]

def LB_74 : List ℕ := [
    4538425, 4539396, 4540350, 4541314, 4542283, 4543232, 4544217, 4545222, 4546175, 4547140,
    4548105, 4549084, 4550046, 4550991, 4551991, 4552964, 4553942, 4554941, 4555925, 4556872,
    4557850, 4558816, 4559774, 4560754, 4561735, 4562718, 4563676, 4564638, 4565628, 4566622,
    4567587, 4568545, 4569549, 4570505, 4571467, 4572456, 4573408, 4574362, 4575304, 4576293,
    4577256, 4578198, 4579190, 4580164, 4581151, 4582108, 4583041, 4584020, 4584993, 4585944,
    4586899, 4587899, 4588886, 4589880, 4590855, 4591845, 4592800, 4593781, 4594739, 4595730]

def LA_75 : List ℕ := [
    4595621, 4596297, 4596989, 4597677, 4598359, 4599069, 4599754, 4600479, 4601166, 4601858,
    4602551, 4603257, 4603957, 4604615, 4605293, 4606000, 4606647, 4607337, 4608031, 4608732,
    4609412, 4610114, 4610777, 4611449, 4612183, 4612884, 4613575, 4614238, 4614910, 4615603,
    4616318, 4617005, 4617708, 4618415, 4619118, 4619815, 4620525, 4621181, 4621879, 4622575,
    4623239, 4623950, 4624645, 4625339, 4626031, 4626712, 4627418, 4628114, 4628778, 4629480,
    4630159, 4630807, 4631513, 4632195, 4632891, 4633581, 4634275, 4634958, 4635677, 4636367,
    4637082, 4637786, 4638483, 4639172, 4639859, 4640557, 4641245, 4641932, 4642655, 4643315,
    4644004, 4644703, 4645398, 4646101, 4646774, 4647446, 4648156, 4648857, 4649584, 4650286,
    4650982, 4651675, 4652347, 4653021]

def LB_75 : List ℕ := [
    4596717, 4597671, 4598643, 4599628, 4600642, 4601620, 4602593, 4603595, 4604539, 4605509,
    4606459, 4607418, 4608417, 4609382, 4610359, 4611313, 4612327, 4613294, 4614260, 4615219,
    4616231, 4617193, 4618181, 4619188, 4620177, 4621136, 4622120, 4623093, 4624069, 4625048,
    4626031, 4626998, 4627992, 4628954, 4629913, 4630865, 4631861, 4632830, 4633789, 4634779,
    4635779, 4636759, 4637765, 4638744, 4639720, 4640705, 4641673, 4642687, 4643628, 4644614,
    4645587, 4646578, 4647523, 4648528, 4649550, 4650545, 4651505, 4652459, 4653450]

def LA_76 : List ℕ := [
    4653723, 4654448, 4655138, 4655823, 4656474, 4657186, 4657879, 4658579, 4659260, 4659947,
    4660656, 4661330, 4662053, 4662745, 4663462, 4664131, 4664820, 4665516, 4666211, 4666925,
    4667627, 4668313, 4668959, 4669637, 4670313, 4670993, 4671700, 4672398, 4673066, 4673789,
    4674511, 4675212, 4675917, 4676600, 4677290, 4677999, 4678675, 4679359, 4680027, 4680740,
    4681417, 4682115, 4682835, 4683561, 4684249, 4684961, 4685663, 4686373, 4687060, 4687764,
    4688455, 4689157, 4689816, 4690537, 4691233, 4691952, 4692669, 4693332, 4694033, 4694754,
    4695448, 4696141, 4696851, 4697563, 4698266, 4698928, 4699611, 4700309, 4701020, 4701704,
    4702387, 4703078, 4703774, 4704473, 4705178, 4705871, 4706559, 4707247, 4707973, 4708643,
    4709348, 4710058, 4710770]

def LB_76 : List ℕ := [
    4654456, 4655439, 4656364, 4657355, 4658364, 4659318, 4660285, 4661268, 4662273, 4663270,
    4664241, 4665211, 4666199, 4667199, 4668175, 4669120, 4670055, 4671034, 4672023, 4672990,
    4674007, 4675013, 4676011, 4676979, 4677958, 4678933, 4679892, 4680876, 4681838, 4682855,
    4683869, 4684861, 4685873, 4686854, 4687831, 4688800, 4689770, 4690771, 4691777, 4692775,
    4693739, 4694751, 4695731, 4696727, 4697725, 4698695, 4699653, 4700627, 4701626, 4702614,
    4703579, 4704576, 4705557, 4706543, 4707518, 4708514, 4709478, 4710494]

def LA_77 : List ℕ := [
    4711491, 4712176, 4712875, 4713573, 4714280, 4715001, 4715662, 4716389, 4717112, 4717819,
    4718511, 4719203, 4719901, 4720599, 4721293, 4722002, 4722705, 4723425, 4724125, 4724828,
    4725571, 4726290, 4726962, 4727668, 4728383, 4729109, 4729813, 4730515, 4731238, 4731935,
    4732643, 4733337, 4734046, 4734731, 4735430, 4736131, 4736808, 4737503, 4738239, 4738942,
    4739633, 4740323, 4741014, 4741684, 4742389, 4743100, 4743788, 4744507, 4745203, 4745919,
    4746595, 4747323, 4748032, 4748748, 4749446, 4750156, 4750863, 4751566, 4752248, 4752938,
    4753621, 4754315, 4755028, 4755705, 4756418, 4757143, 4757818, 4758534, 4759255, 4759935,
    4760628, 4761318, 4762054, 4762751, 4763457, 4764133, 4764825, 4765544, 4766223, 4766922,
    4767630, 4768313]

def LB_77 : List ℕ := [
    4711518, 4712508, 4713486, 4714468, 4715449, 4716466, 4717497, 4718464, 4719455, 4720435,
    4721430, 4722422, 4723433, 4724409, 4725457, 4726455, 4727436, 4728437, 4729436, 4730447,
    4731454, 4732444, 4733449, 4734428, 4735412, 4736395, 4737369, 4738383, 4739385, 4740349,
    4741318, 4742303, 4743310, 4744279, 4745285, 4746274, 4747286, 4748281, 4749284, 4750302,
    4751297, 4752263, 4753244, 4754205, 4755214, 4756189, 4757207, 4758180, 4759193, 4760161,
    4761152, 4762170, 4763143, 4764126, 4765104, 4766110, 4767087, 4768060]

def LA_78 : List ℕ := [
    4769028, 4769709, 4770432, 4771150, 4771836, 4772531, 4773239, 4773963, 4774654, 4775354,
    4776074, 4776762, 4777469, 4778171, 4778870, 4779606, 4780312, 4781032, 4781735, 4782429,
    4783130, 4783862, 4784571, 4785268, 4785944, 4786668, 4787396, 4788069, 4788750, 4789466,
    4790155, 4790829, 4791526, 4792249, 4792914, 4793607, 4794318, 4794994, 4795698, 4796406,
    4797119, 4797825, 4798543, 4799237, 4799937, 4800635, 4801347, 4802036, 4802748, 4803457,
    4804177, 4804859, 4805606, 4806268, 4806963, 4807683, 4808358, 4809089, 4809812, 4810512,
    4811222, 4811933, 4812627, 4813301, 4814025, 4814736, 4815446, 4816154, 4816863, 4817602,
    4818311, 4819018, 4819717, 4820386, 4821082, 4821774, 4822515, 4823255, 4823954, 4824690,
    4825392]

def LB_78 : List ℕ := [
    4769067, 4770054, 4771078, 4772057, 4773041, 4774056, 4775030, 4776041, 4777035, 4778015,
    4779020, 4780044, 4781053, 4782065, 4783039, 4784069, 4785043, 4786015, 4787044, 4788027,
    4788999, 4790009, 4790946, 4791938, 4792916, 4793895, 4794880, 4795884, 4796878, 4797878,
    4798881, 4799864, 4800866, 4801840, 4802850, 4803867, 4804840, 4805862, 4806816, 4807832,
    4808829, 4809839, 4810836, 4811844, 4812826, 4813798, 4814824, 4815826, 4816825, 4817863,
    4818864, 4819852, 4820814, 4821787, 4822841, 4823842, 4824868, 4825873]

def LA_79 : List ℕ := [
    4826109, 4826838, 4827546, 4828246, 4828950, 4829655, 4830346, 4831065, 4831770, 4832497,
    4833164, 4833887, 4834600, 4835298, 4836046, 4836736, 4837415, 4838132, 4838813, 4839508,
    4840202, 4840912, 4841624, 4842316, 4843027, 4843718, 4844422, 4845114, 4845810, 4846512,
    4847228, 4847911, 4848609, 4849335, 4850057, 4850779, 4851450, 4852162, 4852880, 4853565,
    4854269, 4854967, 4855674, 4856392, 4857111, 4857815, 4858512, 4859237, 4859934, 4860631,
    4861368, 4862082, 4862785, 4863475, 4864183, 4864909, 4865606, 4866316, 4867038, 4867753,
    4868462, 4869154, 4869814, 4870516, 4871244, 4871948, 4872646, 4873346, 4874084, 4874810,
    4875532, 4876249, 4876959, 4877640, 4878352, 4879081, 4879795, 4880531, 4881245, 4881938,
    4882667, 4883383]

def LB_79 : List ℕ := [
    4826897, 4827904, 4828890, 4829877, 4830889, 4831887, 4832866, 4833877, 4834877, 4835900,
    4836888, 4837858, 4838852, 4839852, 4840838, 4841822, 4842808, 4843812, 4844810, 4845780,
    4846760, 4847750, 4848764, 4849764, 4850796, 4851763, 4852780, 4853766, 4854766, 4855746,
    4856769, 4857762, 4858767, 4859757, 4860762, 4861777, 4862783, 4863765, 4864786, 4865783,
    4866797, 4867798, 4868801, 4869739, 4870751, 4871756, 4872751, 4873755, 4874790, 4875815,
    4876824, 4877787, 4878814, 4879824, 4880848, 4881842, 4882871]

def LA_80 : List ℕ := [
    4884101, 4884820, 4885539, 4886294, 4887028, 4887732, 4888429, 4889155, 4889861, 4890576,
    4891282, 4891967, 4892660, 4893339, 4894047, 4894722, 4895463, 4896178, 4896891, 4897593,
    4898285, 4898985, 4899685, 4900385, 4901098, 4901811, 4902513, 4903242, 4903928, 4904645,
    4905349, 4906076, 4906816, 4907522, 4908205, 4908934, 4909643, 4910361, 4911045, 4911761,
    4912464, 4913176, 4913926, 4914626, 4915360, 4916107, 4916817, 4917510, 4918215, 4918919,
    4919609, 4920339, 4921038, 4921740, 4922469, 4923140, 4923861, 4924567, 4925288, 4925989,
    4926691, 4927420, 4928124, 4928837, 4929566, 4930282, 4930993, 4931706, 4932433, 4933134,
    4933818, 4934559, 4935254, 4935990, 4936698, 4937389, 4938081, 4938798, 4939503, 4940196]

def LB_80 : List ℕ := [
    4883859, 4884910, 4885923, 4886977, 4887980, 4888986, 4889980, 4891002, 4891976, 4892960,
    4893937, 4894915, 4895935, 4896937, 4897935, 4898927, 4899926, 4900915, 4901909, 4902926,
    4903909, 4904933, 4905947, 4906971, 4907961, 4908971, 4909985, 4910967, 4911968, 4912973,
    4914019, 4915025, 4916073, 4917082, 4918066, 4919053, 4920068, 4921052, 4922081, 4923032,
    4924045, 4925050, 4926057, 4927051, 4928067, 4929090, 4930101, 4931106, 4932133, 4933126,
    4934116, 4935127, 4936153, 4937145, 4938132, 4939138, 4940115]

def LA_81 : List ℕ := [
    4940936, 4941658, 4942373, 4943069, 4943811, 4944506, 4945187, 4945886, 4946578, 4947321,
    4948028, 4948773, 4949475, 4950157, 4950888, 4951618, 4952328, 4953046, 4953737, 4954446,
    4955161, 4955879, 4956575, 4957299, 4958050, 4958749, 4959431, 4960157, 4960877, 4961619,
    4962357, 4963077, 4963750, 4964486, 4965207, 4965933, 4966646, 4967378, 4968128, 4968825,
    4969537, 4970269, 4970953, 4971683, 4972437, 4973168, 4973880, 4974560, 4975264, 4975981,
    4976681, 4977391, 4978122, 4978832, 4979556, 4980290, 4980993, 4981702, 4982410, 4983098,
    4983839, 4984573, 4985287, 4986014, 4986702, 4987445, 4988157, 4988865, 4989596, 4990315,
    4991016, 4991747, 4992474, 4993196, 4993916, 4994632, 4995340, 4996041, 4996780, 4997493,
    4998221]

def LB_81 : List ℕ := [
    4941159, 4942195, 4943183, 4944189, 4945160, 4946147, 4947168, 4948176, 4949215, 4950178,
    4951216, 4952226, 4953241, 4954222, 4955240, 4956227, 4957247, 4958290, 4959268, 4960282,
    4961323, 4962361, 4963349, 4964356, 4965380, 4966419, 4967438, 4968480, 4969475, 4970479,
    4971505, 4972551, 4973548, 4974545, 4975542, 4976544, 4977550, 4978576, 4979592, 4980615,
    4981617, 4982595, 4983623, 4984653, 4985668, 4986668, 4987720, 4988700, 4989737, 4990741,
    4991760, 4992782, 4993803, 4994807, 4995805, 4996844, 4997850]

def LA_82 : List ℕ := [
    4998907, 4999621, 5000349, 5001097, 5001800, 5002518, 5003284, 5003979, 5004697, 5005419,
    5006122, 5006812, 5007550, 5008248, 5008977, 5009684, 5010400, 5011094, 5011817, 5012542,
    5013249, 5013985, 5014696, 5015441, 5016144, 5016837, 5017573, 5018286, 5019006, 5019741,
    5020455, 5021157, 5021899, 5022645, 5023359, 5024092, 5024794, 5025527, 5026231, 5026992,
    5027730, 5028432, 5029159, 5029863, 5030571, 5031286, 5031978, 5032742, 5033488, 5034186,
    5034884, 5035618, 5036323, 5037035, 5037756, 5038486, 5039196, 5039908, 5040643, 5041385,
    5042091, 5042826, 5043541, 5044243, 5044945, 5045681, 5046413, 5047157, 5047888, 5048589,
    5049299, 5050015, 5050729, 5051442, 5052183, 5052889, 5053610, 5054364, 5055089]

def LB_82 : List ℕ := [
    4998850, 4999869, 5000902, 5001910, 5002958, 5003973, 5004995, 5005990, 5006975, 5007991,
    5009016, 5010034, 5011021, 5012042, 5013027, 5014081, 5015105, 5016117, 5017101, 5018134,
    5019140, 5020178, 5021176, 5022216, 5023245, 5024275, 5025296, 5026312, 5027371, 5028379,
    5029397, 5030391, 5031410, 5032422, 5033488, 5034464, 5035492, 5036512, 5037515, 5038532,
    5039553, 5040575, 5041615, 5042627, 5043640, 5044643, 5045666, 5046714, 5047742, 5048750,
    5049766, 5050759, 5051779, 5052799, 5053831, 5054873, 5055885]

def LA_83 : List ℕ := [
    5055795, 5056528, 5057271, 5057982, 5058705, 5059399, 5060090, 5060818, 5061544, 5062266,
    5063012, 5063697, 5064468, 5065176, 5065922, 5066652, 5067350, 5068072, 5068812, 5069521,
    5070239, 5070982, 5071682, 5072404, 5073125, 5073828, 5074550, 5075240, 5075925, 5076654,
    5077390, 5078112, 5078828, 5079558, 5080262, 5081004, 5081748, 5082477, 5083209, 5083921,
    5084653, 5085367, 5086083, 5086824, 5087556, 5088265, 5089001, 5089723, 5090412, 5091143,
    5091880, 5092579, 5093300, 5094028, 5094738, 5095470, 5096191, 5096906, 5097643, 5098360,
    5099098, 5099829, 5100524, 5101290, 5102020, 5102736, 5103457, 5104187, 5104918, 5105631,
    5106351, 5107103, 5107833, 5108558, 5109287, 5110029, 5110745, 5111511, 5112236, 5112987]

def LB_83 : List ℕ := [
    5056903, 5057938, 5058950, 5059921, 5060942, 5061984, 5063019, 5064026, 5065065, 5066089,
    5067104, 5068124, 5069169, 5070179, 5071211, 5072215, 5073230, 5074249, 5075229, 5076219,
    5077251, 5078276, 5079309, 5080304, 5081369, 5082385, 5083418, 5084437, 5085442, 5086485,
    5087521, 5088534, 5089557, 5090558, 5091591, 5092594, 5093609, 5094630, 5095657, 5096691,
    5097712, 5098730, 5099774, 5100781, 5101827, 5102854, 5103878, 5104909, 5105926, 5106975,
    5108007, 5109019, 5110076, 5111108, 5112167, 5113190]

def LA_84 : List ℕ := [
    5113702, 5114423, 5115124, 5115813, 5116552, 5117320, 5118018, 5118744, 5119481, 5120221,
    5120990, 5121728, 5122459, 5123182, 5123925, 5124659, 5125368, 5126092, 5126812, 5127536,
    5128277, 5128965, 5129701, 5130435, 5131194, 5131920, 5132641, 5133352, 5134060, 5134776,
    5135492, 5136203, 5136895, 5137618, 5138310, 5139042, 5139767, 5140478, 5141234, 5141966,
    5142720, 5143463, 5144172, 5144894, 5145596, 5146322, 5147057, 5147798, 5148513, 5149234,
    5149963, 5150699, 5151435, 5152170, 5152908, 5153635, 5154375, 5155122, 5155831, 5156578,
    5157324, 5158048, 5158815, 5159549, 5160252, 5160992, 5161704, 5162446, 5163144, 5163848,
    5164585, 5165329, 5166043, 5166777, 5167507, 5168232, 5168996, 5169697]

def LB_84 : List ℕ := [
    5114220, 5115222, 5116221, 5117296, 5118284, 5119324, 5120379, 5121456, 5122482, 5123508,
    5124561, 5125587, 5126594, 5127620, 5128627, 5129652, 5130708, 5131748, 5132765, 5133757,
    5134779, 5135779, 5136789, 5137792, 5138799, 5139817, 5140850, 5141895, 5142956, 5143974,
    5145011, 5145999, 5147039, 5148080, 5149097, 5150130, 5151156, 5152209, 5153254, 5154279,
    5155325, 5156372, 5157413, 5158437, 5159504, 5160523, 5161532, 5162581, 5163577, 5164594,
    5165632, 5166676, 5167701, 5168761, 5169759]

def LA_85 : List ℕ := [
    5170428, 5171185, 5171935, 5172656, 5173381, 5174121, 5174853, 5175593, 5176339, 5177065,
    5177782, 5178531, 5179261, 5179964, 5180717, 5181439, 5182158, 5182853, 5183588, 5184304,
    5185052, 5185772, 5186523, 5187220, 5187953, 5188677, 5189388, 5190123, 5190853, 5191591,
    5192327, 5193023, 5193754, 5194486, 5195205, 5195944, 5196685, 5197408, 5198115, 5198810,
    5199569, 5200275, 5201001, 5201719, 5202445, 5203163, 5203879, 5204605, 5205311, 5206042,
    5206765, 5207498, 5208233, 5208997, 5209723, 5210436, 5211191, 5211921, 5212664, 5213360,
    5214083, 5214821, 5215540, 5216277, 5217020, 5217758, 5218517, 5219247, 5219960, 5220714,
    5221456, 5222202, 5222915, 5223660, 5224398, 5225146, 5225879, 5226639, 5227389]

def LB_85 : List ℕ := [
    5170797, 5171872, 5172912, 5173923, 5174955, 5176012, 5177055, 5178078, 5179124, 5180127,
    5181187, 5182201, 5183190, 5184219, 5185275, 5186309, 5187320, 5188341, 5189361, 5190394,
    5191441, 5192453, 5193481, 5194502, 5195535, 5196581, 5197603, 5198593, 5199633, 5200645,
    5201658, 5202682, 5203714, 5204725, 5205736, 5206767, 5207803, 5208858, 5209905, 5210923,
    5211976, 5213010, 5214011, 5215039, 5216084, 5217129, 5218182, 5219227, 5220241, 5221319,
    5222362, 5223403, 5224430, 5225492, 5226539, 5227600]

def LA_86 : List ℕ := [
    5228124, 5228834, 5229549, 5230305, 5231033, 5231760, 5232494, 5233263, 5233983, 5234742,
    5235495, 5236227, 5236963, 5237691, 5238409, 5239172, 5239905, 5240614, 5241327, 5242105,
    5242836, 5243576, 5244318, 5245070, 5245798, 5246502, 5247216, 5247990, 5248686, 5249421,
    5250146, 5250890, 5251634, 5252348, 5253092, 5253788, 5254526, 5255287, 5256027, 5256768,
    5257471, 5258231, 5258976, 5259712, 5260448, 5261177, 5261919, 5262662, 5263395, 5264099,
    5264846, 5265586, 5266322, 5267056, 5267831, 5268594, 5269350, 5270058, 5270781, 5271502,
    5272232, 5272960, 5273718, 5274440, 5275167, 5275892, 5276633, 5277368, 5278091, 5278836,
    5279562, 5280296, 5281029, 5281799, 5282542, 5283298, 5284048]

def LB_86 : List ℕ := [
    5228613, 5229631, 5230699, 5231707, 5232761, 5233829, 5234876, 5235935, 5236973, 5237988,
    5239039, 5240074, 5241089, 5242160, 5243222, 5244260, 5245305, 5246333, 5247338, 5248386,
    5249410, 5250430, 5251490, 5252519, 5253529, 5254568, 5255632, 5256685, 5257686, 5258754,
    5259807, 5260846, 5261884, 5262945, 5263940, 5264989, 5266038, 5267080, 5268163, 5269232,
    5270257, 5271261, 5272299, 5273338, 5274390, 5275415, 5276469, 5277480, 5278519, 5279562,
    5280601, 5281659, 5282735, 5283775, 5284836]

def LA_87 : List ℕ := [
    5284779, 5285527, 5286265, 5287033, 5287773, 5288534, 5289259, 5289963, 5290699, 5291458,
    5292183, 5292913, 5293663, 5294383, 5295097, 5295829, 5296570, 5297301, 5298039, 5298805,
    5299528, 5300256, 5301021, 5301737, 5302461, 5303193, 5303916, 5304688, 5305436, 5306183,
    5306899, 5307654, 5308388, 5309155, 5309906, 5310634, 5311413, 5312135, 5312865, 5313596,
    5314335, 5315065, 5315818, 5316512, 5317229, 5317966, 5318701, 5319433, 5320177, 5320911,
    5321644, 5322357, 5323109, 5323883, 5324650, 5325383, 5326114, 5326853, 5327560, 5328336,
    5329062, 5329795, 5330563, 5331315, 5332022, 5332794, 5333527, 5334258, 5334997, 5335717,
    5336467, 5337231, 5337963, 5338687, 5339410, 5340170, 5340903, 5341632]

def LB_87 : List ℕ := [
    5285884, 5286951, 5288015, 5289061, 5290076, 5291115, 5292166, 5293197, 5294224, 5295257,
    5296295, 5297331, 5298390, 5299440, 5300462, 5301531, 5302550, 5303582, 5304645, 5305695,
    5306719, 5307769, 5308845, 5309914, 5310985, 5312018, 5313057, 5314087, 5315123, 5316156,
    5317161, 5318203, 5319243, 5320284, 5321333, 5322346, 5323429, 5324512, 5325536, 5326579,
    5327598, 5328667, 5329708, 5330765, 5331814, 5332873, 5333939, 5334963, 5335994, 5337072,
    5338117, 5339143, 5340183, 5341226]

def LA_88 : List ℕ := [
    5342369, 5343116, 5343850, 5344571, 5345307, 5346031, 5346781, 5347545, 5348281, 5348997,
    5349753, 5350509, 5351262, 5351998, 5352732, 5353490, 5354216, 5354949, 5355691, 5356445,
    5357201, 5357920, 5358621, 5359381, 5360155, 5360890, 5361644, 5362372, 5363109, 5363876,
    5364639, 5365368, 5366113, 5366861, 5367616, 5368337, 5369087, 5369824, 5370586, 5371350,
    5372083, 5372843, 5373544, 5374291, 5375061, 5375802, 5376563, 5377287, 5378025, 5378751,
    5379485, 5380195, 5380923, 5381645, 5382383, 5383092, 5383859, 5384592, 5385319, 5386088,
    5386830, 5387574, 5388292, 5389063, 5389808, 5390566, 5391331, 5392057, 5392784, 5393542,
    5394262, 5395023, 5395754, 5396474, 5397243, 5397983, 5398741]

def LB_88 : List ℕ := [
    5342265, 5343299, 5344351, 5345364, 5346421, 5347481, 5348529, 5349562, 5350628, 5351678,
    5352726, 5353778, 5354816, 5355861, 5356933, 5357968, 5358986, 5360069, 5361126, 5362161,
    5363212, 5364288, 5365339, 5366394, 5367464, 5368486, 5369552, 5370616, 5371678, 5372751,
    5373756, 5374804, 5375878, 5376937, 5377965, 5379022, 5380031, 5381052, 5382083, 5383093,
    5384171, 5385200, 5386269, 5387344, 5388346, 5389424, 5390492, 5391555, 5392590, 5393643,
    5394687, 5395732, 5396766, 5397825, 5398898]

def LA_89 : List ℕ := [
    5399484, 5400257, 5401020, 5401758, 5402503, 5403224, 5403980, 5404683, 5405452, 5406219,
    5406970, 5407701, 5408473, 5409218, 5409942, 5410689, 5411417, 5412175, 5412899, 5413626,
    5414393, 5415134, 5415864, 5416620, 5417359, 5418107, 5418813, 5419540, 5420310, 5421056,
    5421812, 5422577, 5423278, 5424002, 5424770, 5425533, 5426279, 5427011, 5427760, 5428518,
    5429283, 5430053, 5430803, 5431552, 5432284, 5433027, 5433763, 5434510, 5435259, 5435996,
    5436794, 5437542, 5438288, 5439062, 5439802, 5440572, 5441333, 5442039, 5442766, 5443527,
    5444290, 5445020, 5445755, 5446520, 5447256, 5448004, 5448758, 5449502, 5450237, 5451004,
    5451733, 5452501, 5453219, 5453962, 5454723, 5455450]

def LB_89 : List ℕ := [
    5399974, 5401054, 5402098, 5403131, 5404177, 5405226, 5406310, 5407359, 5408420, 5409489,
    5410507, 5411550, 5412607, 5413639, 5414710, 5415764, 5416804, 5417855, 5418886, 5419933,
    5420989, 5422058, 5423091, 5424123, 5425224, 5426267, 5427311, 5428383, 5429444, 5430535,
    5431600, 5432618, 5433690, 5434736, 5435789, 5436893, 5437937, 5439037, 5440102, 5441175,
    5442194, 5443224, 5444313, 5445328, 5446400, 5447470, 5448532, 5449569, 5450623, 5451673,
    5452740, 5453788, 5454837, 5455902]

def LA_90 : List ℕ := [
    5456216, 5456956, 5457703, 5458446, 5459208, 5459925, 5460706, 5461458, 5462199, 5462985,
    5463717, 5464461, 5465218, 5465935, 5466680, 5467426, 5468202, 5468949, 5469700, 5470457,
    5471186, 5471928, 5472698, 5473442, 5474155, 5474919, 5475696, 5476416, 5477177, 5477928,
    5478686, 5479460, 5480238, 5481008, 5481755, 5482511, 5483266, 5484027, 5484794, 5485544,
    5486335, 5487060, 5487828, 5488593, 5489344, 5490088, 5490853, 5491562, 5492316, 5493067,
    5493810, 5494556, 5495288, 5496050, 5496785, 5497537, 5498290, 5499042, 5499808, 5500555,
    5501313, 5502091, 5502832, 5503569, 5504296, 5505066, 5505818, 5506579, 5507321, 5508049,
    5508826, 5509523, 5510304, 5511066, 5511815, 5512590, 5513365]

def LB_90 : List ℕ := [
    5456955, 5458012, 5459068, 5460115, 5461196, 5462244, 5463340, 5464390, 5465447, 5466465,
    5467547, 5468615, 5469678, 5470723, 5471779, 5472857, 5473892, 5474951, 5476032, 5477090,
    5478136, 5479217, 5480316, 5481395, 5482469, 5483534, 5484615, 5485687, 5486773, 5487838,
    5488909, 5489970, 5491039, 5492050, 5493122, 5494186, 5495222, 5496305, 5497339, 5498401,
    5499462, 5500543, 5501621, 5502683, 5503722, 5504794, 5505866, 5506944, 5507968, 5509035,
    5510083, 5511161, 5512230, 5513324]

def LA_91 : List ℕ := [
    5514110, 5514870, 5515648, 5516408, 5517147, 5517910, 5518680, 5519420, 5520195, 5520915,
    5521673, 5522408, 5523158, 5523901, 5524643, 5525393, 5526134, 5526892, 5527650, 5528398,
    5529125, 5529880, 5530620, 5531365, 5532116, 5532870, 5533616, 5534402, 5535140, 5535923,
    5536680, 5537421, 5538207, 5538968, 5539715, 5540461, 5541211, 5541976, 5542772, 5543527,
    5544273, 5545001, 5545749, 5546513, 5547242, 5547985, 5548731, 5549487, 5550255, 5551018,
    5551746, 5552500, 5553296, 5554056, 5554785, 5555507, 5556209, 5556982, 5557734, 5558511,
    5559258, 5560021, 5560762, 5561517, 5562275, 5563032, 5563774, 5564532, 5565307, 5566080,
    5566846, 5567592, 5568354, 5569084, 5569846]

def LB_91 : List ℕ := [
    5514385, 5515471, 5516547, 5517597, 5518692, 5519754, 5520811, 5521865, 5522921, 5523973,
    5525032, 5526081, 5527170, 5528195, 5529249, 5530296, 5531357, 5532434, 5533482, 5534567,
    5535648, 5536731, 5537799, 5538879, 5539954, 5541004, 5542086, 5543176, 5544242, 5545281,
    5546351, 5547395, 5548446, 5549515, 5550591, 5551649, 5552724, 5553824, 5554859, 5555874,
    5556932, 5558005, 5559098, 5560154, 5561214, 5562282, 5563348, 5564399, 5565501, 5566586,
    5567650, 5568694, 5569770]

def LA_92 : List ℕ := [
    5570577, 5571353, 5572068, 5572817, 5573569, 5574349, 5575112, 5575862, 5576632, 5577387,
    5578184, 5578947, 5579694, 5580471, 5581226, 5581998, 5582760, 5583500, 5584232, 5584991,
    5585758, 5586510, 5587280, 5588041, 5588812, 5589587, 5590292, 5591058, 5591818, 5592563,
    5593295, 5594059, 5594802, 5595562, 5596353, 5597123, 5597865, 5598659, 5599418, 5600160,
    5600927, 5601695, 5602434, 5603192, 5603952, 5604730, 5605458, 5606191, 5606953, 5607708,
    5608468, 5609173, 5609903, 5610642, 5611407, 5612213, 5612974, 5613730, 5614485, 5615241,
    5616003, 5616758, 5617505, 5618249, 5619015, 5619788, 5620554, 5621312, 5622070, 5622810,
    5623590, 5624383, 5625148, 5625944, 5626705]

def LB_92 : List ℕ := [
    5570827, 5571882, 5572924, 5574000, 5575099, 5576165, 5577247, 5578345, 5579428, 5580506,
    5581586, 5582669, 5583720, 5584745, 5585844, 5586914, 5587999, 5589087, 5590133, 5591202,
    5592273, 5593310, 5594382, 5595455, 5596544, 5597631, 5598734, 5599788, 5600860, 5601952,
    5602996, 5604062, 5605138, 5606185, 5607270, 5608321, 5609346, 5610388, 5611456, 5612573,
    5613635, 5614718, 5615794, 5616852, 5617913, 5618992, 5620067, 5621156, 5622214, 5623294,
    5624405, 5625480, 5626594, 5627671]

def LA_93 : List ℕ := [
    5627469, 5628256, 5629022, 5629794, 5630569, 5631304, 5632076, 5632840, 5633572, 5634353,
    5635130, 5635850, 5636609, 5637362, 5638144, 5638913, 5639670, 5640418, 5641181, 5641945,
    5642705, 5643494, 5644260, 5645004, 5645756, 5646502, 5647235, 5648049, 5648840, 5649630,
    5650354, 5651121, 5651876, 5652637, 5653366, 5654092, 5654864, 5655590, 5656380, 5657126,
    5657901, 5658633, 5659378, 5660132, 5660914, 5661638, 5662409, 5663169, 5663940, 5664715,
    5665477, 5666232, 5667000, 5667760, 5668549, 5669291, 5670045, 5670802, 5671571, 5672329,
    5673113, 5673880, 5674641, 5675375, 5676161, 5676927, 5677706, 5678474, 5679201, 5679951,
    5680746, 5681534, 5682316, 5683067, 5683843]

def LB_93 : List ℕ := [
    5628777, 5629871, 5630948, 5632025, 5633087, 5634166, 5635253, 5636306, 5637363, 5638460,
    5639531, 5640591, 5641695, 5642764, 5643881, 5644931, 5645987, 5647049, 5648162, 5649290,
    5650333, 5651413, 5652480, 5653526, 5654598, 5655624, 5656725, 5657799, 5658856, 5659919,
    5660992, 5662037, 5663117, 5664198, 5665314, 5666371, 5667455, 5668564, 5669613, 5670673,
    5671756, 5672849, 5673939, 5674996, 5676087, 5677183, 5678270, 5679335, 5680411, 5681518,
    5682618, 5683690, 5684788]

def LA_94 : List ℕ := [
    5684601, 5685368, 5686115, 5686904, 5687653, 5688432, 5689192, 5689934, 5690688, 5691440,
    5692198, 5692949, 5693727, 5694450, 5695181, 5695938, 5696707, 5697465, 5698246, 5699018,
    5699762, 5700527, 5701295, 5702033, 5702787, 5703541, 5704293, 5705028, 5705783, 5706540,
    5707321, 5708114, 5708884, 5709692, 5710444, 5711231, 5711998, 5712725, 5713494, 5714224,
    5715026, 5715788, 5716529, 5717300, 5718052, 5718783, 5719556, 5720334, 5721077, 5721838,
    5722566, 5723335, 5724074, 5724857, 5725646, 5726411, 5727178, 5727948, 5728720, 5729465,
    5730225, 5730965, 5731734, 5732505, 5733314, 5734072, 5734837, 5735588, 5736343, 5737113,
    5737891, 5738680, 5739445, 5740262, 5741078]

def LB_94 : List ℕ := [
    5685846, 5686949, 5688001, 5689104, 5690142, 5691208, 5692289, 5693356, 5694416, 5695444,
    5696521, 5697616, 5698734, 5699779, 5700861, 5701929, 5702989, 5704055, 5705101, 5706169,
    5707264, 5708381, 5709498, 5710573, 5711666, 5712724, 5713787, 5714888, 5715971, 5717050,
    5718108, 5719149, 5720260, 5721316, 5722362, 5723442, 5724494, 5725619, 5726714, 5727797,
    5728880, 5729946, 5730995, 5732087, 5733210, 5734294, 5735363, 5736439, 5737533, 5738633,
    5739726, 5740894]

def LA_95 : List ℕ := [
    5741833, 5742593, 5743339, 5744108, 5744866, 5745606, 5746405, 5747163, 5747889, 5748658,
    5749434, 5750175, 5750947, 5751712, 5752474, 5753236, 5754018, 5754777, 5755580, 5756345,
    5757112, 5757876, 5758645, 5759414, 5760216, 5760974, 5761745, 5762499, 5763266, 5764053,
    5764809, 5765568, 5766322, 5767087, 5767885, 5768658, 5769430, 5770195, 5770965, 5771746,
    5772539, 5773314, 5774071, 5774849, 5775611, 5776385, 5777140, 5777921, 5778686, 5779451,
    5780222, 5780956, 5781725, 5782511, 5783246, 5784008, 5784760, 5785521, 5786314, 5787060,
    5787837, 5788619, 5789394, 5790155, 5790937, 5791724, 5792468, 5793241, 5793969, 5794737,
    5795503, 5796288, 5797036, 5797822]

def LB_95 : List ℕ := [
    5741969, 5743048, 5744112, 5745174, 5746269, 5747342, 5748395, 5749495, 5750544, 5751642,
    5752728, 5753806, 5754913, 5756003, 5757092, 5758186, 5759273, 5760378, 5761455, 5762536,
    5763629, 5764702, 5765791, 5766866, 5767969, 5769083, 5770167, 5771249, 5772367, 5773452,
    5774547, 5775624, 5776713, 5777801, 5778881, 5779956, 5781027, 5782106, 5783186, 5784259,
    5785334, 5786438, 5787526, 5788608, 5789710, 5790800, 5791887, 5792961, 5794019, 5795107,
    5796196, 5797287, 5798347]

def LA_96 : List ℕ := [
    5798549, 5799355, 5800117, 5800876, 5801635, 5802440, 5803194, 5803958, 5804689, 5805446,
    5806212, 5806973, 5807762, 5808524, 5809297, 5810079, 5810872, 5811656, 5812423, 5813192,
    5813983, 5814773, 5815520, 5816298, 5817076, 5817850, 5818646, 5819433, 5820210, 5820970,
    5821744, 5822519, 5823305, 5824082, 5824830, 5825587, 5826357, 5827149, 5827914, 5828677,
    5829479, 5830255, 5831033, 5831782, 5832543, 5833333, 5834117, 5834904, 5835660, 5836429,
    5837203, 5837976, 5838761, 5839503, 5840291, 5841054, 5841845, 5842634, 5843406, 5844162,
    5844925, 5845731, 5846511, 5847258, 5847998, 5848773, 5849568, 5850371, 5851121, 5851868,
    5852629, 5853409, 5854173, 5854932]

def LB_96 : List ℕ := [
    5799460, 5800525, 5801604, 5802723, 5803795, 5804839, 5805925, 5807005, 5808113, 5809197,
    5810286, 5811414, 5812512, 5813603, 5814719, 5815803, 5816885, 5817994, 5819108, 5820211,
    5821302, 5822394, 5823485, 5824585, 5825649, 5826732, 5827828, 5828910, 5830057, 5831145,
    5832222, 5833311, 5834413, 5835507, 5836598, 5837674, 5838797, 5839873, 5840969, 5842079,
    5843171, 5844248, 5845360, 5846462, 5847507, 5848599, 5849702, 5850798, 5851878, 5852971,
    5854040, 5855132]

def LA_97 : List ℕ := [
    5855707, 5856486, 5857273, 5858019, 5858802, 5859587, 5860367, 5861131, 5861861, 5862672,
    5863430, 5864207, 5865017, 5865789, 5866595, 5867379, 5868152, 5868934, 5869690, 5870485,
    5871264, 5872034, 5872825, 5873609, 5874382, 5875156, 5875930, 5876683, 5877453, 5878229,
    5879030, 5879812, 5880594, 5881388, 5882144, 5882902, 5883715, 5884490, 5885274, 5886068,
    5886847, 5887628, 5888421, 5889211, 5889983, 5890746, 5891533, 5892283, 5893080, 5893852,
    5894626, 5895413, 5896169, 5896964, 5897750, 5898517, 5899323, 5900065, 5900850, 5901635,
    5902394, 5903209, 5903975, 5904747, 5905512, 5906277, 5907040, 5907815, 5908602, 5909378,
    5910175, 5910954, 5911713]

def LB_97 : List ℕ := [
    5856225, 5857338, 5858404, 5859518, 5860614, 5861671, 5862794, 5863874, 5865006, 5866113,
    5867220, 5868332, 5869424, 5870519, 5871617, 5872730, 5873829, 5874937, 5876019, 5877087,
    5878190, 5879323, 5880434, 5881543, 5882610, 5883737, 5884829, 5885954, 5887071, 5888169,
    5889285, 5890371, 5891489, 5892561, 5893652, 5894765, 5895844, 5896963, 5898062, 5899175,
    5900267, 5901364, 5902452, 5903589, 5904672, 5905752, 5906822, 5907934, 5909024, 5910148,
    5911274, 5912318]

def LA_98 : List ℕ := [
    5912478, 5913254, 5914025, 5914798, 5915609, 5916386, 5917161, 5917953, 5918724, 5919490,
    5920268, 5921047, 5921802, 5922584, 5923343, 5924115, 5924909, 5925686, 5926471, 5927254,
    5928037, 5928825, 5929634, 5930374, 5931137, 5931905, 5932696, 5933464, 5934246, 5935016,
    5935771, 5936556, 5937310, 5938074, 5938870, 5939671, 5940458, 5941242, 5941990, 5942800,
    5943576, 5944371, 5945162, 5945917, 5946719, 5947497, 5948300, 5949092, 5949850, 5950617,
    5951418, 5952202, 5952954, 5953718, 5954528, 5955295, 5956046, 5956818, 5957615, 5958383,
    5959162, 5959890, 5960687, 5961488, 5962279, 5963056, 5963856, 5964635, 5965389, 5966170,
    5966970, 5967751, 5968491]

def LB_98 : List ℕ := [
    5913414, 5914510, 5915640, 5916723, 5917840, 5918946, 5920044, 5921136, 5922219, 5923299,
    5924394, 5925503, 5926604, 5927717, 5928837, 5929946, 5931012, 5932094, 5933210, 5934307,
    5935396, 5936489, 5937546, 5938657, 5939786, 5940891, 5941975, 5943102, 5944220, 5945327,
    5946422, 5947536, 5948665, 5949760, 5950865, 5951970, 5953044, 5954156, 5955261, 5956319,
    5957425, 5958533, 5959607, 5960703, 5961846, 5962937, 5964058, 5965138, 5966245, 5967368,
    5968439]

def LA_99 : List ℕ := [
    5969266, 5970032, 5970819, 5971628, 5972401, 5973180, 5973985, 5974740, 5975526, 5976310,
    5977099, 5977890, 5978697, 5979471, 5980279, 5981064, 5981876, 5982664, 5983435, 5984208,
    5984994, 5985816, 5986574, 5987373, 5988157, 5988919, 5989702, 5990525, 5991329, 5992123,
    5992916, 5993714, 5994500, 5995274, 5996031, 5996809, 5997561, 5998363, 5999156, 5999939,
    6000715, 6001461, 6002292, 6003075, 6003847, 6004631, 6005413, 6006194, 6006983, 6007754,
    6008540, 6009315, 6010113, 6010888, 6011679, 6012468, 6013273, 6014027, 6014787, 6015559,
    6016329, 6017129, 6017885, 6018672, 6019465, 6020235, 6021008, 6021780, 6022577, 6023386,
    6024193, 6024972, 6025761]

def LB_99 : List ℕ := [
    5969519, 5970613, 5971756, 5972836, 5973980, 5975062, 5976166, 5977296, 5978433, 5979525,
    5980668, 5981799, 5982895, 5983971, 5985110, 5986258, 5987334, 5988436, 5989535, 5990682,
    5991828, 5992941, 5994082, 5995151, 5996234, 5997345, 5998452, 5999566, 6000658, 6001767,
    6002876, 6003983, 6005094, 6006196, 6007298, 6008417, 6009506, 6010611, 6011739, 6012865,
    6013957, 6015023, 6016132, 6017252, 6018321, 6019443, 6020527, 6021640, 6022755, 6023892,
    6025009]

def LA_100 : List ℕ := [
    6026527, 6027305, 6028101, 6028862, 6029656, 6030434, 6031228, 6032019, 6032798, 6033576,
    6034340, 6035153, 6035938, 6036713, 6037483, 6038274, 6039065, 6039867, 6040653, 6041435,
    6042228, 6043025, 6043821, 6044610, 6045412, 6046164, 6046961, 6047719, 6048496, 6049273,
    6050059, 6050832, 6051626, 6052426, 6053227, 6053999, 6054776, 6055591, 6056387, 6057147,
    6057930, 6058724, 6059512, 6060276, 6061073, 6061856, 6062610, 6063387, 6064189, 6064991,
    6065749, 6066551, 6067325, 6068130, 6068891, 6069663, 6070453, 6071237, 6072024, 6072835,
    6073604, 6074411, 6075193, 6076003, 6076786, 6077588, 6078367, 6079136, 6079930, 6080711,
    6081514, 6082307]

def LB_100 : List ℕ := [
    6026112, 6027200, 6028320, 6029413, 6030517, 6031657, 6032757, 6033853, 6034972, 6036082,
    6037175, 6038291, 6039406, 6040536, 6041645, 6042751, 6043896, 6045020, 6046099, 6047203,
    6048279, 6049419, 6050511, 6051618, 6052739, 6053872, 6054962, 6056097, 6057197, 6058316,
    6059417, 6060515, 6061643, 6062719, 6063824, 6064956, 6066038, 6067161, 6068278, 6069371,
    6070477, 6071595, 6072716, 6073833, 6074945, 6076078, 6077197, 6078311, 6079407, 6080535,
    6081640, 6082761]

def LA_101 : List ℕ := [
    6083063, 6083847, 6084636, 6085435, 6086194, 6086987, 6087780, 6088542, 6089324, 6090147,
    6090944, 6091730, 6092492, 6093275, 6094076, 6094860, 6095639, 6096437, 6097214, 6098031,
    6098832, 6099595, 6100354, 6101134, 6101913, 6102722, 6103550, 6104350, 6105131, 6105885,
    6106685, 6107462, 6108250, 6109042, 6109817, 6110629, 6111424, 6112203, 6112998, 6113780,
    6114592, 6115373, 6116188, 6116959, 6117764, 6118572, 6119365, 6120138, 6120925, 6121690,
    6122509, 6123315, 6124077, 6124876, 6125647, 6126428, 6127234, 6127994, 6128809, 6129550,
    6130334, 6131163, 6131965, 6132759, 6133535, 6134324, 6135116, 6135924, 6136672, 6137439,
    6138237, 6139052]

def LB_101 : List ℕ := [
    6083847, 6084963, 6086062, 6087187, 6088280, 6089379, 6090535, 6091652, 6092742, 6093860,
    6094956, 6096059, 6097192, 6098346, 6099439, 6100535, 6101616, 6102762, 6103909, 6105028,
    6106107, 6107233, 6108336, 6109455, 6110578, 6111700, 6112817, 6113928, 6115084, 6116195,
    6117303, 6118443, 6119567, 6120670, 6121750, 6122890, 6124008, 6125128, 6126225, 6127349,
    6128461, 6129541, 6130674, 6131813, 6132933, 6134036, 6135151, 6136264, 6137336, 6138482]

def LA_102 : List ℕ := [
    6139857, 6140636, 6141448, 6142263, 6143025, 6143804, 6144591, 6145368, 6146194, 6146986,
    6147781, 6148568, 6149355, 6150186, 6150972, 6151771, 6152579, 6153378, 6154209, 6154983,
    6155771, 6156568, 6157346, 6158155, 6158951, 6159768, 6160535, 6161329, 6162110, 6162934,
    6163706, 6164535, 6165325, 6166098, 6166886, 6167702, 6168470, 6169247, 6170035, 6170828,
    6171618, 6172401, 6173206, 6173988, 6174791, 6175599, 6176420, 6177204, 6178019, 6178819,
    6179617, 6180403, 6181207, 6182003, 6182791, 6183572, 6184367, 6185172, 6185973, 6186746,
    6187558, 6188355, 6189138, 6189927, 6190713, 6191493, 6192270, 6193035, 6193845, 6194611,
    6195388]

def LB_102 : List ℕ := [
    6139637, 6140733, 6141890, 6142987, 6144086, 6145189, 6146336, 6147451, 6148590, 6149699,
    6150856, 6151991, 6153125, 6154287, 6155377, 6156508, 6157619, 6158746, 6159891, 6161006,
    6162108, 6163240, 6164396, 6165520, 6166615, 6167756, 6168839, 6169959, 6171073, 6172172,
    6173313, 6174426, 6175571, 6176720, 6177863, 6178976, 6180117, 6181239, 6182351, 6183467,
    6184596, 6185734, 6186831, 6187976, 6189096, 6190216, 6191293, 6192416, 6193513, 6194618,
    6195709]

def LA_103 : List ℕ := [
    6196179, 6196969, 6197784, 6198598, 6199408, 6200183, 6200960, 6201762, 6202586, 6203376,
    6204176, 6204951, 6205753, 6206544, 6207319, 6208123, 6208973, 6209771, 6210589, 6211383,
    6212190, 6212980, 6213803, 6214603, 6215403, 6216199, 6217019, 6217819, 6218606, 6219417,
    6220241, 6221033, 6221817, 6222644, 6223450, 6224269, 6225059, 6225868, 6226658, 6227452,
    6228235, 6229042, 6229837, 6230626, 6231414, 6232205, 6232996, 6233749, 6234554, 6235383,
    6236183, 6236978, 6237785, 6238594, 6239390, 6240203, 6241011, 6241786, 6242553, 6243349,
    6244137, 6244939, 6245730, 6246529, 6247333, 6248128, 6248904, 6249694, 6250487, 6251289,
    6252102]

def LB_103 : List ℕ := [
    6196835, 6197982, 6199143, 6200247, 6201357, 6202517, 6203611, 6204739, 6205874, 6207004,
    6208103, 6209287, 6210435, 6211560, 6212686, 6213841, 6214971, 6216111, 6217255, 6218391,
    6219513, 6220662, 6221780, 6222931, 6224083, 6225216, 6226357, 6227463, 6228569, 6229709,
    6230832, 6231946, 6233070, 6234170, 6235310, 6236433, 6237566, 6238728, 6239861, 6241004,
    6242096, 6243197, 6244311, 6245452, 6246571, 6247705, 6248809, 6249926, 6251048, 6252198]

def LA_104 : List ℕ := [
    6252903, 6253712, 6254488, 6255262, 6256074, 6256889, 6257703, 6258478, 6259297, 6260109,
    6260898, 6261683, 6262521, 6263326, 6264118, 6264903, 6265700, 6266485, 6267268, 6268059,
    6268846, 6269653, 6270465, 6271268, 6272104, 6272920, 6273737, 6274523, 6275319, 6276117,
    6276920, 6277724, 6278534, 6279315, 6280145, 6280933, 6281713, 6282518, 6283307, 6284134,
    6284967, 6285732, 6286509, 6287318, 6288124, 6288900, 6289705, 6290524, 6291335, 6292163,
    6292943, 6293746, 6294558, 6295356, 6296141, 6296957, 6297770, 6298549, 6299378, 6300184,
    6300979, 6301796, 6302603, 6303402, 6304205, 6305015, 6305842, 6306626, 6307440, 6308295,
    6309098]

def LB_104 : List ℕ := [
    6253343, 6254455, 6255571, 6256720, 6257853, 6259001, 6260132, 6261248, 6262406, 6263530,
    6264674, 6265789, 6266896, 6267997, 6269107, 6270282, 6271417, 6272579, 6273738, 6274834,
    6275997, 6277119, 6278263, 6279379, 6280540, 6281629, 6282774, 6283918, 6285064, 6286171,
    6287297, 6288436, 6289526, 6290682, 6291872, 6292981, 6294105, 6295264, 6296392, 6297516,
    6298645, 6299809, 6300938, 6302082, 6303205, 6304348, 6305516, 6306638, 6307805, 6308977]

def LA_105 : List ℕ := [
    6309886, 6310681, 6311474, 6312269, 6313013, 6313822, 6314628, 6315406, 6316181, 6316986,
    6317799, 6318592, 6319403, 6320173, 6320950, 6321734, 6322504, 6323293, 6324081, 6324891,
    6325685, 6326533, 6327364, 6328173, 6328968, 6329767, 6330572, 6331338, 6332126, 6332952,
    6333720, 6334505, 6335314, 6336138, 6336961, 6337769, 6338540, 6339383, 6340189, 6340980,
    6341762, 6342569, 6343400, 6344217, 6345001, 6345788, 6346587, 6347376, 6348198, 6349009,
    6349788, 6350615, 6351418, 6352246, 6353052, 6353857, 6354635, 6355447, 6356286, 6357107,
    6357895, 6358694, 6359495, 6360312, 6361096, 6361920, 6362720, 6363497, 6364305, 6365109,
    6365918]

def LB_105 : List ℕ := [
    6310087, 6311196, 6312336, 6313414, 6314562, 6315657, 6316774, 6317930, 6319062, 6320161,
    6321266, 6322359, 6323469, 6324607, 6325741, 6326919, 6328077, 6329214, 6330351, 6331444,
    6332592, 6333687, 6334798, 6335958, 6337132, 6338259, 6339406, 6340518, 6341655, 6342797,
    6343962, 6345084, 6346195, 6347319, 6348479, 6349589, 6350755, 6351912, 6353051, 6354179,
    6355296, 6356477, 6357626, 6358746, 6359898, 6361017, 6362169, 6363264, 6364422, 6365543]

def LA_106 : List ℕ := [
    6366722, 6367551, 6368325, 6369147, 6369959, 6370743, 6371528, 6372291, 6373076, 6373894,
    6374738, 6375545, 6376352, 6377181, 6377998, 6378793, 6379599, 6380379, 6381153, 6381933,
    6382735, 6383552, 6384364, 6385175, 6385977, 6386742, 6387544, 6388335, 6389130, 6389964,
    6390752, 6391560, 6392351, 6393167, 6393970, 6394781, 6395600, 6396420, 6397217, 6398033,
    6398811, 6399641, 6400459, 6401294, 6402109, 6402929, 6403718, 6404527, 6405364, 6406142,
    6406910, 6407702, 6408522, 6409347, 6410137, 6410968, 6411778, 6412579, 6413404, 6414191,
    6415022, 6415876, 6416682, 6417495, 6418314, 6419106, 6419916, 6420735, 6421569, 6422410]

def LB_106 : List ℕ := [
    6366696, 6367863, 6368985, 6370125, 6371234, 6372321, 6373435, 6374629, 6375783, 6376930,
    6378078, 6379224, 6380336, 6381423, 6382548, 6383705, 6384862, 6385986, 6387087, 6388204,
    6389334, 6390475, 6391630, 6392743, 6393893, 6395042, 6396209, 6397347, 6398480, 6399627,
    6400786, 6401961, 6403093, 6404222, 6405408, 6406509, 6407611, 6408788, 6409912, 6411053,
    6412225, 6413370, 6414489, 6415694, 6416851, 6417972, 6419124, 6420274, 6421436, 6422614]

def LA_107 : List ℕ := [
    6423204, 6423994, 6424792, 6425571, 6426362, 6427218, 6428015, 6428823, 6429661, 6430465,
    6431268, 6432071, 6432880, 6433670, 6434432, 6435268, 6436047, 6436864, 6437668, 6438479,
    6439278, 6440068, 6440898, 6441726, 6442526, 6443315, 6444107, 6444924, 6445755, 6446576,
    6447370, 6448187, 6448994, 6449818, 6450605, 6451439, 6452281, 6453106, 6453917, 6454703,
    6455498, 6456349, 6457146, 6457943, 6458765, 6459574, 6460381, 6461184, 6461985, 6462776,
    6463589, 6464424, 6465236, 6466048, 6466839, 6467638, 6468469, 6469302, 6470109, 6470956,
    6471763, 6472599, 6473453, 6474249, 6475062, 6475855, 6476644, 6477445, 6478256, 6479075]

def LB_107 : List ℕ := [
    6423740, 6424869, 6425952, 6427156, 6428292, 6429454, 6430603, 6431741, 6432876, 6433964,
    6435117, 6436237, 6437389, 6438530, 6439656, 6440813, 6441971, 6443084, 6444228, 6445392,
    6446536, 6447682, 6448832, 6449999, 6451120, 6452312, 6453469, 6454597, 6455737, 6456913,
    6458027, 6459188, 6460336, 6461448, 6462601, 6463727, 6464910, 6466050, 6467179, 6468326,
    6469499, 6470664, 6471829, 6472997, 6474166, 6475313, 6476447, 6477563, 6478730]

def LA_108 : List ℕ := [
    6479878, 6480682, 6481489, 6482316, 6483125, 6483947, 6484773, 6485560, 6486362, 6487185,
    6487986, 6488769, 6489572, 6490400, 6491219, 6492053, 6492853, 6493666, 6494472, 6495274,
    6496116, 6496876, 6497670, 6498474, 6499283, 6500103, 6500899, 6501702, 6502531, 6503327,
    6504149, 6504966, 6505785, 6506556, 6507360, 6508158, 6508996, 6509830, 6510619, 6511450,
    6512229, 6513044, 6513826, 6514647, 6515464, 6516291, 6517107, 6517941, 6518709, 6519520,
    6520341, 6521151, 6521950, 6522771, 6523572, 6524373, 6525215, 6526030, 6526847, 6527667,
    6528510, 6529315, 6530127, 6530942, 6531729, 6532538, 6533358, 6534207, 6535018]

def LB_108 : List ℕ := [
    6479856, 6480985, 6482146, 6483303, 6484467, 6485589, 6486729, 6487879, 6489006, 6490147,
    6491311, 6492482, 6493628, 6494778, 6495931, 6497032, 6498158, 6499300, 6500465, 6501564,
    6502753, 6503894, 6505043, 6506168, 6507295, 6508431, 6509620, 6510752, 6511900, 6513035,
    6514163, 6515303, 6516476, 6517652, 6518758, 6519910, 6521066, 6522195, 6523339, 6524469,
    6525645, 6526811, 6527951, 6529138, 6530295, 6531427, 6532566, 6533750, 6534902]

def LA_109 : List ℕ := [
    6535856, 6536682, 6537493, 6538342, 6539148, 6539947, 6540750, 6541574, 6542370, 6543159,
    6543941, 6544754, 6545576, 6546356, 6547182, 6547983, 6548776, 6549581, 6550399, 6551213,
    6552029, 6552906, 6553754, 6554544, 6555363, 6556163, 6556972, 6557792, 6558596, 6559387,
    6560219, 6561034, 6561849, 6562654, 6563483, 6564301, 6565106, 6565948, 6566739, 6567548,
    6568372, 6569204, 6570009, 6570834, 6571623, 6572460, 6573276, 6574095, 6574920, 6575771,
    6576612, 6577415, 6578187, 6578999, 6579806, 6580647, 6581469, 6582255, 6583091, 6583908,
    6584754, 6585566, 6586383, 6587166, 6587981, 6588825, 6589656, 6590458, 6591255]

def LB_109 : List ℕ := [
    6536082, 6537245, 6538420, 6539549, 6540694, 6541842, 6542978, 6544084, 6545219, 6546354,
    6547495, 6548638, 6549772, 6550926, 6552080, 6553330, 6554468, 6555613, 6556745, 6557900,
    6559022, 6560192, 6561335, 6562499, 6563649, 6564830, 6565971, 6567099, 6568271, 6569434,
    6570582, 6571724, 6572894, 6574045, 6575218, 6576403, 6577560, 6578670, 6579815, 6581003,
    6582136, 6583304, 6584471, 6585625, 6586762, 6587914, 6589089, 6590252, 6591377]

def LA_110 : List ℕ := [
    6592063, 6592865, 6593697, 6594527, 6595304, 6596104, 6596946, 6597761, 6598587, 6599436,
    6600240, 6601074, 6601878, 6602676, 6603481, 6604332, 6605166, 6605977, 6606803, 6607636,
    6608447, 6609246, 6610054, 6610912, 6611718, 6612536, 6613358, 6614201, 6615000, 6615818,
    6616607, 6617412, 6618237, 6619048, 6619872, 6620688, 6621540, 6622377, 6623229, 6624059,
    6624840, 6625715, 6626519, 6627352, 6628200, 6629004, 6629850, 6630672, 6631497, 6632312,
    6633134, 6633976, 6634812, 6635630, 6636446, 6637261, 6638061, 6638894, 6639697, 6640516,
    6641349, 6642169, 6642961, 6643775, 6644614, 6645458, 6646271, 6647109, 6647931]

def LB_110 : List ℕ := [
    6592535, 6593684, 6594841, 6595948, 6597128, 6598284, 6599477, 6600627, 6601777, 6602914,
    6604088, 6605273, 6606433, 6607601, 6608764, 6609883, 6611064, 6612209, 6613378, 6614571,
    6615695, 6616834, 6617995, 6619120, 6620288, 6621469, 6622662, 6623851, 6624997, 6626186,
    6627350, 6628512, 6629703, 6630852, 6632036, 6633194, 6634386, 6635542, 6636702, 6637846,
    6639000, 6640153, 6641319, 6642481, 6643606, 6644789, 6645960, 6647135, 6648315]

def LA_111 : List ℕ := [
    6648749, 6649585, 6650413, 6651250, 6652034, 6652847, 6653657, 6654474, 6655326, 6656168,
    6656971, 6657763, 6658608, 6659451, 6660291, 6661076, 6661920, 6662771, 6663594, 6664365,
    6665209, 6666041, 6666856, 6667668, 6668474, 6669277, 6670089, 6670917, 6671735, 6672548,
    6673348, 6674162, 6675010, 6675846, 6676643, 6677490, 6678288, 6679144, 6679972, 6680808,
    6681628, 6682448, 6683278, 6684100, 6684920, 6685776, 6686569, 6687381, 6688202, 6689017,
    6689848, 6690658, 6691511, 6692324, 6693147, 6693978, 6694792, 6695634, 6696447, 6697307,
    6698105, 6698917, 6699721, 6700558, 6701383, 6702193, 6702981, 6703824, 6704641]

def LB_111 : List ℕ := [
    6649464, 6650631, 6651788, 6652943, 6654107, 6655266, 6656455, 6657580, 6658758, 6659944,
    6661082, 6662291, 6663462, 6664586, 6665767, 6666919, 6668060, 6669202, 6670364, 6671520,
    6672667, 6673800, 6674992, 6676155, 6677323, 6678481, 6679667, 6680854, 6682011, 6683170,
    6684341, 6685521, 6686665, 6687810, 6688977, 6690149, 6691314, 6692494, 6693654, 6694808,
    6695989, 6697170, 6698325, 6699457, 6700638, 6701803, 6702914, 6704097]

def LA_112 : List ℕ := [
    6705491, 6706327, 6707116, 6707928, 6708757, 6709581, 6710417, 6711250, 6712111, 6712969,
    6713771, 6714567, 6715385, 6716232, 6717057, 6717861, 6718676, 6719488, 6720316, 6721099,
    6721942, 6722802, 6723645, 6724495, 6725339, 6726168, 6726987, 6727778, 6728598, 6729441,
    6730290, 6731110, 6731943, 6732756, 6733576, 6734400, 6735229, 6736055, 6736892, 6737718,
    6738572, 6739376, 6740178, 6741010, 6741819, 6742653, 6743536, 6744350, 6745191, 6746002,
    6746832, 6747632, 6748458, 6749277, 6750142, 6750978, 6751780, 6752588, 6753371, 6754210,
    6755062, 6755867, 6756725, 6757566, 6758418, 6759230, 6760084, 6760882]

def LB_112 : List ℕ := [
    6705290, 6706446, 6707585, 6708744, 6709923, 6711089, 6712309, 6713468, 6714614, 6715801,
    6716965, 6718120, 6719245, 6720423, 6721556, 6722762, 6723959, 6725172, 6726336, 6727464,
    6728626, 6729826, 6730989, 6732169, 6733303, 6734484, 6735646, 6736832, 6738010, 6739177,
    6740317, 6741480, 6742654, 6743873, 6745052, 6746187, 6747361, 6748516, 6749697, 6750904,
    6752028, 6753170, 6754322, 6755502, 6756702, 6757879, 6759077, 6760254, 6761403]

def LA_113 : List ℕ := [
    6761725, 6762558, 6763368, 6764175, 6765009, 6765843, 6766682, 6767505, 6768307, 6769161,
    6769962, 6770818, 6771665, 6772497, 6773327, 6774158, 6774980, 6775788, 6776587, 6777421,
    6778258, 6779086, 6779879, 6780714, 6781549, 6782369, 6783198, 6784016, 6784827, 6785622,
    6786451, 6787281, 6788108, 6788941, 6789784, 6790602, 6791425, 6792240, 6793040, 6793875,
    6794708, 6795522, 6796342, 6797167, 6797967, 6798816, 6799616, 6800465, 6801264, 6802117,
    6802977, 6803814, 6804634, 6805473, 6806274, 6807099, 6807942, 6808771, 6809625, 6810458,
    6811299, 6812097, 6812960, 6813783, 6814594, 6815456, 6816284, 6817111]

def LB_113 : List ℕ := [
    6762589, 6763738, 6764904, 6766090, 6767259, 6768393, 6769572, 6770767, 6771973, 6773137,
    6774306, 6775464, 6776594, 6777787, 6778963, 6780104, 6781278, 6782439, 6783609, 6784760,
    6785882, 6787073, 6788243, 6789419, 6790592, 6791745, 6792882, 6794067, 6795220, 6796396,
    6797554, 6798723, 6799865, 6801036, 6802226, 6803426, 6804600, 6805771, 6806938, 6808109,
    6809297, 6810487, 6811654, 6812841, 6813986, 6815196, 6816362, 6817535]

def LA_114 : List ℕ := [
    6817928, 6818770, 6819609, 6820454, 6821286, 6822112, 6822922, 6823752, 6824572, 6825384,
    6826237, 6827070, 6827897, 6828739, 6829560, 6830397, 6831213, 6832052, 6832883, 6833734,
    6834597, 6835419, 6836260, 6837093, 6837940, 6838827, 6839616, 6840437, 6841293, 6842135,
    6842967, 6843805, 6844667, 6845517, 6846377, 6847211, 6848032, 6848876, 6849689, 6850491,
    6851319, 6852182, 6853014, 6853850, 6854706, 6855550, 6856378, 6857188, 6858024, 6858817,
    6859642, 6860468, 6861281, 6862095, 6862950, 6863798, 6864594, 6865449, 6866301, 6867133,
    6867952, 6868768, 6869596, 6870448, 6871292, 6872094, 6872910, 6873756]

def LB_114 : List ℕ := [
    6818704, 6819896, 6821081, 6822244, 6823422, 6824571, 6825749, 6826913, 6828100, 6829285,
    6830439, 6831625, 6832791, 6833999, 6835194, 6836375, 6837550, 6838794, 6839934, 6841115,
    6842304, 6843503, 6844710, 6845907, 6847108, 6848255, 6849430, 6850578, 6851770, 6852962,
    6854136, 6855366, 6856516, 6857688, 6858828, 6859993, 6861151, 6862307, 6863511, 6864666,
    6865865, 6867056, 6868220, 6869378, 6870563, 6871754, 6872894, 6874085]

def LA_115 : List ℕ := [
    6874588, 6875428, 6876268, 6877106, 6877928, 6878768, 6879631, 6880416, 6881258, 6882068,
    6882906, 6883711, 6884536, 6885341, 6886137, 6886994, 6887838, 6888686, 6889540, 6890365,
    6891230, 6892033, 6892880, 6893700, 6894566, 6895397, 6896256, 6897114, 6897960, 6898813,
    6899651, 6900491, 6901341, 6902189, 6902997, 6903838, 6904674, 6905529, 6906371, 6907197,
    6908046, 6908848, 6909673, 6910530, 6911334, 6912127, 6913020, 6913878, 6914699, 6915519,
    6916355, 6917164, 6918014, 6918852, 6919725, 6920570, 6921428, 6922236, 6923061, 6923884,
    6924705, 6925540, 6926429, 6927284, 6928127, 6928945, 6929741]

def LB_115 : List ℕ := [
    6875267, 6876452, 6877631, 6878813, 6879995, 6881149, 6882332, 6883478, 6884626, 6885756,
    6886950, 6888148, 6889345, 6890523, 6891717, 6892901, 6894079, 6895267, 6896492, 6897696,
    6898887, 6900077, 6901267, 6902468, 6903630, 6904800, 6906027, 6907186, 6908379, 6909533,
    6910719, 6911833, 6913076, 6914263, 6915434, 6916615, 6917782, 6918955, 6920190, 6921390,
    6922536, 6923717, 6924865, 6926097, 6927305, 6928485, 6929631]

def LA_116 : List ℕ := [
    6930564, 6931394, 6932224, 6933078, 6933944, 6934794, 6935619, 6936470, 6937290, 6938119,
    6938936, 6939771, 6940620, 6941460, 6942298, 6943143, 6943985, 6944815, 6945668, 6946504,
    6947351, 6948203, 6949037, 6949908, 6950752, 6951576, 6952425, 6953265, 6954110, 6954955,
    6955771, 6956602, 6957429, 6958255, 6959085, 6959934, 6960797, 6961646, 6962491, 6963329,
    6964170, 6964945, 6965823, 6966644, 6967472, 6968309, 6969153, 6969981, 6970803, 6971637,
    6972477, 6973307, 6974123, 6974963, 6975785, 6976607, 6977458, 6978276, 6979115, 6979948,
    6980799, 6981679, 6982527, 6983371, 6984229, 6985064, 6985882]

def LB_116 : List ℕ := [
    6930796, 6931970, 6933170, 6934379, 6935560, 6936770, 6937918, 6939088, 6940251, 6941462,
    6942657, 6943842, 6945030, 6946231, 6947416, 6948611, 6949818, 6951016, 6952203, 6953377,
    6954586, 6955754, 6956905, 6958096, 6959271, 6960475, 6961686, 6962869, 6964067, 6965200,
    6966393, 6967575, 6968763, 6969929, 6971109, 6972287, 6973479, 6974638, 6975794, 6976966,
    6978158, 6979310, 6980543, 6981744, 6982954, 6984155, 6985319, 6986517]

def LA_117 : List ℕ := [
    6986732, 6987587, 6988408, 6989307, 6990117, 6990962, 6991828, 6992683, 6993511, 6994389,
    6995233, 6996083, 6996930, 6997783, 6998612, 6999417, 7000253, 7001075, 7001931, 7002777,
    7003587, 7004421, 7005265, 7006077, 7006933, 7007798, 7008654, 7009487, 7010351, 7011163,
    7012026, 7012877, 7013708, 7014555, 7015403, 7016242, 7017104, 7017980, 7018805, 7019674,
    7020468, 7021303, 7022154, 7022998, 7023855, 7024719, 7025554, 7026408, 7027271, 7028118,
    7028925, 7029747, 7030583, 7031448, 7032271, 7033143, 7033959, 7034810, 7035689, 7036555,
    7037346, 7038197, 7039057, 7039909, 7040754, 7041590, 7042445]

def LB_117 : List ℕ := [
    6987707, 6988919, 6990103, 6991310, 6992529, 6993732, 6994908, 6996133, 6997333, 6998502,
    6999666, 7000846, 7002043, 7003215, 7004389, 7005565, 7006751, 7007966, 7009160, 7010373,
    7011541, 7012737, 7013940, 7015132, 7016326, 7017554, 7018755, 7019950, 7021106, 7022300,
    7023508, 7024718, 7025906, 7027131, 7028311, 7029473, 7030652, 7031858, 7033045, 7034229,
    7035467, 7036650, 7037815, 7039025, 7040234, 7041435, 7042627]

def LA_118 : List ℕ := [
    7043307, 7044144, 7045019, 7045846, 7046699, 7047534, 7048375, 7049229, 7050107, 7050948,
    7051801, 7052643, 7053489, 7054325, 7055152, 7056008, 7056902, 7057737, 7058582, 7059419,
    7060231, 7061086, 7061925, 7062763, 7063589, 7064445, 7065291, 7066134, 7066997, 7067855,
    7068721, 7069571, 7070429, 7071285, 7072132, 7072991, 7073858, 7074712, 7075542, 7076371,
    7077213, 7078077, 7078891, 7079760, 7080590, 7081440, 7082300, 7083148, 7083994, 7084837,
    7085657, 7086477, 7087308, 7088159, 7089010, 7089873, 7090744, 7091559, 7092393, 7093256,
    7094102, 7094971, 7095791, 7096659, 7097531, 7098374, 7099209]

def LB_118 : List ℕ := [
    7043835, 7045041, 7046236, 7047437, 7048618, 7049838, 7051040, 7052232, 7053433, 7054602,
    7055812, 7057066, 7058260, 7059427, 7060599, 7061788, 7062962, 7064158, 7065353, 7066563,
    7067773, 7068980, 7070199, 7071428, 7072607, 7073845, 7075047, 7076212, 7077408, 7078605,
    7079811, 7080997, 7082197, 7083376, 7084602, 7085748, 7086929, 7088118, 7089311, 7090549,
    7091725, 7092920, 7094125, 7095331, 7096535, 7097740, 7098958]

def LA_119 : List ℕ := [
    7100055, 7100885, 7101725, 7102566, 7103441, 7104261, 7105132, 7105960, 7106838, 7107680,
    7108544, 7109386, 7110230, 7111084, 7111914, 7112769, 7113625, 7114471, 7115302, 7116135,
    7116989, 7117827, 7118667, 7119528, 7120389, 7121222, 7122111, 7122960, 7123825, 7124642,
    7125508, 7126363, 7127221, 7128080, 7128947, 7129751, 7130625, 7131483, 7132328, 7133181,
    7134021, 7134848, 7135680, 7136567, 7137418, 7138277, 7139100, 7139925, 7140762, 7141588,
    7142432, 7143295, 7144159, 7144993, 7145832, 7146672, 7147543, 7148403, 7149271, 7150118,
    7150987, 7151848, 7152711, 7153576, 7154429, 7155270]

def LB_119 : List ℕ := [
    7100130, 7101313, 7102502, 7103720, 7104929, 7106118, 7107311, 7108533, 7109737, 7110930,
    7112108, 7113319, 7114530, 7115710, 7116904, 7118078, 7119291, 7120501, 7121705, 7122934,
    7124143, 7125349, 7126536, 7127755, 7128972, 7130151, 7131362, 7132567, 7133768, 7134941,
    7136151, 7137363, 7138561, 7139724, 7140921, 7142110, 7143299, 7144509, 7145677, 7146884,
    7148090, 7149339, 7150530, 7151771, 7152991, 7154206, 7155403]

def LA_120 : List ℕ := [
    7156109, 7156959, 7157814, 7158685, 7159544, 7160389, 7161224, 7162088, 7162960, 7163811,
    7164676, 7165518, 7166375, 7167218, 7168079, 7168924, 7169789, 7170640, 7171494, 7172343,
    7173216, 7174038, 7174892, 7175768, 7176597, 7177438, 7178301, 7179172, 7180018, 7180875,
    7181739, 7182564, 7183418, 7184266, 7185125, 7186004, 7186871, 7187708, 7188564, 7189407,
    7190268, 7191118, 7191942, 7192782, 7193656, 7194513, 7195386, 7196225, 7197098, 7197945,
    7198815, 7199659, 7200509, 7201371, 7202214, 7203059, 7203904, 7204748, 7205611, 7206444,
    7207325, 7208142, 7209010, 7209867, 7210715, 7211588]

def LB_120 : List ℕ := [
    7156577, 7157794, 7159006, 7160229, 7161422, 7162650, 7163849, 7165048, 7166274, 7167474,
    7168685, 7169885, 7171102, 7172297, 7173510, 7174697, 7175932, 7177123, 7178319, 7179516,
    7180744, 7181950, 7183142, 7184346, 7185541, 7186808, 7188003, 7189183, 7190411, 7191572,
    7192774, 7193992, 7195246, 7196443, 7197642, 7198871, 7200060, 7201268, 7202472, 7203652,
    7204858, 7206069, 7207290, 7208484, 7209691, 7210877]

def LA_121 : List ℕ := [
    7212410, 7213246, 7214087, 7214942, 7215818, 7216667, 7217527, 7218411, 7219271, 7220143,
    7221001, 7221871, 7222728, 7223596, 7224445, 7225316, 7226130, 7226985, 7227839, 7228687,
    7229538, 7230382, 7231220, 7232078, 7232935, 7233772, 7234636, 7235478, 7236341, 7237183,
    7238020, 7238873, 7239749, 7240595, 7241468, 7242317, 7243201, 7244056, 7244900, 7245760,
    7246611, 7247484, 7248308, 7249171, 7249997, 7250869, 7251697, 7252529, 7253390, 7254268,
    7255121, 7256010, 7256872, 7257725, 7258579, 7259428, 7260284, 7261157, 7261980, 7262864,
    7263694, 7264550, 7265402, 7266252, 7267108]

def LB_121 : List ℕ := [
    7212093, 7213265, 7214480, 7215699, 7216919, 7218139, 7219349, 7220594, 7221805, 7223032,
    7224254, 7225449, 7226637, 7227839, 7229051, 7230227, 7231423, 7232648, 7233835, 7235033,
    7236244, 7237443, 7238627, 7239877, 7241078, 7242296, 7243539, 7244731, 7245948, 7247155,
    7248350, 7249559, 7250764, 7251922, 7253139, 7254369, 7255582, 7256822, 7258033, 7259227,
    7260444, 7261647, 7262880, 7264056, 7265262, 7266475, 7267668]

def LA_122 : List ℕ := [
    7267978, 7268840, 7269720, 7270609, 7271472, 7272324, 7273200, 7274047, 7274883, 7275773,
    7276654, 7277514, 7278361, 7279183, 7280049, 7280895, 7281747, 7282605, 7283487, 7284325,
    7285191, 7286029, 7286854, 7287720, 7288563, 7289423, 7290270, 7291157, 7291986, 7292853,
    7293718, 7294561, 7295413, 7296249, 7297104, 7297990, 7298866, 7299714, 7300592, 7301474,
    7302355, 7303201, 7304057, 7304922, 7305774, 7306657, 7307530, 7308362, 7309241, 7310122,
    7310968, 7311838, 7312735, 7313608, 7314461, 7315330, 7316181, 7317082, 7317937, 7318781,
    7319638, 7320500, 7321366, 7322194, 7323091, 7323958]

def LB_122 : List ℕ := [
    7268909, 7270151, 7271397, 7272599, 7273814, 7275017, 7276278, 7277504, 7278696, 7279883,
    7281103, 7282296, 7283532, 7284721, 7285927, 7287112, 7288321, 7289525, 7290743, 7291944,
    7293172, 7294386, 7295580, 7296767, 7298017, 7299233, 7300450, 7301709, 7302932, 7304138,
    7305361, 7306583, 7307819, 7309023, 7310261, 7311489, 7312729, 7313961, 7315176, 7316395,
    7317638, 7318841, 7320045, 7321270, 7322471, 7323711]

def LA_123 : List ℕ := [
    7324833, 7325688, 7326531, 7327360, 7328226, 7329094, 7329918, 7330742, 7331609, 7332486,
    7333355, 7334222, 7335109, 7335977, 7336844, 7337704, 7338557, 7339421, 7340266, 7341135,
    7342009, 7342850, 7343731, 7344611, 7345478, 7346329, 7347188, 7348081, 7348927, 7349797,
    7350693, 7351535, 7352400, 7353241, 7354115, 7354959, 7355836, 7356694, 7357553, 7358392,
    7359289, 7360158, 7360986, 7361836, 7362729, 7363604, 7364479, 7365362, 7366226, 7367095,
    7367914, 7368801, 7369640, 7370511, 7371347, 7372217, 7373045, 7373885, 7374750, 7375625,
    7376454, 7377309, 7378168, 7379040, 7379899]

def LB_123 : List ℕ := [
    7324956, 7326148, 7327334, 7328563, 7329739, 7330928, 7332175, 7333390, 7334618, 7335856,
    7337093, 7338306, 7339510, 7340713, 7341960, 7343161, 7344396, 7345641, 7346846, 7348087,
    7349280, 7350543, 7351761, 7352966, 7354186, 7355402, 7356624, 7357804, 7359053, 7360288,
    7361442, 7362712, 7363929, 7365207, 7366407, 7367612, 7368852, 7370042, 7371247, 7372451,
    7373646, 7374868, 7376075, 7377274, 7378505, 7379685]

def LA_124 : List ℕ := [
    7380759, 7381610, 7382459, 7383309, 7384174, 7385034, 7385888, 7386749, 7387631, 7388464,
    7389342, 7390205, 7391040, 7391894, 7392780, 7393648, 7394506, 7395352, 7396217, 7397086,
    7397961, 7398835, 7399683, 7400561, 7401436, 7402283, 7403140, 7403987, 7404884, 7405749,
    7406570, 7407407, 7408283, 7409170, 7410038, 7410913, 7411780, 7412626, 7413506, 7414372,
    7415224, 7416122, 7417013, 7417886, 7418744, 7419601, 7420480, 7421321, 7422198, 7423052,
    7423927, 7424810, 7425697, 7426556, 7427439, 7428288, 7429137, 7430023, 7430930, 7431773,
    7432636, 7433505, 7434388, 7435280, 7436133]

def LB_124 : List ℕ := [
    7380924, 7382134, 7383324, 7384561, 7385756, 7386974, 7388196, 7389420, 7390626, 7391832,
    7393066, 7394271, 7395482, 7396707, 7397956, 7399160, 7400412, 7401633, 7402819, 7404045,
    7405292, 7406484, 7407672, 7408936, 7410141, 7411372, 7412590, 7413823, 7415043, 7416295,
    7417559, 7418769, 7419998, 7421203, 7422430, 7423648, 7424892, 7426148, 7427378, 7428567,
    7429807, 7431081, 7432277, 7433508, 7434771, 7436001]

def LA_125 : List ℕ := [
    7436991, 7437872, 7438735, 7439614, 7440483, 7441324, 7442218, 7443062, 7443922, 7444768,
    7445656, 7446505, 7447355, 7448222, 7449096, 7449974, 7450885, 7451751, 7452615, 7453483,
    7454345, 7455217, 7456072, 7456935, 7457805, 7458670, 7459543, 7460394, 7461230, 7462117,
    7462989, 7463842, 7464706, 7465575, 7466456, 7467341, 7468241, 7469092, 7470007, 7470899,
    7471760, 7472614, 7473444, 7474309, 7475190, 7476044, 7476889, 7477757, 7478618, 7479492,
    7480351, 7481204, 7482088, 7482955, 7483825, 7484700, 7485553, 7486399, 7487265, 7488125,
    7489003, 7489859, 7490725, 7491587]

def LB_125 : List ℕ := [
    7437206, 7438424, 7439681, 7440885, 7442135, 7443316, 7444540, 7445781, 7446968, 7448205,
    7449438, 7450713, 7451940, 7453176, 7454386, 7455602, 7456817, 7458059, 7459294, 7460478,
    7461695, 7462933, 7464166, 7465381, 7466628, 7467874, 7469103, 7470392, 7471617, 7472823,
    7474039, 7475260, 7476456, 7477683, 7478902, 7480121, 7481338, 7482587, 7483815, 7485040,
    7486237, 7487454, 7488719, 7489909, 7491126, 7492336]

def LA_126 : List ℕ := [
    7492438, 7493348, 7494224, 7495098, 7495995, 7496821, 7497683, 7498581, 7499472, 7500350,
    7501210, 7502062, 7502909, 7503779, 7504662, 7505512, 7506375, 7507269, 7508127, 7508998,
    7509866, 7510731, 7511614, 7512511, 7513364, 7514269, 7515125, 7515996, 7516868, 7517725,
    7518563, 7519441, 7520277, 7521167, 7522025, 7522894, 7523785, 7524666, 7525512, 7526377,
    7527239, 7528118, 7528995, 7529868, 7530738, 7531625, 7532500, 7533352, 7534260, 7535082,
    7535982, 7536834, 7537702, 7538549, 7539469, 7540335, 7541208, 7542074, 7542974, 7543864,
    7544763, 7545621, 7546508, 7547362, 7548248]

def LB_126 : List ℕ := [
    7493622, 7494854, 7496105, 7497293, 7498538, 7499800, 7501029, 7502239, 7503437, 7504680,
    7505911, 7507139, 7508357, 7509587, 7510813, 7512063, 7513304, 7514554, 7515785, 7517021,
    7518226, 7519439, 7520673, 7521863, 7523101, 7524364, 7525573, 7526787, 7528028, 7529251,
    7530495, 7531759, 7532985, 7534226, 7535431, 7536676, 7537876, 7539142, 7540370, 7541597,
    7542858, 7544133, 7545352, 7546595, 7547840]

def LA_127 : List ℕ := [
    7549103, 7549954, 7550805, 7551618, 7552454, 7553350, 7554236, 7555124, 7555987, 7556863,
    7557756, 7558644, 7559521, 7560384, 7561250, 7562150, 7563044, 7563929, 7564780, 7565628,
    7566520, 7567390, 7568241, 7569099, 7569960, 7570833, 7571709, 7572570, 7573435, 7574314,
    7575182, 7576057, 7576930, 7577759, 7578651, 7579548, 7580402, 7581280, 7582161, 7583042,
    7583897, 7584780, 7585657, 7586502, 7587355, 7588231, 7589119, 7589975, 7590876, 7591753,
    7592619, 7593469, 7594360, 7595229, 7596143, 7597027, 7597876, 7598758, 7599609, 7600516,
    7601382, 7602227, 7603119, 7604005]

def LB_127 : List ℕ := [
    7549047, 7550256, 7551422, 7552623, 7553874, 7555140, 7556340, 7557620, 7558872, 7560099,
    7561320, 7562604, 7563837, 7565039, 7566286, 7567517, 7568710, 7569941, 7571184, 7572413,
    7573647, 7574851, 7576105, 7577331, 7578537, 7579787, 7581011, 7582264, 7583495, 7584741,
    7585975, 7587151, 7588399, 7589645, 7590895, 7592133, 7593338, 7594570, 7595855, 7597106,
    7598322, 7599541, 7600794, 7602020, 7603250, 7604542]

def LA_128 : List ℕ := [
    7604904, 7605785, 7606668, 7607525, 7608420, 7609284, 7610195, 7611056, 7611939, 7612808,
    7613668, 7614550, 7615452, 7616324, 7617227, 7618103, 7618964, 7619844, 7620707, 7621558,
    7622441, 7623307, 7624157, 7625042, 7625923, 7626797, 7627680, 7628533, 7629418, 7630300,
    7631192, 7632092, 7632983, 7633863, 7634706, 7635608, 7636494, 7637383, 7638250, 7639141,
    7640026, 7640922, 7641808, 7642688, 7643566, 7644444, 7645308, 7646191, 7647073, 7647956,
    7648836, 7649725, 7650617, 7651529, 7652411, 7653267, 7654147, 7654986, 7655872, 7656767,
    7657631, 7658524, 7659399, 7660238]

def LB_128 : List ℕ := [
    7605780, 7606997, 7608260, 7609500, 7610751, 7612004, 7613209, 7614442, 7615718, 7616965,
    7618212, 7619454, 7620674, 7621876, 7623119, 7624344, 7625589, 7626822, 7628061, 7629288,
    7630561, 7631814, 7633069, 7634306, 7635552, 7636797, 7638036, 7639298, 7640554, 7641813,
    7643055, 7644303, 7645525, 7646790, 7648024, 7649276, 7650532, 7651817, 7653048, 7654264,
    7655484, 7656746, 7657978, 7659228, 7660438]

def LA_129 : List ℕ := [
    7661116, 7662007, 7662878, 7663756, 7664642, 7665510, 7666364, 7667249, 7668135, 7669019,
    7669913, 7670817, 7671693, 7672557, 7673421, 7674293, 7675157, 7676032, 7676909, 7677756,
    7678607, 7679514, 7680364, 7681243, 7682120, 7683011, 7683875, 7684759, 7685641, 7686546,
    7687395, 7688246, 7689121, 7690023, 7690917, 7691766, 7692680, 7693521, 7694426, 7695290,
    7696163, 7697031, 7697935, 7698796, 7699686, 7700559, 7701427, 7702330, 7703202, 7704092,
    7704907, 7705797, 7706671, 7707588, 7708516, 7709386, 7710218, 7711114, 7711989, 7712873,
    7713748, 7714623, 7715481, 7716369]

def LB_129 : List ℕ := [
    7661677, 7662921, 7664174, 7665406, 7666622, 7667871, 7669134, 7670386, 7671644, 7672872,
    7674102, 7675322, 7676547, 7677775, 7679010, 7680237, 7681477, 7682723, 7683961, 7685194,
    7686459, 7687666, 7688906, 7690181, 7691406, 7692667, 7693878, 7695123, 7696371, 7697617,
    7698845, 7700099, 7701326, 7702583, 7703845, 7705026, 7706273, 7707550, 7708829, 7710029,
    7711275, 7712516, 7713775, 7714982, 7716234]

def LA_130 : List ℕ := [
    7717265, 7718138, 7719064, 7719940, 7720813, 7721727, 7722620, 7723522, 7724415, 7725335,
    7726216, 7727065, 7727970, 7728865, 7729745, 7730637, 7731505, 7732405, 7733313, 7734211,
    7735093, 7735940, 7736836, 7737726, 7738609, 7739522, 7740382, 7741265, 7742151, 7743037,
    7743894, 7744759, 7745636, 7746529, 7747417, 7748295, 7749191, 7750064, 7750935, 7751829,
    7752700, 7753580, 7754470, 7755349, 7756208, 7757096, 7757994, 7758873, 7759757, 7760646,
    7761480, 7762363, 7763234, 7764113, 7765005, 7765881, 7766799, 7767696, 7768578, 7769436,
    7770307, 7771207, 7772113]

def LB_130 : List ℕ := [
    7717497, 7718775, 7720026, 7721287, 7722550, 7723845, 7725111, 7726356, 7727604, 7728864,
    7730121, 7731361, 7732624, 7733919, 7735143, 7736383, 7737638, 7738896, 7740160, 7741390,
    7742645, 7743868, 7745089, 7746346, 7747616, 7748852, 7750099, 7751336, 7752586, 7753825,
    7755057, 7756306, 7757573, 7758816, 7760075, 7761278, 7762538, 7763779, 7765023, 7766259,
    7767569, 7768803, 7770018, 7771289, 7772551]

def LA_131 : List ℕ := [
    7772974, 7773893, 7774784, 7775687, 7776570, 7777483, 7778371, 7779288, 7780154, 7781026,
    7781903, 7782844, 7783715, 7784605, 7785522, 7786382, 7787258, 7788136, 7789015, 7789877,
    7790750, 7791610, 7792504, 7793396, 7794286, 7795180, 7796043, 7796925, 7797782, 7798662,
    7799549, 7800448, 7801355, 7802223, 7803110, 7803964, 7804824, 7805709, 7806614, 7807489,
    7808381, 7809269, 7810113, 7810985, 7811844, 7812760, 7813677, 7814558, 7815426, 7816318,
    7817199, 7818071, 7818929, 7819785, 7820662, 7821579, 7822477, 7823374, 7824288, 7825171,
    7826053, 7826950, 7827837]

def LB_131 : List ℕ := [
    7773802, 7775085, 7776351, 7777628, 7778894, 7780143, 7781377, 7782681, 7783920, 7785197,
    7786421, 7787673, 7788916, 7790138, 7791361, 7792616, 7793889, 7795144, 7796363, 7797598,
    7798841, 7800108, 7801378, 7802625, 7803847, 7805061, 7806311, 7807570, 7808818, 7810061,
    7811266, 7812516, 7813836, 7815063, 7816315, 7817553, 7818785, 7819991, 7821260, 7822535,
    7823806, 7825076, 7826315, 7827577]

def LA_132 : List ℕ := [
    7828727, 7829623, 7830517, 7831341, 7832229, 7833127, 7834021, 7834927, 7835834, 7836736,
    7837593, 7838481, 7839348, 7840234, 7841105, 7842014, 7842888, 7843793, 7844671, 7845559,
    7846448, 7847357, 7848233, 7849124, 7849999, 7850895, 7851838, 7852744, 7853633, 7854486,
    7855371, 7856280, 7857169, 7858093, 7858980, 7859859, 7860733, 7861612, 7862491, 7863382,
    7864287, 7865173, 7866060, 7866963, 7867797, 7868691, 7869585, 7870474, 7871341, 7872242,
    7873136]

def LB_132 : List ℕ := [
    7828841, 7830120, 7831314, 7832553, 7833839, 7835114, 7836379, 7837624, 7838870, 7840113,
    7841357, 7842626, 7843887, 7845123, 7846390, 7847662, 7848913, 7850170, 7851457, 7852748,
    7853991, 7855220, 7856496, 7857776, 7859050, 7860272, 7861524, 7862782, 7864045, 7865295,
    7866568, 7867780, 7869048, 7870296, 7871522, 7872809]

/-! ## The assembled tables -/

def TA_132 : List ℕ := LA_132

def TB_132 : List ℕ := LB_132

def TA_131 : List ℕ := LA_131 ++ TA_132

def TB_131 : List ℕ := LB_131 ++ TB_132

def TA_130 : List ℕ := LA_130 ++ TA_131

def TB_130 : List ℕ := LB_130 ++ TB_131

def TA_129 : List ℕ := LA_129 ++ TA_130

def TB_129 : List ℕ := LB_129 ++ TB_130

def TA_128 : List ℕ := LA_128 ++ TA_129

def TB_128 : List ℕ := LB_128 ++ TB_129

def TA_127 : List ℕ := LA_127 ++ TA_128

def TB_127 : List ℕ := LB_127 ++ TB_128

def TA_126 : List ℕ := LA_126 ++ TA_127

def TB_126 : List ℕ := LB_126 ++ TB_127

def TA_125 : List ℕ := LA_125 ++ TA_126

def TB_125 : List ℕ := LB_125 ++ TB_126

def TA_124 : List ℕ := LA_124 ++ TA_125

def TB_124 : List ℕ := LB_124 ++ TB_125

def TA_123 : List ℕ := LA_123 ++ TA_124

def TB_123 : List ℕ := LB_123 ++ TB_124

def TA_122 : List ℕ := LA_122 ++ TA_123

def TB_122 : List ℕ := LB_122 ++ TB_123

def TA_121 : List ℕ := LA_121 ++ TA_122

def TB_121 : List ℕ := LB_121 ++ TB_122

def TA_120 : List ℕ := LA_120 ++ TA_121

def TB_120 : List ℕ := LB_120 ++ TB_121

def TA_119 : List ℕ := LA_119 ++ TA_120

def TB_119 : List ℕ := LB_119 ++ TB_120

def TA_118 : List ℕ := LA_118 ++ TA_119

def TB_118 : List ℕ := LB_118 ++ TB_119

def TA_117 : List ℕ := LA_117 ++ TA_118

def TB_117 : List ℕ := LB_117 ++ TB_118

def TA_116 : List ℕ := LA_116 ++ TA_117

def TB_116 : List ℕ := LB_116 ++ TB_117

def TA_115 : List ℕ := LA_115 ++ TA_116

def TB_115 : List ℕ := LB_115 ++ TB_116

def TA_114 : List ℕ := LA_114 ++ TA_115

def TB_114 : List ℕ := LB_114 ++ TB_115

def TA_113 : List ℕ := LA_113 ++ TA_114

def TB_113 : List ℕ := LB_113 ++ TB_114

def TA_112 : List ℕ := LA_112 ++ TA_113

def TB_112 : List ℕ := LB_112 ++ TB_113

def TA_111 : List ℕ := LA_111 ++ TA_112

def TB_111 : List ℕ := LB_111 ++ TB_112

def TA_110 : List ℕ := LA_110 ++ TA_111

def TB_110 : List ℕ := LB_110 ++ TB_111

def TA_109 : List ℕ := LA_109 ++ TA_110

def TB_109 : List ℕ := LB_109 ++ TB_110

def TA_108 : List ℕ := LA_108 ++ TA_109

def TB_108 : List ℕ := LB_108 ++ TB_109

def TA_107 : List ℕ := LA_107 ++ TA_108

def TB_107 : List ℕ := LB_107 ++ TB_108

def TA_106 : List ℕ := LA_106 ++ TA_107

def TB_106 : List ℕ := LB_106 ++ TB_107

def TA_105 : List ℕ := LA_105 ++ TA_106

def TB_105 : List ℕ := LB_105 ++ TB_106

def TA_104 : List ℕ := LA_104 ++ TA_105

def TB_104 : List ℕ := LB_104 ++ TB_105

def TA_103 : List ℕ := LA_103 ++ TA_104

def TB_103 : List ℕ := LB_103 ++ TB_104

def TA_102 : List ℕ := LA_102 ++ TA_103

def TB_102 : List ℕ := LB_102 ++ TB_103

def TA_101 : List ℕ := LA_101 ++ TA_102

def TB_101 : List ℕ := LB_101 ++ TB_102

def TA_100 : List ℕ := LA_100 ++ TA_101

def TB_100 : List ℕ := LB_100 ++ TB_101

def TA_99 : List ℕ := LA_99 ++ TA_100

def TB_99 : List ℕ := LB_99 ++ TB_100

def TA_98 : List ℕ := LA_98 ++ TA_99

def TB_98 : List ℕ := LB_98 ++ TB_99

def TA_97 : List ℕ := LA_97 ++ TA_98

def TB_97 : List ℕ := LB_97 ++ TB_98

def TA_96 : List ℕ := LA_96 ++ TA_97

def TB_96 : List ℕ := LB_96 ++ TB_97

def TA_95 : List ℕ := LA_95 ++ TA_96

def TB_95 : List ℕ := LB_95 ++ TB_96

def TA_94 : List ℕ := LA_94 ++ TA_95

def TB_94 : List ℕ := LB_94 ++ TB_95

def TA_93 : List ℕ := LA_93 ++ TA_94

def TB_93 : List ℕ := LB_93 ++ TB_94

def TA_92 : List ℕ := LA_92 ++ TA_93

def TB_92 : List ℕ := LB_92 ++ TB_93

def TA_91 : List ℕ := LA_91 ++ TA_92

def TB_91 : List ℕ := LB_91 ++ TB_92

def TA_90 : List ℕ := LA_90 ++ TA_91

def TB_90 : List ℕ := LB_90 ++ TB_91

def TA_89 : List ℕ := LA_89 ++ TA_90

def TB_89 : List ℕ := LB_89 ++ TB_90

def TA_88 : List ℕ := LA_88 ++ TA_89

def TB_88 : List ℕ := LB_88 ++ TB_89

def TA_87 : List ℕ := LA_87 ++ TA_88

def TB_87 : List ℕ := LB_87 ++ TB_88

def TA_86 : List ℕ := LA_86 ++ TA_87

def TB_86 : List ℕ := LB_86 ++ TB_87

def TA_85 : List ℕ := LA_85 ++ TA_86

def TB_85 : List ℕ := LB_85 ++ TB_86

def TA_84 : List ℕ := LA_84 ++ TA_85

def TB_84 : List ℕ := LB_84 ++ TB_85

def TA_83 : List ℕ := LA_83 ++ TA_84

def TB_83 : List ℕ := LB_83 ++ TB_84

def TA_82 : List ℕ := LA_82 ++ TA_83

def TB_82 : List ℕ := LB_82 ++ TB_83

def TA_81 : List ℕ := LA_81 ++ TA_82

def TB_81 : List ℕ := LB_81 ++ TB_82

def TA_80 : List ℕ := LA_80 ++ TA_81

def TB_80 : List ℕ := LB_80 ++ TB_81

def TA_79 : List ℕ := LA_79 ++ TA_80

def TB_79 : List ℕ := LB_79 ++ TB_80

def TA_78 : List ℕ := LA_78 ++ TA_79

def TB_78 : List ℕ := LB_78 ++ TB_79

def TA_77 : List ℕ := LA_77 ++ TA_78

def TB_77 : List ℕ := LB_77 ++ TB_78

def TA_76 : List ℕ := LA_76 ++ TA_77

def TB_76 : List ℕ := LB_76 ++ TB_77

def TA_75 : List ℕ := LA_75 ++ TA_76

def TB_75 : List ℕ := LB_75 ++ TB_76

def TA_74 : List ℕ := LA_74 ++ TA_75

def TB_74 : List ℕ := LB_74 ++ TB_75

def TA_73 : List ℕ := LA_73 ++ TA_74

def TB_73 : List ℕ := LB_73 ++ TB_74

def TA_72 : List ℕ := LA_72 ++ TA_73

def TB_72 : List ℕ := LB_72 ++ TB_73

def TA_71 : List ℕ := LA_71 ++ TA_72

def TB_71 : List ℕ := LB_71 ++ TB_72

def TA_70 : List ℕ := LA_70 ++ TA_71

def TB_70 : List ℕ := LB_70 ++ TB_71

def TA_69 : List ℕ := LA_69 ++ TA_70

def TB_69 : List ℕ := LB_69 ++ TB_70

def TA_68 : List ℕ := LA_68 ++ TA_69

def TB_68 : List ℕ := LB_68 ++ TB_69

def TA_67 : List ℕ := LA_67 ++ TA_68

def TB_67 : List ℕ := LB_67 ++ TB_68

def TA_66 : List ℕ := LA_66 ++ TA_67

def TB_66 : List ℕ := LB_66 ++ TB_67

def TA_65 : List ℕ := LA_65 ++ TA_66

def TB_65 : List ℕ := LB_65 ++ TB_66

def TA_64 : List ℕ := LA_64 ++ TA_65

def TB_64 : List ℕ := LB_64 ++ TB_65

def TA_63 : List ℕ := LA_63 ++ TA_64

def TB_63 : List ℕ := LB_63 ++ TB_64

def TA_62 : List ℕ := LA_62 ++ TA_63

def TB_62 : List ℕ := LB_62 ++ TB_63

def TA_61 : List ℕ := LA_61 ++ TA_62

def TB_61 : List ℕ := LB_61 ++ TB_62

def TA_60 : List ℕ := LA_60 ++ TA_61

def TB_60 : List ℕ := LB_60 ++ TB_61

def TA_59 : List ℕ := LA_59 ++ TA_60

def TB_59 : List ℕ := LB_59 ++ TB_60

def TA_58 : List ℕ := LA_58 ++ TA_59

def TB_58 : List ℕ := LB_58 ++ TB_59

def TA_57 : List ℕ := LA_57 ++ TA_58

def TB_57 : List ℕ := LB_57 ++ TB_58

def TA_56 : List ℕ := LA_56 ++ TA_57

def TB_56 : List ℕ := LB_56 ++ TB_57

def TA_55 : List ℕ := LA_55 ++ TA_56

def TB_55 : List ℕ := LB_55 ++ TB_56

def TA_54 : List ℕ := LA_54 ++ TA_55

def TB_54 : List ℕ := LB_54 ++ TB_55

def TA_53 : List ℕ := LA_53 ++ TA_54

def TB_53 : List ℕ := LB_53 ++ TB_54

def TA_52 : List ℕ := LA_52 ++ TA_53

def TB_52 : List ℕ := LB_52 ++ TB_53

def TA_51 : List ℕ := LA_51 ++ TA_52

def TB_51 : List ℕ := LB_51 ++ TB_52

def TA_50 : List ℕ := LA_50 ++ TA_51

def TB_50 : List ℕ := LB_50 ++ TB_51

def TA_49 : List ℕ := LA_49 ++ TA_50

def TB_49 : List ℕ := LB_49 ++ TB_50

def TA_48 : List ℕ := LA_48 ++ TA_49

def TB_48 : List ℕ := LB_48 ++ TB_49

def TA_47 : List ℕ := LA_47 ++ TA_48

def TB_47 : List ℕ := LB_47 ++ TB_48

def TA_46 : List ℕ := LA_46 ++ TA_47

def TB_46 : List ℕ := LB_46 ++ TB_47

def TA_45 : List ℕ := LA_45 ++ TA_46

def TB_45 : List ℕ := LB_45 ++ TB_46

def TA_44 : List ℕ := LA_44 ++ TA_45

def TB_44 : List ℕ := LB_44 ++ TB_45

def TA_43 : List ℕ := LA_43 ++ TA_44

def TB_43 : List ℕ := LB_43 ++ TB_44

def TA_42 : List ℕ := LA_42 ++ TA_43

def TB_42 : List ℕ := LB_42 ++ TB_43

def TA_41 : List ℕ := LA_41 ++ TA_42

def TB_41 : List ℕ := LB_41 ++ TB_42

def TA_40 : List ℕ := LA_40 ++ TA_41

def TB_40 : List ℕ := LB_40 ++ TB_41

def TA_39 : List ℕ := LA_39 ++ TA_40

def TB_39 : List ℕ := LB_39 ++ TB_40

def TA_38 : List ℕ := LA_38 ++ TA_39

def TB_38 : List ℕ := LB_38 ++ TB_39

def TA_37 : List ℕ := LA_37 ++ TA_38

def TB_37 : List ℕ := LB_37 ++ TB_38

def TA_36 : List ℕ := LA_36 ++ TA_37

def TB_36 : List ℕ := LB_36 ++ TB_37

def TA_35 : List ℕ := LA_35 ++ TA_36

def TB_35 : List ℕ := LB_35 ++ TB_36

def TA_34 : List ℕ := LA_34 ++ TA_35

def TB_34 : List ℕ := LB_34 ++ TB_35

def TA_33 : List ℕ := LA_33 ++ TA_34

def TB_33 : List ℕ := LB_33 ++ TB_34

def TA_32 : List ℕ := LA_32 ++ TA_33

def TB_32 : List ℕ := LB_32 ++ TB_33

def TA_31 : List ℕ := LA_31 ++ TA_32

def TB_31 : List ℕ := LB_31 ++ TB_32

def TA_30 : List ℕ := LA_30 ++ TA_31

def TB_30 : List ℕ := LB_30 ++ TB_31

def TA_29 : List ℕ := LA_29 ++ TA_30

def TB_29 : List ℕ := LB_29 ++ TB_30

def TA_28 : List ℕ := LA_28 ++ TA_29

def TB_28 : List ℕ := LB_28 ++ TB_29

def TA_27 : List ℕ := LA_27 ++ TA_28

def TB_27 : List ℕ := LB_27 ++ TB_28

def TA_26 : List ℕ := LA_26 ++ TA_27

def TB_26 : List ℕ := LB_26 ++ TB_27

def TA_25 : List ℕ := LA_25 ++ TA_26

def TB_25 : List ℕ := LB_25 ++ TB_26

def TA_24 : List ℕ := LA_24 ++ TA_25

def TB_24 : List ℕ := LB_24 ++ TB_25

def TA_23 : List ℕ := LA_23 ++ TA_24

def TB_23 : List ℕ := LB_23 ++ TB_24

def TA_22 : List ℕ := LA_22 ++ TA_23

def TB_22 : List ℕ := LB_22 ++ TB_23

def TA_21 : List ℕ := LA_21 ++ TA_22

def TB_21 : List ℕ := LB_21 ++ TB_22

def TA_20 : List ℕ := LA_20 ++ TA_21

def TB_20 : List ℕ := LB_20 ++ TB_21

def TA_19 : List ℕ := LA_19 ++ TA_20

def TB_19 : List ℕ := LB_19 ++ TB_20

def TA_18 : List ℕ := LA_18 ++ TA_19

def TB_18 : List ℕ := LB_18 ++ TB_19

def TA_17 : List ℕ := LA_17 ++ TA_18

def TB_17 : List ℕ := LB_17 ++ TB_18

def TA_16 : List ℕ := LA_16 ++ TA_17

def TB_16 : List ℕ := LB_16 ++ TB_17

def TA_15 : List ℕ := LA_15 ++ TA_16

def TB_15 : List ℕ := LB_15 ++ TB_16

def TA_14 : List ℕ := LA_14 ++ TA_15

def TB_14 : List ℕ := LB_14 ++ TB_15

def TA_13 : List ℕ := LA_13 ++ TA_14

def TB_13 : List ℕ := LB_13 ++ TB_14

def TA_12 : List ℕ := LA_12 ++ TA_13

def TB_12 : List ℕ := LB_12 ++ TB_13

def TA_11 : List ℕ := LA_11 ++ TA_12

def TB_11 : List ℕ := LB_11 ++ TB_12

def TA_10 : List ℕ := LA_10 ++ TA_11

def TB_10 : List ℕ := LB_10 ++ TB_11

def TA_9 : List ℕ := LA_9 ++ TA_10

def TB_9 : List ℕ := LB_9 ++ TB_10

def TA_8 : List ℕ := LA_8 ++ TA_9

def TB_8 : List ℕ := LB_8 ++ TB_9

def TA_7 : List ℕ := LA_7 ++ TA_8

def TB_7 : List ℕ := LB_7 ++ TB_8

def TA_6 : List ℕ := LA_6 ++ TA_7

def TB_6 : List ℕ := LB_6 ++ TB_7

def TA_5 : List ℕ := LA_5 ++ TA_6

def TB_5 : List ℕ := LB_5 ++ TB_6

def TA_4 : List ℕ := LA_4 ++ TA_5

def TB_4 : List ℕ := LB_4 ++ TB_5

def TA_3 : List ℕ := LA_3 ++ TA_4

def TB_3 : List ℕ := LB_3 ++ TB_4

def TA_2 : List ℕ := LA_2 ++ TA_3

def TB_2 : List ℕ := LB_2 ++ TB_3

def TA_1 : List ℕ := LA_1 ++ TA_2

def TB_1 : List ℕ := LB_1 ++ TB_2

def TA_0 : List ℕ := LA_0 ++ TA_1

def TB_0 : List ℕ := LB_0 ++ TB_1

/-- `tabA[k] = π(k(k+1)/2)`. -/
def tabA : List ℕ := 0 :: TA_0

/-- `tabB[m] = π(m ^ 2)`. -/
def tabB : List ℕ := 0 :: TB_0

theorem base0 (f : ℕ → ℕ) (h : Nat.count Nat.Prime (f 0) = 0) : Good f 0 [0] := by
  intro i hi
  obtain rfl : i = 0 := by simpa using hi
  simpa using h

set_option maxHeartbeats 400000000 in
/-- All window checks run inside one proof, so that the kernel checks run one after another on
one thread and reuse its memory. -/
theorem goodAB : Good fA 0 tabA ∧ Good fB 0 tabB := by
  have ck_0 : chk2 0 1081344 0 0 LA_0 0 0 LB_0 = true := by decide +kernel
  have g_0 : Good fA 1 LA_0 ∧ Good fB 1 LB_0 :=
    chk2_sound (by norm_num [NMax]) ck_0
      hc0A
      hc0B
  have ck_1 : chk2 1048576 1081344 1448 82061 LA_1 1024 82025 LB_1 = true := by decide +kernel
  have g_1 : Good fA 1449 LA_1 ∧ Good fB 1025 LB_1 :=
    chk2_sound (by norm_num [NMax]) ck_1
      (g_0.1.count_eq (i := 1447) (by decide +kernel) (by decide +kernel))
      (g_0.2.count_eq (i := 1023) (by decide +kernel) (by decide +kernel))
  have ck_2 : chk2 2097152 1081344 2048 155681 LA_2 1449 155778 LB_2 = true := by decide +kernel
  have g_2 : Good fA 2049 LA_2 ∧ Good fB 1450 LB_2 :=
    chk2_sound (by norm_num [NMax]) ck_2
      (g_1.1.count_eq (i := 599) (by decide +kernel) (by decide +kernel))
      (g_1.2.count_eq (i := 424) (by decide +kernel) (by decide +kernel))
  have ck_3 : chk2 3145728 1081344 2508 226586 LA_3 1774 226635 LB_3 = true := by decide +kernel
  have g_3 : Good fA 2509 LA_3 ∧ Good fB 1775 LB_3 :=
    chk2_sound (by norm_num [NMax]) ck_3
      (g_2.1.count_eq (i := 459) (by decide +kernel) (by decide +kernel))
      (g_2.2.count_eq (i := 324) (by decide +kernel) (by decide +kernel))
  have ck_4 : chk2 4194304 1081344 2896 295984 LA_4 2048 295947 LB_4 = true := by decide +kernel
  have g_4 : Good fA 2897 LA_4 ∧ Good fB 2049 LB_4 :=
    chk2_sound (by norm_num [NMax]) ck_4
      (g_3.1.count_eq (i := 387) (by decide +kernel) (by decide +kernel))
      (g_3.2.count_eq (i := 273) (by decide +kernel) (by decide +kernel))
  have ck_5 : chk2 5242880 1081344 3238 364278 LA_5 2290 364290 LB_5 = true := by decide +kernel
  have g_5 : Good fA 3239 LA_5 ∧ Good fB 2291 LB_5 :=
    chk2_sound (by norm_num [NMax]) ck_5
      (g_4.1.count_eq (i := 341) (by decide +kernel) (by decide +kernel))
      (g_4.2.count_eq (i := 241) (by decide +kernel) (by decide +kernel))
  have ck_6 : chk2 6291456 1081344 3547 431563 LA_6 2509 431738 LB_6 = true := by decide +kernel
  have g_6 : Good fA 3548 LA_6 ∧ Good fB 2510 LB_6 :=
    chk2_sound (by norm_num [NMax]) ck_6
      (g_5.1.count_eq (i := 308) (by decide +kernel) (by decide +kernel))
      (g_5.2.count_eq (i := 218) (by decide +kernel) (by decide +kernel))
  have ck_7 : chk2 7340032 1081344 3831 498188 LA_7 2710 498421 LB_7 = true := by decide +kernel
  have g_7 : Good fA 3832 LA_7 ∧ Good fB 2711 LB_7 :=
    chk2_sound (by norm_num [NMax]) ck_7
      (g_6.1.count_eq (i := 283) (by decide +kernel) (by decide +kernel))
      (g_6.2.count_eq (i := 200) (by decide +kernel) (by decide +kernel))
  have ck_8 : chk2 8388608 1081344 4096 564294 LA_8 2897 564420 LB_8 = true := by decide +kernel
  have g_8 : Good fA 4097 LA_8 ∧ Good fB 2898 LB_8 :=
    chk2_sound (by norm_num [NMax]) ck_8
      (g_7.1.count_eq (i := 264) (by decide +kernel) (by decide +kernel))
      (g_7.2.count_eq (i := 186) (by decide +kernel) (by decide +kernel))
  have ck_9 : chk2 9437184 1081344 4344 629694 LA_9 3072 629686 LB_9 = true := by decide +kernel
  have g_9 : Good fA 4345 LA_9 ∧ Good fB 3073 LB_9 :=
    chk2_sound (by norm_num [NMax]) ck_9
      (g_8.1.count_eq (i := 247) (by decide +kernel) (by decide +kernel))
      (g_8.2.count_eq (i := 174) (by decide +kernel) (by decide +kernel))
  have ck_10 : chk2 10485760 1081344 4579 694725 LA_10 3239 695064 LB_10 = true := by decide +kernel
  have g_10 : Good fA 4580 LA_10 ∧ Good fB 3240 LB_10 :=
    chk2_sound (by norm_num [NMax]) ck_10
      (g_9.1.count_eq (i := 234) (by decide +kernel) (by decide +kernel))
      (g_9.2.count_eq (i := 166) (by decide +kernel) (by decide +kernel))
  have ck_11 : chk2 11534336 1081344 4803 759550 LA_11 3397 759732 LB_11 = true := by decide +kernel
  have g_11 : Good fA 4804 LA_11 ∧ Good fB 3398 LB_11 :=
    chk2_sound (by norm_num [NMax]) ck_11
      (g_10.1.count_eq (i := 223) (by decide +kernel) (by decide +kernel))
      (g_10.2.count_eq (i := 157) (by decide +kernel) (by decide +kernel))
  have ck_12 : chk2 12582912 1081344 5017 824042 LA_12 3548 824086 LB_12 = true := by decide +kernel
  have g_12 : Good fA 5018 LA_12 ∧ Good fB 3549 LB_12 :=
    chk2_sound (by norm_num [NMax]) ck_12
      (g_11.1.count_eq (i := 213) (by decide +kernel) (by decide +kernel))
      (g_11.2.count_eq (i := 150) (by decide +kernel) (by decide +kernel))
  have ck_13 : chk2 13631488 1081344 5221 887676 LA_13 3693 888061 LB_13 = true := by decide +kernel
  have g_13 : Good fA 5222 LA_13 ∧ Good fB 3694 LB_13 :=
    chk2_sound (by norm_num [NMax]) ck_13
      (g_12.1.count_eq (i := 203) (by decide +kernel) (by decide +kernel))
      (g_12.2.count_eq (i := 144) (by decide +kernel) (by decide +kernel))
  have ck_14 : chk2 14680064 1081344 5418 951352 LA_14 3832 951630 LB_14 = true := by decide +kernel
  have g_14 : Good fA 5419 LA_14 ∧ Good fB 3833 LB_14 :=
    chk2_sound (by norm_num [NMax]) ck_14
      (g_13.1.count_eq (i := 196) (by decide +kernel) (by decide +kernel))
      (g_13.2.count_eq (i := 138) (by decide +kernel) (by decide +kernel))
  have ck_15 : chk2 15728640 1081344 5609 1015011 LA_15 3966 1014761 LB_15 = true := by decide +kernel
  have g_15 : Good fA 5610 LA_15 ∧ Good fB 3967 LB_15 :=
    chk2_sound (by norm_num [NMax]) ck_15
      (g_14.1.count_eq (i := 190) (by decide +kernel) (by decide +kernel))
      (g_14.2.count_eq (i := 133) (by decide +kernel) (by decide +kernel))
  have ck_16 : chk2 16777216 1081344 5793 1078185 LA_16 4096 1077871 LB_16 = true := by decide +kernel
  have g_16 : Good fA 5794 LA_16 ∧ Good fB 4097 LB_16 :=
    chk2_sound (by norm_num [NMax]) ck_16
      (g_15.1.count_eq (i := 183) (by decide +kernel) (by decide +kernel))
      (g_15.2.count_eq (i := 129) (by decide +kernel) (by decide +kernel))
  have ck_17 : chk2 17825792 1081344 5971 1141085 LA_17 4223 1141346 LB_17 = true := by decide +kernel
  have g_17 : Good fA 5972 LA_17 ∧ Good fB 4224 LB_17 :=
    chk2_sound (by norm_num [NMax]) ck_17
      (g_16.1.count_eq (i := 177) (by decide +kernel) (by decide +kernel))
      (g_16.2.count_eq (i := 126) (by decide +kernel) (by decide +kernel))
  have ck_18 : chk2 18874368 1081344 6144 1203747 LA_18 4345 1203838 LB_18 = true := by decide +kernel
  have g_18 : Good fA 6145 LA_18 ∧ Good fB 4346 LB_18 :=
    chk2_sound (by norm_num [NMax]) ck_18
      (g_17.1.count_eq (i := 172) (by decide +kernel) (by decide +kernel))
      (g_17.2.count_eq (i := 121) (by decide +kernel) (by decide +kernel))
  have ck_19 : chk2 19922944 1081344 6312 1266059 LA_19 4464 1266272 LB_19 = true := by decide +kernel
  have g_19 : Good fA 6313 LA_19 ∧ Good fB 4465 LB_19 :=
    chk2_sound (by norm_num [NMax]) ck_19
      (g_18.1.count_eq (i := 167) (by decide +kernel) (by decide +kernel))
      (g_18.2.count_eq (i := 118) (by decide +kernel) (by decide +kernel))
  have ck_20 : chk2 20971520 1081344 6476 1328294 LA_20 4580 1328530 LB_20 = true := by decide +kernel
  have g_20 : Good fA 6477 LA_20 ∧ Good fB 4581 LB_20 :=
    chk2_sound (by norm_num [NMax]) ck_20
      (g_19.1.count_eq (i := 163) (by decide +kernel) (by decide +kernel))
      (g_19.2.count_eq (i := 115) (by decide +kernel) (by decide +kernel))
  have ck_21 : chk2 22020096 1081344 6636 1390529 LA_21 4693 1390706 LB_21 = true := by decide +kernel
  have g_21 : Good fA 6637 LA_21 ∧ Good fB 4694 LB_21 :=
    chk2_sound (by norm_num [NMax]) ck_21
      (g_20.1.count_eq (i := 159) (by decide +kernel) (by decide +kernel))
      (g_20.2.count_eq (i := 112) (by decide +kernel) (by decide +kernel))
  have ck_22 : chk2 23068672 1081344 6792 1452337 LA_22 4803 1452323 LB_22 = true := by decide +kernel
  have g_22 : Good fA 6793 LA_22 ∧ Good fB 4804 LB_22 :=
    chk2_sound (by norm_num [NMax]) ck_22
      (g_21.1.count_eq (i := 155) (by decide +kernel) (by decide +kernel))
      (g_21.2.count_eq (i := 109) (by decide +kernel) (by decide +kernel))
  have ck_23 : chk2 24117248 1081344 6945 1514172 LA_23 4911 1514061 LB_23 = true := by decide +kernel
  have g_23 : Good fA 6946 LA_23 ∧ Good fB 4912 LB_23 :=
    chk2_sound (by norm_num [NMax]) ck_23
      (g_22.1.count_eq (i := 152) (by decide +kernel) (by decide +kernel))
      (g_22.2.count_eq (i := 107) (by decide +kernel) (by decide +kernel))
  have ck_24 : chk2 25165824 1081344 7094 1575667 LA_24 5017 1575914 LB_24 = true := by decide +kernel
  have g_24 : Good fA 7095 LA_24 ∧ Good fB 5018 LB_24 :=
    chk2_sound (by norm_num [NMax]) ck_24
      (g_23.1.count_eq (i := 148) (by decide +kernel) (by decide +kernel))
      (g_23.2.count_eq (i := 105) (by decide +kernel) (by decide +kernel))
  have ck_25 : chk2 26214400 1081344 7241 1637378 LA_25 5120 1637054 LB_25 = true := by decide +kernel
  have g_25 : Good fA 7242 LA_25 ∧ Good fB 5121 LB_25 :=
    chk2_sound (by norm_num [NMax]) ck_25
      (g_24.1.count_eq (i := 146) (by decide +kernel) (by decide +kernel))
      (g_24.2.count_eq (i := 102) (by decide +kernel) (by decide +kernel))
  have ck_26 : chk2 27262976 1081344 7384 1698572 LA_26 5222 1698785 LB_26 = true := by decide +kernel
  have g_26 : Good fA 7385 LA_26 ∧ Good fB 5223 LB_26 :=
    chk2_sound (by norm_num [NMax]) ck_26
      (g_25.1.count_eq (i := 142) (by decide +kernel) (by decide +kernel))
      (g_25.2.count_eq (i := 101) (by decide +kernel) (by decide +kernel))
  have ck_27 : chk2 28311552 1081344 7525 1759946 LA_27 5321 1759738 LB_27 = true := by decide +kernel
  have g_27 : Good fA 7526 LA_27 ∧ Good fB 5322 LB_27 :=
    chk2_sound (by norm_num [NMax]) ck_27
      (g_26.1.count_eq (i := 140) (by decide +kernel) (by decide +kernel))
      (g_26.2.count_eq (i := 98) (by decide +kernel) (by decide +kernel))
  have ck_28 : chk2 29360128 1081344 7663 1820905 LA_28 5419 1820960 LB_28 = true := by decide +kernel
  have g_28 : Good fA 7664 LA_28 ∧ Good fB 5420 LB_28 :=
    chk2_sound (by norm_num [NMax]) ck_28
      (g_27.1.count_eq (i := 137) (by decide +kernel) (by decide +kernel))
      (g_27.2.count_eq (i := 97) (by decide +kernel) (by decide +kernel))
  have ck_29 : chk2 30408704 1081344 7799 1882143 LA_29 5515 1882095 LB_29 = true := by decide +kernel
  have g_29 : Good fA 7800 LA_29 ∧ Good fB 5516 LB_29 :=
    chk2_sound (by norm_num [NMax]) ck_29
      (g_28.1.count_eq (i := 135) (by decide +kernel) (by decide +kernel))
      (g_28.2.count_eq (i := 95) (by decide +kernel) (by decide +kernel))
  have ck_30 : chk2 31457280 1081344 7932 1942672 LA_30 5609 1942592 LB_30 = true := by decide +kernel
  have g_30 : Good fA 7933 LA_30 ∧ Good fB 5610 LB_30 :=
    chk2_sound (by norm_num [NMax]) ck_30
      (g_29.1.count_eq (i := 132) (by decide +kernel) (by decide +kernel))
      (g_29.2.count_eq (i := 93) (by decide +kernel) (by decide +kernel))
  have ck_31 : chk2 32505856 1081344 8063 2003327 LA_31 5702 2003492 LB_31 = true := by decide +kernel
  have g_31 : Good fA 8064 LA_31 ∧ Good fB 5703 LB_31 :=
    chk2_sound (by norm_num [NMax]) ck_31
      (g_30.1.count_eq (i := 130) (by decide +kernel) (by decide +kernel))
      (g_30.2.count_eq (i := 92) (by decide +kernel) (by decide +kernel))
  have ck_32 : chk2 33554432 1081344 8192 2063947 LA_32 5793 2063961 LB_32 = true := by decide +kernel
  have g_32 : Good fA 8193 LA_32 ∧ Good fB 5794 LB_32 :=
    chk2_sound (by norm_num [NMax]) ck_32
      (g_31.1.count_eq (i := 128) (by decide +kernel) (by decide +kernel))
      (g_31.2.count_eq (i := 90) (by decide +kernel) (by decide +kernel))
  have ck_33 : chk2 34603008 1081344 8319 2124206 LA_33 5883 2124357 LB_33 = true := by decide +kernel
  have g_33 : Good fA 8320 LA_33 ∧ Good fB 5884 LB_33 :=
    chk2_sound (by norm_num [NMax]) ck_33
      (g_32.1.count_eq (i := 126) (by decide +kernel) (by decide +kernel))
      (g_32.2.count_eq (i := 89) (by decide +kernel) (by decide +kernel))
  have ck_34 : chk2 35651584 1081344 8444 2184437 LA_34 5971 2184335 LB_34 = true := by decide +kernel
  have g_34 : Good fA 8445 LA_34 ∧ Good fB 5972 LB_34 :=
    chk2_sound (by norm_num [NMax]) ck_34
      (g_33.1.count_eq (i := 124) (by decide +kernel) (by decide +kernel))
      (g_33.2.count_eq (i := 87) (by decide +kernel) (by decide +kernel))
  have ck_35 : chk2 36700160 1081344 8567 2244526 LA_35 6059 2245115 LB_35 = true := by decide +kernel
  have g_35 : Good fA 8568 LA_35 ∧ Good fB 6060 LB_35 :=
    chk2_sound (by norm_num [NMax]) ck_35
      (g_34.1.count_eq (i := 122) (by decide +kernel) (by decide +kernel))
      (g_34.2.count_eq (i := 87) (by decide +kernel) (by decide +kernel))
  have ck_36 : chk2 37748736 1081344 8689 2304935 LA_36 6144 2304655 LB_36 = true := by decide +kernel
  have g_36 : Good fA 8690 LA_36 ∧ Good fB 6145 LB_36 :=
    chk2_sound (by norm_num [NMax]) ck_36
      (g_35.1.count_eq (i := 121) (by decide +kernel) (by decide +kernel))
      (g_35.2.count_eq (i := 84) (by decide +kernel) (by decide +kernel))
  have ck_37 : chk2 38797312 1081344 8809 2365153 LA_37 6229 2364973 LB_37 = true := by decide +kernel
  have g_37 : Good fA 8810 LA_37 ∧ Good fB 6230 LB_37 :=
    chk2_sound (by norm_num [NMax]) ck_37
      (g_36.1.count_eq (i := 119) (by decide +kernel) (by decide +kernel))
      (g_36.2.count_eq (i := 84) (by decide +kernel) (by decide +kernel))
  have ck_38 : chk2 39845888 1081344 8927 2425155 LA_38 6313 2425368 LB_38 = true := by decide +kernel
  have g_38 : Good fA 8928 LA_38 ∧ Good fB 6314 LB_38 :=
    chk2_sound (by norm_num [NMax]) ck_38
      (g_37.1.count_eq (i := 117) (by decide +kernel) (by decide +kernel))
      (g_37.2.count_eq (i := 83) (by decide +kernel) (by decide +kernel))
  have ck_39 : chk2 40894464 1081344 9044 2485158 LA_39 6395 2484861 LB_39 = true := by decide +kernel
  have g_39 : Good fA 9045 LA_39 ∧ Good fB 6396 LB_39 :=
    chk2_sound (by norm_num [NMax]) ck_39
      (g_38.1.count_eq (i := 116) (by decide +kernel) (by decide +kernel))
      (g_38.2.count_eq (i := 81) (by decide +kernel) (by decide +kernel))
  have ck_40 : chk2 41943040 1081344 9159 2544710 LA_40 6477 2544902 LB_40 = true := by decide +kernel
  have g_40 : Good fA 9160 LA_40 ∧ Good fB 6478 LB_40 :=
    chk2_sound (by norm_num [NMax]) ck_40
      (g_39.1.count_eq (i := 114) (by decide +kernel) (by decide +kernel))
      (g_39.2.count_eq (i := 81) (by decide +kernel) (by decide +kernel))
  have ck_41 : chk2 42991616 1081344 9273 2604472 LA_41 6557 2604212 LB_41 = true := by decide +kernel
  have g_41 : Good fA 9274 LA_41 ∧ Good fB 6558 LB_41 :=
    chk2_sound (by norm_num [NMax]) ck_41
      (g_40.1.count_eq (i := 113) (by decide +kernel) (by decide +kernel))
      (g_40.2.count_eq (i := 79) (by decide +kernel) (by decide +kernel))
  have ck_42 : chk2 44040192 1081344 9385 2663878 LA_42 6637 2664215 LB_42 = true := by decide +kernel
  have g_42 : Good fA 9386 LA_42 ∧ Good fB 6638 LB_42 :=
    chk2_sound (by norm_num [NMax]) ck_42
      (g_41.1.count_eq (i := 111) (by decide +kernel) (by decide +kernel))
      (g_41.2.count_eq (i := 79) (by decide +kernel) (by decide +kernel))
  have ck_43 : chk2 45088768 1081344 9496 2723423 LA_43 6715 2723396 LB_43 = true := by decide +kernel
  have g_43 : Good fA 9497 LA_43 ∧ Good fB 6716 LB_43 :=
    chk2_sound (by norm_num [NMax]) ck_43
      (g_42.1.count_eq (i := 110) (by decide +kernel) (by decide +kernel))
      (g_42.2.count_eq (i := 77) (by decide +kernel) (by decide +kernel))
  have ck_44 : chk2 46137344 1081344 9606 2783089 LA_44 6793 2783224 LB_44 = true := by decide +kernel
  have g_44 : Good fA 9607 LA_44 ∧ Good fB 6794 LB_44 :=
    chk2_sound (by norm_num [NMax]) ck_44
      (g_43.1.count_eq (i := 109) (by decide +kernel) (by decide +kernel))
      (g_43.2.count_eq (i := 77) (by decide +kernel) (by decide +kernel))
  have ck_45 : chk2 47185920 1081344 9715 2842742 LA_45 6870 2842819 LB_45 = true := by decide +kernel
  have g_45 : Good fA 9716 LA_45 ∧ Good fB 6871 LB_45 :=
    chk2_sound (by norm_num [NMax]) ck_45
      (g_44.1.count_eq (i := 108) (by decide +kernel) (by decide +kernel))
      (g_44.2.count_eq (i := 76) (by decide +kernel) (by decide +kernel))
  have ck_46 : chk2 48234496 1081344 9822 2901667 LA_46 6946 2902019 LB_46 = true := by decide +kernel
  have g_46 : Good fA 9823 LA_46 ∧ Good fB 6947 LB_46 :=
    chk2_sound (by norm_num [NMax]) ck_46
      (g_45.1.count_eq (i := 106) (by decide +kernel) (by decide +kernel))
      (g_45.2.count_eq (i := 75) (by decide +kernel) (by decide +kernel))
  have ck_47 : chk2 49283072 1081344 9928 2960786 LA_47 7021 2961184 LB_47 = true := by decide +kernel
  have g_47 : Good fA 9929 LA_47 ∧ Good fB 7022 LB_47 :=
    chk2_sound (by norm_num [NMax]) ck_47
      (g_46.1.count_eq (i := 105) (by decide +kernel) (by decide +kernel))
      (g_46.2.count_eq (i := 74) (by decide +kernel) (by decide +kernel))
  have ck_48 : chk2 50331648 1081344 10033 3020048 LA_48 7095 3020247 LB_48 = true := by decide +kernel
  have g_48 : Good fA 10034 LA_48 ∧ Good fB 7096 LB_48 :=
    chk2_sound (by norm_num [NMax]) ck_48
      (g_47.1.count_eq (i := 104) (by decide +kernel) (by decide +kernel))
      (g_47.2.count_eq (i := 73) (by decide +kernel) (by decide +kernel))
  have ck_49 : chk2 51380224 1081344 10137 3079149 LA_49 7168 3078902 LB_49 = true := by decide +kernel
  have g_49 : Good fA 10138 LA_49 ∧ Good fB 7169 LB_49 :=
    chk2_sound (by norm_num [NMax]) ck_49
      (g_48.1.count_eq (i := 103) (by decide +kernel) (by decide +kernel))
      (g_48.2.count_eq (i := 72) (by decide +kernel) (by decide +kernel))
  have ck_50 : chk2 52428800 1081344 10240 3138200 LA_50 7241 3138091 LB_50 = true := by decide +kernel
  have g_50 : Good fA 10241 LA_50 ∧ Good fB 7242 LB_50 :=
    chk2_sound (by norm_num [NMax]) ck_50
      (g_49.1.count_eq (i := 102) (by decide +kernel) (by decide +kernel))
      (g_49.2.count_eq (i := 72) (by decide +kernel) (by decide +kernel))
  have ck_51 : chk2 53477376 1081344 10342 3197208 LA_51 7313 3197012 LB_51 = true := by decide +kernel
  have g_51 : Good fA 10343 LA_51 ∧ Good fB 7314 LB_51 :=
    chk2_sound (by norm_num [NMax]) ck_51
      (g_50.1.count_eq (i := 101) (by decide +kernel) (by decide +kernel))
      (g_50.2.count_eq (i := 71) (by decide +kernel) (by decide +kernel))
  have ck_52 : chk2 54525952 1081344 10443 3256051 LA_52 7385 3256332 LB_52 = true := by decide +kernel
  have g_52 : Good fA 10444 LA_52 ∧ Good fB 7386 LB_52 :=
    chk2_sound (by norm_num [NMax]) ck_52
      (g_51.1.count_eq (i := 100) (by decide +kernel) (by decide +kernel))
      (g_51.2.count_eq (i := 71) (by decide +kernel) (by decide +kernel))
  have ck_53 : chk2 55574528 1081344 10543 3314869 LA_53 7455 3314554 LB_53 = true := by decide +kernel
  have g_53 : Good fA 10544 LA_53 ∧ Good fB 7456 LB_53 :=
    chk2_sound (by norm_num [NMax]) ck_53
      (g_52.1.count_eq (i := 99) (by decide +kernel) (by decide +kernel))
      (g_52.2.count_eq (i := 69) (by decide +kernel) (by decide +kernel))
  have ck_54 : chk2 56623104 1081344 10642 3373692 LA_54 7525 3373381 LB_54 = true := by decide +kernel
  have g_54 : Good fA 10643 LA_54 ∧ Good fB 7526 LB_54 :=
    chk2_sound (by norm_num [NMax]) ck_54
      (g_53.1.count_eq (i := 98) (by decide +kernel) (by decide +kernel))
      (g_53.2.count_eq (i := 69) (by decide +kernel) (by decide +kernel))
  have ck_55 : chk2 57671680 1081344 10740 3432481 LA_55 7595 3432759 LB_55 = true := by decide +kernel
  have g_55 : Good fA 10741 LA_55 ∧ Good fB 7596 LB_55 :=
    chk2_sound (by norm_num [NMax]) ck_55
      (g_54.1.count_eq (i := 97) (by decide +kernel) (by decide +kernel))
      (g_54.2.count_eq (i := 69) (by decide +kernel) (by decide +kernel))
  have ck_56 : chk2 58720256 1081344 10837 3490964 LA_56 7663 3490734 LB_56 = true := by decide +kernel
  have g_56 : Good fA 10838 LA_56 ∧ Good fB 7664 LB_56 :=
    chk2_sound (by norm_num [NMax]) ck_56
      (g_55.1.count_eq (i := 96) (by decide +kernel) (by decide +kernel))
      (g_55.2.count_eq (i := 67) (by decide +kernel) (by decide +kernel))
  have ck_57 : chk2 59768832 1081344 10933 3549300 LA_57 7732 3550044 LB_57 = true := by decide +kernel
  have g_57 : Good fA 10934 LA_57 ∧ Good fB 7733 LB_57 :=
    chk2_sound (by norm_num [NMax]) ck_57
      (g_56.1.count_eq (i := 95) (by decide +kernel) (by decide +kernel))
      (g_56.2.count_eq (i := 68) (by decide +kernel) (by decide +kernel))
  have ck_58 : chk2 60817408 1081344 11029 3608240 LA_58 7799 3608211 LB_58 = true := by decide +kernel
  have g_58 : Good fA 11030 LA_58 ∧ Good fB 7800 LB_58 :=
    chk2_sound (by norm_num [NMax]) ck_58
      (g_57.1.count_eq (i := 95) (by decide +kernel) (by decide +kernel))
      (g_57.2.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
  have ck_59 : chk2 61865984 1081344 11123 3666139 LA_59 7866 3666576 LB_59 = true := by decide +kernel
  have g_59 : Good fA 11124 LA_59 ∧ Good fB 7867 LB_59 :=
    chk2_sound (by norm_num [NMax]) ck_59
      (g_58.1.count_eq (i := 93) (by decide +kernel) (by decide +kernel))
      (g_58.2.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
  have ck_60 : chk2 62914560 1081344 11217 3724673 LA_60 7932 3724694 LB_60 = true := by decide +kernel
  have g_60 : Good fA 11218 LA_60 ∧ Good fB 7933 LB_60 :=
    chk2_sound (by norm_num [NMax]) ck_60
      (g_59.1.count_eq (i := 93) (by decide +kernel) (by decide +kernel))
      (g_59.2.count_eq (i := 65) (by decide +kernel) (by decide +kernel))
  have ck_61 : chk2 63963136 1081344 11310 3783069 LA_61 7998 3783314 LB_61 = true := by decide +kernel
  have g_61 : Good fA 11311 LA_61 ∧ Good fB 7999 LB_61 :=
    chk2_sound (by norm_num [NMax]) ck_61
      (g_60.1.count_eq (i := 92) (by decide +kernel) (by decide +kernel))
      (g_60.2.count_eq (i := 65) (by decide +kernel) (by decide +kernel))
  have ck_62 : chk2 65011712 1081344 11403 3841668 LA_62 8063 3841215 LB_62 = true := by decide +kernel
  have g_62 : Good fA 11404 LA_62 ∧ Good fB 8064 LB_62 :=
    chk2_sound (by norm_num [NMax]) ck_62
      (g_61.1.count_eq (i := 92) (by decide +kernel) (by decide +kernel))
      (g_61.2.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
  have ck_63 : chk2 66060288 1081344 11494 3899607 LA_63 8128 3899761 LB_63 = true := by decide +kernel
  have g_63 : Good fA 11495 LA_63 ∧ Good fB 8129 LB_63 :=
    chk2_sound (by norm_num [NMax]) ck_63
      (g_62.1.count_eq (i := 90) (by decide +kernel) (by decide +kernel))
      (g_62.2.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
  have ck_64 : chk2 67108864 1081344 11585 3957973 LA_64 8192 3957809 LB_64 = true := by decide +kernel
  have g_64 : Good fA 11586 LA_64 ∧ Good fB 8193 LB_64 :=
    chk2_sound (by norm_num [NMax]) ck_64
      (g_63.1.count_eq (i := 90) (by decide +kernel) (by decide +kernel))
      (g_63.2.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
  have ck_65 : chk2 68157440 1081344 11675 4016108 LA_65 8256 4016265 LB_65 = true := by decide +kernel
  have g_65 : Good fA 11676 LA_65 ∧ Good fB 8257 LB_65 :=
    chk2_sound (by norm_num [NMax]) ck_65
      (g_64.1.count_eq (i := 89) (by decide +kernel) (by decide +kernel))
      (g_64.2.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
  have ck_66 : chk2 69206016 1081344 11765 4074480 LA_66 8320 4074960 LB_66 = true := by decide +kernel
  have g_66 : Good fA 11766 LA_66 ∧ Good fB 8321 LB_66 :=
    chk2_sound (by norm_num [NMax]) ck_66
      (g_65.1.count_eq (i := 89) (by decide +kernel) (by decide +kernel))
      (g_65.2.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
  have ck_67 : chk2 70254592 1081344 11854 4132716 LA_67 8382 4132346 LB_67 = true := by decide +kernel
  have g_67 : Good fA 11855 LA_67 ∧ Good fB 8383 LB_67 :=
    chk2_sound (by norm_num [NMax]) ck_67
      (g_66.1.count_eq (i := 88) (by decide +kernel) (by decide +kernel))
      (g_66.2.count_eq (i := 61) (by decide +kernel) (by decide +kernel))
  have ck_68 : chk2 71303168 1081344 11942 4190616 LA_68 8445 4190971 LB_68 = true := by decide +kernel
  have g_68 : Good fA 11943 LA_68 ∧ Good fB 8446 LB_68 :=
    chk2_sound (by norm_num [NMax]) ck_68
      (g_67.1.count_eq (i := 87) (by decide +kernel) (by decide +kernel))
      (g_67.2.count_eq (i := 62) (by decide +kernel) (by decide +kernel))
  have ck_69 : chk2 72351744 1081344 12029 4248408 LA_69 8506 4248286 LB_69 = true := by decide +kernel
  have g_69 : Good fA 12030 LA_69 ∧ Good fB 8507 LB_69 :=
    chk2_sound (by norm_num [NMax]) ck_69
      (g_68.1.count_eq (i := 86) (by decide +kernel) (by decide +kernel))
      (g_68.2.count_eq (i := 60) (by decide +kernel) (by decide +kernel))
  have ck_70 : chk2 73400320 1081344 12116 4306379 LA_70 8568 4306691 LB_70 = true := by decide +kernel
  have g_70 : Good fA 12117 LA_70 ∧ Good fB 8569 LB_70 :=
    chk2_sound (by norm_num [NMax]) ck_70
      (g_69.1.count_eq (i := 86) (by decide +kernel) (by decide +kernel))
      (g_69.2.count_eq (i := 61) (by decide +kernel) (by decide +kernel))
  have ck_71 : chk2 74448896 1081344 12202 4364029 LA_71 8629 4364533 LB_71 = true := by decide +kernel
  have g_71 : Good fA 12203 LA_71 ∧ Good fB 8630 LB_71 :=
    chk2_sound (by norm_num [NMax]) ck_71
      (g_70.1.count_eq (i := 85) (by decide +kernel) (by decide +kernel))
      (g_70.2.count_eq (i := 60) (by decide +kernel) (by decide +kernel))
  have ck_72 : chk2 75497472 1081344 12288 4422178 LA_72 8689 4421893 LB_72 = true := by decide +kernel
  have g_72 : Good fA 12289 LA_72 ∧ Good fB 8690 LB_72 :=
    chk2_sound (by norm_num [NMax]) ck_72
      (g_71.1.count_eq (i := 85) (by decide +kernel) (by decide +kernel))
      (g_71.2.count_eq (i := 59) (by decide +kernel) (by decide +kernel))
  have ck_73 : chk2 76546048 1081344 12373 4479895 LA_73 8750 4480501 LB_73 = true := by decide +kernel
  have g_73 : Good fA 12374 LA_73 ∧ Good fB 8751 LB_73 :=
    chk2_sound (by norm_num [NMax]) ck_73
      (g_72.1.count_eq (i := 84) (by decide +kernel) (by decide +kernel))
      (g_72.2.count_eq (i := 60) (by decide +kernel) (by decide +kernel))
  have ck_74 : chk2 77594624 1081344 12457 4537277 LA_74 8809 4537472 LB_74 = true := by decide +kernel
  have g_74 : Good fA 12458 LA_74 ∧ Good fB 8810 LB_74 :=
    chk2_sound (by norm_num [NMax]) ck_74
      (g_73.1.count_eq (i := 83) (by decide +kernel) (by decide +kernel))
      (g_73.2.count_eq (i := 58) (by decide +kernel) (by decide +kernel))
  have ck_75 : chk2 78643200 1081344 12541 4594913 LA_75 8869 4595730 LB_75 = true := by decide +kernel
  have g_75 : Good fA 12542 LA_75 ∧ Good fB 8870 LB_75 :=
    chk2_sound (by norm_num [NMax]) ck_75
      (g_74.1.count_eq (i := 83) (by decide +kernel) (by decide +kernel))
      (g_74.2.count_eq (i := 59) (by decide +kernel) (by decide +kernel))
  have ck_76 : chk2 79691776 1081344 12625 4653021 LA_76 8928 4653450 LB_76 = true := by decide +kernel
  have g_76 : Good fA 12626 LA_76 ∧ Good fB 8929 LB_76 :=
    chk2_sound (by norm_num [NMax]) ck_76
      (g_75.1.count_eq (i := 83) (by decide +kernel) (by decide +kernel))
      (g_75.2.count_eq (i := 58) (by decide +kernel) (by decide +kernel))
  have ck_77 : chk2 80740352 1081344 12708 4710770 LA_77 8986 4710494 LB_77 = true := by decide +kernel
  have g_77 : Good fA 12709 LA_77 ∧ Good fB 8987 LB_77 :=
    chk2_sound (by norm_num [NMax]) ck_77
      (g_76.1.count_eq (i := 82) (by decide +kernel) (by decide +kernel))
      (g_76.2.count_eq (i := 57) (by decide +kernel) (by decide +kernel))
  have ck_78 : chk2 81788928 1081344 12790 4768313 LA_78 9044 4768060 LB_78 = true := by decide +kernel
  have g_78 : Good fA 12791 LA_78 ∧ Good fB 9045 LB_78 :=
    chk2_sound (by norm_num [NMax]) ck_78
      (g_77.1.count_eq (i := 81) (by decide +kernel) (by decide +kernel))
      (g_77.2.count_eq (i := 57) (by decide +kernel) (by decide +kernel))
  have ck_79 : chk2 82837504 1081344 12871 4825392 LA_79 9102 4825873 LB_79 = true := by decide +kernel
  have g_79 : Good fA 12872 LA_79 ∧ Good fB 9103 LB_79 :=
    chk2_sound (by norm_num [NMax]) ck_79
      (g_78.1.count_eq (i := 80) (by decide +kernel) (by decide +kernel))
      (g_78.2.count_eq (i := 57) (by decide +kernel) (by decide +kernel))
  have ck_80 : chk2 83886080 1081344 12953 4883383 LA_80 9159 4882871 LB_80 = true := by decide +kernel
  have g_80 : Good fA 12954 LA_80 ∧ Good fB 9160 LB_80 :=
    chk2_sound (by norm_num [NMax]) ck_80
      (g_79.1.count_eq (i := 81) (by decide +kernel) (by decide +kernel))
      (g_79.2.count_eq (i := 56) (by decide +kernel) (by decide +kernel))
  have ck_81 : chk2 84934656 1081344 13033 4940196 LA_81 9216 4940115 LB_81 = true := by decide +kernel
  have g_81 : Good fA 13034 LA_81 ∧ Good fB 9217 LB_81 :=
    chk2_sound (by norm_num [NMax]) ck_81
      (g_80.1.count_eq (i := 79) (by decide +kernel) (by decide +kernel))
      (g_80.2.count_eq (i := 56) (by decide +kernel) (by decide +kernel))
  have ck_82 : chk2 85983232 1081344 13114 4998221 LA_82 9273 4997850 LB_82 = true := by decide +kernel
  have g_82 : Good fA 13115 LA_82 ∧ Good fB 9274 LB_82 :=
    chk2_sound (by norm_num [NMax]) ck_82
      (g_81.1.count_eq (i := 80) (by decide +kernel) (by decide +kernel))
      (g_81.2.count_eq (i := 56) (by decide +kernel) (by decide +kernel))
  have ck_83 : chk2 87031808 1081344 13193 5055089 LA_83 9330 5055885 LB_83 = true := by decide +kernel
  have g_83 : Good fA 13194 LA_83 ∧ Good fB 9331 LB_83 :=
    chk2_sound (by norm_num [NMax]) ck_83
      (g_82.1.count_eq (i := 78) (by decide +kernel) (by decide +kernel))
      (g_82.2.count_eq (i := 56) (by decide +kernel) (by decide +kernel))
  have ck_84 : chk2 88080384 1081344 13273 5112987 LA_84 9386 5113190 LB_84 = true := by decide +kernel
  have g_84 : Good fA 13274 LA_84 ∧ Good fB 9387 LB_84 :=
    chk2_sound (by norm_num [NMax]) ck_84
      (g_83.1.count_eq (i := 79) (by decide +kernel) (by decide +kernel))
      (g_83.2.count_eq (i := 55) (by decide +kernel) (by decide +kernel))
  have ck_85 : chk2 89128960 1081344 13351 5169697 LA_85 9441 5169759 LB_85 = true := by decide +kernel
  have g_85 : Good fA 13352 LA_85 ∧ Good fB 9442 LB_85 :=
    chk2_sound (by norm_num [NMax]) ck_85
      (g_84.1.count_eq (i := 77) (by decide +kernel) (by decide +kernel))
      (g_84.2.count_eq (i := 54) (by decide +kernel) (by decide +kernel))
  have ck_86 : chk2 90177536 1081344 13430 5227389 LA_86 9497 5227600 LB_86 = true := by decide +kernel
  have g_86 : Good fA 13431 LA_86 ∧ Good fB 9498 LB_86 :=
    chk2_sound (by norm_num [NMax]) ck_86
      (g_85.1.count_eq (i := 78) (by decide +kernel) (by decide +kernel))
      (g_85.2.count_eq (i := 55) (by decide +kernel) (by decide +kernel))
  have ck_87 : chk2 91226112 1081344 13507 5284048 LA_87 9552 5284836 LB_87 = true := by decide +kernel
  have g_87 : Good fA 13508 LA_87 ∧ Good fB 9553 LB_87 :=
    chk2_sound (by norm_num [NMax]) ck_87
      (g_86.1.count_eq (i := 76) (by decide +kernel) (by decide +kernel))
      (g_86.2.count_eq (i := 54) (by decide +kernel) (by decide +kernel))
  have ck_88 : chk2 92274688 1081344 13585 5341632 LA_88 9606 5341226 LB_88 = true := by decide +kernel
  have g_88 : Good fA 13586 LA_88 ∧ Good fB 9607 LB_88 :=
    chk2_sound (by norm_num [NMax]) ck_88
      (g_87.1.count_eq (i := 77) (by decide +kernel) (by decide +kernel))
      (g_87.2.count_eq (i := 53) (by decide +kernel) (by decide +kernel))
  have ck_89 : chk2 93323264 1081344 13662 5398741 LA_89 9661 5398898 LB_89 = true := by decide +kernel
  have g_89 : Good fA 13663 LA_89 ∧ Good fB 9662 LB_89 :=
    chk2_sound (by norm_num [NMax]) ck_89
      (g_88.1.count_eq (i := 76) (by decide +kernel) (by decide +kernel))
      (g_88.2.count_eq (i := 54) (by decide +kernel) (by decide +kernel))
  have ck_90 : chk2 94371840 1081344 13738 5455450 LA_90 9715 5455902 LB_90 = true := by decide +kernel
  have g_90 : Good fA 13739 LA_90 ∧ Good fB 9716 LB_90 :=
    chk2_sound (by norm_num [NMax]) ck_90
      (g_89.1.count_eq (i := 75) (by decide +kernel) (by decide +kernel))
      (g_89.2.count_eq (i := 53) (by decide +kernel) (by decide +kernel))
  have ck_91 : chk2 95420416 1081344 13815 5513365 LA_91 9769 5513324 LB_91 = true := by decide +kernel
  have g_91 : Good fA 13816 LA_91 ∧ Good fB 9770 LB_91 :=
    chk2_sound (by norm_num [NMax]) ck_91
      (g_90.1.count_eq (i := 76) (by decide +kernel) (by decide +kernel))
      (g_90.2.count_eq (i := 53) (by decide +kernel) (by decide +kernel))
  have ck_92 : chk2 96468992 1081344 13890 5569846 LA_92 9822 5569770 LB_92 = true := by decide +kernel
  have g_92 : Good fA 13891 LA_92 ∧ Good fB 9823 LB_92 :=
    chk2_sound (by norm_num [NMax]) ck_92
      (g_91.1.count_eq (i := 74) (by decide +kernel) (by decide +kernel))
      (g_91.2.count_eq (i := 52) (by decide +kernel) (by decide +kernel))
  have ck_93 : chk2 97517568 1081344 13965 5626705 LA_93 9876 5627671 LB_93 = true := by decide +kernel
  have g_93 : Good fA 13966 LA_93 ∧ Good fB 9877 LB_93 :=
    chk2_sound (by norm_num [NMax]) ck_93
      (g_92.1.count_eq (i := 74) (by decide +kernel) (by decide +kernel))
      (g_92.2.count_eq (i := 53) (by decide +kernel) (by decide +kernel))
  have ck_94 : chk2 98566144 1081344 14040 5683843 LA_94 9929 5684788 LB_94 = true := by decide +kernel
  have g_94 : Good fA 14041 LA_94 ∧ Good fB 9930 LB_94 :=
    chk2_sound (by norm_num [NMax]) ck_94
      (g_93.1.count_eq (i := 74) (by decide +kernel) (by decide +kernel))
      (g_93.2.count_eq (i := 52) (by decide +kernel) (by decide +kernel))
  have ck_95 : chk2 99614720 1081344 14115 5741078 LA_95 9981 5740894 LB_95 = true := by decide +kernel
  have g_95 : Good fA 14116 LA_95 ∧ Good fB 9982 LB_95 :=
    chk2_sound (by norm_num [NMax]) ck_95
      (g_94.1.count_eq (i := 74) (by decide +kernel) (by decide +kernel))
      (g_94.2.count_eq (i := 51) (by decide +kernel) (by decide +kernel))
  have ck_96 : chk2 100663296 1081344 14189 5797822 LA_96 10034 5798347 LB_96 = true := by decide +kernel
  have g_96 : Good fA 14190 LA_96 ∧ Good fB 10035 LB_96 :=
    chk2_sound (by norm_num [NMax]) ck_96
      (g_95.1.count_eq (i := 73) (by decide +kernel) (by decide +kernel))
      (g_95.2.count_eq (i := 52) (by decide +kernel) (by decide +kernel))
  have ck_97 : chk2 101711872 1081344 14263 5854932 LA_97 10086 5855132 LB_97 = true := by decide +kernel
  have g_97 : Good fA 14264 LA_97 ∧ Good fB 10087 LB_97 :=
    chk2_sound (by norm_num [NMax]) ck_97
      (g_96.1.count_eq (i := 73) (by decide +kernel) (by decide +kernel))
      (g_96.2.count_eq (i := 51) (by decide +kernel) (by decide +kernel))
  have ck_98 : chk2 102760448 1081344 14336 5911713 LA_98 10138 5912318 LB_98 = true := by decide +kernel
  have g_98 : Good fA 14337 LA_98 ∧ Good fB 10139 LB_98 :=
    chk2_sound (by norm_num [NMax]) ck_98
      (g_97.1.count_eq (i := 72) (by decide +kernel) (by decide +kernel))
      (g_97.2.count_eq (i := 51) (by decide +kernel) (by decide +kernel))
  have ck_99 : chk2 103809024 1081344 14409 5968491 LA_99 10189 5968439 LB_99 = true := by decide +kernel
  have g_99 : Good fA 14410 LA_99 ∧ Good fB 10190 LB_99 :=
    chk2_sound (by norm_num [NMax]) ck_99
      (g_98.1.count_eq (i := 72) (by decide +kernel) (by decide +kernel))
      (g_98.2.count_eq (i := 50) (by decide +kernel) (by decide +kernel))
  have ck_100 : chk2 104857600 1081344 14482 6025761 LA_100 10240 6025009 LB_100 = true := by decide +kernel
  have g_100 : Good fA 14483 LA_100 ∧ Good fB 10241 LB_100 :=
    chk2_sound (by norm_num [NMax]) ck_100
      (g_99.1.count_eq (i := 72) (by decide +kernel) (by decide +kernel))
      (g_99.2.count_eq (i := 50) (by decide +kernel) (by decide +kernel))
  have ck_101 : chk2 105906176 1081344 14554 6082307 LA_101 10292 6082761 LB_101 = true := by decide +kernel
  have g_101 : Good fA 14555 LA_101 ∧ Good fB 10293 LB_101 :=
    chk2_sound (by norm_num [NMax]) ck_101
      (g_100.1.count_eq (i := 71) (by decide +kernel) (by decide +kernel))
      (g_100.2.count_eq (i := 51) (by decide +kernel) (by decide +kernel))
  have ck_102 : chk2 106954752 1081344 14626 6139052 LA_102 10342 6138482 LB_102 = true := by decide +kernel
  have g_102 : Good fA 14627 LA_102 ∧ Good fB 10343 LB_102 :=
    chk2_sound (by norm_num [NMax]) ck_102
      (g_101.1.count_eq (i := 71) (by decide +kernel) (by decide +kernel))
      (g_101.2.count_eq (i := 49) (by decide +kernel) (by decide +kernel))
  have ck_103 : chk2 108003328 1081344 14697 6195388 LA_103 10393 6195709 LB_103 = true := by decide +kernel
  have g_103 : Good fA 14698 LA_103 ∧ Good fB 10394 LB_103 :=
    chk2_sound (by norm_num [NMax]) ck_103
      (g_102.1.count_eq (i := 70) (by decide +kernel) (by decide +kernel))
      (g_102.2.count_eq (i := 50) (by decide +kernel) (by decide +kernel))
  have ck_104 : chk2 109051904 1081344 14768 6252102 LA_104 10443 6252198 LB_104 = true := by decide +kernel
  have g_104 : Good fA 14769 LA_104 ∧ Good fB 10444 LB_104 :=
    chk2_sound (by norm_num [NMax]) ck_104
      (g_103.1.count_eq (i := 70) (by decide +kernel) (by decide +kernel))
      (g_103.2.count_eq (i := 49) (by decide +kernel) (by decide +kernel))
  have ck_105 : chk2 110100480 1081344 14839 6309098 LA_105 10493 6308977 LB_105 = true := by decide +kernel
  have g_105 : Good fA 14840 LA_105 ∧ Good fB 10494 LB_105 :=
    chk2_sound (by norm_num [NMax]) ck_105
      (g_104.1.count_eq (i := 70) (by decide +kernel) (by decide +kernel))
      (g_104.2.count_eq (i := 49) (by decide +kernel) (by decide +kernel))
  have ck_106 : chk2 111149056 1081344 14910 6365918 LA_106 10543 6365543 LB_106 = true := by decide +kernel
  have g_106 : Good fA 14911 LA_106 ∧ Good fB 10544 LB_106 :=
    chk2_sound (by norm_num [NMax]) ck_106
      (g_105.1.count_eq (i := 70) (by decide +kernel) (by decide +kernel))
      (g_105.2.count_eq (i := 49) (by decide +kernel) (by decide +kernel))
  have ck_107 : chk2 112197632 1081344 14980 6422410 LA_107 10593 6422614 LB_107 = true := by decide +kernel
  have g_107 : Good fA 14981 LA_107 ∧ Good fB 10594 LB_107 :=
    chk2_sound (by norm_num [NMax]) ck_107
      (g_106.1.count_eq (i := 69) (by decide +kernel) (by decide +kernel))
      (g_106.2.count_eq (i := 49) (by decide +kernel) (by decide +kernel))
  have ck_108 : chk2 113246208 1081344 15050 6479075 LA_108 10642 6478730 LB_108 = true := by decide +kernel
  have g_108 : Good fA 15051 LA_108 ∧ Good fB 10643 LB_108 :=
    chk2_sound (by norm_num [NMax]) ck_108
      (g_107.1.count_eq (i := 69) (by decide +kernel) (by decide +kernel))
      (g_107.2.count_eq (i := 48) (by decide +kernel) (by decide +kernel))
  have ck_109 : chk2 114294784 1081344 15119 6535018 LA_109 10691 6534902 LB_109 = true := by decide +kernel
  have g_109 : Good fA 15120 LA_109 ∧ Good fB 10692 LB_109 :=
    chk2_sound (by norm_num [NMax]) ck_109
      (g_108.1.count_eq (i := 68) (by decide +kernel) (by decide +kernel))
      (g_108.2.count_eq (i := 48) (by decide +kernel) (by decide +kernel))
  have ck_110 : chk2 115343360 1081344 15188 6591255 LA_110 10740 6591377 LB_110 = true := by decide +kernel
  have g_110 : Good fA 15189 LA_110 ∧ Good fB 10741 LB_110 :=
    chk2_sound (by norm_num [NMax]) ck_110
      (g_109.1.count_eq (i := 68) (by decide +kernel) (by decide +kernel))
      (g_109.2.count_eq (i := 48) (by decide +kernel) (by decide +kernel))
  have ck_111 : chk2 116391936 1081344 15257 6647931 LA_111 10789 6648315 LB_111 = true := by decide +kernel
  have g_111 : Good fA 15258 LA_111 ∧ Good fB 10790 LB_111 :=
    chk2_sound (by norm_num [NMax]) ck_111
      (g_110.1.count_eq (i := 68) (by decide +kernel) (by decide +kernel))
      (g_110.2.count_eq (i := 48) (by decide +kernel) (by decide +kernel))
  have ck_112 : chk2 117440512 1081344 15326 6704641 LA_112 10837 6704097 LB_112 = true := by decide +kernel
  have g_112 : Good fA 15327 LA_112 ∧ Good fB 10838 LB_112 :=
    chk2_sound (by norm_num [NMax]) ck_112
      (g_111.1.count_eq (i := 68) (by decide +kernel) (by decide +kernel))
      (g_111.2.count_eq (i := 47) (by decide +kernel) (by decide +kernel))
  have ck_113 : chk2 118489088 1081344 15394 6760882 LA_113 10886 6761403 LB_113 = true := by decide +kernel
  have g_113 : Good fA 15395 LA_113 ∧ Good fB 10887 LB_113 :=
    chk2_sound (by norm_num [NMax]) ck_113
      (g_112.1.count_eq (i := 67) (by decide +kernel) (by decide +kernel))
      (g_112.2.count_eq (i := 48) (by decide +kernel) (by decide +kernel))
  have ck_114 : chk2 119537664 1081344 15462 6817111 LA_114 10934 6817535 LB_114 = true := by decide +kernel
  have g_114 : Good fA 15463 LA_114 ∧ Good fB 10935 LB_114 :=
    chk2_sound (by norm_num [NMax]) ck_114
      (g_113.1.count_eq (i := 67) (by decide +kernel) (by decide +kernel))
      (g_113.2.count_eq (i := 47) (by decide +kernel) (by decide +kernel))
  have ck_115 : chk2 120586240 1081344 15530 6873756 LA_115 10982 6874085 LB_115 = true := by decide +kernel
  have g_115 : Good fA 15531 LA_115 ∧ Good fB 10983 LB_115 :=
    chk2_sound (by norm_num [NMax]) ck_115
      (g_114.1.count_eq (i := 67) (by decide +kernel) (by decide +kernel))
      (g_114.2.count_eq (i := 47) (by decide +kernel) (by decide +kernel))
  have ck_116 : chk2 121634816 1081344 15597 6929741 LA_116 11029 6929631 LB_116 = true := by decide +kernel
  have g_116 : Good fA 15598 LA_116 ∧ Good fB 11030 LB_116 :=
    chk2_sound (by norm_num [NMax]) ck_116
      (g_115.1.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
      (g_115.2.count_eq (i := 46) (by decide +kernel) (by decide +kernel))
  have ck_117 : chk2 122683392 1081344 15664 6985882 LA_117 11077 6986517 LB_117 = true := by decide +kernel
  have g_117 : Good fA 15665 LA_117 ∧ Good fB 11078 LB_117 :=
    chk2_sound (by norm_num [NMax]) ck_117
      (g_116.1.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
      (g_116.2.count_eq (i := 47) (by decide +kernel) (by decide +kernel))
  have ck_118 : chk2 123731968 1081344 15731 7042445 LA_118 11124 7042627 LB_118 = true := by decide +kernel
  have g_118 : Good fA 15732 LA_118 ∧ Good fB 11125 LB_118 :=
    chk2_sound (by norm_num [NMax]) ck_118
      (g_117.1.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
      (g_117.2.count_eq (i := 46) (by decide +kernel) (by decide +kernel))
  have ck_119 : chk2 124780544 1081344 15798 7099209 LA_119 11171 7098958 LB_119 = true := by decide +kernel
  have g_119 : Good fA 15799 LA_119 ∧ Good fB 11172 LB_119 :=
    chk2_sound (by norm_num [NMax]) ck_119
      (g_118.1.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
      (g_118.2.count_eq (i := 46) (by decide +kernel) (by decide +kernel))
  have ck_120 : chk2 125829120 1081344 15864 7155270 LA_120 11218 7155403 LB_120 = true := by decide +kernel
  have g_120 : Good fA 15865 LA_120 ∧ Good fB 11219 LB_120 :=
    chk2_sound (by norm_num [NMax]) ck_120
      (g_119.1.count_eq (i := 65) (by decide +kernel) (by decide +kernel))
      (g_119.2.count_eq (i := 46) (by decide +kernel) (by decide +kernel))
  have ck_121 : chk2 126877696 1081344 15930 7211588 LA_121 11264 7210877 LB_121 = true := by decide +kernel
  have g_121 : Good fA 15931 LA_121 ∧ Good fB 11265 LB_121 :=
    chk2_sound (by norm_num [NMax]) ck_121
      (g_120.1.count_eq (i := 65) (by decide +kernel) (by decide +kernel))
      (g_120.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_122 : chk2 127926272 1081344 15995 7267108 LA_122 11311 7267668 LB_122 = true := by decide +kernel
  have g_122 : Good fA 15996 LA_122 ∧ Good fB 11312 LB_122 :=
    chk2_sound (by norm_num [NMax]) ck_122
      (g_121.1.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
      (g_121.2.count_eq (i := 46) (by decide +kernel) (by decide +kernel))
  have ck_123 : chk2 128974848 1081344 16061 7323958 LA_123 11357 7323711 LB_123 = true := by decide +kernel
  have g_123 : Good fA 16062 LA_123 ∧ Good fB 11358 LB_123 :=
    chk2_sound (by norm_num [NMax]) ck_123
      (g_122.1.count_eq (i := 65) (by decide +kernel) (by decide +kernel))
      (g_122.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_124 : chk2 130023424 1081344 16126 7379899 LA_124 11403 7379685 LB_124 = true := by decide +kernel
  have g_124 : Good fA 16127 LA_124 ∧ Good fB 11404 LB_124 :=
    chk2_sound (by norm_num [NMax]) ck_124
      (g_123.1.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
      (g_123.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_125 : chk2 131072000 1081344 16191 7436133 LA_125 11449 7436001 LB_125 = true := by decide +kernel
  have g_125 : Good fA 16192 LA_125 ∧ Good fB 11450 LB_125 :=
    chk2_sound (by norm_num [NMax]) ck_125
      (g_124.1.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
      (g_124.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_126 : chk2 132120576 1081344 16255 7491587 LA_126 11495 7492336 LB_126 = true := by decide +kernel
  have g_126 : Good fA 16256 LA_126 ∧ Good fB 11496 LB_126 :=
    chk2_sound (by norm_num [NMax]) ck_126
      (g_125.1.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
      (g_125.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_127 : chk2 133169152 1081344 16320 7548248 LA_127 11540 7547840 LB_127 = true := by decide +kernel
  have g_127 : Good fA 16321 LA_127 ∧ Good fB 11541 LB_127 :=
    chk2_sound (by norm_num [NMax]) ck_127
      (g_126.1.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
      (g_126.2.count_eq (i := 44) (by decide +kernel) (by decide +kernel))
  have ck_128 : chk2 134217728 1081344 16384 7604005 LA_128 11586 7604542 LB_128 = true := by decide +kernel
  have g_128 : Good fA 16385 LA_128 ∧ Good fB 11587 LB_128 :=
    chk2_sound (by norm_num [NMax]) ck_128
      (g_127.1.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
      (g_127.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_129 : chk2 135266304 1081344 16448 7660238 LA_129 11631 7660438 LB_129 = true := by decide +kernel
  have g_129 : Good fA 16449 LA_129 ∧ Good fB 11632 LB_129 :=
    chk2_sound (by norm_num [NMax]) ck_129
      (g_128.1.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
      (g_128.2.count_eq (i := 44) (by decide +kernel) (by decide +kernel))
  have ck_130 : chk2 136314880 1081344 16512 7716369 LA_130 11676 7716234 LB_130 = true := by decide +kernel
  have g_130 : Good fA 16513 LA_130 ∧ Good fB 11677 LB_130 :=
    chk2_sound (by norm_num [NMax]) ck_130
      (g_129.1.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
      (g_129.2.count_eq (i := 44) (by decide +kernel) (by decide +kernel))
  have ck_131 : chk2 137363456 1081344 16575 7772113 LA_131 11721 7772551 LB_131 = true := by decide +kernel
  have g_131 : Good fA 16576 LA_131 ∧ Good fB 11722 LB_131 :=
    chk2_sound (by norm_num [NMax]) ck_131
      (g_130.1.count_eq (i := 62) (by decide +kernel) (by decide +kernel))
      (g_130.2.count_eq (i := 44) (by decide +kernel) (by decide +kernel))
  have ck_132 : chk2 138412032 1081344 16638 7827837 LA_132 11765 7827577 LB_132 = true := by decide +kernel
  have g_132 : Good fA 16639 LA_132 ∧ Good fB 11766 LB_132 :=
    chk2_sound (by norm_num [NMax]) ck_132
      (g_131.1.count_eq (i := 62) (by decide +kernel) (by decide +kernel))
      (g_131.2.count_eq (i := 43) (by decide +kernel) (by decide +kernel))
  have GA_132 : Good fA 16639 TA_132 := g_132.1
  have GB_132 : Good fB 11766 TB_132 := g_132.2
  have GA_131 : Good fA 16576 TA_131 := Good.append g_131.1 GA_132 (by decide +kernel)
  have GB_131 : Good fB 11722 TB_131 := Good.append g_131.2 GB_132 (by decide +kernel)
  have GA_130 : Good fA 16513 TA_130 := Good.append g_130.1 GA_131 (by decide +kernel)
  have GB_130 : Good fB 11677 TB_130 := Good.append g_130.2 GB_131 (by decide +kernel)
  have GA_129 : Good fA 16449 TA_129 := Good.append g_129.1 GA_130 (by decide +kernel)
  have GB_129 : Good fB 11632 TB_129 := Good.append g_129.2 GB_130 (by decide +kernel)
  have GA_128 : Good fA 16385 TA_128 := Good.append g_128.1 GA_129 (by decide +kernel)
  have GB_128 : Good fB 11587 TB_128 := Good.append g_128.2 GB_129 (by decide +kernel)
  have GA_127 : Good fA 16321 TA_127 := Good.append g_127.1 GA_128 (by decide +kernel)
  have GB_127 : Good fB 11541 TB_127 := Good.append g_127.2 GB_128 (by decide +kernel)
  have GA_126 : Good fA 16256 TA_126 := Good.append g_126.1 GA_127 (by decide +kernel)
  have GB_126 : Good fB 11496 TB_126 := Good.append g_126.2 GB_127 (by decide +kernel)
  have GA_125 : Good fA 16192 TA_125 := Good.append g_125.1 GA_126 (by decide +kernel)
  have GB_125 : Good fB 11450 TB_125 := Good.append g_125.2 GB_126 (by decide +kernel)
  have GA_124 : Good fA 16127 TA_124 := Good.append g_124.1 GA_125 (by decide +kernel)
  have GB_124 : Good fB 11404 TB_124 := Good.append g_124.2 GB_125 (by decide +kernel)
  have GA_123 : Good fA 16062 TA_123 := Good.append g_123.1 GA_124 (by decide +kernel)
  have GB_123 : Good fB 11358 TB_123 := Good.append g_123.2 GB_124 (by decide +kernel)
  have GA_122 : Good fA 15996 TA_122 := Good.append g_122.1 GA_123 (by decide +kernel)
  have GB_122 : Good fB 11312 TB_122 := Good.append g_122.2 GB_123 (by decide +kernel)
  have GA_121 : Good fA 15931 TA_121 := Good.append g_121.1 GA_122 (by decide +kernel)
  have GB_121 : Good fB 11265 TB_121 := Good.append g_121.2 GB_122 (by decide +kernel)
  have GA_120 : Good fA 15865 TA_120 := Good.append g_120.1 GA_121 (by decide +kernel)
  have GB_120 : Good fB 11219 TB_120 := Good.append g_120.2 GB_121 (by decide +kernel)
  have GA_119 : Good fA 15799 TA_119 := Good.append g_119.1 GA_120 (by decide +kernel)
  have GB_119 : Good fB 11172 TB_119 := Good.append g_119.2 GB_120 (by decide +kernel)
  have GA_118 : Good fA 15732 TA_118 := Good.append g_118.1 GA_119 (by decide +kernel)
  have GB_118 : Good fB 11125 TB_118 := Good.append g_118.2 GB_119 (by decide +kernel)
  have GA_117 : Good fA 15665 TA_117 := Good.append g_117.1 GA_118 (by decide +kernel)
  have GB_117 : Good fB 11078 TB_117 := Good.append g_117.2 GB_118 (by decide +kernel)
  have GA_116 : Good fA 15598 TA_116 := Good.append g_116.1 GA_117 (by decide +kernel)
  have GB_116 : Good fB 11030 TB_116 := Good.append g_116.2 GB_117 (by decide +kernel)
  have GA_115 : Good fA 15531 TA_115 := Good.append g_115.1 GA_116 (by decide +kernel)
  have GB_115 : Good fB 10983 TB_115 := Good.append g_115.2 GB_116 (by decide +kernel)
  have GA_114 : Good fA 15463 TA_114 := Good.append g_114.1 GA_115 (by decide +kernel)
  have GB_114 : Good fB 10935 TB_114 := Good.append g_114.2 GB_115 (by decide +kernel)
  have GA_113 : Good fA 15395 TA_113 := Good.append g_113.1 GA_114 (by decide +kernel)
  have GB_113 : Good fB 10887 TB_113 := Good.append g_113.2 GB_114 (by decide +kernel)
  have GA_112 : Good fA 15327 TA_112 := Good.append g_112.1 GA_113 (by decide +kernel)
  have GB_112 : Good fB 10838 TB_112 := Good.append g_112.2 GB_113 (by decide +kernel)
  have GA_111 : Good fA 15258 TA_111 := Good.append g_111.1 GA_112 (by decide +kernel)
  have GB_111 : Good fB 10790 TB_111 := Good.append g_111.2 GB_112 (by decide +kernel)
  have GA_110 : Good fA 15189 TA_110 := Good.append g_110.1 GA_111 (by decide +kernel)
  have GB_110 : Good fB 10741 TB_110 := Good.append g_110.2 GB_111 (by decide +kernel)
  have GA_109 : Good fA 15120 TA_109 := Good.append g_109.1 GA_110 (by decide +kernel)
  have GB_109 : Good fB 10692 TB_109 := Good.append g_109.2 GB_110 (by decide +kernel)
  have GA_108 : Good fA 15051 TA_108 := Good.append g_108.1 GA_109 (by decide +kernel)
  have GB_108 : Good fB 10643 TB_108 := Good.append g_108.2 GB_109 (by decide +kernel)
  have GA_107 : Good fA 14981 TA_107 := Good.append g_107.1 GA_108 (by decide +kernel)
  have GB_107 : Good fB 10594 TB_107 := Good.append g_107.2 GB_108 (by decide +kernel)
  have GA_106 : Good fA 14911 TA_106 := Good.append g_106.1 GA_107 (by decide +kernel)
  have GB_106 : Good fB 10544 TB_106 := Good.append g_106.2 GB_107 (by decide +kernel)
  have GA_105 : Good fA 14840 TA_105 := Good.append g_105.1 GA_106 (by decide +kernel)
  have GB_105 : Good fB 10494 TB_105 := Good.append g_105.2 GB_106 (by decide +kernel)
  have GA_104 : Good fA 14769 TA_104 := Good.append g_104.1 GA_105 (by decide +kernel)
  have GB_104 : Good fB 10444 TB_104 := Good.append g_104.2 GB_105 (by decide +kernel)
  have GA_103 : Good fA 14698 TA_103 := Good.append g_103.1 GA_104 (by decide +kernel)
  have GB_103 : Good fB 10394 TB_103 := Good.append g_103.2 GB_104 (by decide +kernel)
  have GA_102 : Good fA 14627 TA_102 := Good.append g_102.1 GA_103 (by decide +kernel)
  have GB_102 : Good fB 10343 TB_102 := Good.append g_102.2 GB_103 (by decide +kernel)
  have GA_101 : Good fA 14555 TA_101 := Good.append g_101.1 GA_102 (by decide +kernel)
  have GB_101 : Good fB 10293 TB_101 := Good.append g_101.2 GB_102 (by decide +kernel)
  have GA_100 : Good fA 14483 TA_100 := Good.append g_100.1 GA_101 (by decide +kernel)
  have GB_100 : Good fB 10241 TB_100 := Good.append g_100.2 GB_101 (by decide +kernel)
  have GA_99 : Good fA 14410 TA_99 := Good.append g_99.1 GA_100 (by decide +kernel)
  have GB_99 : Good fB 10190 TB_99 := Good.append g_99.2 GB_100 (by decide +kernel)
  have GA_98 : Good fA 14337 TA_98 := Good.append g_98.1 GA_99 (by decide +kernel)
  have GB_98 : Good fB 10139 TB_98 := Good.append g_98.2 GB_99 (by decide +kernel)
  have GA_97 : Good fA 14264 TA_97 := Good.append g_97.1 GA_98 (by decide +kernel)
  have GB_97 : Good fB 10087 TB_97 := Good.append g_97.2 GB_98 (by decide +kernel)
  have GA_96 : Good fA 14190 TA_96 := Good.append g_96.1 GA_97 (by decide +kernel)
  have GB_96 : Good fB 10035 TB_96 := Good.append g_96.2 GB_97 (by decide +kernel)
  have GA_95 : Good fA 14116 TA_95 := Good.append g_95.1 GA_96 (by decide +kernel)
  have GB_95 : Good fB 9982 TB_95 := Good.append g_95.2 GB_96 (by decide +kernel)
  have GA_94 : Good fA 14041 TA_94 := Good.append g_94.1 GA_95 (by decide +kernel)
  have GB_94 : Good fB 9930 TB_94 := Good.append g_94.2 GB_95 (by decide +kernel)
  have GA_93 : Good fA 13966 TA_93 := Good.append g_93.1 GA_94 (by decide +kernel)
  have GB_93 : Good fB 9877 TB_93 := Good.append g_93.2 GB_94 (by decide +kernel)
  have GA_92 : Good fA 13891 TA_92 := Good.append g_92.1 GA_93 (by decide +kernel)
  have GB_92 : Good fB 9823 TB_92 := Good.append g_92.2 GB_93 (by decide +kernel)
  have GA_91 : Good fA 13816 TA_91 := Good.append g_91.1 GA_92 (by decide +kernel)
  have GB_91 : Good fB 9770 TB_91 := Good.append g_91.2 GB_92 (by decide +kernel)
  have GA_90 : Good fA 13739 TA_90 := Good.append g_90.1 GA_91 (by decide +kernel)
  have GB_90 : Good fB 9716 TB_90 := Good.append g_90.2 GB_91 (by decide +kernel)
  have GA_89 : Good fA 13663 TA_89 := Good.append g_89.1 GA_90 (by decide +kernel)
  have GB_89 : Good fB 9662 TB_89 := Good.append g_89.2 GB_90 (by decide +kernel)
  have GA_88 : Good fA 13586 TA_88 := Good.append g_88.1 GA_89 (by decide +kernel)
  have GB_88 : Good fB 9607 TB_88 := Good.append g_88.2 GB_89 (by decide +kernel)
  have GA_87 : Good fA 13508 TA_87 := Good.append g_87.1 GA_88 (by decide +kernel)
  have GB_87 : Good fB 9553 TB_87 := Good.append g_87.2 GB_88 (by decide +kernel)
  have GA_86 : Good fA 13431 TA_86 := Good.append g_86.1 GA_87 (by decide +kernel)
  have GB_86 : Good fB 9498 TB_86 := Good.append g_86.2 GB_87 (by decide +kernel)
  have GA_85 : Good fA 13352 TA_85 := Good.append g_85.1 GA_86 (by decide +kernel)
  have GB_85 : Good fB 9442 TB_85 := Good.append g_85.2 GB_86 (by decide +kernel)
  have GA_84 : Good fA 13274 TA_84 := Good.append g_84.1 GA_85 (by decide +kernel)
  have GB_84 : Good fB 9387 TB_84 := Good.append g_84.2 GB_85 (by decide +kernel)
  have GA_83 : Good fA 13194 TA_83 := Good.append g_83.1 GA_84 (by decide +kernel)
  have GB_83 : Good fB 9331 TB_83 := Good.append g_83.2 GB_84 (by decide +kernel)
  have GA_82 : Good fA 13115 TA_82 := Good.append g_82.1 GA_83 (by decide +kernel)
  have GB_82 : Good fB 9274 TB_82 := Good.append g_82.2 GB_83 (by decide +kernel)
  have GA_81 : Good fA 13034 TA_81 := Good.append g_81.1 GA_82 (by decide +kernel)
  have GB_81 : Good fB 9217 TB_81 := Good.append g_81.2 GB_82 (by decide +kernel)
  have GA_80 : Good fA 12954 TA_80 := Good.append g_80.1 GA_81 (by decide +kernel)
  have GB_80 : Good fB 9160 TB_80 := Good.append g_80.2 GB_81 (by decide +kernel)
  have GA_79 : Good fA 12872 TA_79 := Good.append g_79.1 GA_80 (by decide +kernel)
  have GB_79 : Good fB 9103 TB_79 := Good.append g_79.2 GB_80 (by decide +kernel)
  have GA_78 : Good fA 12791 TA_78 := Good.append g_78.1 GA_79 (by decide +kernel)
  have GB_78 : Good fB 9045 TB_78 := Good.append g_78.2 GB_79 (by decide +kernel)
  have GA_77 : Good fA 12709 TA_77 := Good.append g_77.1 GA_78 (by decide +kernel)
  have GB_77 : Good fB 8987 TB_77 := Good.append g_77.2 GB_78 (by decide +kernel)
  have GA_76 : Good fA 12626 TA_76 := Good.append g_76.1 GA_77 (by decide +kernel)
  have GB_76 : Good fB 8929 TB_76 := Good.append g_76.2 GB_77 (by decide +kernel)
  have GA_75 : Good fA 12542 TA_75 := Good.append g_75.1 GA_76 (by decide +kernel)
  have GB_75 : Good fB 8870 TB_75 := Good.append g_75.2 GB_76 (by decide +kernel)
  have GA_74 : Good fA 12458 TA_74 := Good.append g_74.1 GA_75 (by decide +kernel)
  have GB_74 : Good fB 8810 TB_74 := Good.append g_74.2 GB_75 (by decide +kernel)
  have GA_73 : Good fA 12374 TA_73 := Good.append g_73.1 GA_74 (by decide +kernel)
  have GB_73 : Good fB 8751 TB_73 := Good.append g_73.2 GB_74 (by decide +kernel)
  have GA_72 : Good fA 12289 TA_72 := Good.append g_72.1 GA_73 (by decide +kernel)
  have GB_72 : Good fB 8690 TB_72 := Good.append g_72.2 GB_73 (by decide +kernel)
  have GA_71 : Good fA 12203 TA_71 := Good.append g_71.1 GA_72 (by decide +kernel)
  have GB_71 : Good fB 8630 TB_71 := Good.append g_71.2 GB_72 (by decide +kernel)
  have GA_70 : Good fA 12117 TA_70 := Good.append g_70.1 GA_71 (by decide +kernel)
  have GB_70 : Good fB 8569 TB_70 := Good.append g_70.2 GB_71 (by decide +kernel)
  have GA_69 : Good fA 12030 TA_69 := Good.append g_69.1 GA_70 (by decide +kernel)
  have GB_69 : Good fB 8507 TB_69 := Good.append g_69.2 GB_70 (by decide +kernel)
  have GA_68 : Good fA 11943 TA_68 := Good.append g_68.1 GA_69 (by decide +kernel)
  have GB_68 : Good fB 8446 TB_68 := Good.append g_68.2 GB_69 (by decide +kernel)
  have GA_67 : Good fA 11855 TA_67 := Good.append g_67.1 GA_68 (by decide +kernel)
  have GB_67 : Good fB 8383 TB_67 := Good.append g_67.2 GB_68 (by decide +kernel)
  have GA_66 : Good fA 11766 TA_66 := Good.append g_66.1 GA_67 (by decide +kernel)
  have GB_66 : Good fB 8321 TB_66 := Good.append g_66.2 GB_67 (by decide +kernel)
  have GA_65 : Good fA 11676 TA_65 := Good.append g_65.1 GA_66 (by decide +kernel)
  have GB_65 : Good fB 8257 TB_65 := Good.append g_65.2 GB_66 (by decide +kernel)
  have GA_64 : Good fA 11586 TA_64 := Good.append g_64.1 GA_65 (by decide +kernel)
  have GB_64 : Good fB 8193 TB_64 := Good.append g_64.2 GB_65 (by decide +kernel)
  have GA_63 : Good fA 11495 TA_63 := Good.append g_63.1 GA_64 (by decide +kernel)
  have GB_63 : Good fB 8129 TB_63 := Good.append g_63.2 GB_64 (by decide +kernel)
  have GA_62 : Good fA 11404 TA_62 := Good.append g_62.1 GA_63 (by decide +kernel)
  have GB_62 : Good fB 8064 TB_62 := Good.append g_62.2 GB_63 (by decide +kernel)
  have GA_61 : Good fA 11311 TA_61 := Good.append g_61.1 GA_62 (by decide +kernel)
  have GB_61 : Good fB 7999 TB_61 := Good.append g_61.2 GB_62 (by decide +kernel)
  have GA_60 : Good fA 11218 TA_60 := Good.append g_60.1 GA_61 (by decide +kernel)
  have GB_60 : Good fB 7933 TB_60 := Good.append g_60.2 GB_61 (by decide +kernel)
  have GA_59 : Good fA 11124 TA_59 := Good.append g_59.1 GA_60 (by decide +kernel)
  have GB_59 : Good fB 7867 TB_59 := Good.append g_59.2 GB_60 (by decide +kernel)
  have GA_58 : Good fA 11030 TA_58 := Good.append g_58.1 GA_59 (by decide +kernel)
  have GB_58 : Good fB 7800 TB_58 := Good.append g_58.2 GB_59 (by decide +kernel)
  have GA_57 : Good fA 10934 TA_57 := Good.append g_57.1 GA_58 (by decide +kernel)
  have GB_57 : Good fB 7733 TB_57 := Good.append g_57.2 GB_58 (by decide +kernel)
  have GA_56 : Good fA 10838 TA_56 := Good.append g_56.1 GA_57 (by decide +kernel)
  have GB_56 : Good fB 7664 TB_56 := Good.append g_56.2 GB_57 (by decide +kernel)
  have GA_55 : Good fA 10741 TA_55 := Good.append g_55.1 GA_56 (by decide +kernel)
  have GB_55 : Good fB 7596 TB_55 := Good.append g_55.2 GB_56 (by decide +kernel)
  have GA_54 : Good fA 10643 TA_54 := Good.append g_54.1 GA_55 (by decide +kernel)
  have GB_54 : Good fB 7526 TB_54 := Good.append g_54.2 GB_55 (by decide +kernel)
  have GA_53 : Good fA 10544 TA_53 := Good.append g_53.1 GA_54 (by decide +kernel)
  have GB_53 : Good fB 7456 TB_53 := Good.append g_53.2 GB_54 (by decide +kernel)
  have GA_52 : Good fA 10444 TA_52 := Good.append g_52.1 GA_53 (by decide +kernel)
  have GB_52 : Good fB 7386 TB_52 := Good.append g_52.2 GB_53 (by decide +kernel)
  have GA_51 : Good fA 10343 TA_51 := Good.append g_51.1 GA_52 (by decide +kernel)
  have GB_51 : Good fB 7314 TB_51 := Good.append g_51.2 GB_52 (by decide +kernel)
  have GA_50 : Good fA 10241 TA_50 := Good.append g_50.1 GA_51 (by decide +kernel)
  have GB_50 : Good fB 7242 TB_50 := Good.append g_50.2 GB_51 (by decide +kernel)
  have GA_49 : Good fA 10138 TA_49 := Good.append g_49.1 GA_50 (by decide +kernel)
  have GB_49 : Good fB 7169 TB_49 := Good.append g_49.2 GB_50 (by decide +kernel)
  have GA_48 : Good fA 10034 TA_48 := Good.append g_48.1 GA_49 (by decide +kernel)
  have GB_48 : Good fB 7096 TB_48 := Good.append g_48.2 GB_49 (by decide +kernel)
  have GA_47 : Good fA 9929 TA_47 := Good.append g_47.1 GA_48 (by decide +kernel)
  have GB_47 : Good fB 7022 TB_47 := Good.append g_47.2 GB_48 (by decide +kernel)
  have GA_46 : Good fA 9823 TA_46 := Good.append g_46.1 GA_47 (by decide +kernel)
  have GB_46 : Good fB 6947 TB_46 := Good.append g_46.2 GB_47 (by decide +kernel)
  have GA_45 : Good fA 9716 TA_45 := Good.append g_45.1 GA_46 (by decide +kernel)
  have GB_45 : Good fB 6871 TB_45 := Good.append g_45.2 GB_46 (by decide +kernel)
  have GA_44 : Good fA 9607 TA_44 := Good.append g_44.1 GA_45 (by decide +kernel)
  have GB_44 : Good fB 6794 TB_44 := Good.append g_44.2 GB_45 (by decide +kernel)
  have GA_43 : Good fA 9497 TA_43 := Good.append g_43.1 GA_44 (by decide +kernel)
  have GB_43 : Good fB 6716 TB_43 := Good.append g_43.2 GB_44 (by decide +kernel)
  have GA_42 : Good fA 9386 TA_42 := Good.append g_42.1 GA_43 (by decide +kernel)
  have GB_42 : Good fB 6638 TB_42 := Good.append g_42.2 GB_43 (by decide +kernel)
  have GA_41 : Good fA 9274 TA_41 := Good.append g_41.1 GA_42 (by decide +kernel)
  have GB_41 : Good fB 6558 TB_41 := Good.append g_41.2 GB_42 (by decide +kernel)
  have GA_40 : Good fA 9160 TA_40 := Good.append g_40.1 GA_41 (by decide +kernel)
  have GB_40 : Good fB 6478 TB_40 := Good.append g_40.2 GB_41 (by decide +kernel)
  have GA_39 : Good fA 9045 TA_39 := Good.append g_39.1 GA_40 (by decide +kernel)
  have GB_39 : Good fB 6396 TB_39 := Good.append g_39.2 GB_40 (by decide +kernel)
  have GA_38 : Good fA 8928 TA_38 := Good.append g_38.1 GA_39 (by decide +kernel)
  have GB_38 : Good fB 6314 TB_38 := Good.append g_38.2 GB_39 (by decide +kernel)
  have GA_37 : Good fA 8810 TA_37 := Good.append g_37.1 GA_38 (by decide +kernel)
  have GB_37 : Good fB 6230 TB_37 := Good.append g_37.2 GB_38 (by decide +kernel)
  have GA_36 : Good fA 8690 TA_36 := Good.append g_36.1 GA_37 (by decide +kernel)
  have GB_36 : Good fB 6145 TB_36 := Good.append g_36.2 GB_37 (by decide +kernel)
  have GA_35 : Good fA 8568 TA_35 := Good.append g_35.1 GA_36 (by decide +kernel)
  have GB_35 : Good fB 6060 TB_35 := Good.append g_35.2 GB_36 (by decide +kernel)
  have GA_34 : Good fA 8445 TA_34 := Good.append g_34.1 GA_35 (by decide +kernel)
  have GB_34 : Good fB 5972 TB_34 := Good.append g_34.2 GB_35 (by decide +kernel)
  have GA_33 : Good fA 8320 TA_33 := Good.append g_33.1 GA_34 (by decide +kernel)
  have GB_33 : Good fB 5884 TB_33 := Good.append g_33.2 GB_34 (by decide +kernel)
  have GA_32 : Good fA 8193 TA_32 := Good.append g_32.1 GA_33 (by decide +kernel)
  have GB_32 : Good fB 5794 TB_32 := Good.append g_32.2 GB_33 (by decide +kernel)
  have GA_31 : Good fA 8064 TA_31 := Good.append g_31.1 GA_32 (by decide +kernel)
  have GB_31 : Good fB 5703 TB_31 := Good.append g_31.2 GB_32 (by decide +kernel)
  have GA_30 : Good fA 7933 TA_30 := Good.append g_30.1 GA_31 (by decide +kernel)
  have GB_30 : Good fB 5610 TB_30 := Good.append g_30.2 GB_31 (by decide +kernel)
  have GA_29 : Good fA 7800 TA_29 := Good.append g_29.1 GA_30 (by decide +kernel)
  have GB_29 : Good fB 5516 TB_29 := Good.append g_29.2 GB_30 (by decide +kernel)
  have GA_28 : Good fA 7664 TA_28 := Good.append g_28.1 GA_29 (by decide +kernel)
  have GB_28 : Good fB 5420 TB_28 := Good.append g_28.2 GB_29 (by decide +kernel)
  have GA_27 : Good fA 7526 TA_27 := Good.append g_27.1 GA_28 (by decide +kernel)
  have GB_27 : Good fB 5322 TB_27 := Good.append g_27.2 GB_28 (by decide +kernel)
  have GA_26 : Good fA 7385 TA_26 := Good.append g_26.1 GA_27 (by decide +kernel)
  have GB_26 : Good fB 5223 TB_26 := Good.append g_26.2 GB_27 (by decide +kernel)
  have GA_25 : Good fA 7242 TA_25 := Good.append g_25.1 GA_26 (by decide +kernel)
  have GB_25 : Good fB 5121 TB_25 := Good.append g_25.2 GB_26 (by decide +kernel)
  have GA_24 : Good fA 7095 TA_24 := Good.append g_24.1 GA_25 (by decide +kernel)
  have GB_24 : Good fB 5018 TB_24 := Good.append g_24.2 GB_25 (by decide +kernel)
  have GA_23 : Good fA 6946 TA_23 := Good.append g_23.1 GA_24 (by decide +kernel)
  have GB_23 : Good fB 4912 TB_23 := Good.append g_23.2 GB_24 (by decide +kernel)
  have GA_22 : Good fA 6793 TA_22 := Good.append g_22.1 GA_23 (by decide +kernel)
  have GB_22 : Good fB 4804 TB_22 := Good.append g_22.2 GB_23 (by decide +kernel)
  have GA_21 : Good fA 6637 TA_21 := Good.append g_21.1 GA_22 (by decide +kernel)
  have GB_21 : Good fB 4694 TB_21 := Good.append g_21.2 GB_22 (by decide +kernel)
  have GA_20 : Good fA 6477 TA_20 := Good.append g_20.1 GA_21 (by decide +kernel)
  have GB_20 : Good fB 4581 TB_20 := Good.append g_20.2 GB_21 (by decide +kernel)
  have GA_19 : Good fA 6313 TA_19 := Good.append g_19.1 GA_20 (by decide +kernel)
  have GB_19 : Good fB 4465 TB_19 := Good.append g_19.2 GB_20 (by decide +kernel)
  have GA_18 : Good fA 6145 TA_18 := Good.append g_18.1 GA_19 (by decide +kernel)
  have GB_18 : Good fB 4346 TB_18 := Good.append g_18.2 GB_19 (by decide +kernel)
  have GA_17 : Good fA 5972 TA_17 := Good.append g_17.1 GA_18 (by decide +kernel)
  have GB_17 : Good fB 4224 TB_17 := Good.append g_17.2 GB_18 (by decide +kernel)
  have GA_16 : Good fA 5794 TA_16 := Good.append g_16.1 GA_17 (by decide +kernel)
  have GB_16 : Good fB 4097 TB_16 := Good.append g_16.2 GB_17 (by decide +kernel)
  have GA_15 : Good fA 5610 TA_15 := Good.append g_15.1 GA_16 (by decide +kernel)
  have GB_15 : Good fB 3967 TB_15 := Good.append g_15.2 GB_16 (by decide +kernel)
  have GA_14 : Good fA 5419 TA_14 := Good.append g_14.1 GA_15 (by decide +kernel)
  have GB_14 : Good fB 3833 TB_14 := Good.append g_14.2 GB_15 (by decide +kernel)
  have GA_13 : Good fA 5222 TA_13 := Good.append g_13.1 GA_14 (by decide +kernel)
  have GB_13 : Good fB 3694 TB_13 := Good.append g_13.2 GB_14 (by decide +kernel)
  have GA_12 : Good fA 5018 TA_12 := Good.append g_12.1 GA_13 (by decide +kernel)
  have GB_12 : Good fB 3549 TB_12 := Good.append g_12.2 GB_13 (by decide +kernel)
  have GA_11 : Good fA 4804 TA_11 := Good.append g_11.1 GA_12 (by decide +kernel)
  have GB_11 : Good fB 3398 TB_11 := Good.append g_11.2 GB_12 (by decide +kernel)
  have GA_10 : Good fA 4580 TA_10 := Good.append g_10.1 GA_11 (by decide +kernel)
  have GB_10 : Good fB 3240 TB_10 := Good.append g_10.2 GB_11 (by decide +kernel)
  have GA_9 : Good fA 4345 TA_9 := Good.append g_9.1 GA_10 (by decide +kernel)
  have GB_9 : Good fB 3073 TB_9 := Good.append g_9.2 GB_10 (by decide +kernel)
  have GA_8 : Good fA 4097 TA_8 := Good.append g_8.1 GA_9 (by decide +kernel)
  have GB_8 : Good fB 2898 TB_8 := Good.append g_8.2 GB_9 (by decide +kernel)
  have GA_7 : Good fA 3832 TA_7 := Good.append g_7.1 GA_8 (by decide +kernel)
  have GB_7 : Good fB 2711 TB_7 := Good.append g_7.2 GB_8 (by decide +kernel)
  have GA_6 : Good fA 3548 TA_6 := Good.append g_6.1 GA_7 (by decide +kernel)
  have GB_6 : Good fB 2510 TB_6 := Good.append g_6.2 GB_7 (by decide +kernel)
  have GA_5 : Good fA 3239 TA_5 := Good.append g_5.1 GA_6 (by decide +kernel)
  have GB_5 : Good fB 2291 TB_5 := Good.append g_5.2 GB_6 (by decide +kernel)
  have GA_4 : Good fA 2897 TA_4 := Good.append g_4.1 GA_5 (by decide +kernel)
  have GB_4 : Good fB 2049 TB_4 := Good.append g_4.2 GB_5 (by decide +kernel)
  have GA_3 : Good fA 2509 TA_3 := Good.append g_3.1 GA_4 (by decide +kernel)
  have GB_3 : Good fB 1775 TB_3 := Good.append g_3.2 GB_4 (by decide +kernel)
  have GA_2 : Good fA 2049 TA_2 := Good.append g_2.1 GA_3 (by decide +kernel)
  have GB_2 : Good fB 1450 TB_2 := Good.append g_2.2 GB_3 (by decide +kernel)
  have GA_1 : Good fA 1449 TA_1 := Good.append g_1.1 GA_2 (by decide +kernel)
  have GB_1 : Good fB 1025 TB_1 := Good.append g_1.2 GB_2 (by decide +kernel)
  have GA_0 : Good fA 1 TA_0 := Good.append g_0.1 GA_1 (by decide +kernel)
  have GB_0 : Good fB 1 TB_0 := Good.append g_0.2 GB_1 (by decide +kernel)
  exact ⟨Good.append (base0 fA hc0A) GA_0 rfl, Good.append (base0 fB hc0B) GB_0 rfl⟩


theorem tabA_length : tabA.length = 16690 := by decide +kernel

theorem tabB_length : tabB.length = 11802 := by decide +kernel

/-- `π(k(k+1)/2) = tabA[k]` for `k ≤ 16689`. -/
theorem primeCounting_tri (k : ℕ) (hk : k ≤ 16689) :
    Nat.primeCounting (k * (k + 1) / 2) = tabA.getD k 0 := by
  rw [← count_fA]
  have h := goodAB.1 k (by rw [tabA_length]; omega)
  rwa [zero_add] at h

/-- `π(m ^ 2) = tabB[m]` for `m ≤ 11801`. -/
theorem primeCounting_sq (m : ℕ) (hm : m ≤ 11801) :
    Nat.primeCounting (m ^ 2) = tabB.getD m 0 := by
  rw [← count_fB]
  have h := goodAB.2 m (by rw [tabB_length]; omega)
  rwa [zero_add] at h

theorem tri_mono {k k' : ℕ} (h : k ≤ k') : k * (k + 1) / 2 ≤ k' * (k' + 1) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

theorem sq_mono {m m' : ℕ} (h : m ≤ m') : m ^ 2 ≤ m' ^ 2 := Nat.pow_le_pow_left h 2

/-! ## A merge of two sorted lists -/

/-- Adjacent entries are in order. -/
def sortedB : List ℕ → Bool
  | a :: b :: l => decide (a ≤ b) && sortedB (b :: l)
  | _ => true

theorem sortedB_tail {a : ℕ} {l : List ℕ} (h : sortedB (a :: l) = true) : sortedB l = true := by
  match l, h with
  | [], _ => rfl
  | b :: l, h =>
    simp only [sortedB, Bool.and_eq_true] at h
    exact h.2

theorem sortedB_head {a : ℕ} : ∀ {l : List ℕ}, sortedB (a :: l) = true → ∀ x ∈ l, a ≤ x
  | [], _, x, hx => by simp at hx
  | b :: l, h, x, hx => by
    simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact le_trans h.1 (sortedB_head h.2 x hx)

/-- The common values of two sorted lists, by a merge with fuel `n`. -/
def common : ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | _ + 1, _ :: _, [] => []
  | n + 1, a :: as, b :: bs =>
    if a < b then common n as (b :: bs)
    else if b < a then common n (a :: as) bs
    else a :: common n as bs

theorem mem_common : ∀ (n : ℕ) (as bs : List ℕ), as.length + bs.length ≤ n →
    sortedB as = true → sortedB bs = true → ∀ x, x ∈ as → x ∈ bs → x ∈ common n as bs
  | 0, as, bs, hn, _, _, x, hx, _ => by
    have : as = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp at hx
  | _ + 1, [], _, _, _, _, x, hx, _ => by simp at hx
  | _ + 1, _ :: _, [], _, _, _, x, _, hy => by simp at hy
  | n + 1, a :: as, b :: bs, hn, hsa, hsb, x, hx, hy => by
    simp only [List.length_cons] at hn
    simp only [common]
    by_cases h1 : a < b
    · rw [if_pos h1]
      apply mem_common n as (b :: bs) (by simp only [List.length_cons]; omega)
        (sortedB_tail hsa) hsb x _ hy
      rcases List.mem_cons.mp hx with hxa | hx'
      · exfalso
        rcases List.mem_cons.mp hy with h | h
        · omega
        · have := sortedB_head hsb x h
          omega
      · exact hx'
    · rw [if_neg h1]
      by_cases h2 : b < a
      · rw [if_pos h2]
        apply mem_common n (a :: as) bs (by simp only [List.length_cons]; omega)
          hsa (sortedB_tail hsb) x hx _
        rcases List.mem_cons.mp hy with hyb | hy'
        · exfalso
          rcases List.mem_cons.mp hx with h | h
          · omega
          · have := sortedB_head hsa x h
            omega
        · exact hy'
      · rw [if_neg h2]
        by_cases hxa : x = a
        · rw [hxa]
          exact List.mem_cons_self
        · apply List.mem_cons_of_mem
          apply mem_common n as bs (by omega) (sortedB_tail hsa) (sortedB_tail hsb) x
          · exact (List.mem_cons.mp hx).resolve_left hxa
          · exact (List.mem_cons.mp hy).resolve_left (by omega)

/-! ## The pair check for `n = 7872413` -/

/-- `π(T_k)` for `k ≤ 16688`. -/
def AL : List ℕ := tabA.take 16689

/-- `7872413 - π(m ^ 2)` for `m = 11800, ..., 0`, in increasing order. -/
def BL : List ℕ := ((tabB.take 11801).map (fun y => 7872413 - y)).reverse

theorem merge_check : sortedB AL = true ∧ sortedB BL = true ∧ AL.length + BL.length ≤ 30000 ∧
    common 30000 AL BL = [6450605] := by
  decide +kernel

theorem table_values : tabA.getD 16689 0 = 7873136 ∧ tabB.getD 11801 0 = 7872809 ∧
    tabA.getD 15014 0 = 6449818 ∧ tabA.getD 15015 0 = 6450605 ∧ tabA.getD 15016 0 = 6451439 ∧
    tabB.getD 4748 0 = 1421226 ∧ tabB.getD 4749 0 = 1421808 ∧ tabB.getD 4750 0 = 1422368 := by
  decide +kernel

theorem getD_mem_take {L : List ℕ} {n k : ℕ} (hk : k < n) (hkL : k < L.length) :
    L.getD k 0 ∈ L.take n := by
  rw [List.getD_eq_getElem _ _ hkL]
  have h : k < (L.take n).length := by rw [List.length_take]; omega
  have hm := List.getElem_mem h
  rwa [List.getElem_take] at hm

/-- The only representation of `7872413` is `(15015, 4749)`. -/
theorem uniq (k m : ℕ)
    (heq : Nat.primeCounting (k * (k + 1) / 2) + Nat.primeCounting (m ^ 2) = 7872413) :
    k = 15015 ∧ m = 4749 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := table_values
  obtain ⟨s1, s2, s3, s4⟩ := merge_check
  have hk : k ≤ 16688 := by
    by_contra h
    have := Nat.monotone_primeCounting (tri_mono (show 16689 ≤ k by omega))
    rw [primeCounting_tri 16689 le_rfl, v1] at this
    omega
  have hm : m ≤ 11800 := by
    by_contra h
    have := Nat.monotone_primeCounting (sq_mono (show 11801 ≤ m by omega))
    rw [primeCounting_sq 11801 le_rfl, v2] at this
    omega
  rw [primeCounting_tri k (by omega), primeCounting_sq m (by omega)] at heq
  have hA : tabA.getD k 0 ∈ AL := getD_mem_take (by omega) (by rw [tabA_length]; omega)
  have hB0 : tabB.getD m 0 ∈ tabB.take 11801 :=
    getD_mem_take (by omega) (by rw [tabB_length]; omega)
  have hB : tabA.getD k 0 ∈ BL := by
    rw [BL, List.mem_reverse, show tabA.getD k 0 = 7872413 - tabB.getD m 0 by omega]
    exact List.mem_map.mpr ⟨_, hB0, rfl⟩
  have hc := mem_common 30000 AL BL s3 s1 s2 _ hA hB
  rw [s4, List.mem_singleton] at hc
  constructor
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := Nat.monotone_primeCounting (tri_mono (show k ≤ 15014 by omega))
      rw [primeCounting_tri k (by omega), primeCounting_tri 15014 (by norm_num), v3] at this
      omega
    · have := Nat.monotone_primeCounting (tri_mono (show 15016 ≤ k by omega))
      rw [primeCounting_tri k (by omega), primeCounting_tri 15016 (by norm_num), v5] at this
      omega
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := Nat.monotone_primeCounting (sq_mono (show m ≤ 4748 by omega))
      rw [primeCounting_sq m (by omega), primeCounting_sq 4748 (by norm_num), v6] at this
      omega
    · have := Nat.monotone_primeCounting (sq_mono (show 4750 ≤ m by omega))
      rw [primeCounting_sq m (by omega), primeCounting_sq 4750 (by norm_num), v8] at this
      omega

theorem rep (k m : ℕ) (hk : k = 15015) (hm : m = 4749) :
    Nat.primeCounting (k * (k + 1) / 2) + Nat.primeCounting (m ^ 2) = 7872413 := by
  have e1 := primeCounting_tri k (by omega)
  have e2 := primeCounting_sq m (by omega)
  obtain ⟨-, -, -, v4, -, -, v7, -⟩ := table_values
  subst hk hm
  omega

theorem pairs_eq : pairs 7872413 = {(15015, 4749)} := by
  ext ⟨k, m⟩
  rw [pairs, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨_, heq⟩
    exact uniq k m heq
  · rintro ⟨hk, hm⟩
    refine ⟨?_, rep k m hk hm⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    omega

theorem a_eq_one : a 7872413 = 1 := by
  rw [a, pairs_eq, Finset.card_singleton]

end OMA.A262999Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a262999.main) := by
  intro h
  have h1 := h.2 7872413 OMA.A262999Disproof.a_eq_one
  simp at h1
