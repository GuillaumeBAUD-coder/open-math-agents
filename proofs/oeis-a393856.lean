import OMAStatements.S_oeis_a393856
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a393856

open OMA.S_oeis_a393856

/-- Geometric series `x / (1 - c * x) = ∑_{n ≥ 1} c^(n - 1) * x^n`. -/
private def geom {R : Type*} [CommRing R] (c : R) (n : ℕ) : R :=
  if n = 0 then 0 else c ^ (n - 1)

/-- Power-of-two indicator series `∑_{k ≥ 0} x^(2^k)` in `(ZMod 2)[[x]]`. -/
private noncomputable def pow2Seq (n : ℕ) : ZMod 2 := by
  classical exact if ∃ k : ℕ, n = 2 ^ k then 1 else 0

private lemma powSeq_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : ℕ → R) :
    ∀ k n : ℕ, φ (powSeq g k n) = powSeq (fun i => φ (g i)) k n := by
  intro k
  induction k with
  | zero => intro n; dsimp [powSeq]; split_ifs <;> simp
  | succ k ih => intro n; simp only [powSeq, map_sum, map_mul, ih]

private lemma comp_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f g : ℕ → R) (n : ℕ) :
    φ (comp f g n) = comp (fun i => φ (f i)) (fun i => φ (g i)) n := by
  simp only [comp, map_sum, map_mul, powSeq_map]

private lemma powSeq_zero_of_lt {R : Type*} [CommRing R] {g : ℕ → R} (hg0 : g 0 = 0) :
    ∀ k n : ℕ, n < k → powSeq g k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi0 : i = 0
    · subst hi0; simp [hg0]
    · rw [ih (n - i) (by omega), mul_zero]

private lemma powSeq_diag {R : Type*} [CommRing R] {g : ℕ → R} (hg0 : g 0 = 0) :
    ∀ k : ℕ, powSeq g k k = (g 1) ^ k := by
  intro k
  induction k with
  | zero => simp [powSeq]
  | succ k ih =>
    simp only [powSeq]
    have hterm : ∀ i ∈ Finset.range (k + 2),
        g i * powSeq g k (k + 1 - i) = if i = 1 then g 1 * (g 1) ^ k else 0 := by
      intro i hi
      have hik : i ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hi0 : i = 0
      · subst hi0; simp [hg0]
      · by_cases hi1 : i = 1
        · subst hi1; simp [ih]
        · rw [if_neg hi1, powSeq_zero_of_lt hg0 k (k + 1 - i) (by omega), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ 1,
      if_pos (Finset.mem_range.mpr (by omega)), pow_succ']

private lemma powSeq_congr {R : Type*} [CommRing R] {g1 g2 : ℕ → R} {N : ℕ}
    (hg : ∀ i ≤ N, g1 i = g2 i) : ∀ k n : ℕ, n ≤ N → powSeq g1 k n = powSeq g2 k n := by
  intro k
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hg i (le_trans hin hn), ih (n - i) (by omega)]

/-- Hockey-stick identity: `∑_{j=0}^{m} C(j + k, k) = C(m + k + 1, k + 1)`. -/
private lemma hockey_stick (k : ℕ) :
    ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), Nat.choose (j + k) k = Nat.choose (m + k + 1) (k + 1) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : m + 1 + k = (m + k) + 1 := by omega
    rw [h1, add_comm, ← Nat.choose_succ_succ]

private lemma powSeq_geom {R : Type*} [CommRing R] (b : R) :
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ,
      powSeq (geom b) k n = if k ≤ n then (Nat.choose (n - 1) (k - 1) : R) * b ^ (n - k) else 0 := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · intro n
      simp only [powSeq, geom]
      by_cases hn : 1 ≤ n
      · rw [if_pos hn]
        have hterm : ∀ i ∈ Finset.range (n + 1),
            (if i = 0 then (0 : R) else b ^ (i - 1)) * (if n - i = 0 then 1 else 0) =
            if i = n then b ^ (n - 1) else 0 := by
          intro i hi
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          by_cases h : i = n
          · subst h; simp [show i ≠ 0 by omega]
          · simp [h, show n - i ≠ 0 by omega]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ n,
          if_pos (Finset.mem_range.mpr (Nat.lt_succ_self n))]
        simp
      · have hn0 : n = 0 := by omega
        subst hn0; simp
    · intro n
      simp only [powSeq]
      have hih := ih hkpos
      by_cases hkn : k + 1 ≤ n
      · rw [if_pos hkn]
        have hterm : ∀ i ∈ Finset.range (n + 1),
            geom b i * powSeq (geom b) k (n - i) =
            if 1 ≤ i ∧ i ≤ n - k then
              (Nat.choose (n - i - 1) (k - 1) : R) * b ^ (n - (k + 1))
            else 0 := by
          intro i hi
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [hih (n - i)]
          dsimp [geom]
          by_cases hi0 : i = 0
          · subst hi0; simp
          · rw [if_neg hi0]
            by_cases hle : k ≤ n - i
            · rw [if_pos hle, if_pos ⟨by omega, by omega⟩]
              have hexp : (i - 1) + (n - i - k) = n - (k + 1) := by omega
              rw [← mul_assoc, mul_comm (b ^ (i - 1)), mul_assoc, ← pow_add, hexp]
            · rw [if_neg hle, if_neg (by omega), mul_zero]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.sum_mul]
        congr 1
        have hbij : ∑ i ∈ (Finset.range (n + 1)).filter (fun i => 1 ≤ i ∧ i ≤ n - k),
            (Nat.choose (n - i - 1) (k - 1) : R) =
            ∑ j ∈ Finset.range (n - k), (Nat.choose (j + (k - 1)) (k - 1) : R) := by
          refine Finset.sum_bij (fun i _ => n - i - k) ?_ ?_ ?_ ?_
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
          · intro i1 h1 i2 h2 heq; simp only [Finset.mem_filter, Finset.mem_range] at h1 h2; omega
          · intro j hj
            have hj_lt : j < n - k := Finset.mem_range.mp hj
            refine ⟨n - k - j, ?_, by omega⟩
            simp only [Finset.mem_filter, Finset.mem_range]; omega
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi; congr 2; omega
        rw [hbij, ← Nat.cast_sum]
        have hnk : n - k = (n - k - 1) + 1 := by omega
        rw [hnk, hockey_stick (k - 1) (n - k - 1)]
        congr 2 <;> omega
      · rw [if_neg hkn]
        refine Finset.sum_eq_zero (fun i hi => ?_)
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [hih (n - i)]
        dsimp [geom]
        by_cases hi0 : i = 0
        · subst hi0; simp
        · rw [if_neg hi0, if_neg (by omega), mul_zero]

private lemma comp_geom {R : Type*} [CommRing R] (a b : R) :
    comp (geom a) (geom b) = geom (a + b) := by
  ext n
  cases n with
  | zero => simp [comp, geom]
  | succ n =>
    simp only [comp, geom, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [Finset.sum_range_succ']
    simp only [if_true, zero_mul, add_zero]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (if k + 1 = 0 then (0 : R) else a ^ (k + 1 - 1)) * powSeq (geom b) (k + 1) (n + 1) =
        a ^ k * b ^ (n - k) * (Nat.choose n k : R) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, powSeq_geom b (k + 1) (by omega) (n + 1),
        if_pos (by omega), Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.succ_sub_succ]
      ring
    rw [Finset.sum_congr rfl hterm, ← add_pow]

/-- Powers of `x + x^2` in `(ZMod 2)[[x]]`: `[x^n] (x + x^2)^k = C(k, n - k)` (for `k ≤ n ≤ 2k`). -/
private def xPlusX2 (n : ℕ) : ZMod 2 :=
  if n = 1 ∨ n = 2 then 1 else 0

private lemma powSeq_xPlusX2 :
    ∀ k n : ℕ, powSeq xPlusX2 k n = if k ≤ n then (Nat.choose k (n - k) : ZMod 2) else 0 := by
  intro k
  induction k with
  | zero =>
    intro n
    dsimp [powSeq]
    cases n with
    | zero => simp
    | succ n => simp
  | succ k ih =>
    intro n
    simp only [powSeq]
    have hterm : ∀ i ∈ Finset.range (n + 1),
        xPlusX2 i * powSeq xPlusX2 k (n - i) =
        (if i = 1 then powSeq xPlusX2 k (n - 1) else 0) +
        (if i = 2 then powSeq xPlusX2 k (n - 2) else 0) := by
      intro i _
      dsimp [xPlusX2]
      by_cases h1 : i = 1
      · subst h1; simp
      · by_cases h2 : i = 2
        · subst h2; simp
        · simp [h1, h2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_ite_eq' _ 1, Finset.sum_ite_eq' _ 2]
    by_cases hn1 : 1 ≤ n
    · rw [if_pos (Finset.mem_range.mpr (by omega)), ih (n - 1)]
      by_cases hn2 : 2 ≤ n
      · rw [if_pos (Finset.mem_range.mpr (by omega)), ih (n - 2)]
        by_cases hkn : k + 1 ≤ n
        · rw [if_pos hkn, if_pos (by omega)]
          by_cases hkn2 : k ≤ n - 2
          · rw [if_pos hkn2]
            have h1 : n - 1 - k = (n - 2 - k) + 1 := by omega
            have h2 : n - (k + 1) = (n - 2 - k) + 1 := by omega
            rw [h1, h2, Nat.choose_succ_succ, Nat.cast_add, add_comm]
          · rw [if_neg hkn2, add_zero]
            have h1 : n - 1 - k = 0 := by omega
            have h2 : n - (k + 1) = 0 := by omega
            rw [h1, h2]; simp
        · rw [if_neg hkn, if_neg (by omega), if_neg (by omega), add_zero]
      · rw [if_neg (show 2 ∉ Finset.range (n + 1) by simp only [Finset.mem_range]; omega), add_zero]
        have hn1eq : n = 1 := by omega
        subst hn1eq
        cases k with
        | zero => simp
        | succ k => simp
    · have hn0 : n = 0 := by omega
      subst hn0; simp

/-- In `ZMod 2`, `(x + x^2)^(2^j) = x^(2^j) + x^(2^(j+1))`! -/
private lemma powSeq_xPlusX2_two_pow (j n : ℕ) :
    powSeq xPlusX2 (2 ^ j) n =
      (if n = 2 ^ j then 1 else 0) + (if n = 2 ^ (j + 1) then 1 else 0) := by
  rw [powSeq_xPlusX2]
  have h2pos : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
  by_cases h1 : n = 2 ^ j
  · subst h1
    have hne : 2 ^ j ≠ 2 ^ (j + 1) := by rw [pow_succ]; omega
    simp [hne]
  · by_cases h2 : n = 2 ^ (j + 1)
    · subst h2
      have hle : 2 ^ j ≤ 2 ^ (j + 1) := by rw [pow_succ]; omega
      have hsub : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by rw [pow_succ]; omega
      simp [h1, hle, hsub]
    · rw [if_neg h1, if_neg h2, add_zero]
      by_cases hle : 2 ^ j ≤ n
      · rw [if_pos hle]
        by_cases hgt : 2 ^ j < n - 2 ^ j
        · rw [Nat.choose_eq_zero_of_lt hgt, Nat.cast_zero]
        · -- `0 < n - 2^j < 2^j`, so `2 ∣ C(2^j, n - 2^j)`!
          set r := n - 2 ^ j
          have hr0 : 0 < r := by omega
          have hrlt : r < 2 ^ j := by
            have : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
            omega
          have hdvd : 2 ∣ Nat.choose (2 ^ j) r :=
            Nat.Prime.dvd_choose_pow Nat.prime_two (Nat.ne_of_gt hr0) (Nat.ne_of_lt hrlt)
          exact (ZMod.natCast_eq_zero_iff _ 2).mpr hdvd
      · rw [if_neg hle]

/-- Telescoping composition in `(ZMod 2)[[x]]`: `comp pow2Seq xPlusX2 n = [n = 1]`. -/
private lemma comp_pow2Seq_xPlusX2 (n : ℕ) :
    comp pow2Seq xPlusX2 n = if n = 1 then 1 else 0 := by
  classical
  simp only [comp]
  -- Sum over `k ∈ range (n + 1)` with `k = 2^j` is a sum over `j ∈ range (n + 1)`!
  have hbij : ∑ k ∈ Finset.range (n + 1), pow2Seq k * powSeq xPlusX2 k n =
      ∑ j ∈ Finset.range (n + 1), powSeq xPlusX2 (2 ^ j) n := by
    have hfilt : ∑ k ∈ Finset.range (n + 1), pow2Seq k * powSeq xPlusX2 k n =
        ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ∃ j : ℕ, k = 2 ^ j), powSeq xPlusX2 k n := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      dsimp [pow2Seq]; split_ifs <;> simp
    rw [hfilt]
    have hsub : ∑ j ∈ Finset.range (n + 1), powSeq xPlusX2 (2 ^ j) n =
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => 2 ^ j ≤ n), powSeq xPlusX2 (2 ^ j) n := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hj : 2 ^ j ≤ n
      · rw [if_pos hj]
      · rw [if_neg hj, powSeq_zero_of_lt (by decide : xPlusX2 0 = 0) (2 ^ j) n (by omega)]
    rw [hsub]
    refine (Finset.sum_bij (fun j _ => 2 ^ j) ?_ ?_ ?_ ?_).symm
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨by omega, ⟨j, rfl⟩⟩
    · intro j1 _ j2 _ heq
      exact Nat.pow_right_injective (by norm_num : 1 < 2) heq
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨j, rfl⟩ := hk.2
      have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
      have h2le : 2 ^ j ≤ n := by omega
      refine ⟨j, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, h2le⟩
    · intro _ _; rfl
  rw [hbij]
  have htele : ∑ j ∈ Finset.range (n + 1), powSeq xPlusX2 (2 ^ j) n =
      (if n = 2 ^ 0 then (1 : ZMod 2) else 0) + (if n = 2 ^ (n + 1) then 1 else 0) := by
    have hrew : ∑ j ∈ Finset.range (n + 1), powSeq xPlusX2 (2 ^ j) n =
        ∑ j ∈ Finset.range (n + 1),
          ((if n = 2 ^ j then (1 : ZMod 2) else 0) + (if n = 2 ^ (j + 1) then 1 else 0)) :=
      Finset.sum_congr rfl (fun j _ => powSeq_xPlusX2_two_pow j n)
    rw [hrew]
    -- In `ZMod 2`, `x + x = 0`, so `∑_{j=0}^m (f j + f (j+1)) = f 0 + f (m+1)`!
    have hgen : ∀ (m : ℕ) (f : ℕ → ZMod 2),
        ∑ j ∈ Finset.range m, (f j + f (j + 1)) = f 0 + f m := by
      intro m f
      induction m with
      | zero =>
        simp only [Finset.sum_range_zero]
        have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
        exact (h2 (f 0)).symm
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
        calc f 0 + f m + (f m + f (m + 1))
            = f 0 + (f m + f m) + f (m + 1) := by ring
          _ = f 0 + 0 + f (m + 1) := by rw [h2]
          _ = f 0 + f (m + 1) := by ring
    exact hgen (n + 1) (fun j => if n = 2 ^ j then 1 else 0)
  rw [htele, pow_zero]
  have hgt : n < 2 ^ (n + 1) := lt_trans (Nat.lt_succ_self n) Nat.lt_two_pow_self
  rw [if_neg (Nat.ne_of_lt hgt), add_zero]

private lemma prove_a393856 (a : ℕ → ℤ) (ha0 : a 0 = 0)
    (harec : ∀ n : ℕ, comp a (innerSeq a) n = if n = 1 then 1 else 0)
    (n : ℕ) (hn : 1 ≤ n) :
    a n ≡ 1 [ZMOD 5] ∧ (Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  -- First, `a 1 = 1` from `comp a (innerSeq a) 1 = 1`!
  have ha1 : a 1 = 1 := by
    have h := harec 1
    simp only [comp, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      powSeq, innerSeq, ha0, zero_mul, ↓reduceIte] at h
    simpa using h
  -- Part 1: mod 5 (`a k ≡ 1 (mod 5)` for `k ≥ 1`)
  let φ : ℤ →+* ZMod 5 := Int.castRingHom (ZMod 5)
  have hmod5 : ∀ k : ℕ, φ (a k) = geom (1 : ZMod 5) k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [ha0, geom]
      · have hcomp := congr_arg φ (harec k)
        rw [comp_map] at hcomp
        have hinner : ∀ i ≤ k, φ (innerSeq a i) = geom (-1 : ZMod 5) i := by
          intro i hi
          rcases i with _ | _ | i
          · simp [innerSeq, geom]
          · simp [innerSeq, geom]
          · simp only [innerSeq, map_mul, map_neg, map_pow, map_ofNat, geom,
              Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
            have hih : φ (a (i + 1)) = 1 := by
              have := ih (i + 1) (by omega)
              simpa [φ, geom] using this
            rw [hih, mul_one]
            have h4 : (4 : ZMod 5) = -1 := by decide
            rw [h4, pow_succ']; ring
        have hcomp_geom : comp (geom (1 : ZMod 5)) (geom (-1 : ZMod 5)) k = if k = 1 then 1 else 0 := by
          rw [comp_geom, add_neg_cancel]
          dsimp [geom]
          rcases k with _ | _ | k
          · omega
          · simp
          · simp [zero_pow (Nat.succ_ne_zero k)]
        -- Compare `comp (φ ∘ a) (geom (-1)) k` and `comp (geom 1) (geom (-1)) k`!
        have hcongr_in : comp (fun i => φ (a i)) (fun i => φ (innerSeq a i)) k =
            comp (fun i => φ (a i)) (geom (-1 : ZMod 5)) k := by
          simp only [comp]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [powSeq_congr hinner j k le_rfl]
        rw [hcongr_in] at hcomp
        have hrhs : φ (if k = 1 then 1 else 0) = if k = 1 then 1 else 0 := by split_ifs <;> simp
        rw [hrhs, ← hcomp_geom] at hcomp
        simp only [comp] at hcomp
        rw [Finset.sum_range_succ, Finset.sum_range_succ] at hcomp
        have hrest : ∑ j ∈ Finset.range k, φ (a j) * powSeq (geom (-1 : ZMod 5)) j k =
            ∑ j ∈ Finset.range k, geom (1 : ZMod 5) j * powSeq (geom (-1 : ZMod 5)) j k := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [ih j (Finset.mem_range.mp hj)]
        rw [hrest] at hcomp
        have hdiag : powSeq (geom (-1 : ZMod 5)) k k = 1 := by
          rw [powSeq_diag (by simp [geom]), show geom (-1 : ZMod 5) 1 = 1 by simp [geom], one_pow]
        rw [hdiag, mul_one, mul_one] at hcomp
        exact add_left_cancel hcomp
  -- Part 2: mod 2 (`(a k : ZMod 2) = pow2Seq k`)
  let ψ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hmod2 : ∀ k : ℕ, ψ (a k) = pow2Seq k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [ψ, Int.coe_castRingHom, ha0, Int.cast_zero, pow2Seq]
        rw [if_neg]; rintro ⟨j, hj⟩; have := Nat.one_le_pow j 2 (by norm_num); omega
      · have hcomp := congr_arg ψ (harec k)
        rw [comp_map] at hcomp
        have hinner : ∀ i ≤ k, ψ (innerSeq a i) = xPlusX2 i := by
          intro i _
          rcases i with _ | _ | _ | i
          · simp [innerSeq, xPlusX2]
          · simp [innerSeq, xPlusX2]
          · simp [innerSeq, xPlusX2, ha1]
          · simp only [innerSeq, xPlusX2, map_mul, map_neg, map_pow, map_ofNat]
            have h4 : (4 : ZMod 2) = 0 := by decide
            rw [h4, zero_pow (Nat.succ_ne_zero i), neg_zero, zero_mul]
            rw [if_neg (by omega)]
        have hcongr_in : comp (fun i => ψ (a i)) (fun i => ψ (innerSeq a i)) k =
            comp (fun i => ψ (a i)) xPlusX2 k := by
          simp only [comp]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [powSeq_congr hinner j k le_rfl]
        rw [hcongr_in] at hcomp
        have hrhs : ψ (if k = 1 then 1 else 0) = if k = 1 then 1 else 0 := by split_ifs <;> simp
        rw [hrhs, ← comp_pow2Seq_xPlusX2 k] at hcomp
        simp only [comp] at hcomp
        rw [Finset.sum_range_succ, Finset.sum_range_succ] at hcomp
        have hrest : ∑ j ∈ Finset.range k, ψ (a j) * powSeq xPlusX2 j k =
            ∑ j ∈ Finset.range k, pow2Seq j * powSeq xPlusX2 j k := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [ih j (Finset.mem_range.mp hj)]
        rw [hrest] at hcomp
        have hdiag : powSeq xPlusX2 k k = 1 := by
          rw [powSeq_diag (by decide : xPlusX2 0 = 0), show xPlusX2 1 = 1 by decide, one_pow]
        rw [hdiag, mul_one, mul_one] at hcomp
        exact add_left_cancel hcomp
  constructor
  · have h1 : (a n : ZMod 5) = ((1 : ℤ) : ZMod 5) := by
      have := hmod5 n
      simpa [φ, geom, show n ≠ 0 by omega] using this
    exact (ZMod.intCast_eq_intCast_iff (a n) 1 5).mp h1
  · have h2 : (a n : ZMod 2) = pow2Seq n := hmod2 n
    constructor
    · intro hodd
      by_contra hnot
      simp only [pow2Seq, if_neg hnot] at h2
      have hdvd : (2 : ℤ) ∣ a n := (ZMod.intCast_zmod_eq_zero_iff_dvd (a n) 2).mp h2
      obtain ⟨t, ht⟩ := hodd
      obtain ⟨s, hs⟩ := hdvd
      omega
    · intro hex
      simp only [pow2Seq, if_pos hex] at h2
      have hndvd : ¬ (2 : ℤ) ∣ a n := by
        intro hdvd
        have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (a n) 2).mpr hdvd
        rw [h2] at h0; exact one_ne_zero h0
      exact Int.odd_iff.mpr (by omega)

end OMA.P_oeis_a393856

theorem OMA.solution : type_of% @OMA.S_oeis_a393856.main :=
  OMA.P_oeis_a393856.prove_a393856
