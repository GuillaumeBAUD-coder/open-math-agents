import OMAReductions.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1

/-!
# Proof of `Erdos1186.erdos_1186.variants.prs_conjecture.R1.H3`

We decompose `x ∈ Icc 1 (1096 * w)` into `2 * w * i + r + 1` (`0 ≤ i < 548`, `0 ≤ r < 2 * w`) and
`y ∈ Icc 1 (1096 * w)` into `w * k + t + 1` (`0 ≤ k < 1096`, `0 ≤ t < w`). On each block `(i, k)`,
the number of admissible residue pairs `(r, t)` is an exact multiple `wt i k * w ^ 2`, and the
sum of `wt i k` over the twelve constant-colour intervals evaluates to `322224`.
-/

-- Step Erdos1186.erdos_1186.variants.prs_conjecture.R1.H3: hypothesis H3 of reduction Erdos1186.erdos_1186.variants.prs_conjecture.R1
-- Credit: @umarsxlim

namespace Erdos1186H3

open Finset

def refB (b : ℕ) : Bool :=
  b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
  (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)

lemma refB_eq_true_iff (b : ℕ) :
    refB b = true ↔ b < 28 ∨ (34 ≤ b ∧ b < 62) ∨ (99 ≤ b ∧ b < 158) ∨
      (274 ≤ b ∧ b < 390) ∨ (449 ≤ b ∧ b < 486) ∨ (514 ≤ b ∧ b < 520) := by
  simp [refB, or_assoc]

def wt (i k : ℕ) : ℕ :=
  if refB i ≠ refB (k / 2) then
    (if i ≤ k ∧ k < i + 548 then 1 else 0) +
    (if i < k ∧ k ≤ i + 548 then 1 else 0)
  else 0

def intWeight (i c d : ℕ) : ℕ :=
  (min (i + 548) d - max i c) + (min (i + 549) d - max (i + 1) c)

def innerVal (i : ℕ) : ℕ :=
  if refB i = true then
    intWeight i 56 68 + intWeight i 124 198 + intWeight i 316 548 +
    intWeight i 780 898 + intWeight i 972 1028 + intWeight i 1040 1096
  else
    intWeight i 0 56 + intWeight i 68 124 + intWeight i 198 316 +
    intWeight i 548 780 + intWeight i 898 972 + intWeight i 1028 1040

def sumPow2 (a : ℕ) : ℕ → ℕ
  | 0 => innerVal a
  | k + 1 => sumPow2 a k + sumPow2 (a + 2 ^ k) k

lemma sum_Ico_pow2 (k : ℕ) : ∀ a : ℕ, ∑ i ∈ Ico a (a + 2 ^ k), innerVal i = sumPow2 a k := by
  induction k with
  | zero =>
    intro a
    simp [sumPow2]
  | succ k ih =>
    intro a
    have h1 : a ≤ a + 2 ^ k := Nat.le_add_right a (2 ^ k)
    have h2 : a + 2 ^ k ≤ a + 2 ^ (k + 1) := by
      have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      omega
    rw [← Finset.sum_Ico_consecutive innerVal h1 h2, ih a]
    have h3 : a + 2 ^ (k + 1) = (a + 2 ^ k) + 2 ^ k := by ring
    rw [h3, ih (a + 2 ^ k), sumPow2]

lemma sumPow2_total : sumPow2 0 9 + sumPow2 512 5 + sumPow2 544 2 = 322224 := by
  decide

lemma sum_Ico_ite_Ico (lo hi c d : ℕ) :
    ∑ k ∈ Ico c d, (if lo ≤ k ∧ k < hi then 1 else 0) = min hi d - max lo c := by
  simp only [Finset.sum_boole, Nat.cast_id]
  have h : (Ico c d).filter (fun k => lo ≤ k ∧ k < hi) = Ico (max lo c) (min hi d) := by
    ext k
    simp only [mem_filter, mem_Ico, max_le_iff, lt_min_iff]
    omega
  rw [h, Nat.card_Ico]

lemma sum_Ico_wt_of_const (i c d : ℕ) (v : Bool)
    (hv : ∀ k, c ≤ k → k < d → refB (k / 2) = v) :
    ∑ k ∈ Ico c d, wt i k = if refB i ≠ v then intWeight i c d else 0 := by
  by_cases hne : refB i ≠ v
  · rw [if_pos hne]
    have hcongr : ∑ k ∈ Ico c d, wt i k =
        ∑ k ∈ Ico c d,
          ((if i ≤ k ∧ k < i + 548 then 1 else 0) +
           (if i + 1 ≤ k ∧ k < i + 549 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [mem_Ico] at hk
      unfold wt
      rw [hv k hk.1 hk.2, if_pos hne]
      congr 1
      by_cases h1 : i < k ∧ k ≤ i + 548
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
    rw [hcongr, Finset.sum_add_distrib, sum_Ico_ite_Ico, sum_Ico_ite_Ico]
    rfl
  · rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro k hk
    rw [mem_Ico] at hk
    unfold wt
    rw [hv k hk.1 hk.2, if_neg hne]

lemma refB_const_on (a b : ℕ) (v : Bool)
    (h : ∀ q, a ≤ q → q < b → refB q = v) :
    ∀ k, 2 * a ≤ k → k < 2 * b → refB (k / 2) = v := by
  intro k hk1 hk2
  exact h (k / 2) (by omega) (by omega)

lemma sum_wt_eq_innerVal (i : ℕ) : ∑ k ∈ range 1096, wt i k = innerVal i := by
  rw [Finset.range_eq_Ico]
  have s0 : ∑ k ∈ Ico 0 1096, wt i k =
      (∑ k ∈ Ico 0 56, wt i k) + (∑ k ∈ Ico 56 68, wt i k) +
      (∑ k ∈ Ico 68 124, wt i k) + (∑ k ∈ Ico 124 198, wt i k) +
      (∑ k ∈ Ico 198 316, wt i k) + (∑ k ∈ Ico 316 548, wt i k) +
      (∑ k ∈ Ico 548 780, wt i k) + (∑ k ∈ Ico 780 898, wt i k) +
      (∑ k ∈ Ico 898 972, wt i k) + (∑ k ∈ Ico 972 1028, wt i k) +
      (∑ k ∈ Ico 1028 1040, wt i k) + (∑ k ∈ Ico 1040 1096, wt i k) := by
    have h1 := Finset.sum_Ico_consecutive (wt i) (by decide : 0 ≤ 56) (by decide : 56 ≤ 68)
    have h2 := Finset.sum_Ico_consecutive (wt i) (by decide : 0 ≤ 68) (by decide : 68 ≤ 124)
    have h3 := Finset.sum_Ico_consecutive (wt i) (by decide : 0 ≤ 124) (by decide : 124 ≤ 198)
    have h4 := Finset.sum_Ico_consecutive (wt i) (by decide : 0 ≤ 198) (by decide : 198 ≤ 316)
    have h5 := Finset.sum_Ico_consecutive (wt i) (by decide : 0 ≤ 316) (by decide : 316 ≤ 548)
    have h6 := Finset.sum_Ico_consecutive (wt i) (by decide : 0 ≤ 548) (by decide : 548 ≤ 780)
    have h7 := Finset.sum_Ico_consecutive (wt i) (by decide : 0 ≤ 780) (by decide : 780 ≤ 898)
    have h8 := Finset.sum_Ico_consecutive (wt i) (by decide : 0 ≤ 898) (by decide : 898 ≤ 972)
    have h9 := Finset.sum_Ico_consecutive (wt i) (by decide : 0 ≤ 972) (by decide : 972 ≤ 1028)
    have h10 := Finset.sum_Ico_consecutive (wt i) (by decide : 0 ≤ 1028) (by decide : 1028 ≤ 1040)
    have h11 := Finset.sum_Ico_consecutive (wt i) (by decide : 0 ≤ 1040) (by decide : 1040 ≤ 1096)
    omega
  rw [s0]
  have c1 : ∀ k, 0 ≤ k → k < 56 → refB (k / 2) = true :=
    refB_const_on 0 28 true (fun q _ _ => by rw [refB_eq_true_iff]; omega)
  have c2 : ∀ k, 56 ≤ k → k < 68 → refB (k / 2) = false :=
    refB_const_on 28 34 false (fun q _ _ => by
      cases h : refB q
      · rfl
      · rw [refB_eq_true_iff] at h; omega)
  have c3 : ∀ k, 68 ≤ k → k < 124 → refB (k / 2) = true :=
    refB_const_on 34 62 true (fun q _ _ => by rw [refB_eq_true_iff]; omega)
  have c4 : ∀ k, 124 ≤ k → k < 198 → refB (k / 2) = false :=
    refB_const_on 62 99 false (fun q _ _ => by
      cases h : refB q
      · rfl
      · rw [refB_eq_true_iff] at h; omega)
  have c5 : ∀ k, 198 ≤ k → k < 316 → refB (k / 2) = true :=
    refB_const_on 99 158 true (fun q _ _ => by rw [refB_eq_true_iff]; omega)
  have c6 : ∀ k, 316 ≤ k → k < 548 → refB (k / 2) = false :=
    refB_const_on 158 274 false (fun q _ _ => by
      cases h : refB q
      · rfl
      · rw [refB_eq_true_iff] at h; omega)
  have c7 : ∀ k, 548 ≤ k → k < 780 → refB (k / 2) = true :=
    refB_const_on 274 390 true (fun q _ _ => by rw [refB_eq_true_iff]; omega)
  have c8 : ∀ k, 780 ≤ k → k < 898 → refB (k / 2) = false :=
    refB_const_on 390 449 false (fun q _ _ => by
      cases h : refB q
      · rfl
      · rw [refB_eq_true_iff] at h; omega)
  have c9 : ∀ k, 898 ≤ k → k < 972 → refB (k / 2) = true :=
    refB_const_on 449 486 true (fun q _ _ => by rw [refB_eq_true_iff]; omega)
  have c10 : ∀ k, 972 ≤ k → k < 1028 → refB (k / 2) = false :=
    refB_const_on 486 514 false (fun q _ _ => by
      cases h : refB q
      · rfl
      · rw [refB_eq_true_iff] at h; omega)
  have c11 : ∀ k, 1028 ≤ k → k < 1040 → refB (k / 2) = true :=
    refB_const_on 514 520 true (fun q _ _ => by rw [refB_eq_true_iff]; omega)
  have c12 : ∀ k, 1040 ≤ k → k < 1096 → refB (k / 2) = false :=
    refB_const_on 520 548 false (fun q _ _ => by
      cases h : refB q
      · rfl
      · rw [refB_eq_true_iff] at h; omega)
  rw [sum_Ico_wt_of_const i 0 56 true c1,
      sum_Ico_wt_of_const i 56 68 false c2,
      sum_Ico_wt_of_const i 68 124 true c3,
      sum_Ico_wt_of_const i 124 198 false c4,
      sum_Ico_wt_of_const i 198 316 true c5,
      sum_Ico_wt_of_const i 316 548 false c6,
      sum_Ico_wt_of_const i 548 780 true c7,
      sum_Ico_wt_of_const i 780 898 false c8,
      sum_Ico_wt_of_const i 898 972 true c9,
      sum_Ico_wt_of_const i 972 1028 false c10,
      sum_Ico_wt_of_const i 1028 1040 true c11,
      sum_Ico_wt_of_const i 1040 1096 false c12]
  rcases Bool.eq_false_or_eq_true (refB i) with h | h <;> simp [h, innerVal]

lemma sum_wt_total : ∑ i ∈ range 548, ∑ k ∈ range 1096, wt i k = 322224 := by
  rw [Finset.sum_congr rfl (fun i _ => sum_wt_eq_innerVal i), Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive innerVal (by decide : 0 ≤ 544) (by decide : 544 ≤ 548),
      ← Finset.sum_Ico_consecutive innerVal (by decide : 0 ≤ 512) (by decide : 512 ≤ 544)]
  have s1 : ∑ i ∈ Ico 0 512, innerVal i = sumPow2 0 9 := by
    simpa using sum_Ico_pow2 9 0
  have s2 : ∑ i ∈ Ico 512 544, innerVal i = sumPow2 512 5 := by
    simpa using sum_Ico_pow2 5 512
  have s3 : ∑ i ∈ Ico 544 548, innerVal i = sumPow2 544 2 := by
    simpa using sum_Ico_pow2 2 544
  rw [s1, s2, s3]
  exact sumPow2_total

lemma sum_odd_eq_sq (w : ℕ) : ∑ t ∈ range w, (2 * t + 1) = w ^ 2 := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Finset.sum_range_succ, ih]
    ring

lemma card_filter_le_two_mul (w : ℕ) :
    ((range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ => rt.1 ≤ 2 * rt.2)).card = w ^ 2 := by
  rw [Finset.card_filter, Finset.sum_product_right]
  have hinner : ∀ t ∈ range w,
      ∑ r ∈ range (2 * w), (if r ≤ 2 * t then 1 else 0) = 2 * t + 1 := by
    intro t ht
    rw [mem_range] at ht
    simp only [Finset.sum_boole, Nat.cast_id]
    have hf : (range (2 * w)).filter (fun r => r ≤ 2 * t) = range (2 * t + 1) := by
      ext r
      simp only [mem_filter, mem_range]
      omega
    rw [hf, Finset.card_range]
  rw [Finset.sum_congr rfl hinner, sum_odd_eq_sq]

lemma card_filter_gt_two_mul (w : ℕ) :
    ((range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ => 2 * rt.2 + 1 ≤ rt.1)).card = w ^ 2 := by
  have hcompl := Finset.card_filter_add_card_filter_not (s := range (2 * w) ×ˢ range w)
    (p := fun rt : ℕ × ℕ => rt.1 ≤ 2 * rt.2)
  have hfeq : (range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ => ¬ rt.1 ≤ 2 * rt.2) =
      (range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ => 2 * rt.2 + 1 ≤ rt.1) := by
    ext rt
    simp only [mem_filter]
    exact and_congr_right fun _ => by omega
  rw [hfeq, card_filter_le_two_mul, Finset.card_product, Finset.card_range, Finset.card_range] at hcompl
  have hsq : 2 * w * w = 2 * w ^ 2 := by ring
  omega

lemma fiber_card (w i k : ℕ) :
    ((range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ =>
      (2 * w * i + rt.1 + 1 + 1 ≤ 2 * (w * k + rt.2 + 1) ∧
       2 * (w * k + rt.2 + 1) ≤ 2 * w * i + rt.1 + 1 + 1096 * w) ∧
      refB i ≠ refB (k / 2))).card = wt i k * w ^ 2 := by
  unfold wt
  by_cases href : refB i ≠ refB (k / 2)
  · rw [if_pos href]
    have hsimp : (range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ =>
        (2 * w * i + rt.1 + 1 + 1 ≤ 2 * (w * k + rt.2 + 1) ∧
         2 * (w * k + rt.2 + 1) ≤ 2 * w * i + rt.1 + 1 + 1096 * w) ∧
        refB i ≠ refB (k / 2)) =
      (range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ =>
        2 * w * i + rt.1 ≤ 2 * w * k + 2 * rt.2 ∧
        2 * w * k + 2 * rt.2 + 1 ≤ 2 * w * (i + 548) + rt.1) := by
      ext rt
      simp only [mem_filter]
      have hlin : 2 * w * (i + 548) = 2 * w * i + 1096 * w := by ring
      have hlin2 : 2 * (w * k + rt.2 + 1) = 2 * w * k + 2 * rt.2 + 2 := by ring
      rw [hlin, hlin2]
      exact ⟨fun ⟨hm, ⟨h1, h2⟩, _⟩ => ⟨hm, by omega, by omega⟩,
             fun ⟨hm, h1, h2⟩ => ⟨hm, ⟨by omega, by omega⟩, href⟩⟩
    rw [hsimp]
    by_cases hlt : k < i
    · have h0 : (if i ≤ k ∧ k < i + 548 then 1 else 0) +
          (if i < k ∧ k ≤ i + 548 then 1 else 0) = 0 := by
        rw [if_neg (by omega), if_neg (by omega)]
      rw [h0, zero_mul]
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro rt hrt
      simp only [mem_product, mem_range] at hrt
      intro hcond
      have hmul : 2 * w * (k + 1) ≤ 2 * w * i := Nat.mul_le_mul_left (2 * w) (by omega)
      nlinarith
    · by_cases heq1 : k = i
      · subst heq1
        have h1 : (if k ≤ k ∧ k < k + 548 then 1 else 0) +
            (if k < k ∧ k ≤ k + 548 then 1 else 0) = 1 := by
          rw [if_pos (by omega), if_neg (by omega)]
        rw [h1, one_mul]
        have hf : (range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ =>
            2 * w * k + rt.1 ≤ 2 * w * k + 2 * rt.2 ∧
            2 * w * k + 2 * rt.2 + 1 ≤ 2 * w * (k + 548) + rt.1) =
          (range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ => rt.1 ≤ 2 * rt.2) := by
          ext rt
          simp only [mem_filter, mem_product, mem_range]
          have hlin : 2 * w * (k + 548) = 2 * w * k + 1096 * w := by ring
          rw [hlin]
          constructor
          · rintro ⟨hmem, h1, _⟩
            exact ⟨hmem, by omega⟩
          · rintro ⟨⟨hr, ht⟩, h1⟩
            exact ⟨⟨hr, ht⟩, by omega, by omega⟩
        rw [hf, card_filter_le_two_mul]
      · by_cases hmid : k < i + 548
        · have h2 : (if i ≤ k ∧ k < i + 548 then 1 else 0) +
              (if i < k ∧ k ≤ i + 548 then 1 else 0) = 2 := by
            rw [if_pos (by omega), if_pos (by omega)]
          rw [h2]
          have hf : (range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ =>
              2 * w * i + rt.1 ≤ 2 * w * k + 2 * rt.2 ∧
              2 * w * k + 2 * rt.2 + 1 ≤ 2 * w * (i + 548) + rt.1) =
            range (2 * w) ×ˢ range w := by
            rw [Finset.filter_eq_self]
            intro rt hrt
            simp only [mem_product, mem_range] at hrt
            have hmul1 : 2 * w * (i + 1) ≤ 2 * w * k := Nat.mul_le_mul_left (2 * w) (by omega)
            have hmul2 : 2 * w * (k + 1) ≤ 2 * w * (i + 548) :=
              Nat.mul_le_mul_left (2 * w) (by omega)
            constructor <;> nlinarith
          rw [hf, Finset.card_product, Finset.card_range, Finset.card_range]
          ring
        · by_cases heq2 : k = i + 548
          · subst heq2
            have h1 : (if i ≤ i + 548 ∧ i + 548 < i + 548 then 1 else 0) +
                (if i < i + 548 ∧ i + 548 ≤ i + 548 then 1 else 0) = 1 := by
              rw [if_neg (by omega), if_pos (by omega)]
            rw [h1, one_mul]
            have hf : (range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ =>
                2 * w * i + rt.1 ≤ 2 * w * (i + 548) + 2 * rt.2 ∧
                2 * w * (i + 548) + 2 * rt.2 + 1 ≤ 2 * w * (i + 548) + rt.1) =
              (range (2 * w) ×ˢ range w).filter (fun rt : ℕ × ℕ => 2 * rt.2 + 1 ≤ rt.1) := by
              ext rt
              simp only [mem_filter, mem_product, mem_range]
              have hlin : 2 * w * (i + 548) = 2 * w * i + 1096 * w := by ring
              rw [hlin]
              constructor
              · rintro ⟨hmem, _, h2⟩
                exact ⟨hmem, by omega⟩
              · rintro ⟨⟨hr, ht⟩, h2⟩
                exact ⟨⟨hr, ht⟩, by omega, by omega⟩
            rw [hf, card_filter_gt_two_mul]
          · have h0 : (if i ≤ k ∧ k < i + 548 then 1 else 0) +
                (if i < k ∧ k ≤ i + 548 then 1 else 0) = 0 := by
              rw [if_neg (by omega), if_neg (by omega)]
            rw [h0, zero_mul]
            apply Finset.card_eq_zero.mpr
            rw [Finset.filter_eq_empty_iff]
            intro rt hrt
            simp only [mem_product, mem_range] at hrt
            intro hcond
            have hmul : 2 * w * (i + 549) ≤ 2 * w * k := Nat.mul_le_mul_left (2 * w) (by omega)
            nlinarith
  · rw [if_neg href, zero_mul]
    apply Finset.card_eq_zero.mpr
    rw [Finset.filter_eq_empty_iff]
    intro rt _ hcond
    exact href hcond.2

lemma div_two_mul_left (w i r : ℕ) (hw : 1 ≤ w) (hr : r < 2 * w) :
    (2 * w * i + r) / (2 * w) = i := by
  rw [Nat.mul_add_div (by omega : 0 < 2 * w), Nat.div_eq_of_lt hr, add_zero]

lemma div_two_mul_right (w k t : ℕ) (hw : 1 ≤ w) (ht : t < w) :
    (w * k + t) / (2 * w) = k / 2 := by
  rw [show 2 * w = w * 2 by ring, ← Nat.div_div_eq_div_mul,
    Nat.mul_add_div (by omega : 0 < w), Nat.div_eq_of_lt ht, add_zero]

def Tset (w : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((range 548 ×ˢ range 1096) ×ˢ (range (2 * w) ×ˢ range w)).filter
    (fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 * w * q.1.1 + q.2.1 + 1 + 1 ≤ 2 * (w * q.1.2 + q.2.2 + 1) ∧
       2 * (w * q.1.2 + q.2.2 + 1) ≤ 2 * w * q.1.1 + q.2.1 + 1 + 1096 * w) ∧
      refB q.1.1 ≠ refB (q.1.2 / 2))

lemma Tset_card (w : ℕ) : (Tset w).card = 322224 * w ^ 2 := by
  unfold Tset
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_product]
  have hfiber : ∀ i ∈ range 548, ∀ k ∈ range 1096,
      ∑ rt ∈ range (2 * w) ×ˢ range w,
        (if (2 * w * i + rt.1 + 1 + 1 ≤ 2 * (w * k + rt.2 + 1) ∧
             2 * (w * k + rt.2 + 1) ≤ 2 * w * i + rt.1 + 1 + 1096 * w) ∧
            refB i ≠ refB (k / 2) then 1 else 0) =
        wt i k * w ^ 2 := by
    intro i _ k _
    rw [← Finset.card_filter]
    exact fiber_card w i k
  calc
    ∑ i ∈ range 548, ∑ k ∈ range 1096,
        ∑ rt ∈ range (2 * w) ×ˢ range w,
          (if (2 * w * i + rt.1 + 1 + 1 ≤ 2 * (w * k + rt.2 + 1) ∧
               2 * (w * k + rt.2 + 1) ≤ 2 * w * i + rt.1 + 1 + 1096 * w) ∧
              refB i ≠ refB (k / 2) then 1 else 0)
        = ∑ i ∈ range 548, ∑ k ∈ range 1096, wt i k * w ^ 2 :=
          Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun k hk => hfiber i hi k hk))
    _ = (∑ i ∈ range 548, ∑ k ∈ range 1096, wt i k) * w ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => (Finset.sum_mul _ _ _).symm)
    _ = 322224 * w ^ 2 := by rw [sum_wt_total]

lemma bij_mem (w : ℕ) (hw : 1 ≤ w) (x y : ℕ)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 1096 * w) (hy1 : 1 ≤ y) (hy2 : y ≤ 1096 * w)
    (h1 : x + 1 ≤ 2 * y) (h2 : 2 * y ≤ x + 1096 * w)
    (href : refB ((x - 1) / (2 * w)) ≠ refB ((y - 1) / (2 * w))) :
    (((x - 1) / (2 * w), (y - 1) / w), ((x - 1) % (2 * w), (y - 1) % w)) ∈ Tset w := by
  simp only [Tset, mem_filter, mem_product, mem_range]
  have hx : 2 * w * ((x - 1) / (2 * w)) + (x - 1) % (2 * w) + 1 = x := by
    have := Nat.div_add_mod (x - 1) (2 * w)
    omega
  have hy : w * ((y - 1) / w) + (y - 1) % w + 1 = y := by
    have := Nat.div_add_mod (y - 1) w
    omega
  have hi : (x - 1) / (2 * w) < 548 := Nat.div_lt_of_lt_mul (by omega)
  have hk : (y - 1) / w < 1096 := Nat.div_lt_of_lt_mul (by omega)
  have hr : (x - 1) % (2 * w) < 2 * w := Nat.mod_lt _ (by omega)
  have ht : (y - 1) % w < w := Nat.mod_lt _ (by omega)
  have hydiv : (y - 1) / (2 * w) = ((y - 1) / w) / 2 := by
    rw [show 2 * w = w * 2 by ring, ← Nat.div_div_eq_div_mul]
  refine ⟨⟨⟨hi, hk⟩, ⟨hr, ht⟩⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hx, hy]; exact h1
  · rw [hx, hy]; exact h2
  · rw [← hydiv]; exact href

lemma bij_inj (w x₁ y₁ x₂ y₂ : ℕ) (hx₁ : 1 ≤ x₁) (hy₁ : 1 ≤ y₁) (hx₂ : 1 ≤ x₂) (hy₂ : 1 ≤ y₂)
    (heq : (((x₁ - 1) / (2 * w), (y₁ - 1) / w), ((x₁ - 1) % (2 * w), (y₁ - 1) % w)) =
           (((x₂ - 1) / (2 * w), (y₂ - 1) / w), ((x₂ - 1) % (2 * w), (y₂ - 1) % w))) :
    (x₁, y₁) = (x₂, y₂) := by
  simp only [Prod.mk.injEq] at heq
  obtain ⟨⟨hd1, hd2⟩, ⟨hm1, hm2⟩⟩ := heq
  have h1 := Nat.div_add_mod (x₁ - 1) (2 * w)
  have h2 := Nat.div_add_mod (x₂ - 1) (2 * w)
  have h3 := Nat.div_add_mod (y₁ - 1) w
  have h4 := Nat.div_add_mod (y₂ - 1) w
  rw [hd1, hm1] at h1
  rw [hd2, hm2] at h3
  exact Prod.ext (by omega) (by omega)

lemma bij_preimg_eq (w i k r t : ℕ) (hw : 1 ≤ w) (hr : r < 2 * w) (ht : t < w) :
    (((2 * w * i + r + 1 - 1) / (2 * w), (w * k + t + 1 - 1) / w),
     ((2 * w * i + r + 1 - 1) % (2 * w), (w * k + t + 1 - 1) % w)) = ((i, k), (r, t)) := by
  simp only [Nat.add_sub_cancel, Prod.mk.injEq]
  refine ⟨⟨div_two_mul_left w i r hw hr, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Nat.mul_add_div (by omega : 0 < w), Nat.div_eq_of_lt ht, add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht]

set_option maxRecDepth 8192 in
lemma h3_proof : OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1.H3 := by
  intro w hw
  dsimp only
  rw [← Tset_card w]
  apply le_of_eq
  apply Finset.card_bij
    (fun (p : ℕ × ℕ) _ =>
      (((p.1 - 1) / (2 * w), (p.2 - 1) / w), ((p.1 - 1) % (2 * w), (p.2 - 1) % w)))
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_product, mem_Icc] at hp
    exact bij_mem w hw x y hp.1.1.1.1 hp.1.1.1.2 hp.1.1.2.1 hp.1.1.2.2 hp.1.2.1 hp.1.2.2 hp.2
  · rintro ⟨x₁, y₁⟩ hp₁ ⟨x₂, y₂⟩ hp₂ heq
    simp only [mem_filter, mem_product, mem_Icc] at hp₁ hp₂
    exact bij_inj w x₁ y₁ x₂ y₂ hp₁.1.1.1.1 hp₁.1.1.2.1 hp₂.1.1.1.1 hp₂.1.1.2.1 heq
  · rintro ⟨⟨i, k⟩, ⟨r, t⟩⟩ hq
    simp only [Tset, mem_filter, mem_product, mem_range] at hq
    obtain ⟨⟨⟨hi, hk⟩, ⟨hr, ht⟩⟩, ⟨h1, h2⟩, href⟩ := hq
    refine ⟨(2 * w * i + r + 1, w * k + t + 1), ?_, bij_preimg_eq w i k r t hw hr ht⟩
    simp only [mem_filter, mem_product, mem_Icc]
    have hx2 : 2 * w * i + r + 1 ≤ 1096 * w := by
      have : 2 * w * i ≤ 2 * w * 547 := Nat.mul_le_mul_left (2 * w) (by omega)
      omega
    have hy2 : w * k + t + 1 ≤ 1096 * w := by
      have : w * k ≤ w * 1095 := Nat.mul_le_mul_left w (by omega)
      omega
    refine ⟨⟨⟨⟨by omega, hx2⟩, ⟨by omega, hy2⟩⟩, h1, h2⟩, ?_⟩
    change refB ((2 * w * i + r + 1 - 1) / (2 * w)) ≠
      refB ((w * k + t + 1 - 1) / (2 * w))
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel,
      div_two_mul_left w i r hw hr,
      div_two_mul_right w k t hw ht]
    exact href

end Erdos1186H3

theorem OMA.solution : OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1.H3 :=
  Erdos1186H3.h3_proof
