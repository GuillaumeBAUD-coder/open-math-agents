import OMAStatements.S_oeis_a227012
import Mathlib

/-!
Proof of the A227012 floor formula. The integers (n - 1)^3 + 1, ..., n^3 form the interval
[c - w, c + w] with w = 3 n (n - 1) / 2 and c = n^3 - w. Pairing 1/(c - e) + 1/(c + e) and
expanding to fourth order gives explicit rational lower and upper bounds for the reciprocal
sum; the resulting bounds for the harmonic mean lie strictly between the predicted value and
the predicted value plus one. After writing n = 4 q + s + 3, both comparisons are polynomial
inequalities in q with nonnegative coefficients. The cases n = 1 and n = 2 are checked
directly from the same bounds.
-/

namespace OMA.Helpers

open Finset

/-- Sum of the squares `1^2 + ... + w^2`, as a real polynomial. -/
noncomputable def hmSq2 (w : ℝ) : ℝ := w * (w + 1) * (2 * w + 1) / 6

/-- Sum of the fourth powers `1^4 + ... + w^4`, as a real polynomial. -/
noncomputable def hmSq4 (w : ℝ) : ℝ := w * (w + 1) * (2 * w + 1) * (3 * w ^ 2 + 3 * w - 1) / 30

/-- Lower bound for the sum of `1/k` over `[c - w, c + w]`. -/
noncomputable def hmLow (x w : ℝ) : ℝ :=
  (2 * w + 1) / x + 2 * hmSq2 w / x ^ 3 + 2 * hmSq4 w / x ^ 5

/-- Upper bound for the sum of `1/k` over `[c - w, c + w]`, valid for `w ≤ W < c`. -/
noncomputable def hmUp (x w W : ℝ) : ℝ :=
  (2 * w + 1) / x + 2 * hmSq2 w / x ^ 3 + 2 * hmSq4 w / (x ^ 3 * (x ^ 2 - W ^ 2))

theorem hm_pair_low (x e : ℝ) (he : 0 < e) (hx : e < x) :
    2 / x + 2 * e ^ 2 / x ^ 3 + 2 * e ^ 4 / x ^ 5 ≤ 1 / (x - e) + 1 / (x + e) := by
  have hx0 : 0 < x := he.trans hx
  have h1 : 0 < x - e := by linarith
  have h2 : 0 < x + e := by linarith
  have key : 1 / (x - e) + 1 / (x + e) - (2 / x + 2 * e ^ 2 / x ^ 3 + 2 * e ^ 4 / x ^ 5)
      = 2 * e ^ 6 / (x ^ 5 * ((x - e) * (x + e))) := by
    field_simp
    ring
  have : 0 ≤ 2 * e ^ 6 / (x ^ 5 * ((x - e) * (x + e))) := by positivity
  linarith

theorem hm_pair_up (x e W : ℝ) (he : 0 < e) (heW : e ≤ W) (hW : W < x) :
    1 / (x - e) + 1 / (x + e) ≤ 2 / x + 2 * e ^ 2 / x ^ 3 + 2 * e ^ 4 / (x ^ 3 * (x ^ 2 - W ^ 2)) := by
  have hx0 : 0 < x := he.trans_le heW |>.trans hW
  have h1 : 0 < x - e := by linarith
  have h2 : 0 < x + e := by linarith
  have hW0 : 0 < x ^ 2 - W ^ 2 := by nlinarith
  have key : 1 / (x - e) + 1 / (x + e)
      = 2 / x + 2 * e ^ 2 / x ^ 3 + 2 * e ^ 4 / (x ^ 3 * ((x - e) * (x + e))) := by
    field_simp
    ring
  rw [key]
  have hle : x ^ 3 * (x ^ 2 - W ^ 2) ≤ x ^ 3 * ((x - e) * (x + e)) := by
    have : x ^ 2 - W ^ 2 ≤ (x - e) * (x + e) := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have : 2 * e ^ 4 / (x ^ 3 * ((x - e) * (x + e))) ≤ 2 * e ^ 4 / (x ^ 3 * (x ^ 2 - W ^ 2)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hle
  linarith

theorem hm_split (c w : ℕ) (hw : w + 1 ≤ c) (f : ℕ → ℝ) :
    ∑ k ∈ Icc (c - (w + 1)) (c + (w + 1)), f k
      = f (c - (w + 1)) + ∑ k ∈ Icc (c - w) (c + w), f k + f (c + w + 1) := by
  rw [show c + (w + 1) = (c + w) + 1 by omega, Finset.sum_Icc_succ_top (by omega)]
  rw [← Finset.insert_Icc_add_one_left_eq_Icc (show c - (w + 1) ≤ c + w by omega),
    Finset.sum_insert (by simp), show c - (w + 1) + 1 = c - w by omega]

theorem hm_bounds (c W : ℕ) (hW : W < c) : ∀ w : ℕ, w ≤ W →
    hmLow c w ≤ ∑ k ∈ Icc (c - w) (c + w), 1 / (k : ℝ) ∧
    ∑ k ∈ Icc (c - w) (c + w), 1 / (k : ℝ) ≤ hmUp c w W := by
  have hc : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  intro w
  induction w with
  | zero =>
    intro _
    simp [hmLow, hmUp, hmSq2, hmSq4]
  | succ w ih =>
    intro hw
    obtain ⟨ihl, ihu⟩ := ih (by omega)
    rw [hm_split c w (by omega)]
    have e1 : ((c - (w + 1) : ℕ) : ℝ) = (c : ℝ) - ((w : ℝ) + 1) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have e2 : ((c + w + 1 : ℕ) : ℝ) = (c : ℝ) + ((w : ℝ) + 1) := by push_cast; ring
    rw [e1, e2]
    have hpos : (0 : ℝ) < (w : ℝ) + 1 := by positivity
    have hlt : (w : ℝ) + 1 < c := by exact_mod_cast (show w + 1 < c by omega)
    have hle : (w : ℝ) + 1 ≤ W := by exact_mod_cast hw
    have hWc : (W : ℝ) < c := by exact_mod_cast hW
    have pl := hm_pair_low c ((w : ℝ) + 1) hpos hlt
    have pu := hm_pair_up c ((w : ℝ) + 1) W hpos hle hWc
    have sl : hmLow c ((w + 1 : ℕ) : ℝ) = hmLow c w
        + (2 / c + 2 * ((w : ℝ) + 1) ^ 2 / (c : ℝ) ^ 3 + 2 * ((w : ℝ) + 1) ^ 4 / (c : ℝ) ^ 5) := by
      simp only [hmLow, hmSq2, hmSq4]; push_cast; ring
    have su : hmUp c ((w + 1 : ℕ) : ℝ) W = hmUp c w W
        + (2 / c + 2 * ((w : ℝ) + 1) ^ 2 / (c : ℝ) ^ 3
          + 2 * ((w : ℝ) + 1) ^ 4 / ((c : ℝ) ^ 3 * ((c : ℝ) ^ 2 - (W : ℝ) ^ 2))) := by
      simp only [hmUp, hmSq2, hmSq4]; push_cast; ring
    rw [sl, su]
    constructor <;> linarith


theorem hm_condA (x y p : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (hxy : y < x)
    (h : 0 ≤ (2 * y + 1) * (x ^ 3 * (x ^ 2 - y ^ 2)) - p * ((2 * y + 1) * x ^ 2 * (x ^ 2 - y ^ 2)
      + 2 * hmSq2 y * (x ^ 2 - y ^ 2) + 2 * hmSq4 y)) :
    p * hmUp x y y ≤ 2 * y + 1 := by
  have h0 : 0 < x ^ 2 - y ^ 2 := by nlinarith
  have hd : 0 < x ^ 3 * (x ^ 2 - y ^ 2) := by positivity
  have e : hmUp x y y = ((2 * y + 1) * x ^ 2 * (x ^ 2 - y ^ 2) + 2 * hmSq2 y * (x ^ 2 - y ^ 2)
      + 2 * hmSq4 y) / (x ^ 3 * (x ^ 2 - y ^ 2)) := by
    unfold hmUp
    field_simp
  rw [e, ← mul_div_assoc, div_le_iff₀ hd]
  linarith

theorem hm_condB (x y p : ℝ) (hx : 0 < x)
    (h : 0 < (p + 1) * ((2 * y + 1) * x ^ 4 + 2 * hmSq2 y * x ^ 2 + 2 * hmSq4 y) - (2 * y + 1) * x ^ 5) :
    2 * y + 1 < (p + 1) * hmLow x y := by
  have e : hmLow x y = ((2 * y + 1) * x ^ 4 + 2 * hmSq2 y * x ^ 2 + 2 * hmSq4 y) / x ^ 5 := by
    unfold hmLow
    field_simp
  rw [e, ← mul_div_assoc, lt_div_iff₀ (by positivity)]
  linarith

theorem hm_floor (n c w p : ℕ) (hlo : OMA.S_oeis_a227012.cube (n - 1) + 1 = c - w)
    (hhi : OMA.S_oeis_a227012.cube n = c + w) (hwc : w < c)
    (hA : (p : ℝ) * hmUp c w w ≤ 2 * w + 1) (hB : 2 * (w : ℝ) + 1 < (p + 1) * hmLow c w) :
    Nat.floor (OMA.S_oeis_a227012.raw n) = p := by
  obtain ⟨hl, hu⟩ := hm_bounds c w hwc w le_rfl
  have hS : 0 < ∑ k ∈ Finset.Icc (c - w) (c + w), 1 / (k : ℝ) := by
    apply Finset.sum_pos
    · intro k hk
      have : 1 ≤ k := by simp only [Finset.mem_Icc] at hk; omega
      have : (0 : ℝ) < k := by exact_mod_cast this
      positivity
    · exact ⟨c, by simp only [Finset.mem_Icc]; omega⟩
  have hraw : OMA.S_oeis_a227012.raw n
      = (2 * (w : ℝ) + 1) / ∑ k ∈ Finset.Icc (c - w) (c + w), 1 / (k : ℝ) := by
    simp only [OMA.S_oeis_a227012.raw]
    rw [hlo, hhi, show c + w - (c - w) + 1 = 2 * w + 1 by omega]
    push_cast
    ring
  rw [hraw, Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ hS]
    calc (p : ℝ) * ∑ k ∈ Finset.Icc (c - w) (c + w), 1 / (k : ℝ) ≤ p * hmUp c w w :=
          mul_le_mul_of_nonneg_left hu (by positivity)
      _ ≤ _ := hA
  · rw [div_lt_iff₀ hS]
    calc 2 * (w : ℝ) + 1 < (p + 1) * hmLow c w := hB
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

theorem hm_pred (k T q : ℕ) (hk : 1 ≤ k) (hT : 2 * T = k * (k + 1)) (hq : (k - 2) / 4 = q) :
    OMA.S_oeis_a227012.predicted (k + 1) = T * (2 * k + 1) + 1 + q := by
  unfold OMA.S_oeis_a227012.predicted
  have h3 : 3 * (k + 1) ^ 2 ≤ 2 * (k + 1) ^ 3 := by nlinarith
  have e : 2 * (k + 1) ^ 3 - 3 * (k + 1) ^ 2 + (k + 1) + 2 = (T * (2 * k + 1) + 1) * 2 := by
    have hTz : (2 * T : ℤ) = k * (k + 1) := by exact_mod_cast hT
    zify [h3]
    linear_combination (-(2 * (k : ℤ) + 1)) * hTz
  rw [e, Nat.mul_div_cancel _ (by norm_num), show k + 1 - 3 = k - 2 by omega, hq]

theorem hm_gen (k T q : ℕ) (hk : 1 ≤ k) (hT : 2 * T = k * (k + 1)) (hq : (k - 2) / 4 = q)
    (hA : 0 ≤ (2 * ((3 * T : ℕ) : ℝ) + 1) * (((k ^ 3 + 1 + 3 * T : ℕ) : ℝ) ^ 3
        * (((k ^ 3 + 1 + 3 * T : ℕ) : ℝ) ^ 2 - ((3 * T : ℕ) : ℝ) ^ 2))
      - ((T * (2 * k + 1) + 1 + q : ℕ) : ℝ) * ((2 * ((3 * T : ℕ) : ℝ) + 1) * ((k ^ 3 + 1 + 3 * T : ℕ) : ℝ) ^ 2
        * (((k ^ 3 + 1 + 3 * T : ℕ) : ℝ) ^ 2 - ((3 * T : ℕ) : ℝ) ^ 2)
        + 2 * hmSq2 ((3 * T : ℕ) : ℝ) * (((k ^ 3 + 1 + 3 * T : ℕ) : ℝ) ^ 2 - ((3 * T : ℕ) : ℝ) ^ 2)
        + 2 * hmSq4 ((3 * T : ℕ) : ℝ)))
    (hB : 0 < (((T * (2 * k + 1) + 1 + q : ℕ) : ℝ) + 1) * ((2 * ((3 * T : ℕ) : ℝ) + 1)
        * ((k ^ 3 + 1 + 3 * T : ℕ) : ℝ) ^ 4
        + 2 * hmSq2 ((3 * T : ℕ) : ℝ) * ((k ^ 3 + 1 + 3 * T : ℕ) : ℝ) ^ 2 + 2 * hmSq4 ((3 * T : ℕ) : ℝ))
      - (2 * ((3 * T : ℕ) : ℝ) + 1) * ((k ^ 3 + 1 + 3 * T : ℕ) : ℝ) ^ 5) :
    Nat.floor (OMA.S_oeis_a227012.raw (k + 1)) = OMA.S_oeis_a227012.predicted (k + 1) := by
  rw [hm_pred k T q hk hT hq]
  have hc : (0 : ℝ) < ((k ^ 3 + 1 + 3 * T : ℕ) : ℝ) := by exact_mod_cast (show 0 < k ^ 3 + 1 + 3 * T by omega)
  have hwc : 3 * T < k ^ 3 + 1 + 3 * T := by omega
  have hwc' : ((3 * T : ℕ) : ℝ) < ((k ^ 3 + 1 + 3 * T : ℕ) : ℝ) := by exact_mod_cast hwc
  apply hm_floor (k + 1) (k ^ 3 + 1 + 3 * T) (3 * T) _ _ _ hwc
  · exact hm_condA _ _ _ hc (by positivity) hwc' hA
  · exact hm_condB _ _ _ hc hB
  · simp only [OMA.S_oeis_a227012.cube, Nat.add_sub_cancel]
  · simp only [OMA.S_oeis_a227012.cube]
    have hTz : (2 * T : ℤ) = k * (k + 1) := by exact_mod_cast hT
    zify
    linear_combination (-3 : ℤ) * hTz

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a227012.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [show OMA.S_oeis_a227012.predicted (0 + 1) = 1 by decide]
      apply OMA.Helpers.hm_floor (0 + 1) 1 0 1 (by decide) (by decide) (by norm_num)
      · norm_num [OMA.Helpers.hmUp, OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
      · norm_num [OMA.Helpers.hmLow, OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
    · apply OMA.Helpers.hm_gen 1 1 0 (by norm_num) (by norm_num) (by norm_num)
      · norm_num [OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
      · norm_num [OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
  · obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 4 ∧ k = 4 * q + s + 2 :=
      ⟨(k - 2) / 4, (k - 2) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    interval_cases s
    · apply OMA.Helpers.hm_gen (4 * q + 0 + 2) ((2 * q + 1) * (4 * q + 3)) q (by omega) (by ring) (by omega)
      · simp only [OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
        push_cast
        ring_nf
        positivity
      · simp only [OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
        push_cast
        ring_nf
        positivity
    · apply OMA.Helpers.hm_gen (4 * q + 1 + 2) ((4 * q + 3) * (2 * q + 2)) q (by omega) (by ring) (by omega)
      · simp only [OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
        push_cast
        ring_nf
        positivity
      · simp only [OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
        push_cast
        ring_nf
        positivity
    · apply OMA.Helpers.hm_gen (4 * q + 2 + 2) ((2 * q + 2) * (4 * q + 5)) q (by omega) (by ring) (by omega)
      · simp only [OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
        push_cast
        ring_nf
        positivity
      · simp only [OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
        push_cast
        ring_nf
        positivity
    · apply OMA.Helpers.hm_gen (4 * q + 3 + 2) ((4 * q + 5) * (2 * q + 3)) q (by omega) (by ring) (by omega)
      · simp only [OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
        push_cast
        ring_nf
        positivity
      · simp only [OMA.Helpers.hmSq2, OMA.Helpers.hmSq4]
        push_cast
        ring_nf
        positivity
