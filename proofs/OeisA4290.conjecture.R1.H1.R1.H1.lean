import OMAReductions.R_OeisA4290_conjecture_R1_H1_R1
import Mathlib

-- Step OeisA4290.conjecture.R1.H1.R1.H1: hypothesis H1 of reduction OeisA4290.conjecture.R1.H1.R1
-- Credit: @ivillar. Digit stacking: layer l of n has a 1 wherever the digit of n exceeds l; the nine layers
-- are stacked in blocks of t digits, which is congruent to n modulo 10^t - 1.

/-! Multiples with digits 0 and 1 for divisors of 10^t - 1. -/

namespace P7A4290H1

/-- All decimal digits are `0` or `1`. -/
def D01 (m : ℕ) : Prop := ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

lemma d01_step (a y : ℕ) (ha : a ≤ 1) (hy : D01 y) : D01 (a + 10 * y) := by
  rcases Nat.eq_zero_or_pos y with rfl | hy0
  · interval_cases a <;> simp [D01]
  · intro d hd
    rw [Nat.digits_add 10 (by norm_num) a y (by omega) (Or.inr hy0.ne')] at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · omega
    · exact hy d hd

lemma d01_mod (B : ℕ) (h : D01 B) : B % 10 ≤ 1 ∧ D01 (B / 10) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp [D01]
  · have hd := Nat.digits_def' (by norm_num : 1 < 10) hB
    refine ⟨?_, fun d hd' => h d (by rw [hd]; exact List.mem_cons_of_mem _ hd')⟩
    rcases h (B % 10) (by rw [hd]; exact List.mem_cons_self) with h0 | h0 <;> omega

lemma d01_concat (t : ℕ) : ∀ B C : ℕ, B < 10 ^ t → D01 B → D01 C → D01 (B + 10 ^ t * C) := by
  induction t with
  | zero =>
    intro B C hB _ hC
    have : B = 0 := by simpa using hB
    subst this
    simpa using hC
  | succ t ih =>
    intro B C hB hDB hC
    obtain ⟨h1, h2⟩ := d01_mod B hDB
    have hlt : B / 10 < 10 ^ t := by
      rw [pow_succ] at hB
      omega
    have := d01_step (B % 10) (B / 10 + 10 ^ t * C) h1 (ih (B / 10) C hlt h2 hC)
    have e : B % 10 + 10 * (B / 10 + 10 ^ t * C) = B + 10 ^ (t + 1) * C := by
      rw [pow_succ]
      have := Nat.mod_add_div B 10
      nlinarith
    rwa [e] at this

/-- The `l`-th digit layer of `x`: a `1` at every position whose digit exceeds `l`. -/
def blk (l : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | s + 1, x => (if l < x % 10 then 1 else 0) + 10 * blk l s (x / 10)

lemma blk_d01 (l s x : ℕ) : D01 (blk l s x) := by
  induction s generalizing x with
  | zero => simp [blk, D01]
  | succ s ih =>
    simp only [blk]
    exact d01_step _ _ (by split_ifs <;> omega) (ih _)

lemma blk_bound (l s x : ℕ) : 9 * blk l s x + 1 ≤ 10 ^ s := by
  induction s generalizing x with
  | zero => simp [blk]
  | succ s ih =>
    simp only [blk, pow_succ]
    have := ih (x / 10)
    split_ifs <;> omega

lemma sum_ite (d : ℕ) (hd : d < 10) :
    ∑ l ∈ Finset.range 9, (if l < d then 1 else 0) = d := by
  interval_cases d <;> decide

lemma blk_sum (s x : ℕ) (hx : x < 10 ^ s) : ∑ l ∈ Finset.range 9, blk l s x = x := by
  induction s generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    subst this
    simp [blk]
  | succ s ih =>
    simp only [blk]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_ite _ (Nat.mod_lt _ (by norm_num)),
      ih (x / 10) (by rw [pow_succ] at hx; omega)]
    omega

/-- Stack the nine layers `l, l+1, ...` in blocks of `t` digits. -/
def S (t x : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | l, j + 1 => blk l t x + 10 ^ t * S t x (l + 1) j

lemma S_d01 (t x l j : ℕ) : D01 (S t x l j) := by
  induction j generalizing l with
  | zero => simp [S, D01]
  | succ j ih =>
    simp only [S]
    exact d01_concat t _ _ (by have := blk_bound l t x; omega) (blk_d01 _ _ _) (ih _)

lemma S_modEq (t x l j : ℕ) :
    S t x l j ≡ ∑ i ∈ Finset.range j, blk (l + i) t x [MOD 10 ^ t - 1] := by
  have h1 : 10 ^ t ≡ 1 [MOD 10 ^ t - 1] := by
    have hp : 1 ≤ 10 ^ t := Nat.one_le_pow _ _ (by norm_num)
    exact (Nat.modEq_iff_dvd' hp).mpr dvd_rfl |>.symm
  induction j generalizing l with
  | zero => simp [S]; rfl
  | succ j ih =>
    simp only [S]
    have e : ∑ i ∈ Finset.range (j + 1), blk (l + i) t x =
        blk l t x + ∑ i ∈ Finset.range j, blk (l + 1 + i) t x := by
      rw [Finset.sum_range_succ', add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring
    rw [e]
    have := (h1.mul (ih (l + 1))).add_left (blk l t x)
    simpa only [one_mul] using this

lemma S_ge (t x l j : ℕ) : ∑ i ∈ Finset.range j, blk (l + i) t x ≤ S t x l j := by
  induction j generalizing l with
  | zero => simp [S]
  | succ j ih =>
    simp only [S]
    rw [Finset.sum_range_succ']
    have h := ih (l + 1)
    have hp : 1 ≤ 10 ^ t := Nat.one_le_pow _ _ (by norm_num)
    have e : ∑ i ∈ Finset.range j, blk (l + (i + 1)) t x = ∑ i ∈ Finset.range j, blk (l + 1 + i) t x := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring
    rw [e, add_zero]
    nlinarith

lemma S_bound (t x l j : ℕ) : 9 * S t x l j + 1 ≤ 10 ^ (t * j) := by
  induction j generalizing l with
  | zero => simp [S]
  | succ j ih =>
    simp only [S]
    have h1 := blk_bound l t x
    have h2 := ih (l + 1)
    rw [show t * (j + 1) = t + t * j by ring, pow_add]
    nlinarith [Nat.mul_le_mul_left (10 ^ t) h2]

lemma S_bound_lt (t x l j : ℕ) (i : ℕ) (hi : i < j) (h : 9 * blk (l + i) t x + 1 < 10 ^ t) :
    9 * S t x l j + 1 < 10 ^ (t * j) := by
  induction j generalizing l i with
  | zero => omega
  | succ j ih =>
    simp only [S]
    have h1 := blk_bound l t x
    have h2 := S_bound t x (l + 1) j
    rw [show t * (j + 1) = t + t * j by ring, pow_add]
    rcases i with _ | i
    · simp only [add_zero] at h
      nlinarith [Nat.mul_le_mul_left (10 ^ t) h2]
    · have h3 := ih (l + 1) i (by omega) (by rw [show l + 1 + i = l + (i + 1) by ring]; exact h)
      nlinarith [Nat.mul_le_mul_left (10 ^ t) h3]

lemma finish (k m : ℕ) (h : 9 * m + 2 ≤ 10 ^ (9 * k)) : m < (10 ^ (9 * k) - 1) / 9 := by
  have hd : 9 ∣ 10 ^ (9 * k) - 1 := by
    have h := (show 10 ≡ 1 [MOD 9] by decide).pow (9 * k)
    rw [one_pow] at h
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h.symm
  obtain ⟨R, hR⟩ := hd
  rw [hR, Nat.mul_div_cancel_left _ (by norm_num)]
  omega

end P7A4290H1

open P7A4290H1

theorem OMA.solution : OMA.R_OeisA4290_conjecture_R1_H1_R1.H1 := by
  unfold OMA.R_OeisA4290_conjecture_R1_H1_R1.H1
  intro k n t hn hnk ht htk hdvd
  have hp : 1 ≤ 10 ^ t := Nat.one_le_pow _ _ (by norm_num)
  have hn1 : n ≤ 10 ^ t - 1 := Nat.le_of_dvd (by
    have : 10 ^ 1 ≤ 10 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    omega) hdvd
  have hsum := blk_sum t n (by omega)
  refine ⟨S t n 0 9, ?_, ?_, ?_, S_d01 t n 0 9⟩
  · apply finish
    have hkt : 10 ^ (9 * t) ≤ 10 ^ (9 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    by_cases hc : n < 10 ^ t - 1
    · obtain ⟨l, hl, hlt⟩ : ∃ l ∈ Finset.range 9, 9 * blk l t n + 1 < 10 ^ t := by
        by_contra hne
        simp only [not_exists, not_and, not_lt] at hne
        have := Finset.sum_le_sum hne
        simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hsum] at this
        omega
      have := S_bound_lt t n 0 9 l (Finset.mem_range.mp hl) (by simpa using hlt)
      rw [mul_comm t 9] at this
      omega
    · have htk' : t < k := by
        rcases Nat.lt_or_ge t k with h | h
        · exact h
        · have : t = k := by omega
          subst this
          omega
      have := S_bound t n 0 9
      have hlt : 10 ^ (9 * t) < 10 ^ (9 * k) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      rw [mul_comm t 9] at this
      omega
  · have := S_ge t n 0 9
    simp only [zero_add] at this
    omega
  · have hm := (S_modEq t n 0 9).of_dvd hdvd
    simp only [zero_add, hsum] at hm
    exact Nat.dvd_of_mod_eq_zero (by rw [hm, Nat.mod_self])
