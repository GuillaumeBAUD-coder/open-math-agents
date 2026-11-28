import OMAStatements.S_oeis_a266595
import Mathlib

open OMA.S_oeis_a266595

private def live (t : ℕ) (i : ℤ) : Prop :=
  (t = 0 ∧ i = 0) ∨ (t = 1 ∧ i ≠ -1 ∧ i ≠ 1) ∨ (2 ≤ t ∧ t % 2 = 0 ∧ -1 ≤ i ∧ i ≤ 1) ∨ (3 ≤ t ∧ t % 2 = 1 ∧ (i ≤ -3 ∨ 3 ≤ i))

private lemma table (l c r : Bool) :
    eca 37 l c r = true ↔ (l = false ∧ r = false) ∨ (l = true ∧ c = false ∧ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

set_option maxHeartbeats 4000000 in
private lemma state_iff (t : ℕ) (i : ℤ) : state t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [state, live]
  | succ t ih =>
    rw [state, table]
    simp only [Bool.eq_false_iff, ne_eq, ih, live]
    omega

private lemma cnt2 (t : ℕ) (ht : 2 ≤ t) (p : ℕ → Bool) (c : Bool)
    (h : ∀ k < 2 * t + 1, (k < t - 2 ∨ t + 2 < k) → p k = c) :
    ((Finset.range (2 * t + 1)).filter fun k => p k = true).card =
      (if c then 2 * t - 4 else 0) + ((if p (t - 2) then 1 else 0) + (if p (t - 2 + 1) then 1 else 0) +
        (if p (t - 2 + 2) then 1 else 0) + (if p (t - 2 + 3) then 1 else 0) +
        (if p (t - 2 + 4) then 1 else 0)) := by
  have h1 : ∑ x ∈ Finset.range (t - 2), (if p x = true then 1 else 0) =
      ∑ x ∈ Finset.range (t - 2), (if c = true then 1 else 0) :=
    Finset.sum_congr rfl (fun k hk => by simp at hk; rw [h k (by omega) (by omega)])
  have h3 : ∑ x ∈ Finset.range (t - 2), (if p (t - 2 + 5 + x) = true then 1 else 0) =
      ∑ x ∈ Finset.range (t - 2), (if c = true then 1 else 0) :=
    Finset.sum_congr rfl (fun k hk => by simp at hk; rw [h _ (by omega) (by omega)])
  rw [Finset.card_filter, show 2 * t + 1 = (t - 2) + 5 + (t - 2) by omega, Finset.sum_range_add,
    Finset.sum_range_add, h1, h3]
  simp only [Finset.sum_const, Finset.card_range, Finset.sum_range_succ, Finset.sum_range_zero,
    smul_eq_mul, zero_add, Nat.add_zero]
  cases c <;> simp <;> omega

private def blk (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => state t ((i : ℤ) - (t : ℤ))).card

private def bf (t : ℕ) : ℕ := if t ≤ 1 then 1 else if t % 2 = 0 then 3 else 2 * t - 4

private def bz (t : ℕ) : ℤ := if t ≤ 1 then 1 else if t % 2 = 0 then 3 else 2 * (t : ℤ) - 4

private lemma bfz (t : ℕ) : (bf t : ℤ) = bz t := by
  unfold bf bz; split_ifs <;> push_cast <;> omega

private lemma blk_eq (t : ℕ) : blk t = bf t := by
  rcases Nat.lt_or_ge t 2 with h | h
  · interval_cases t <;> decide
  · unfold blk
    rw [cnt2 t h _ (decide (t % 2 = 1))]
    · unfold bf
      have e0 : state t (((t - 2 : ℕ) : ℤ) - t) = decide (t = t + 1) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff, decide_eq_true_iff]; unfold live
        omega
      have e1 : state t (((t - 2 + 1 : ℕ) : ℤ) - t) = decide (t % 2 = 0) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff, decide_eq_true_iff]; unfold live
        omega
      have e2 : state t (((t - 2 + 2 : ℕ) : ℤ) - t) = decide (t % 2 = 0) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff, decide_eq_true_iff]; unfold live
        omega
      have e3 : state t (((t - 2 + 3 : ℕ) : ℤ) - t) = decide (t % 2 = 0) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff, decide_eq_true_iff]; unfold live
        omega
      have e4 : state t (((t - 2 + 4 : ℕ) : ℤ) - t) = decide (t = t + 1) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff, decide_eq_true_iff]; unfold live
        omega
      rw [e0, e1, e2, e3, e4]
      split_ifs <;> simp_all <;> omega
    · intro k hk hk'
      apply Bool.eq_iff_iff.mpr; rw [state_iff]; simp only [decide_eq_true_eq, live]
      omega

private lemma white_eq (t : ℕ) : white t = 2 * t + 1 - blk t := by
  unfold white blk
  have := Finset.card_filter_add_card_filter_not (s := Finset.range (2 * t + 1))
    (p := fun i : ℕ => state t ((i : ℤ) - (t : ℤ)) = true)
  simp only [Bool.not_eq_true, Finset.card_range] at this
  omega

private lemma cf (t : ℕ) : (white t : ℤ) = 2 * t + 1 - bz t := by
  have h1 := white_eq t
  have h2 : blk t ≤ 2 * t + 1 := by
    unfold blk; exact (Finset.card_filter_le _ _).trans (by simp)
  rw [← bfz, h1, blk_eq] at *; push_cast [h2]; omega

private lemma cn (t : ℕ) : white t = 2 * t + 1 - bf t := by rw [white_eq, blk_eq]

private lemma ev (m : ℕ) : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
private lemma od (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a266595.main) := by
  intro h
  have h5 := h.2.1 5 (by norm_num)
  have v5 : a 5 = 5 := by simp [a, cn, bf]
  have v3 : a 3 = 5 := by simp [a, cn, bf]
  have v1 : a 1 = 2 := by simp [a, cn, bf]
  simp only [show (5 : ℕ) - 2 = 3 from rfl, show (5 : ℕ) - 4 = 1 from rfl, v5, v3, v1] at h5
  norm_num at h5
