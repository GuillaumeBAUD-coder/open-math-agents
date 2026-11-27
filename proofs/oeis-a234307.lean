import OMAStatements.S_oeis_a234307
import Mathlib

open OMA.S_oeis_a234307

theorem a234307_split (f : ℕ → ℚ) (N : ℕ) :
    ∑ k ∈ Finset.range (2 * N), f k =
      ∑ t ∈ Finset.range N, f (2 * t) + ∑ t ∈ Finset.range N, f (2 * t + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

theorem a234307_icc (f : ℕ → ℚ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, f k = ∑ k ∈ Finset.range N, f (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem a234307_odd (t m : ℕ) : Nat.gcd (2 * t + 1) (2 * m) = Nat.gcd (2 * t + 1) m := by
  apply Nat.Coprime.gcd_mul_left_cancel_right
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a234307.main := by
  intro n hn
  have hL : (a n : ℚ) = ∑ s ∈ Finset.range n, (Nat.gcd (s + 1) (2 * n) : ℚ) := by
    unfold a
    push_cast
    rw [a234307_icc (fun i => (Nat.gcd (2 * n - i) i : ℚ))]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_range] at hs
    rw [Nat.gcd_sub_self_left (by omega), Nat.gcd_comm]
  -- odd part
  set u : ℕ → ℚ := fun t => (Nat.gcd (2 * t + 1) (4 * n) : ℚ) with hu
  have hodd : ∑ t ∈ Finset.range (2 * n), u t = 2 * ∑ t ∈ Finset.range n, u t := by
    rw [two_mul n, Finset.sum_range_add, two_mul]
    congr 1
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    simp only [hu]
    have h1 : 2 * (n + (n - 1 - t)) + 1 = 4 * n - (2 * t + 1) := by omega
    rw [h1, Nat.gcd_self_sub_left (by omega)]
  have hR : ∑ k ∈ Finset.Icc 1 (4 * n), (-1 : ℚ) ^ k * (Nat.gcd k (8 * n) : ℚ) =
      ∑ t ∈ Finset.range (2 * n), (Nat.gcd (2 * t + 2) (8 * n) : ℚ) -
        ∑ t ∈ Finset.range (2 * n), u t := by
    rw [a234307_icc, show 4 * n = 2 * (2 * n) by ring, a234307_split]
    rw [sub_eq_neg_add, ← Finset.sum_neg_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro t _
      simp only [hu]
      rw [show 8 * n = 2 * (4 * n) by ring, a234307_odd, pow_succ, pow_mul]
      norm_num
    · apply Finset.sum_congr rfl
      intro t _
      rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring, pow_mul]
      norm_num
  have hE : ∑ t ∈ Finset.range (2 * n), (Nat.gcd (2 * t + 2) (8 * n) : ℚ) =
      2 * ∑ t ∈ Finset.range n, u t + 4 * ∑ s ∈ Finset.range n, (Nat.gcd (s + 1) (2 * n) : ℚ) := by
    rw [a234307_split, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro t _
      simp only [hu]
      rw [show 2 * (2 * t) + 2 = 2 * (2 * t + 1) by ring, show 8 * n = 2 * (4 * n) by ring,
        Nat.gcd_mul_left]
      push_cast; ring
    · apply Finset.sum_congr rfl
      intro t _
      rw [show 2 * (2 * t + 1) + 2 = 4 * (t + 1) by ring, show 8 * n = 4 * (2 * n) by ring,
        Nat.gcd_mul_left]
      push_cast; ring
  rw [hL, hR, hE, hodd]
  ring
