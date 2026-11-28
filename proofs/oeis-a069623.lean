import OMAStatements.S_oeis_a069623
import Mathlib

/-!
# A069623: the number of perfect powers up to n is O(sqrt(n))

Every perfect power x = m ^ k with 1 ≤ x ≤ n comes from a pair (m, k) in one of two boxes:
* m ≤ s and k ∈ {2, 3}, where s = Nat.sqrt n (if m = 1 use the pair (1, 2); if k ≤ 3 then
  m ^ 2 ≤ m ^ k ≤ n);
* m ≤ t and 1 ≤ k ≤ 4t, where t = Nat.sqrt s (if k ≥ 4 then m ^ 4 ≤ n, so m ≤ t, and
  2 ^ k ≤ m ^ k ≤ n < (t + 1) ^ 4 ≤ 2 ^ (4t), so k < 4t).
Hence a(n) ≤ 2s + 4t^2 ≤ 6s ≤ 6 sqrt(n).
-/

namespace OMA.P069623

open OMA.S_oeis_a069623

/-- Each perfect power in [1, n] is p.1 ^ p.2 for a pair p in one of the two boxes. -/
lemma mem_image (n x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) (hp : IsPerfectPower x) :
    x ∈ ((Finset.Icc 1 (Nat.sqrt n) ×ˢ Finset.Icc 2 3) ∪
      (Finset.Icc 1 (Nat.sqrt (Nat.sqrt n)) ×ˢ Finset.Icc 1 (4 * Nat.sqrt (Nat.sqrt n)))).image
        (fun p : ℕ × ℕ => p.1 ^ p.2) := by
  obtain ⟨m, k, hk, rfl⟩ := hp
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      rw [zero_pow (by omega)] at hx1
      omega
    · exact h0
  rw [Finset.mem_image]
  by_cases hm1 : m = 1
  · subst hm1
    refine ⟨(1, 2), ?_, by simp⟩
    rw [one_pow] at hxn
    apply Finset.mem_union_left
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨le_refl 1, Nat.le_sqrt.mpr (by omega)⟩, le_refl 2, by norm_num⟩
  · have hm2 : 2 ≤ m := by omega
    by_cases hk3 : k ≤ 3
    · refine ⟨(m, k), ?_, rfl⟩
      apply Finset.mem_union_left
      simp only [Finset.mem_product, Finset.mem_Icc]
      refine ⟨⟨hm, ?_⟩, hk, hk3⟩
      apply Nat.le_sqrt'.mpr
      calc m ^ 2 ≤ m ^ k := Nat.pow_le_pow_right hm hk
        _ ≤ n := hxn
    · have hk4 : 4 ≤ k := by omega
      refine ⟨(m, k), ?_, rfl⟩
      apply Finset.mem_union_right
      simp only [Finset.mem_product, Finset.mem_Icc]
      have h4 : m ^ 4 ≤ n := le_trans (Nat.pow_le_pow_right hm (by omega)) hxn
      have ht : m ≤ Nat.sqrt (Nat.sqrt n) := by
        apply Nat.le_sqrt'.mpr
        apply Nat.le_sqrt'.mpr
        calc (m ^ 2) ^ 2 = m ^ 4 := by ring
          _ ≤ n := h4
      refine ⟨⟨hm, ht⟩, by omega, ?_⟩
      have h1 : n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
      have h2 : Nat.sqrt n < (Nat.sqrt (Nat.sqrt n) + 1) ^ 2 := Nat.lt_succ_sqrt' (Nat.sqrt n)
      have h3 : n < (Nat.sqrt (Nat.sqrt n) + 1) ^ 4 := by
        have h2' : Nat.sqrt n + 1 ≤ (Nat.sqrt (Nat.sqrt n) + 1) ^ 2 := h2
        calc n < (Nat.sqrt n + 1) ^ 2 := h1
          _ ≤ ((Nat.sqrt (Nat.sqrt n) + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h2' 2
          _ = (Nat.sqrt (Nat.sqrt n) + 1) ^ 4 := by ring
      have h5 : Nat.sqrt (Nat.sqrt n) + 1 ≤ 2 ^ Nat.sqrt (Nat.sqrt n) := Nat.lt_two_pow_self
      have h7 : 2 ^ k < 2 ^ (4 * Nat.sqrt (Nat.sqrt n)) := by
        calc 2 ^ k ≤ m ^ k := Nat.pow_le_pow_left hm2 k
          _ ≤ n := hxn
          _ < (Nat.sqrt (Nat.sqrt n) + 1) ^ 4 := h3
          _ ≤ (2 ^ Nat.sqrt (Nat.sqrt n)) ^ 4 := Nat.pow_le_pow_left h5 4
          _ = 2 ^ (4 * Nat.sqrt (Nat.sqrt n)) := by ring
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h7
      omega

/-- The explicit bound a(n) ≤ 6 Nat.sqrt n, for every n. -/
lemma a_le (n : ℕ) : a n ≤ 6 * Nat.sqrt n := by
  classical
  unfold a
  have hsub : (Finset.Icc 1 n).filter IsPerfectPower ⊆
      ((Finset.Icc 1 (Nat.sqrt n) ×ˢ Finset.Icc 2 3) ∪
        (Finset.Icc 1 (Nat.sqrt (Nat.sqrt n)) ×ˢ Finset.Icc 1 (4 * Nat.sqrt (Nat.sqrt n)))).image
          (fun p : ℕ × ℕ => p.1 ^ p.2) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    exact mem_image n x hx.1.1 hx.1.2 hx.2
  have ht : Nat.sqrt (Nat.sqrt n) * Nat.sqrt (Nat.sqrt n) ≤ Nat.sqrt n := Nat.sqrt_le _
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ ≤ _ := Finset.card_union_le _ _
    _ = Nat.sqrt n * 2 + Nat.sqrt (Nat.sqrt n) * (4 * Nat.sqrt (Nat.sqrt n)) := by
        simp [Finset.card_product, Nat.card_Icc]
    _ ≤ 6 * Nat.sqrt n := by nlinarith

theorem sol : type_of% @OMA.S_oeis_a069623.main := by
  apply Asymptotics.IsBigO.of_bound 6
  filter_upwards with n
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc (a n : ℝ) ≤ ((6 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast a_le n
    _ = 6 * (Nat.sqrt n : ℝ) := by push_cast; ring
    _ ≤ 6 * Real.sqrt (n : ℝ) := by gcongr; exact Real.nat_sqrt_le_real_sqrt

end OMA.P069623

theorem OMA.solution : type_of% @OMA.S_oeis_a069623.main := OMA.P069623.sol
