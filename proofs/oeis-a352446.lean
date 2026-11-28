import OMAStatements.S_oeis_a352446
import Mathlib

namespace ConsecutiveParts

open Finset OMA.S_oeis_a352446

private theorem sum_even_length (j k : ℕ) :
    consecSum (j + 1) (2 * k) = k * (2 * k + 1) + 2 * k * j := by
  induction k with
  | zero => simp [consecSum]
  | succ k ih =>
    have hlen : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    conv_lhs =>
      rw [hlen, consecSum, sum_range_succ, sum_range_succ]
    change consecSum (j + 1) (2 * k) + (j + 1 + 2 * k) + (j + 1 + (2 * k + 1)) = _
    rw [ih]
    ring

private theorem reindex (n : ℕ) :
    a n = ∑ k ∈ Icc 1 n, ∑ j ∈ range (n + 1),
      if k * (2 * k + 1) + 2 * k * j = n then 2 * k else 0 := by
  let s := (Icc 1 n ×ˢ Icc 1 n).filter (fun p : ℕ × ℕ =>
    Even p.2 ∧ consecSum p.1 p.2 = n)
  let t := (Icc 1 n ×ˢ range (n + 1)).filter (fun p : ℕ × ℕ =>
    p.1 * (2 * p.1 + 1) + 2 * p.1 * p.2 = n)
  have hs {m L : ℕ} : (m, L) ∈ s ↔
      (1 ≤ m ∧ m ≤ n) ∧ (1 ≤ L ∧ L ≤ n) ∧ Even L ∧ consecSum m L = n := by
    simp only [s, mem_filter, mem_product, mem_Icc, and_assoc]
  have ht {k j : ℕ} : (k, j) ∈ t ↔
      (1 ≤ k ∧ k ≤ n) ∧ j < n + 1 ∧ k * (2 * k + 1) + 2 * k * j = n := by
    simp only [t, mem_filter, mem_product, mem_Icc, mem_range, and_assoc]
  calc
    a n = ∑ p ∈ s, p.2 := by
      simp only [a, s, sum_filter, sum_product]
    _ = ∑ p ∈ t, 2 * p.1 := by
      refine sum_nbij' (fun p : ℕ × ℕ => (p.2 / 2, p.1 - 1))
        (fun p : ℕ × ℕ => (p.2 + 1, 2 * p.1)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨m, L⟩ hp
        obtain ⟨⟨hm, hmn⟩, ⟨hL, hLn⟩, ⟨k, hk⟩, hsum⟩ := hs.mp hp
        have htwo : L = 2 * k := by omega
        have hstart : m - 1 + 1 = m := by omega
        change (L / 2, m - 1) ∈ t
        rw [htwo, show 2 * k / 2 = k by omega]
        refine ht.mpr ⟨⟨by omega, by omega⟩, by omega, ?_⟩
        rw [htwo, ← hstart, sum_even_length] at hsum
        exact hsum
      · rintro ⟨k, j⟩ hp
        obtain ⟨⟨hk, _⟩, _, hsum⟩ := ht.mp hp
        have hlength : 2 * k ≤ k * (2 * k + 1) := by
          simpa [Nat.mul_comm 2 k] using Nat.mul_le_mul_left k (show 2 ≤ 2 * k + 1 by omega)
        have hj : j ≤ 2 * k * j := by
          simpa using Nat.mul_le_mul_right j (show 1 ≤ 2 * k by omega)
        change (j + 1, 2 * k) ∈ s
        exact hs.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
          ⟨k, by omega⟩, (sum_even_length j k).trans hsum⟩
      · rintro ⟨m, L⟩ hp
        obtain ⟨⟨hm, _⟩, _, ⟨k, hk⟩, _⟩ := hs.mp hp
        exact Prod.ext (by dsimp; omega) (by dsimp; omega)
      · rintro ⟨k, j⟩ _
        exact Prod.ext (by dsimp; omega) rfl
      · rintro ⟨m, L⟩ hp
        obtain ⟨_, _, ⟨k, hk⟩, _⟩ := hs.mp hp
        dsimp
        omega
    _ = _ := by
      simp only [t, sum_filter, sum_product]

end ConsecutiveParts

theorem OMA.solution : type_of% @OMA.S_oeis_a352446.main := by
  intro n _
  exact ConsecutiveParts.reindex n