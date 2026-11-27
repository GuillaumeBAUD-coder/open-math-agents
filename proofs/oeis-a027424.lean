import OMAStatements.S_oeis_a027424
import Mathlib

open OMA.S_oeis_a027424 Finset

namespace OMA.P_oeis_a027424

theorem inner_eq (n m : ℕ) :
    S_oeis_a027424.inner n m = (((Icc 1 (n ^ 2)).filter (fun k => k ∣ m ∧ m ≤ n * k ∧ k ≤ n)).card : ℤ) := by
  unfold S_oeis_a027424.inner
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h1 : k ∣ m <;> by_cases h2 : m ≤ n * k <;> by_cases h3 : k ≤ n <;> simp [h1, h2, h3]

theorem mem_prods_iff (n m : ℕ) (hm : 1 ≤ m) :
    m ∈ prods n ↔ ∃ k ∈ Icc 1 (n ^ 2), k ∣ m ∧ m ≤ n * k ∧ k ≤ n := by
  unfold prods
  simp only [mem_image, mem_product, mem_Icc, Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨⟨hi1, hin⟩, hj1, hjn⟩, rfl⟩
    refine ⟨i, ⟨hi1, ?_⟩, dvd_mul_right i j, ?_, hin⟩
    · nlinarith
    · nlinarith
  · rintro ⟨k, ⟨hk1, -⟩, ⟨j, rfl⟩, hle, hkn⟩
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp at hm
      · exact h
    refine ⟨k, j, ⟨⟨hk1, hkn⟩, hj1, ?_⟩, rfl⟩
    have : k * j ≤ k * n := by linarith [mul_comm n k]
    exact Nat.le_of_mul_le_mul_left this (by omega)

theorem sign_inner (n m : ℕ) (hm : 1 ≤ m) :
    Int.sign (S_oeis_a027424.inner n m) = if m ∈ prods n then 1 else 0 := by
  rw [inner_eq]
  by_cases h : m ∈ prods n
  · rw [if_pos h]
    obtain ⟨k, hk, h1, h2, h3⟩ := (mem_prods_iff n m hm).mp h
    have hpos : 0 < ((Icc 1 (n ^ 2)).filter (fun k => k ∣ m ∧ m ≤ n * k ∧ k ≤ n)).card :=
      Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, h1, h2, h3⟩⟩
    exact Int.sign_eq_one_of_pos (by exact_mod_cast hpos)
  · rw [if_neg h]
    have h0 : ((Icc 1 (n ^ 2)).filter (fun k => k ∣ m ∧ m ≤ n * k ∧ k ≤ n)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk hk'
      exact h ((mem_prods_iff n m hm).mpr ⟨k, hk, hk'⟩)
    rw [h0]
    rfl

theorem prods_sub (n : ℕ) : prods n ⊆ Icc 1 (n ^ 2) := by
  intro m hm
  unfold prods at hm
  simp only [mem_image, mem_product, mem_Icc, Prod.exists] at hm
  obtain ⟨i, j, ⟨⟨hi1, hin⟩, hj1, hjn⟩, rfl⟩ := hm
  simp only [mem_Icc]
  constructor
  · nlinarith
  · nlinarith

end OMA.P_oeis_a027424

theorem OMA.solution : type_of% @OMA.S_oeis_a027424.main := by
  intro n _
  rw [Finset.sum_congr rfl (fun m hm => OMA.P_oeis_a027424.sign_inner n m (Finset.mem_Icc.mp hm).1)]
  rw [Finset.sum_boole]
  unfold a
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (OMA.P_oeis_a027424.prods_sub n)]
