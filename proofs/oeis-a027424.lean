import OMAStatements.S_oeis_a027424

namespace OMA.S_oeis_a027424

open Finset




/-- The entry's conjecture. -/
def Conjecture : Prop := ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = ∑ m ∈ Icc 1 (n ^ 2), Int.sign (inner n m)

theorem inner_eq (n m : ℕ) :
    inner n m = (((Icc 1 (n ^ 2)).filter fun k => k ∣ m ∧ m ≤ n * k ∧ k ≤ n).card : ℤ) := by
  rw [inner, card_filter]
  push_cast
  refine sum_congr rfl fun k _ => ?_
  by_cases h1 : k ∣ m <;> by_cases h2 : m ≤ n * k <;> by_cases h3 : k ≤ n <;> simp [h1, h2, h3]

theorem mem_prods {n m : ℕ} : m ∈ prods n ↔ ∃ i j, 1 ≤ i ∧ i ≤ n ∧ 1 ≤ j ∧ j ≤ n ∧ i * j = m := by
  simp only [prods, mem_image, mem_product, mem_Icc, Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    exact ⟨i, j, h1, h2, h3, h4, rfl⟩
  · rintro ⟨i, j, h1, h2, h3, h4, rfl⟩
    exact ⟨i, j, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩

theorem filter_nonempty_iff {n m : ℕ} (hm : 1 ≤ m) :
    ((Icc 1 (n ^ 2)).filter fun k => k ∣ m ∧ m ≤ n * k ∧ k ≤ n).Nonempty ↔ m ∈ prods n := by
  rw [mem_prods]
  constructor
  · rintro ⟨k, hk⟩
    simp only [mem_filter, mem_Icc] at hk
    obtain ⟨⟨hk1, -⟩, ⟨j, rfl⟩, hle, hkn⟩ := hk
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp at hm
      · exact h
    have hjn : j ≤ n := by
      have : k * j ≤ k * n := by linarith [mul_comm n k]
      exact Nat.le_of_mul_le_mul_left this (by omega)
    exact ⟨k, j, hk1, hkn, hj, hjn, rfl⟩
  · rintro ⟨i, j, h1, h2, h3, h4, rfl⟩
    refine ⟨i, ?_⟩
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨h1, ?_⟩, dvd_mul_right i j, ?_, h2⟩
    · nlinarith
    · nlinarith

theorem sign_inner {n m : ℕ} (hm : 1 ≤ m) :
    Int.sign (inner n m) = if m ∈ prods n then 1 else 0 := by
  rw [inner_eq]
  split_ifs with h
  · have hpos := (filter_nonempty_iff hm).2 h
    have : 0 < ((Icc 1 (n ^ 2)).filter fun k => k ∣ m ∧ m ≤ n * k ∧ k ≤ n).card :=
      card_pos.2 hpos
    exact Int.sign_eq_one_of_pos (by exact_mod_cast this)
  · have hne : ¬ ((Icc 1 (n ^ 2)).filter fun k => k ∣ m ∧ m ≤ n * k ∧ k ≤ n).Nonempty :=
      fun hne => h ((filter_nonempty_iff hm).1 hne)
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty]
    rfl

theorem prods_subset (n : ℕ) : prods n ⊆ Icc 1 (n ^ 2) := by
  intro m hm
  obtain ⟨i, j, h1, h2, h3, h4, rfl⟩ := mem_prods.1 hm
  simp only [mem_Icc]
  constructor
  · nlinarith
  · nlinarith

theorem proof : Conjecture := by
  intro n _
  rw [sum_congr rfl fun m hm => sign_inner (mem_Icc.1 hm).1, sum_boole, filter_mem_eq_inter,
    inter_eq_right.2 (prods_subset n), a]

/-- Control: the first terms of the entry. -/
theorem a_values : (List.range 12).map (fun n => a (n + 1)) = [1, 3, 6, 9, 14, 18, 25, 30, 36, 42, 53, 59] := by
  decide +kernel

end OMA.S_oeis_a027424

theorem OMA.solution : type_of% @OMA.S_oeis_a027424.main :=
  OMA.S_oeis_a027424.proof
