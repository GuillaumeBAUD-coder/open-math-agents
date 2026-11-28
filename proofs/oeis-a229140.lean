import OMAStatements.S_oeis_a229140
import Mathlib

namespace OMA.A229140Proof

open OMA.S_oeis_a229140

lemma inf : (Set.ofPred IsSumTwoSq).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro b
  refine ⟨(b + 1) ^ 2, ⟨0, b + 1, by ring⟩, ?_⟩
  nlinarith

lemma A001481_succ (n : ℕ) : A001481 (n + 1) = Nat.nth IsSumTwoSq n := by
  simp [A001481]

lemma exists_index {x : ℕ} (hx : IsSumTwoSq x) : ∃ n, Nat.nth IsSumTwoSq n = x := by
  obtain ⟨n, -, hn⟩ := Nat.exists_lt_card_nth_eq hx
  exact ⟨n, hn⟩

lemma a_eq_zero_of {n l : ℕ} (h : l ^ 2 = A001481 n) : a n = 0 := by
  have : a n ≤ 0 := Nat.sInf_le ⟨l, by simpa using h⟩
  omega

lemma a_ne_zero_of {n : ℕ} (hn : 1 ≤ n) (h1 : 625 < A001481 n) (h2 : A001481 n < 676) :
    a n ≠ 0 := by
  intro h0
  have hmem : IsSumTwoSq (A001481 n) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [A001481_succ]
    exact Nat.nth_mem_of_infinite inf m
  have hne : {k : ℕ | ∃ l : ℕ, k ^ 2 + l ^ 2 = A001481 n}.Nonempty := by
    obtain ⟨k, l, hkl⟩ := hmem
    exact ⟨k, l, hkl⟩
  have hm := Nat.sInf_mem hne
  rw [show sInf {k : ℕ | ∃ l : ℕ, k ^ 2 + l ^ 2 = A001481 n} = a n from rfl, h0] at hm
  obtain ⟨l, hl⟩ := hm
  rcases Nat.lt_or_ge l 26 with h | h
  · have : l ^ 2 ≤ 25 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  · have : 26 ^ 2 ≤ l ^ 2 := Nat.pow_le_pow_left h 2
    omega

lemma a_628 {n : ℕ} (h : A001481 n = 628) : a n = 12 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨22, by rw [h]; norm_num⟩
  · unfold a
    refine le_csInf ⟨12, 22, by rw [h]; norm_num⟩ ?_
    rintro k ⟨l, hl⟩
    rw [h] at hl
    by_contra hk
    have hl' : l < 26 := by nlinarith
    interval_cases k <;> interval_cases l <;> omega

lemma a_673 {n : ℕ} (h : A001481 n = 673) : a n = 12 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨23, by rw [h]; norm_num⟩
  · unfold a
    refine le_csInf ⟨12, 23, by rw [h]; norm_num⟩ ?_
    rintro k ⟨l, hl⟩
    rw [h] at hl
    by_contra hk
    have hl' : l < 26 := by nlinarith
    interval_cases k <;> interval_cases l <;> omega

theorem main_disproof :
    ¬ (∀ z1 z2 : ℕ, 1 ≤ z1 → z1 < z2 → a z1 = 0 → a z2 = 0 →
      (∀ t, z1 < t → t < z2 → a t ≠ 0) →
      ∀ i j : ℕ, z1 < i → i < j → j < z2 → a i ≠ a j) := by
  intro H
  obtain ⟨n0, h0⟩ := exists_index (x := 625) ⟨0, 25, by norm_num⟩
  obtain ⟨n1, h1⟩ := exists_index (x := 628) ⟨12, 22, by norm_num⟩
  obtain ⟨n2, h2⟩ := exists_index (x := 673) ⟨12, 23, by norm_num⟩
  obtain ⟨n3, h3⟩ := exists_index (x := 676) ⟨0, 26, by norm_num⟩
  have l01 : n0 < n1 := (Nat.nth_lt_nth inf).1 (by omega)
  have l12 : n1 < n2 := (Nat.nth_lt_nth inf).1 (by omega)
  have l23 : n2 < n3 := (Nat.nth_lt_nth inf).1 (by omega)
  have hb : ∀ t, n0 + 1 < t → t < n3 + 1 → a t ≠ 0 := by
    intro t ht1 ht2
    obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
    have e1 : 625 < Nat.nth IsSumTwoSq m := h0 ▸ (Nat.nth_lt_nth inf).2 (by omega)
    have e2 : Nat.nth IsSumTwoSq m < 676 := h3 ▸ (Nat.nth_lt_nth inf).2 (by omega)
    exact a_ne_zero_of (by omega) (by rw [A001481_succ]; exact e1)
      (by rw [A001481_succ]; exact e2)
  refine H (n0 + 1) (n3 + 1) (by omega) (by omega)
    (a_eq_zero_of (l := 25) (by rw [A001481_succ, h0]; norm_num))
    (a_eq_zero_of (l := 26) (by rw [A001481_succ, h3]; norm_num)) hb (n1 + 1) (n2 + 1)
    (by omega) (by omega) (by omega) ?_
  rw [a_628 (by rw [A001481_succ, h1]), a_673 (by rw [A001481_succ, h2])]

end OMA.A229140Proof

open OMA.A229140Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a229140.main) := main_disproof
