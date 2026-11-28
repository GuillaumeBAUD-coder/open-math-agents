import OMAReductions.R_opg_strange_series_R1
import Mathlib

-- Credit: @LordMike

open OMA.S_opg_strange_series

lemma qs_f_even (m : ℕ) (hm : m % 2 = 0) (h1 : m ≠ 1) : f m = m / 2 := by
  unfold f
  split_ifs <;> omega

lemma qs_f_odd (m : ℕ) (hm : m % 2 = 1) (h1 : m ≠ 1) : f m = 3 * m + 1 := by
  unfold f
  split_ifs <;> omega

lemma qs_even_eq {m p : ℕ} (hm : m % 2 = 0) (h1 : m ≠ 1) (hp : m / 2 = p) : f m = p := by
  rw [qs_f_even m hm h1, hp]

lemma qs_odd_eq {m p : ℕ} (hm : m % 2 = 1) (h1 : m ≠ 1) (hp : 3 * m + 1 = p) : f m = p := by
  rw [qs_f_odd m hm h1, hp]

lemma qs_iter3 (g : ℕ → ℕ) (x : ℕ) : g^[3] x = g (g (g x)) := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]

lemma qs_iter6 (g : ℕ → ℕ) (x : ℕ) : g^[6] x = g (g (g (g (g (g x))))) := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]

lemma qs_iter8 (g : ℕ → ℕ) (x : ℕ) : g^[8] x = g (g (g (g (g (g (g (g x))))))) := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]

lemma qs_desc_even (n : ℕ) (hn : 1 < n) (h : n % 2 = 0) : ∃ k : ℕ, f^[k] n < n := by
  refine ⟨1, ?_⟩
  rw [Function.iterate_one, qs_f_even n h (by omega)]
  omega

lemma qs_desc_4 (n : ℕ) (hn : 1 < n) (h : n % 4 = 1) : ∃ k : ℕ, f^[k] n < n := by
  refine ⟨3, ?_⟩
  rw [qs_iter3, qs_f_odd n (by omega) (by omega), qs_f_even (3 * n + 1) (by omega) (by omega),
    qs_f_even ((3 * n + 1) / 2) (by omega) (by omega)]
  omega

lemma qs11_1 (b : ℕ) : f (32 * b + 11) = 96 * b + 34 := qs_odd_eq (by omega) (by omega) (by omega)
lemma qs11_2 (b : ℕ) : f (96 * b + 34) = 48 * b + 17 := qs_even_eq (by omega) (by omega) (by omega)
lemma qs11_3 (b : ℕ) : f (48 * b + 17) = 144 * b + 52 := qs_odd_eq (by omega) (by omega) (by omega)
lemma qs11_4 (b : ℕ) : f (144 * b + 52) = 72 * b + 26 := qs_even_eq (by omega) (by omega) (by omega)
lemma qs11_5 (b : ℕ) : f (72 * b + 26) = 36 * b + 13 := qs_even_eq (by omega) (by omega) (by omega)
lemma qs11_6 (b : ℕ) : f (36 * b + 13) = 108 * b + 40 := qs_odd_eq (by omega) (by omega) (by omega)
lemma qs11_7 (b : ℕ) : f (108 * b + 40) = 54 * b + 20 := qs_even_eq (by omega) (by omega) (by omega)
lemma qs11_8 (b : ℕ) : f (54 * b + 20) = 27 * b + 10 := qs_even_eq (by omega) (by omega) (by omega)

lemma qs23_1 (b : ℕ) : f (32 * b + 23) = 96 * b + 70 := qs_odd_eq (by omega) (by omega) (by omega)
lemma qs23_2 (b : ℕ) : f (96 * b + 70) = 48 * b + 35 := qs_even_eq (by omega) (by omega) (by omega)
lemma qs23_3 (b : ℕ) : f (48 * b + 35) = 144 * b + 106 := qs_odd_eq (by omega) (by omega) (by omega)
lemma qs23_4 (b : ℕ) : f (144 * b + 106) = 72 * b + 53 := qs_even_eq (by omega) (by omega) (by omega)
lemma qs23_5 (b : ℕ) : f (72 * b + 53) = 216 * b + 160 := qs_odd_eq (by omega) (by omega) (by omega)
lemma qs23_6 (b : ℕ) : f (216 * b + 160) = 108 * b + 80 := qs_even_eq (by omega) (by omega) (by omega)
lemma qs23_7 (b : ℕ) : f (108 * b + 80) = 54 * b + 40 := qs_even_eq (by omega) (by omega) (by omega)
lemma qs23_8 (b : ℕ) : f (54 * b + 40) = 27 * b + 20 := qs_even_eq (by omega) (by omega) (by omega)

lemma qs16_1 (a : ℕ) : f (16 * a + 3) = 48 * a + 10 := qs_odd_eq (by omega) (by omega) (by omega)
lemma qs16_2 (a : ℕ) : f (48 * a + 10) = 24 * a + 5 := qs_even_eq (by omega) (by omega) (by omega)
lemma qs16_3 (a : ℕ) : f (24 * a + 5) = 72 * a + 16 := qs_odd_eq (by omega) (by omega) (by omega)
lemma qs16_4 (a : ℕ) : f (72 * a + 16) = 36 * a + 8 := qs_even_eq (by omega) (by omega) (by omega)
lemma qs16_5 (a : ℕ) : f (36 * a + 8) = 18 * a + 4 := qs_even_eq (by omega) (by omega) (by omega)
lemma qs16_6 (a : ℕ) : f (18 * a + 4) = 9 * a + 2 := qs_even_eq (by omega) (by omega) (by omega)

lemma qs_desc_16 (n : ℕ) (hn : 1 < n) (h : n % 16 = 3) : ∃ k : ℕ, f^[k] n < n := by
  obtain ⟨a, rfl⟩ : ∃ a, n = 16 * a + 3 := ⟨n / 16, by omega⟩
  refine ⟨6, ?_⟩
  rw [qs_iter6, qs16_1, qs16_2, qs16_3, qs16_4, qs16_5, qs16_6]
  omega

lemma qs_desc_11 (n : ℕ) (hn : 1 < n) (h : n % 32 = 11) : ∃ k : ℕ, f^[k] n < n := by
  obtain ⟨b, rfl⟩ : ∃ b, n = 32 * b + 11 := ⟨n / 32, by omega⟩
  refine ⟨8, ?_⟩
  rw [qs_iter8, qs11_1, qs11_2, qs11_3, qs11_4, qs11_5, qs11_6, qs11_7, qs11_8]
  omega

lemma qs_desc_23 (n : ℕ) (hn : 1 < n) (h : n % 32 = 23) : ∃ k : ℕ, f^[k] n < n := by
  obtain ⟨b, rfl⟩ : ∃ b, n = 32 * b + 23 := ⟨n / 32, by omega⟩
  refine ⟨8, ?_⟩
  rw [qs_iter8, qs23_1, qs23_2, qs23_3, qs23_4, qs23_5, qs23_6, qs23_7, qs23_8]
  omega

theorem OMA.solution : OMA.R_opg_strange_series_R1.H1 := by
  unfold OMA.R_opg_strange_series_R1.H1
  intro n hn h7 h15 h27 h31
  by_cases h2 : n % 2 = 0
  · exact qs_desc_even n hn h2
  · have hcases : n % 4 = 1 ∨ n % 16 = 3 ∨ n % 32 = 11 ∨ n % 32 = 23 := by omega
    rcases hcases with h | h | h | h
    · exact qs_desc_4 n hn h
    · exact qs_desc_16 n hn h
    · exact qs_desc_11 n hn h
    · exact qs_desc_23 n hn h
