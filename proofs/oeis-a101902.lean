import OMAStatements.S_oeis_a101902
import Mathlib

namespace OMA.Helpers

theorem a101902_rep (n : ℕ) (hn : 0 < n) (hnot : ¬ (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 12 ∨ n = 14 ∨ n = 18 ∨ n = 30 ∨ n = 38 ∨ n = 42 ∨ n = 62)) :
    ∃ a b c d e : ℕ, 1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧
      a * b + b * c + c * d + d * e + e * a = n := by
  by_cases hbig : 84 ≤ n
  · rcases (by omega : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6) with h | h | h | h | h | h | h
    · exact ⟨1, 2, 5, 6, n / 7 - 6, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, 1, 1, 6, n / 7 - 1, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, 3, 3, 6, n / 7 - 4, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨2, 3, 4, 5, n / 7 - 5, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, 2, 2, 6, n / 7 - 2, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, 2, 3, 6, n / 7 - 3, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, 2, 4, 6, n / 7 - 4, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · interval_cases n
    · omega
    · omega
    · omega
    · omega
    · exact ⟨1, 1, 1, 1, 1, by norm_num⟩
    · omega
    · exact ⟨1, 1, 1, 1, 2, by norm_num⟩
    · omega
    · exact ⟨1, 1, 1, 1, 3, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 2, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 4, by norm_num⟩
    · omega
    · exact ⟨1, 1, 1, 1, 5, by norm_num⟩
    · omega
    · exact ⟨1, 1, 1, 1, 6, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 4, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 7, by norm_num⟩
    · omega
    · exact ⟨1, 1, 1, 1, 8, by norm_num⟩
    · exact ⟨2, 2, 2, 2, 2, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 9, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 6, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 10, by norm_num⟩
    · exact ⟨1, 2, 2, 3, 3, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 11, by norm_num⟩
    · exact ⟨1, 1, 1, 4, 4, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 12, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 8, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 13, by norm_num⟩
    · omega
    · exact ⟨1, 1, 1, 1, 14, by norm_num⟩
    · exact ⟨1, 2, 2, 3, 5, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 15, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 10, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 16, by norm_num⟩
    · exact ⟨1, 1, 1, 4, 6, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 17, by norm_num⟩
    · omega
    · exact ⟨1, 1, 1, 1, 18, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 12, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 19, by norm_num⟩
    · omega
    · exact ⟨1, 1, 1, 1, 20, by norm_num⟩
    · exact ⟨1, 2, 2, 3, 8, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 21, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 14, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 22, by norm_num⟩
    · exact ⟨1, 2, 2, 3, 9, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 23, by norm_num⟩
    · exact ⟨1, 1, 1, 6, 6, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 24, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 16, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 25, by norm_num⟩
    · exact ⟨1, 2, 2, 4, 8, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 26, by norm_num⟩
    · exact ⟨1, 1, 1, 4, 10, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 27, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 18, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 28, by norm_num⟩
    · exact ⟨1, 2, 2, 3, 12, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 29, by norm_num⟩
    · omega
    · exact ⟨1, 1, 1, 1, 30, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 20, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 31, by norm_num⟩
    · exact ⟨1, 1, 1, 4, 12, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 32, by norm_num⟩
    · exact ⟨1, 2, 2, 3, 14, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 33, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 22, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 34, by norm_num⟩
    · exact ⟨1, 2, 2, 3, 15, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 35, by norm_num⟩
    · exact ⟨1, 2, 2, 4, 12, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 36, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 24, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 37, by norm_num⟩
    · exact ⟨1, 1, 1, 6, 10, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 38, by norm_num⟩
    · exact ⟨1, 2, 2, 3, 17, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 39, by norm_num⟩
    · exact ⟨1, 1, 1, 2, 26, by norm_num⟩
    · exact ⟨1, 1, 1, 1, 40, by norm_num⟩

theorem a101902_not_rep (n : ℕ) (hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 12 ∨ n = 14 ∨ n = 18 ∨ n = 30 ∨ n = 38 ∨ n = 42 ∨ n = 62) (a b c d e : ℕ) (h1 : 1 ≤ a) (h2 : a ≤ b)
    (h3 : b ≤ c) (h4 : c ≤ d) (h5 : d ≤ e) (hs : a * b + b * c + c * d + d * e + e * a = n) :
    False := by
  have hn62 : n ≤ 62 := by omega
  have hde : d * e ≤ a * b + b * c + c * d + d * e + e * a := by omega
  have hdd : d * d ≤ d * e := Nat.mul_le_mul_left d h5
  have hd : d ≤ 7 := by
    by_contra hc
    have : 8 * 8 ≤ d * d := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hc : c ≤ 7 := by omega
  have hb : b ≤ 7 := by omega
  have ha : a ≤ 7 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> omega

theorem a101902_main :
    {n : ℕ | 0 < n ∧ ¬ ∃ a b c d e : ℕ, 1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧
        a * b + b * c + c * d + d * e + e * a = n} =
      ({1, 2, 3, 4, 6, 8, 12, 14, 18, 30, 38, 42, 62} : Set ℕ) := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, hnot⟩
    by_contra hmem
    exact hnot (a101902_rep n hn hmem)
  · intro hn
    refine ⟨by omega, ?_⟩
    rintro ⟨a, b, c, d, e, h1, h2, h3, h4, h5, hs⟩
    exact a101902_not_rep n hn a b c d e h1 h2 h3 h4 h5 hs

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a101902.main := OMA.Helpers.a101902_main
