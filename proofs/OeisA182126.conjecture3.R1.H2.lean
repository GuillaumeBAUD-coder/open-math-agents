import OMAReductions.R_OeisA182126_conjecture3_R1

-- Credit: @jagong-cmu

/-! Proof of step H2 of reduction OeisA182126.conjecture3.R1: the finite check of a(1), ..., a(61). -/

namespace OMA.A182126H2

set_option maxRecDepth 100000 in
lemma np0 : Nat.nth Nat.Prime 0 = 2 := by
  have h : Nat.count Nat.Prime 2 = 0 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np1 : Nat.nth Nat.Prime 1 = 3 := by
  have h : Nat.count Nat.Prime 3 = 1 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np2 : Nat.nth Nat.Prime 2 = 5 := by
  have h : Nat.count Nat.Prime 5 = 2 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np3 : Nat.nth Nat.Prime 3 = 7 := by
  have h : Nat.count Nat.Prime 7 = 3 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np4 : Nat.nth Nat.Prime 4 = 11 := by
  have h : Nat.count Nat.Prime 11 = 4 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np5 : Nat.nth Nat.Prime 5 = 13 := by
  have h : Nat.count Nat.Prime 13 = 5 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np6 : Nat.nth Nat.Prime 6 = 17 := by
  have h : Nat.count Nat.Prime 17 = 6 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np7 : Nat.nth Nat.Prime 7 = 19 := by
  have h : Nat.count Nat.Prime 19 = 7 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np8 : Nat.nth Nat.Prime 8 = 23 := by
  have h : Nat.count Nat.Prime 23 = 8 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np9 : Nat.nth Nat.Prime 9 = 29 := by
  have h : Nat.count Nat.Prime 29 = 9 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np10 : Nat.nth Nat.Prime 10 = 31 := by
  have h : Nat.count Nat.Prime 31 = 10 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np11 : Nat.nth Nat.Prime 11 = 37 := by
  have h : Nat.count Nat.Prime 37 = 11 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np12 : Nat.nth Nat.Prime 12 = 41 := by
  have h : Nat.count Nat.Prime 41 = 12 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np13 : Nat.nth Nat.Prime 13 = 43 := by
  have h : Nat.count Nat.Prime 43 = 13 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np14 : Nat.nth Nat.Prime 14 = 47 := by
  have h : Nat.count Nat.Prime 47 = 14 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np15 : Nat.nth Nat.Prime 15 = 53 := by
  have h : Nat.count Nat.Prime 53 = 15 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np16 : Nat.nth Nat.Prime 16 = 59 := by
  have h : Nat.count Nat.Prime 59 = 16 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np17 : Nat.nth Nat.Prime 17 = 61 := by
  have h : Nat.count Nat.Prime 61 = 17 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np18 : Nat.nth Nat.Prime 18 = 67 := by
  have h : Nat.count Nat.Prime 67 = 18 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np19 : Nat.nth Nat.Prime 19 = 71 := by
  have h : Nat.count Nat.Prime 71 = 19 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np20 : Nat.nth Nat.Prime 20 = 73 := by
  have h : Nat.count Nat.Prime 73 = 20 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np21 : Nat.nth Nat.Prime 21 = 79 := by
  have h : Nat.count Nat.Prime 79 = 21 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np22 : Nat.nth Nat.Prime 22 = 83 := by
  have h : Nat.count Nat.Prime 83 = 22 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np23 : Nat.nth Nat.Prime 23 = 89 := by
  have h : Nat.count Nat.Prime 89 = 23 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np24 : Nat.nth Nat.Prime 24 = 97 := by
  have h : Nat.count Nat.Prime 97 = 24 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np25 : Nat.nth Nat.Prime 25 = 101 := by
  have h : Nat.count Nat.Prime 101 = 25 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np26 : Nat.nth Nat.Prime 26 = 103 := by
  have h : Nat.count Nat.Prime 103 = 26 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np27 : Nat.nth Nat.Prime 27 = 107 := by
  have h : Nat.count Nat.Prime 107 = 27 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np28 : Nat.nth Nat.Prime 28 = 109 := by
  have h : Nat.count Nat.Prime 109 = 28 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np29 : Nat.nth Nat.Prime 29 = 113 := by
  have h : Nat.count Nat.Prime 113 = 29 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np30 : Nat.nth Nat.Prime 30 = 127 := by
  have h : Nat.count Nat.Prime 127 = 30 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np31 : Nat.nth Nat.Prime 31 = 131 := by
  have h : Nat.count Nat.Prime 131 = 31 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np32 : Nat.nth Nat.Prime 32 = 137 := by
  have h : Nat.count Nat.Prime 137 = 32 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np33 : Nat.nth Nat.Prime 33 = 139 := by
  have h : Nat.count Nat.Prime 139 = 33 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np34 : Nat.nth Nat.Prime 34 = 149 := by
  have h : Nat.count Nat.Prime 149 = 34 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np35 : Nat.nth Nat.Prime 35 = 151 := by
  have h : Nat.count Nat.Prime 151 = 35 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np36 : Nat.nth Nat.Prime 36 = 157 := by
  have h : Nat.count Nat.Prime 157 = 36 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np37 : Nat.nth Nat.Prime 37 = 163 := by
  have h : Nat.count Nat.Prime 163 = 37 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np38 : Nat.nth Nat.Prime 38 = 167 := by
  have h : Nat.count Nat.Prime 167 = 38 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np39 : Nat.nth Nat.Prime 39 = 173 := by
  have h : Nat.count Nat.Prime 173 = 39 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np40 : Nat.nth Nat.Prime 40 = 179 := by
  have h : Nat.count Nat.Prime 179 = 40 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np41 : Nat.nth Nat.Prime 41 = 181 := by
  have h : Nat.count Nat.Prime 181 = 41 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np42 : Nat.nth Nat.Prime 42 = 191 := by
  have h : Nat.count Nat.Prime 191 = 42 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np43 : Nat.nth Nat.Prime 43 = 193 := by
  have h : Nat.count Nat.Prime 193 = 43 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np44 : Nat.nth Nat.Prime 44 = 197 := by
  have h : Nat.count Nat.Prime 197 = 44 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np45 : Nat.nth Nat.Prime 45 = 199 := by
  have h : Nat.count Nat.Prime 199 = 45 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np46 : Nat.nth Nat.Prime 46 = 211 := by
  have h : Nat.count Nat.Prime 211 = 46 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np47 : Nat.nth Nat.Prime 47 = 223 := by
  have h : Nat.count Nat.Prime 223 = 47 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np48 : Nat.nth Nat.Prime 48 = 227 := by
  have h : Nat.count Nat.Prime 227 = 48 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np49 : Nat.nth Nat.Prime 49 = 229 := by
  have h : Nat.count Nat.Prime 229 = 49 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np50 : Nat.nth Nat.Prime 50 = 233 := by
  have h : Nat.count Nat.Prime 233 = 50 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np51 : Nat.nth Nat.Prime 51 = 239 := by
  have h : Nat.count Nat.Prime 239 = 51 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np52 : Nat.nth Nat.Prime 52 = 241 := by
  have h : Nat.count Nat.Prime 241 = 52 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np53 : Nat.nth Nat.Prime 53 = 251 := by
  have h : Nat.count Nat.Prime 251 = 53 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np54 : Nat.nth Nat.Prime 54 = 257 := by
  have h : Nat.count Nat.Prime 257 = 54 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np55 : Nat.nth Nat.Prime 55 = 263 := by
  have h : Nat.count Nat.Prime 263 = 55 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np56 : Nat.nth Nat.Prime 56 = 269 := by
  have h : Nat.count Nat.Prime 269 = 56 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np57 : Nat.nth Nat.Prime 57 = 271 := by
  have h : Nat.count Nat.Prime 271 = 57 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np58 : Nat.nth Nat.Prime 58 = 277 := by
  have h : Nat.count Nat.Prime 277 = 58 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np59 : Nat.nth Nat.Prime 59 = 281 := by
  have h : Nat.count Nat.Prime 281 = 59 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np60 : Nat.nth Nat.Prime 60 = 283 := by
  have h : Nat.count Nat.Prime 283 = 60 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np61 : Nat.nth Nat.Prime 61 = 293 := by
  have h : Nat.count Nat.Prime 293 = 61 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

set_option maxRecDepth 100000 in
lemma np62 : Nat.nth Nat.Prime 62 = 307 := by
  have h : Nat.count Nat.Prime 307 = 62 := by decide
  rw [← h]
  exact Nat.nth_count (by norm_num)

theorem H2 : ∀ n : ℕ, 0 < n → n ≤ 61 → (OeisA182126.a n).Prime →
    OeisA182126.a n ∈ ([2, 7, 11, 13, 29] : List ℕ) := by
  intro n h0 h61 hp
  interval_cases n <;> simp [OeisA182126.a, OeisA182126.prime, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36, np37, np38, np39, np40, np41, np42, np43, np44, np45, np46, np47, np48, np49, np50, np51, np52, np53, np54, np55, np56, np57, np58, np59, np60, np61, np62] at hp ⊢ <;> norm_num at hp

end OMA.A182126H2


theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := OMA.A182126H2.H2
