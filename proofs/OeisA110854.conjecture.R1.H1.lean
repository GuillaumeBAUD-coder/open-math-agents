import OMAReductions.R_OeisA110854_conjecture_R1

namespace A110854Aux

def go (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | d, f + 1 => if n < d * d then true else if n % d = 0 then false else go n (d + 1) f

def pB (n : ℕ) : Bool := 2 ≤ n && go n 2 n

theorem go_true {n : ℕ} : ∀ (f d : ℕ), 2 ≤ d → n < d + f → go n d f = true →
    ∀ m, 2 ≤ m → m * m ≤ n → d ≤ m → ¬ m ∣ n := by
  intro f
  induction f with
  | zero => intro d hd hf _ m hm hmm hdm; nlinarith
  | succ f ih =>
    intro d hd hf h m hm hmm hdm
    simp only [go] at h
    by_cases h1 : n < d * d
    · nlinarith [Nat.mul_le_mul hdm hdm]
    · rw [if_neg h1] at h
      by_cases h2 : n % d = 0
      · rw [if_pos h2] at h; exact absurd h (by simp)
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hdm with e | e
        · subst e; intro hdv; exact h2 (Nat.mod_eq_zero_of_dvd hdv)
        · exact ih (d + 1) (by omega) (by omega) h m hm hmm e

theorem go_prime {n : ℕ} (hn : n.Prime) : ∀ (f d : ℕ), 2 ≤ d → go n d f = true := by
  intro f
  induction f with
  | zero => intro d _; simp [go]
  | succ f ih =>
    intro d hd
    simp only [go]
    by_cases h1 : n < d * d
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : n % d = 0
      · exfalso
        have hdv : d ∣ n := Nat.dvd_of_mod_eq_zero h2
        rcases hn.eq_one_or_self_of_dvd d hdv with e | e
        · omega
        · subst e; nlinarith
      · rw [if_neg h2]; exact ih (d + 1) (by omega)

theorem pB_iff (n : ℕ) : pB n = true ↔ n.Prime := by
  constructor
  · intro h
    simp only [pB, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [Nat.prime_def_le_sqrt]
    refine ⟨h.1, fun m hm hms => ?_⟩
    have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
    exact go_true n 2 le_rfl (by omega) h.2 m hm hmm hm
  · intro h
    simp only [pB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.two_le, go_prime h n 2 le_rfl⟩

def C (q : ℕ) : ℕ := Nat.count (fun n => pB n = true) q

theorem C_eq (q : ℕ) : Nat.count Nat.Prime q = C q := by
  unfold C
  simp only [Nat.count_eq_card_filter_range, pB_iff]

theorem step {a j : ℕ} (h : C a = j) (b : ℕ) {m : ℕ}
    (hm : Nat.count (fun k => pB (a + k) = true) b = m) : C (a + b) = j + m := by
  unfold C at *
  rw [Nat.count_add, h, hm]

theorem nthP {q j : ℕ} (h : C q = j) (hq : pB q = true) : Nat.nth Nat.Prime j = q := by
  rw [← h, ← C_eq]
  exact Nat.nth_count ((pB_iff q).mp hq)


theorem c0 : C 2 = 0 := by decide +kernel

theorem n0 : Nat.nth Nat.Prime 0 = 2 := nthP c0 (by decide +kernel)

theorem c1 : C 3 = 1 := step c0 1 (m := 1) (by decide +kernel)

theorem n1 : Nat.nth Nat.Prime 1 = 3 := nthP c1 (by decide +kernel)

theorem c2 : C 5 = 2 := step c1 2 (m := 1) (by decide +kernel)

theorem n2 : Nat.nth Nat.Prime 2 = 5 := nthP c2 (by decide +kernel)

theorem c3 : C 7 = 3 := step c2 2 (m := 1) (by decide +kernel)

theorem n3 : Nat.nth Nat.Prime 3 = 7 := nthP c3 (by decide +kernel)

theorem c4 : C 11 = 4 := step c3 4 (m := 1) (by decide +kernel)

theorem n4 : Nat.nth Nat.Prime 4 = 11 := nthP c4 (by decide +kernel)

theorem c5 : C 13 = 5 := step c4 2 (m := 1) (by decide +kernel)

theorem n5 : Nat.nth Nat.Prime 5 = 13 := nthP c5 (by decide +kernel)

theorem c6 : C 17 = 6 := step c5 4 (m := 1) (by decide +kernel)

theorem n6 : Nat.nth Nat.Prime 6 = 17 := nthP c6 (by decide +kernel)

theorem c7 : C 19 = 7 := step c6 2 (m := 1) (by decide +kernel)

theorem n7 : Nat.nth Nat.Prime 7 = 19 := nthP c7 (by decide +kernel)

theorem c8 : C 23 = 8 := step c7 4 (m := 1) (by decide +kernel)

theorem n8 : Nat.nth Nat.Prime 8 = 23 := nthP c8 (by decide +kernel)

theorem c9 : C 29 = 9 := step c8 6 (m := 1) (by decide +kernel)

theorem n9 : Nat.nth Nat.Prime 9 = 29 := nthP c9 (by decide +kernel)

theorem c16 : C 59 = 16 := step c9 30 (m := 7) (by decide +kernel)

theorem n16 : Nat.nth Nat.Prime 16 = 59 := nthP c16 (by decide +kernel)

theorem c17 : C 61 = 17 := step c16 2 (m := 1) (by decide +kernel)

theorem n17 : Nat.nth Nat.Prime 17 = 61 := nthP c17 (by decide +kernel)

theorem c18 : C 67 = 18 := step c17 6 (m := 1) (by decide +kernel)

theorem n18 : Nat.nth Nat.Prime 18 = 67 := nthP c18 (by decide +kernel)

theorem c19 : C 71 = 19 := step c18 4 (m := 1) (by decide +kernel)

theorem n19 : Nat.nth Nat.Prime 19 = 71 := nthP c19 (by decide +kernel)

theorem c44 : C 197 = 44 := step c19 126 (m := 25) (by decide +kernel)

theorem n44 : Nat.nth Nat.Prime 44 = 197 := nthP c44 (by decide +kernel)

theorem c45 : C 199 = 45 := step c44 2 (m := 1) (by decide +kernel)

theorem n45 : Nat.nth Nat.Prime 45 = 199 := nthP c45 (by decide +kernel)

theorem c46 : C 211 = 46 := step c45 12 (m := 1) (by decide +kernel)

theorem n46 : Nat.nth Nat.Prime 46 = 211 := nthP c46 (by decide +kernel)

theorem c47 : C 223 = 47 := step c46 12 (m := 1) (by decide +kernel)

theorem n47 : Nat.nth Nat.Prime 47 = 223 := nthP c47 (by decide +kernel)

theorem c58 : C 277 = 58 := step c47 54 (m := 11) (by decide +kernel)

theorem n58 : Nat.nth Nat.Prime 58 = 277 := nthP c58 (by decide +kernel)

theorem c59 : C 281 = 59 := step c58 4 (m := 1) (by decide +kernel)

theorem n59 : Nat.nth Nat.Prime 59 = 281 := nthP c59 (by decide +kernel)

theorem c60 : C 283 = 60 := step c59 2 (m := 1) (by decide +kernel)

theorem n60 : Nat.nth Nat.Prime 60 = 283 := nthP c60 (by decide +kernel)

theorem c61 : C 293 = 61 := step c60 10 (m := 1) (by decide +kernel)

theorem n61 : Nat.nth Nat.Prime 61 = 293 := nthP c61 (by decide +kernel)

theorem c90 : C 467 = 90 := step c61 174 (m := 29) (by decide +kernel)

theorem n90 : Nat.nth Nat.Prime 90 = 467 := nthP c90 (by decide +kernel)

theorem c91 : C 479 = 91 := step c90 12 (m := 1) (by decide +kernel)

theorem n91 : Nat.nth Nat.Prime 91 = 479 := nthP c91 (by decide +kernel)

theorem c92 : C 487 = 92 := step c91 8 (m := 1) (by decide +kernel)

theorem n92 : Nat.nth Nat.Prime 92 = 487 := nthP c92 (by decide +kernel)

theorem c93 : C 491 = 93 := step c92 4 (m := 1) (by decide +kernel)

theorem n93 : Nat.nth Nat.Prime 93 = 491 := nthP c93 (by decide +kernel)

theorem c186 : C 1117 = 186 := step c93 626 (m := 93) (by decide +kernel)

theorem n186 : Nat.nth Nat.Prime 186 = 1117 := nthP c186 (by decide +kernel)

theorem c187 : C 1123 = 187 := step c186 6 (m := 1) (by decide +kernel)

theorem n187 : Nat.nth Nat.Prime 187 = 1123 := nthP c187 (by decide +kernel)

theorem c188 : C 1129 = 188 := step c187 6 (m := 1) (by decide +kernel)

theorem n188 : Nat.nth Nat.Prime 188 = 1129 := nthP c188 (by decide +kernel)

theorem c189 : C 1151 = 189 := step c188 22 (m := 1) (by decide +kernel)

theorem n189 : Nat.nth Nat.Prime 189 = 1151 := nthP c189 (by decide +kernel)

theorem c190 : C 1153 = 190 := step c189 2 (m := 1) (by decide +kernel)

theorem n190 : Nat.nth Nat.Prime 190 = 1153 := nthP c190 (by decide +kernel)

theorem c191 : C 1163 = 191 := step c190 10 (m := 1) (by decide +kernel)

theorem n191 : Nat.nth Nat.Prime 191 = 1163 := nthP c191 (by decide +kernel)

theorem c204 : C 1259 = 204 := step c191 96 (m := 13) (by decide +kernel)

theorem n204 : Nat.nth Nat.Prime 204 = 1259 := nthP c204 (by decide +kernel)

theorem c205 : C 1277 = 205 := step c204 18 (m := 1) (by decide +kernel)

theorem n205 : Nat.nth Nat.Prime 205 = 1277 := nthP c205 (by decide +kernel)

theorem c206 : C 1279 = 206 := step c205 2 (m := 1) (by decide +kernel)

theorem n206 : Nat.nth Nat.Prime 206 = 1279 := nthP c206 (by decide +kernel)

theorem c207 : C 1283 = 207 := step c206 4 (m := 1) (by decide +kernel)

theorem n207 : Nat.nth Nat.Prime 207 = 1283 := nthP c207 (by decide +kernel)

theorem c214 : C 1319 = 214 := step c207 36 (m := 7) (by decide +kernel)

theorem n214 : Nat.nth Nat.Prime 214 = 1319 := nthP c214 (by decide +kernel)

theorem c215 : C 1321 = 215 := step c214 2 (m := 1) (by decide +kernel)

theorem n215 : Nat.nth Nat.Prime 215 = 1321 := nthP c215 (by decide +kernel)

theorem c216 : C 1327 = 216 := step c215 6 (m := 1) (by decide +kernel)

theorem n216 : Nat.nth Nat.Prime 216 = 1327 := nthP c216 (by decide +kernel)

theorem c217 : C 1361 = 217 := step c216 34 (m := 1) (by decide +kernel)

theorem n217 : Nat.nth Nat.Prime 217 = 1361 := nthP c217 (by decide +kernel)

theorem c218 : C 1367 = 218 := step c217 6 (m := 1) (by decide +kernel)

theorem n218 : Nat.nth Nat.Prime 218 = 1367 := nthP c218 (by decide +kernel)

theorem c219 : C 1373 = 219 := step c218 6 (m := 1) (by decide +kernel)

theorem n219 : Nat.nth Nat.Prime 219 = 1373 := nthP c219 (by decide +kernel)

theorem c260 : C 1663 = 260 := step c219 290 (m := 41) (by decide +kernel)

theorem n260 : Nat.nth Nat.Prime 260 = 1663 := nthP c260 (by decide +kernel)

theorem c261 : C 1667 = 261 := step c260 4 (m := 1) (by decide +kernel)

theorem n261 : Nat.nth Nat.Prime 261 = 1667 := nthP c261 (by decide +kernel)

theorem c262 : C 1669 = 262 := step c261 2 (m := 1) (by decide +kernel)

theorem n262 : Nat.nth Nat.Prime 262 = 1669 := nthP c262 (by decide +kernel)

theorem c263 : C 1693 = 263 := step c262 24 (m := 1) (by decide +kernel)

theorem n263 : Nat.nth Nat.Prime 263 = 1693 := nthP c263 (by decide +kernel)

theorem c264 : C 1697 = 264 := step c263 4 (m := 1) (by decide +kernel)

theorem n264 : Nat.nth Nat.Prime 264 = 1697 := nthP c264 (by decide +kernel)

theorem c265 : C 1699 = 265 := step c264 2 (m := 1) (by decide +kernel)

theorem n265 : Nat.nth Nat.Prime 265 = 1699 := nthP c265 (by decide +kernel)

theorem c326 : C 2179 = 326 := step c265 480 (m := 61) (by decide +kernel)

theorem n326 : Nat.nth Nat.Prime 326 = 2179 := nthP c326 (by decide +kernel)

theorem c327 : C 2203 = 327 := step c326 24 (m := 1) (by decide +kernel)

theorem n327 : Nat.nth Nat.Prime 327 = 2203 := nthP c327 (by decide +kernel)

theorem c328 : C 2207 = 328 := step c327 4 (m := 1) (by decide +kernel)

theorem n328 : Nat.nth Nat.Prime 328 = 2207 := nthP c328 (by decide +kernel)

theorem c329 : C 2213 = 329 := step c328 6 (m := 1) (by decide +kernel)

theorem n329 : Nat.nth Nat.Prime 329 = 2213 := nthP c329 (by decide +kernel)

theorem c982 : C 7753 = 982 := step c329 5540 (m := 653) (by decide +kernel)

theorem n982 : Nat.nth Nat.Prime 982 = 7753 := nthP c982 (by decide +kernel)

theorem c983 : C 7757 = 983 := step c982 4 (m := 1) (by decide +kernel)

theorem n983 : Nat.nth Nat.Prime 983 = 7757 := nthP c983 (by decide +kernel)

theorem c984 : C 7759 = 984 := step c983 2 (m := 1) (by decide +kernel)

theorem n984 : Nat.nth Nat.Prime 984 = 7759 := nthP c984 (by decide +kernel)

theorem c985 : C 7789 = 985 := step c984 30 (m := 1) (by decide +kernel)

theorem n985 : Nat.nth Nat.Prime 985 = 7789 := nthP c985 (by decide +kernel)

theorem c1050 : C 8389 = 1050 := step c985 600 (m := 65) (by decide +kernel)

theorem n1050 : Nat.nth Nat.Prime 1050 = 8389 := nthP c1050 (by decide +kernel)

theorem c1051 : C 8419 = 1051 := step c1050 30 (m := 1) (by decide +kernel)

theorem n1051 : Nat.nth Nat.Prime 1051 = 8419 := nthP c1051 (by decide +kernel)

theorem c1052 : C 8423 = 1052 := step c1051 4 (m := 1) (by decide +kernel)

theorem n1052 : Nat.nth Nat.Prime 1052 = 8423 := nthP c1052 (by decide +kernel)

theorem c1053 : C 8429 = 1053 := step c1052 6 (m := 1) (by decide +kernel)

theorem n1053 : Nat.nth Nat.Prime 1053 = 8429 := nthP c1053 (by decide +kernel)

theorem c1408 : C 11743 = 1408 := step c1053 3314 (m := 355) (by decide +kernel)

theorem n1408 : Nat.nth Nat.Prime 1408 = 11743 := nthP c1408 (by decide +kernel)

theorem c1409 : C 11777 = 1409 := step c1408 34 (m := 1) (by decide +kernel)

theorem n1409 : Nat.nth Nat.Prime 1409 = 11777 := nthP c1409 (by decide +kernel)

theorem c1410 : C 11779 = 1410 := step c1409 2 (m := 1) (by decide +kernel)

theorem n1410 : Nat.nth Nat.Prime 1410 = 11779 := nthP c1410 (by decide +kernel)

theorem c1411 : C 11783 = 1411 := step c1410 4 (m := 1) (by decide +kernel)

theorem n1411 : Nat.nth Nat.Prime 1411 = 11783 := nthP c1411 (by decide +kernel)

end A110854Aux


theorem OMA.solution : OMA.R_OeisA110854_conjecture_R1.H1 := by
  intro d hd hor
  interval_cases d
  · refine ⟨2, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n2, A110854Aux.n3, A110854Aux.n4, A110854Aux.n5]
  · refine ⟨1, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n0, A110854Aux.n1, A110854Aux.n2, A110854Aux.n3]
  · refine ⟨9, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n16, A110854Aux.n17, A110854Aux.n18, A110854Aux.n19]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨4, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n6, A110854Aux.n7, A110854Aux.n8, A110854Aux.n9]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨30, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n58, A110854Aux.n59, A110854Aux.n60, A110854Aux.n61]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨46, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n90, A110854Aux.n91, A110854Aux.n92, A110854Aux.n93]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨23, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n44, A110854Aux.n45, A110854Aux.n46, A110854Aux.n47]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨95, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n188, A110854Aux.n189, A110854Aux.n190, A110854Aux.n191]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨103, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n204, A110854Aux.n205, A110854Aux.n206, A110854Aux.n207]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨94, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n186, A110854Aux.n187, A110854Aux.n188, A110854Aux.n189]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨164, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n326, A110854Aux.n327, A110854Aux.n328, A110854Aux.n329]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨131, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n260, A110854Aux.n261, A110854Aux.n262, A110854Aux.n263]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨132, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n262, A110854Aux.n263, A110854Aux.n264, A110854Aux.n265]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨526, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n1050, A110854Aux.n1051, A110854Aux.n1052, A110854Aux.n1053]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨492, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n982, A110854Aux.n983, A110854Aux.n984, A110854Aux.n985]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨109, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n216, A110854Aux.n217, A110854Aux.n218, A110854Aux.n219]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨705, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n1408, A110854Aux.n1409, A110854Aux.n1410, A110854Aux.n1411]
  · exfalso; rcases hor with h | h
    · omega
    · rcases h with ⟨r, hr⟩; omega
  · refine ⟨108, by norm_num, ?_⟩
    simp only [OeisA110854.a]
    norm_num [A110854Aux.n214, A110854Aux.n215, A110854Aux.n216, A110854Aux.n217]
