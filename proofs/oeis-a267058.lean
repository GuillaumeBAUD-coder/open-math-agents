import OMAStatements.S_oeis_a267058

open OMA.S_oeis_a267058

def blocks (w : List Bool) : ℕ → List Bool → List Bool
  | 0, tail => tail
  | k + 1, tail => w ++ blocks w k tail

lemma blocks_append (w : List Bool) (k : ℕ) (u v : List Bool) :
    blocks w k u ++ v = blocks w k (u ++ v) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, List.append_assoc, ih]

def word0 (k : ℕ) : List Bool :=
  [true, false, false, false, false, false, false, false, false] ++ blocks [false, false, false, false, false, false, false, false] k []

def word1 (k : ℕ) : List Bool :=
  [false, false, false, true, true, true, true, true, true, true, true] ++ blocks [true, true, true, true, true, true, true, true] k []

def word2 (k : ℕ) : List Bool :=
  [true, false, true, false, false, false, false, false, false, false, false, false, false] ++ blocks [false, false, false, false, false, false, false, false] k []

def word3 (k : ℕ) : List Bool :=
  [false, false, true, false, false, true, true, true, true, true, true, true, true, true, true] ++ blocks [true, true, true, true, true, true, true, true] k []

lemma align1 (k : ℕ) (tail : List Bool) :
    blocks [false, false, false, false, false, false, false, false] (k + 1) tail =
      [false, false, false, false] ++ blocks [false, false, false, false, false, false, false, false] k ([false, false, false, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false, false, false, false, false, false, false] ++ rest) ih

lemma align2 (k : ℕ) (tail : List Bool) :
    blocks [true, true, true, true, true, true, true, true] (k + 1) tail =
      [true, true] ++ blocks [true, true, true, true, true, true, true, true] k ([true, true, true, true, true, true] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true, true, true, true, true, true, true] ++ rest) ih

lemma scanBlock1 (k : ℕ) (tail : List Bool) :
    scan false false (blocks [false, false, false, false, false, false, false, false] k tail) =
      blocks [true, true, true, true, true, true, true, true] k (scan false false tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [true, true, true, true, true, true, true, true] ++ rest) ih

lemma align3 (k : ℕ) (tail : List Bool) :
    blocks [true, true, true, true, true, true, true, true] (k + 1) tail =
      [true, true, true, true] ++ blocks [true, true, true, true, true, true, true, true] k ([true, true, true, true] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true, true, true, true, true, true, true] ++ rest) ih

lemma align4 (k : ℕ) (tail : List Bool) :
    blocks [false, false, false, false, false, false, false, false] (k + 1) tail =
      [false, false] ++ blocks [false, false, false, false, false, false, false, false] k ([false, false, false, false, false, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false, false, false, false, false, false, false] ++ rest) ih

lemma scanBlock2 (k : ℕ) (tail : List Bool) :
    scan true true (blocks [true, true, true, true, true, true, true, true] k tail) =
      blocks [false, false, false, false, false, false, false, false] k (scan true true tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [false, false, false, false, false, false, false, false] ++ rest) ih

lemma align5 (k : ℕ) (tail : List Bool) :
    blocks [false, false, false, false, false, false, false, false] (k + 2) tail =
      [false, false, false, false, false, false, false, false] ++ blocks [false, false, false, false, false, false, false, false] k ([false, false, false, false, false, false, false, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false, false, false, false, false, false, false] ++ rest) ih

lemma phase0 (k : ℕ) :
    scan false false ((word0 k) ++ [false, false]) =
      word1 k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word0, word1, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan false false ([true, false, false, false, false, false, false, false, false] ++ blocks [false, false, false, false, false, false, false, false] (k + 1) ([false, false])) = [false, false, false, true, true, true, true, true, true, true, true] ++ blocks [true, true, true, true, true, true, true, true] (k + 1) []
    conv => lhs; rw [align1]
    conv => rhs; rw [align2]
    simp only [List.cons_append, List.nil_append, scan, scanBlock1]
    <;> rfl

lemma phase1 (k : ℕ) :
    scan true true ((word1 k) ++ [true, true]) =
      word2 k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word1, word2, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan true true ([false, false, false, true, true, true, true, true, true, true, true] ++ blocks [true, true, true, true, true, true, true, true] (k + 1) ([true, true])) = [true, false, true, false, false, false, false, false, false, false, false, false, false] ++ blocks [false, false, false, false, false, false, false, false] (k + 1) []
    conv => lhs; rw [align3]
    conv => rhs; rw [align4]
    simp only [List.cons_append, List.nil_append, scan, scanBlock2]
    <;> rfl

lemma phase2 (k : ℕ) :
    scan false false ((word2 k) ++ [false, false]) =
      word3 k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word2, word3, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan false false ([true, false, true, false, false, false, false, false, false, false, false, false, false] ++ blocks [false, false, false, false, false, false, false, false] (k + 1) ([false, false])) = [false, false, true, false, false, true, true, true, true, true, true, true, true, true, true] ++ blocks [true, true, true, true, true, true, true, true] (k + 1) []
    conv => lhs; rw [align1]
    conv => rhs; rw [align2]
    simp only [List.cons_append, List.nil_append, scan, scanBlock1]
    <;> rfl

lemma phase3 (k : ℕ) :
    scan true true ((word3 k) ++ [true, true]) =
      word0 (k + 1) := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word3, word0, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan true true ([false, false, true, false, false, true, true, true, true, true, true, true, true, true, true] ++ blocks [true, true, true, true, true, true, true, true] (k + 1) ([true, true])) = [true, false, false, false, false, false, false, false, false] ++ blocks [false, false, false, false, false, false, false, false] (k + 2) []
    conv => lhs; rw [align2]
    conv => rhs; rw [align5]
    simp only [List.cons_append, List.nil_append, scan, scanBlock2]
    <;> rfl

lemma cycle (k : ℕ) :
    (row (4 * k + 4) = word0 k ∧ background (4 * k + 4) = false) ∧
    (row (4 * k + 5) = word1 k ∧ background (4 * k + 5) = true) ∧
    (row (4 * k + 6) = word2 k ∧ background (4 * k + 6) = false) ∧
    (row (4 * k + 7) = word3 k ∧ background (4 * k + 7) = true) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h0 : row (4 * (k + 1) + 4) = word0 (k+1) ∧ background (4 * (k + 1) + 4) = false := by
      rw [show 4 * (k + 1) + 4 = (4 * k + 7) + 1 by omega]
      exact ⟨by rw [row, ih.2.2.2.1, ih.2.2.2.2]; exact phase3 k, by rw [background, ih.2.2.2.2]; rfl⟩
    have h1 : row (4 * (k + 1) + 5) = word1 (k+1) ∧ background (4 * (k + 1) + 5) = true := by
      rw [show 4 * (k + 1) + 5 = (4 * (k + 1) + 4) + 1 by omega]
      exact ⟨by rw [row, h0.1, h0.2]; exact phase0 (k + 1), by rw [background, h0.2]; rfl⟩
    have h2 : row (4 * (k + 1) + 6) = word2 (k+1) ∧ background (4 * (k + 1) + 6) = false := by
      rw [show 4 * (k + 1) + 6 = (4 * (k + 1) + 5) + 1 by omega]
      exact ⟨by rw [row, h1.1, h1.2]; exact phase1 (k + 1), by rw [background, h1.2]; rfl⟩
    have h3 : row (4 * (k + 1) + 7) = word3 (k+1) ∧ background (4 * (k + 1) + 7) = true := by
      rw [show 4 * (k + 1) + 7 = (4 * (k + 1) + 6) + 1 by omega]
      exact ⟨by rw [row, h2.1, h2.2]; exact phase2 (k + 1), by rw [background, h2.2]; rfl⟩
    exact ⟨h0, h1, h2, h3⟩

def magnitude (w : List Bool) : ℚ := (2 : ℚ) ^ w.length

def encode (w : List Bool) : ℚ := (Nat.ofDigits 2 (w.map Bool.toNat).reverse : ℕ)

lemma magnitude_append (u v : List Bool) : magnitude (u ++ v) = magnitude u * magnitude v := by
  simp [magnitude, pow_add]

lemma encode_append (u v : List Bool) : encode (u ++ v) = encode u * magnitude v + encode v := by
  simp [encode, magnitude, Nat.ofDigits_append]
  ring

lemma run00000000 (k : ℕ) (tail : List Bool) :
    magnitude (blocks [false, false, false, false, false, false, false, false] k tail) = (256 : ℚ) ^ k * magnitude tail ∧
    encode (blocks [false, false, false, false, false, false, false, false] k tail) =
      0 * ((256 : ℚ) ^ k - 1) * magnitude tail + encode tail := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    rw [blocks, magnitude_append, encode_append, ih.1, ih.2, pow_succ]
    have hm : magnitude [false, false, false, false, false, false, false, false] = 256 := by decide
    have he : encode [false, false, false, false, false, false, false, false] = 0 := by decide
    rw [hm, he]
    constructor <;> ring

lemma run11111111 (k : ℕ) (tail : List Bool) :
    magnitude (blocks [true, true, true, true, true, true, true, true] k tail) = (256 : ℚ) ^ k * magnitude tail ∧
    encode (blocks [true, true, true, true, true, true, true, true] k tail) =
      1 * ((256 : ℚ) ^ k - 1) * magnitude tail + encode tail := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    rw [blocks, magnitude_append, encode_append, ih.1, ih.2, pow_succ]
    have hm : magnitude [true, true, true, true, true, true, true, true] = 256 := by decide
    have he : encode [true, true, true, true, true, true, true, true] = 255 := by decide
    rw [hm, he]
    constructor <;> ring

lemma value0 (k : ℕ) : (a (4 * k + 4) : ℚ) = 256 * (256 : ℚ) ^ k := by
  change encode (row (4 * k + 4)) = _
  rw [(cycle k).1.1, word0]
  have e0 : encode [] = 0 := by decide
  have m0 : magnitude [] = 1 := by decide
  have e1 : encode [true, false, false, false, false, false, false, false, false] = 256 := by decide
  have m1 : magnitude [true, false, false, false, false, false, false, false, false] = 512 := by decide
  have z0 := fun tail => (run00000000 k tail).1
  have y0 := fun tail => (run00000000 k tail).2
  simp only [encode_append, magnitude_append, e0, m0, e1, m1, z0, y0]
  have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
    calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  push_cast
  norm_num [pow_succ, pow_add, pow_mul]
  all_goals try simp only [p256]
  all_goals ring

lemma value1 (k : ℕ) : (a (4 * k + 5) : ℚ) = (-1) + 256 * (256 : ℚ) ^ k := by
  change encode (row (4 * k + 5)) = _
  rw [(cycle k).2.1.1, word1]
  have e0 : encode [] = 0 := by decide
  have m0 : magnitude [] = 1 := by decide
  have e1 : encode [false, false, false, true, true, true, true, true, true, true, true] = 255 := by decide
  have m1 : magnitude [false, false, false, true, true, true, true, true, true, true, true] = 2048 := by decide
  have z0 := fun tail => (run11111111 k tail).1
  have y0 := fun tail => (run11111111 k tail).2
  simp only [encode_append, magnitude_append, e0, m0, e1, m1, z0, y0]
  have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
    calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  push_cast
  norm_num [pow_succ, pow_add, pow_mul]
  all_goals try simp only [p256]
  all_goals ring

lemma value2 (k : ℕ) : (a (4 * k + 6) : ℚ) = 5120 * (256 : ℚ) ^ k := by
  change encode (row (4 * k + 6)) = _
  rw [(cycle k).2.2.1.1, word2]
  have e0 : encode [] = 0 := by decide
  have m0 : magnitude [] = 1 := by decide
  have e1 : encode [true, false, true, false, false, false, false, false, false, false, false, false, false] = 5120 := by decide
  have m1 : magnitude [true, false, true, false, false, false, false, false, false, false, false, false, false] = 8192 := by decide
  have z0 := fun tail => (run00000000 k tail).1
  have y0 := fun tail => (run00000000 k tail).2
  simp only [encode_append, magnitude_append, e0, m0, e1, m1, z0, y0]
  have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
    calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  push_cast
  norm_num [pow_succ, pow_add, pow_mul]
  all_goals try simp only [p256]
  all_goals ring

lemma value3 (k : ℕ) : (a (4 * k + 7) : ℚ) = (-1) + 5120 * (256 : ℚ) ^ k := by
  change encode (row (4 * k + 7)) = _
  rw [(cycle k).2.2.2.1, word3]
  have e0 : encode [] = 0 := by decide
  have m0 : magnitude [] = 1 := by decide
  have e1 : encode [false, false, true, false, false, true, true, true, true, true, true, true, true, true, true] = 5119 := by decide
  have m1 : magnitude [false, false, true, false, false, true, true, true, true, true, true, true, true, true, true] = 32768 := by decide
  have z0 := fun tail => (run11111111 k tail).1
  have y0 := fun tail => (run11111111 k tail).2
  simp only [encode_append, magnitude_append, e0, m0, e1, m1, z0, y0]
  have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
    calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  push_cast
  norm_num [pow_succ, pow_add, pow_mul]
  all_goals try simp only [p256]
  all_goals ring


lemma initial0 : a 0 = 1 := by rfl
lemma initial1 : a 1 = 0 := by rfl
lemma initial2 : a 2 = 20 := by rfl
lemma initial3 : a 3 = 19 := by rfl
lemma initial4 : a 4 = 256 := by rfl
lemma initial5 : a 5 = 255 := by rfl
lemma initial6 : a 6 = 5120 := by rfl
lemma initial7 : a 7 = 5119 := by rfl
lemma initial8 : a 8 = 65536 := by rfl
lemma initial9 : a 9 = 65535 := by rfl
lemma initial10 : a 10 = 1310720 := by rfl
lemma initial11 : a 11 = 1310719 := by rfl

lemma claim1 : ∀ n : ℕ, 5 < n → (a n : ℤ) = (a (n - 2) : ℤ) + 256 * (a (n - 4) : ℤ) - 256 * (a (n - 6) : ℤ) := by
  intro n hn
  suffices hq : (a n : ℚ) = (a (n - 2) : ℚ) + 256 * (a (n - 4) : ℚ) - 256 * (a (n - 6) : ℚ) by exact_mod_cast hq
  by_cases small : n < 12
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9, initial10, initial11] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 12 ∨ n = 4 * k + 13 ∨ n = 4 * k + 14 ∨ n = 4 * k + 15 := by
    exact ⟨(n - 12) / 4, by omega⟩
  rcases hk with hk | hk | hk | hk
  · have v0 : (a n : ℚ) = 256 * (256 : ℚ) ^ (k + 2) := by
      rw [show n = 4 * (k + 2) + 4 by omega]
      exact value0 (k + 2)
    have v1 : (a (n - 2) : ℚ) = 5120 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 2 = 4 * (k + 1) + 6 by omega]
      exact value2 (k + 1)
    have v2 : (a (n - 6) : ℚ) = 5120 * (256 : ℚ) ^ k := by
      rw [show n - 6 = 4 * k + 6 by omega]
      exact value2 k
    have v3 : (a (n - 4) : ℚ) = 256 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1) + 256 * (256 : ℚ) ^ (k + 2) := by
      rw [show n = 4 * (k + 2) + 5 by omega]
      exact value1 (k + 2)
    have v1 : (a (n - 2) : ℚ) = (-1) + 5120 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 2 = 4 * (k + 1) + 7 by omega]
      exact value3 (k + 1)
    have v2 : (a (n - 6) : ℚ) = (-1) + 5120 * (256 : ℚ) ^ k := by
      rw [show n - 6 = 4 * k + 7 by omega]
      exact value3 k
    have v3 : (a (n - 4) : ℚ) = (-1) + 256 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring
  · have v0 : (a n : ℚ) = 5120 * (256 : ℚ) ^ (k + 2) := by
      rw [show n = 4 * (k + 2) + 6 by omega]
      exact value2 (k + 2)
    have v1 : (a (n - 2) : ℚ) = 256 * (256 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 4 * (k + 2) + 4 by omega]
      exact value0 (k + 2)
    have v2 : (a (n - 6) : ℚ) = 256 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 6 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    have v3 : (a (n - 4) : ℚ) = 5120 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 4 * (k + 1) + 6 by omega]
      exact value2 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1) + 5120 * (256 : ℚ) ^ (k + 2) := by
      rw [show n = 4 * (k + 2) + 7 by omega]
      exact value3 (k + 2)
    have v1 : (a (n - 2) : ℚ) = (-1) + 256 * (256 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 4 * (k + 2) + 5 by omega]
      exact value1 (k + 2)
    have v2 : (a (n - 6) : ℚ) = (-1) + 256 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 6 = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    have v3 : (a (n - 4) : ℚ) = (-1) + 5120 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 4 * (k + 1) + 7 by omega]
      exact value3 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring

lemma claim2Tail : ∀ n : ℕ, 5 < n → (a n : ℚ) = -(256 * (a (n - 6) : ℚ) + -256 * (a (n - 4) : ℚ) + -1 * (a (n - 2) : ℚ)) := by
  intro n hn
  by_cases small : n < 12
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9, initial10, initial11] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 12 ∨ n = 4 * k + 13 ∨ n = 4 * k + 14 ∨ n = 4 * k + 15 := by
    exact ⟨(n - 12) / 4, by omega⟩
  rcases hk with hk | hk | hk | hk
  · have v0 : (a n : ℚ) = 256 * (256 : ℚ) ^ (k + 2) := by
      rw [show n = 4 * (k + 2) + 4 by omega]
      exact value0 (k + 2)
    have v1 : (a (n - 2) : ℚ) = 5120 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 2 = 4 * (k + 1) + 6 by omega]
      exact value2 (k + 1)
    have v2 : (a (n - 6) : ℚ) = 5120 * (256 : ℚ) ^ k := by
      rw [show n - 6 = 4 * k + 6 by omega]
      exact value2 k
    have v3 : (a (n - 4) : ℚ) = 256 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1) + 256 * (256 : ℚ) ^ (k + 2) := by
      rw [show n = 4 * (k + 2) + 5 by omega]
      exact value1 (k + 2)
    have v1 : (a (n - 2) : ℚ) = (-1) + 5120 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 2 = 4 * (k + 1) + 7 by omega]
      exact value3 (k + 1)
    have v2 : (a (n - 6) : ℚ) = (-1) + 5120 * (256 : ℚ) ^ k := by
      rw [show n - 6 = 4 * k + 7 by omega]
      exact value3 k
    have v3 : (a (n - 4) : ℚ) = (-1) + 256 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring
  · have v0 : (a n : ℚ) = 5120 * (256 : ℚ) ^ (k + 2) := by
      rw [show n = 4 * (k + 2) + 6 by omega]
      exact value2 (k + 2)
    have v1 : (a (n - 2) : ℚ) = 256 * (256 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 4 * (k + 2) + 4 by omega]
      exact value0 (k + 2)
    have v2 : (a (n - 6) : ℚ) = 256 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 6 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    have v3 : (a (n - 4) : ℚ) = 5120 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 4 * (k + 1) + 6 by omega]
      exact value2 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1) + 5120 * (256 : ℚ) ^ (k + 2) := by
      rw [show n = 4 * (k + 2) + 7 by omega]
      exact value3 (k + 2)
    have v1 : (a (n - 2) : ℚ) = (-1) + 256 * (256 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 4 * (k + 2) + 5 by omega]
      exact value1 (k + 2)
    have v2 : (a (n - 6) : ℚ) = (-1) + 256 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 6 = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    have v3 : (a (n - 4) : ℚ) = (-1) + 5120 * (256 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 4 * (k + 1) + 7 by omega]
      exact value3 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring

open PowerSeries in
lemma claim2 : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + 16 * X ^ 2)) = 1 + 19 * X ^ 2 + 19 * X ^ 3 - 20 * X ^ 4 + 236 * X ^ 5 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  have hd : s * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + 16 * X ^ 2)) = PowerSeries.C (1 : ℚ) * (s * X ^ 0) + PowerSeries.C (-1 : ℚ) * (s * X ^ 2) + PowerSeries.C (-256 : ℚ) * (s * X ^ 4) + PowerSeries.C (256 : ℚ) * (s * X ^ 6) := by norm_num [map_ofNat] <;> ring
  have hn : 1 + 19 * X ^ 2 + 19 * X ^ 3 - 20 * X ^ 4 + 236 * X ^ 5 = PowerSeries.C (1 : ℚ) * (X ^ 0 : PowerSeries ℚ) + PowerSeries.C (19 : ℚ) * (X ^ 2 : PowerSeries ℚ) + PowerSeries.C (19 : ℚ) * (X ^ 3 : PowerSeries ℚ) + PowerSeries.C (-20 : ℚ) * (X ^ 4 : PowerSeries ℚ) + PowerSeries.C (236 : ℚ) * (X ^ 5 : PowerSeries ℚ) := by norm_num [map_ofNat] <;> ring
  rw [hd, hn]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_X_pow, coeff_mul_X_pow', s, coeff_mk]
  by_cases h : n ≤ 5
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3, initial4, initial5]
  · have hr := claim2Tail n (by omega)
    simp only [if_pos (show 6 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 0 ≤ n by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega), Nat.sub_zero]
    linarith

lemma claim3 : ∀ n : ℕ, Odd n → (a n : ℚ) = 256 ^ (⌊((n : ℚ) / 4 : ℚ)⌋).toNat * ((((n - 1) / 2 + 1) % 2 : ℕ) : ℚ) + 20 * 256 ^ (⌊((n : ℚ) / 4 : ℚ)⌋).toNat * (((n - 1) / 2 % 2 : ℕ) : ℚ) - 1 := by
  intro n hpar
  by_cases small : n < 4
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 4 ∨ n = 4 * k + 5 ∨ n = 4 * k + 6 ∨ n = 4 * k + 7 := by
    exact ⟨(n - 4) / 4, by omega⟩
  rcases hk with hk | hk | hk | hk
  · rw [Nat.odd_iff] at hpar
    omega
  · have v0 : (a n : ℚ) = (-1) + 256 * (256 : ℚ) ^ k := by
      rw [show n = 4 * k + 5 by omega]
      exact value1 k
    have power1 : (256 : ℚ) ^ ((⌊((n : ℚ) / 4 : ℚ)⌋).toNat) = (256 : ℚ) ^ k * (256 : ℚ) ^ 1 := by
      have hf : ⌊((n : ℚ) / 4)⌋ = (n : ℤ) / 4 := Rat.floor_natCast_div_natCast n 4
      rw [show (⌊((n : ℚ) / 4 : ℚ)⌋).toNat = 1 * k + 1 by rw [hf]; omega, pow_add, pow_mul]
      norm_num
    have residue0 : ((n - 1) / 2 + 1) % 2 = 1 := by omega
    have residue1 : (n - 1) / 2 % 2 = 0 := by omega
    simp only [v0, power1, residue0, residue1]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring
  · rw [Nat.odd_iff] at hpar
    omega
  · have v0 : (a n : ℚ) = (-1) + 5120 * (256 : ℚ) ^ k := by
      rw [show n = 4 * k + 7 by omega]
      exact value3 k
    have power1 : (256 : ℚ) ^ ((⌊((n : ℚ) / 4 : ℚ)⌋).toNat) = (256 : ℚ) ^ k * (256 : ℚ) ^ 1 := by
      have hf : ⌊((n : ℚ) / 4)⌋ = (n : ℤ) / 4 := Rat.floor_natCast_div_natCast n 4
      rw [show (⌊((n : ℚ) / 4 : ℚ)⌋).toNat = 1 * k + 1 by rw [hf]; omega, pow_add, pow_mul]
      norm_num
    have residue0 : ((n - 1) / 2 + 1) % 2 = 0 := by omega
    have residue1 : (n - 1) / 2 % 2 = 1 := by omega
    simp only [v0, power1, residue0, residue1]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring

lemma claim4 : ∀ n : ℕ, Even n → (a n : ℚ) = 256 ^ (⌊((n : ℚ) / 4 : ℚ)⌋).toNat * (((n / 2 + 1) % 2 : ℕ) : ℚ) + 20 * 256 ^ (⌊((n : ℚ) / 4 : ℚ)⌋).toNat * ((n / 2 % 2 : ℕ) : ℚ) := by
  intro n hpar
  by_cases small : n < 4
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 4 ∨ n = 4 * k + 5 ∨ n = 4 * k + 6 ∨ n = 4 * k + 7 := by
    exact ⟨(n - 4) / 4, by omega⟩
  rcases hk with hk | hk | hk | hk
  · have v0 : (a n : ℚ) = 256 * (256 : ℚ) ^ k := by
      rw [show n = 4 * k + 4 by omega]
      exact value0 k
    have power1 : (256 : ℚ) ^ ((⌊((n : ℚ) / 4 : ℚ)⌋).toNat) = (256 : ℚ) ^ k * (256 : ℚ) ^ 1 := by
      have hf : ⌊((n : ℚ) / 4)⌋ = (n : ℤ) / 4 := Rat.floor_natCast_div_natCast n 4
      rw [show (⌊((n : ℚ) / 4 : ℚ)⌋).toNat = 1 * k + 1 by rw [hf]; omega, pow_add, pow_mul]
      norm_num
    have residue0 : (n / 2 + 1) % 2 = 1 := by omega
    have residue1 : n / 2 % 2 = 0 := by omega
    simp only [v0, power1, residue0, residue1]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring
  · rw [Nat.even_iff] at hpar
    omega
  · have v0 : (a n : ℚ) = 5120 * (256 : ℚ) ^ k := by
      rw [show n = 4 * k + 6 by omega]
      exact value2 k
    have power1 : (256 : ℚ) ^ ((⌊((n : ℚ) / 4 : ℚ)⌋).toNat) = (256 : ℚ) ^ k * (256 : ℚ) ^ 1 := by
      have hf : ⌊((n : ℚ) / 4)⌋ = (n : ℤ) / 4 := Rat.floor_natCast_div_natCast n 4
      rw [show (⌊((n : ℚ) / 4 : ℚ)⌋).toNat = 1 * k + 1 by rw [hf]; omega, pow_add, pow_mul]
      norm_num
    have residue0 : (n / 2 + 1) % 2 = 0 := by omega
    have residue1 : n / 2 % 2 = 1 := by omega
    simp only [v0, power1, residue0, residue1]
    try rw [hk]
    all_goals
      have p256 : (256 : ℚ) ^ k = (2 ^ k : ℚ) ^ 8 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 8) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p256]
      all_goals ring
  · rw [Nat.even_iff] at hpar
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a267058.main := by
  exact ⟨claim1, claim2, claim3, claim4⟩
