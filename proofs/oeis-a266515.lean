import OMAStatements.S_oeis_a266515

namespace Ours

def update (l c r : Bool) : Bool :=
  (29 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)
def background : ℕ → Bool
  | 0 => false
  | n + 1 => let b := background n; update b b b
def scan (l c : Bool) : List Bool → List Bool
  | [] => []
  | r :: rs => update l c r :: scan c r rs
def row : ℕ → List Bool
  | 0 => [true]
  | n + 1 =>
    let b := background n
    scan b b (row n ++ [b, b])
def a (n : ℕ) : ℕ := Nat.ofDigits 10 ((row n).map Bool.toNat).reverse



def blocks (w : List Bool) : ℕ → List Bool → List Bool
  | 0, tail => tail
  | k + 1, tail => w ++ blocks w k tail

lemma blocks_append (w : List Bool) (k : ℕ) (u v : List Bool) :
    blocks w k u ++ v = blocks w k (u ++ v) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, List.append_assoc, ih]

def word0 (k : ℕ) : List Bool :=
  blocks [false, false] k ([false, false, true, false, false] ++ blocks [false, false] k [])

def word1 (k : ℕ) : List Bool :=
  blocks [true, true] k ([true, true, false, true, true, true, true] ++ blocks [true, true] k [])

lemma align1 (k : ℕ) (tail : List Bool) :
    blocks [false, false] (k + 2) tail =
      [false, false] ++ blocks [false, false] k ([false, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false] ++ rest) ih

lemma align2 (k : ℕ) (tail : List Bool) :
    blocks [false, false] (k + 2) tail =
      [false, false, false, false] ++ blocks [false, false] k tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false] ++ rest) ih

lemma align3 (k : ℕ) (tail : List Bool) :
    blocks [true, true] (k + 2) tail =
      [true, true] ++ blocks [true, true] k ([true, true] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true] ++ rest) ih

lemma scanBlock1 (k : ℕ) (tail : List Bool) :
    scan false false (blocks [false, false] k tail) =
      blocks [true, true] k (scan false false tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [true, true] ++ rest) ih

lemma align4 (k : ℕ) (tail : List Bool) :
    blocks [true, true] (k + 1) tail =
      [true, true] ++ blocks [true, true] k tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true] ++ rest) ih

lemma scanBlock2 (k : ℕ) (tail : List Bool) :
    scan true true (blocks [true, true] k tail) =
      blocks [false, false] k (scan true true tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [false, false] ++ rest) ih

lemma phase0 (k : ℕ) :
    scan false false ((word0 k) ++ [false, false]) =
      word1 k := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [word0, word1, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
      change scan false false (blocks [false, false] (k + 2) ([false, false, true, false, false] ++ blocks [false, false] (k + 2) ([false, false]))) = blocks [true, true] (k + 2) ([true, true, false, true, true, true, true] ++ blocks [true, true] (k + 2) [])
      conv => lhs; rw [align1]
      conv => lhs; rw [align2]
      conv => rhs; rw [align3]
      conv => rhs; rw [align3]
      simp only [List.cons_append, List.nil_append, scan, scanBlock1]
      <;> rfl

lemma phase1 (k : ℕ) :
    scan true true ((word1 k) ++ [true, true]) =
      word0 (k + 1) := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word1, word0, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan true true (blocks [true, true] (k + 1) ([true, true, false, true, true, true, true] ++ blocks [true, true] (k + 1) ([true, true]))) = blocks [false, false] (k + 2) ([false, false, true, false, false] ++ blocks [false, false] (k + 2) [])
    conv => lhs; rw [align4]
    conv => lhs; rw [align4]
    conv => rhs; rw [align1]
    conv => rhs; rw [align1]
    simp only [List.cons_append, List.nil_append, scan, scanBlock2]
    <;> rfl

lemma cycle (k : ℕ) :
    (row (2 * k + 2) = word0 k ∧ background (2 * k + 2) = false) ∧
    (row (2 * k + 3) = word1 k ∧ background (2 * k + 3) = true) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h0 : row (2 * (k + 1) + 2) = word0 (k+1) ∧ background (2 * (k + 1) + 2) = false := by
      rw [show 2 * (k + 1) + 2 = (2 * k + 3) + 1 by omega]
      exact ⟨by rw [row, ih.2.1, ih.2.2]; exact phase1 k, by rw [background, ih.2.2]; rfl⟩
    have h1 : row (2 * (k + 1) + 3) = word1 (k+1) ∧ background (2 * (k + 1) + 3) = true := by
      rw [show 2 * (k + 1) + 3 = (2 * (k + 1) + 2) + 1 by omega]
      exact ⟨by rw [row, h0.1, h0.2]; exact phase0 (k + 1), by rw [background, h0.2]; rfl⟩
    exact ⟨h0, h1⟩

def magnitude (w : List Bool) : ℚ := (10 : ℚ) ^ w.length

def encode (w : List Bool) : ℚ := (Nat.ofDigits 10 (w.map Bool.toNat).reverse : ℕ)

lemma magnitude_append (u v : List Bool) : magnitude (u ++ v) = magnitude u * magnitude v := by
  simp [magnitude, pow_add]

lemma encode_append (u v : List Bool) : encode (u ++ v) = encode u * magnitude v + encode v := by
  simp [encode, magnitude, Nat.ofDigits_append]
  ring

lemma run00 (k : ℕ) (tail : List Bool) :
    magnitude (blocks [false, false] k tail) = (100 : ℚ) ^ k * magnitude tail ∧
    encode (blocks [false, false] k tail) =
      0 * ((100 : ℚ) ^ k - 1) * magnitude tail + encode tail := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    rw [blocks, magnitude_append, encode_append, ih.1, ih.2, pow_succ]
    have hm : magnitude [false, false] = 100 := by decide
    have he : encode [false, false] = 0 := by decide
    rw [hm, he]
    constructor <;> ring

lemma run11 (k : ℕ) (tail : List Bool) :
    magnitude (blocks [true, true] k tail) = (100 : ℚ) ^ k * magnitude tail ∧
    encode (blocks [true, true] k tail) =
      (1 / 9) * ((100 : ℚ) ^ k - 1) * magnitude tail + encode tail := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    rw [blocks, magnitude_append, encode_append, ih.1, ih.2, pow_succ]
    have hm : magnitude [true, true] = 100 := by decide
    have he : encode [true, true] = 11 := by decide
    rw [hm, he]
    constructor <;> ring

lemma value0 (k : ℕ) : (a (2 * k + 2) : ℚ) = 100 * (100 : ℚ) ^ k := by
  change encode (row (2 * k + 2)) = _
  rw [(cycle k).1.1, word0]
  have e0 : encode [] = 0 := by decide
  have m0 : magnitude [] = 1 := by decide
  have e1 : encode [false, false, true, false, false] = 100 := by decide
  have m1 : magnitude [false, false, true, false, false] = 100000 := by decide
  have z0 := fun tail => (run00 k tail).1
  have y0 := fun tail => (run00 k tail).2
  simp only [encode_append, magnitude_append, e0, m0, e1, m1, z0, y0]
  have p100 : (100 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 2 := by
    calc _ = (((2 : ℚ) ^ 2) * (5 ^ 2)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
    calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  push_cast
  norm_num [pow_succ, pow_add, pow_mul]
  all_goals try simp only [p100, p10000]
  all_goals ring

lemma value1 (k : ℕ) : (a (2 * k + 3) : ℚ) = (-1 / 9) + (-10000) * (100 : ℚ) ^ k + (10000000 / 9) * (10000 : ℚ) ^ k := by
  change encode (row (2 * k + 3)) = _
  rw [(cycle k).2.1, word1]
  have e0 : encode [] = 0 := by decide
  have m0 : magnitude [] = 1 := by decide
  have e1 : encode [true, true, false, true, true, true, true] = 1101111 := by decide
  have m1 : magnitude [true, true, false, true, true, true, true] = 10000000 := by decide
  have z0 := fun tail => (run11 k tail).1
  have y0 := fun tail => (run11 k tail).2
  simp only [encode_append, magnitude_append, e0, m0, e1, m1, z0, y0]
  have p100 : (100 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 2 := by
    calc _ = (((2 : ℚ) ^ 2) * (5 ^ 2)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
    calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  push_cast
  norm_num [pow_succ, pow_add, pow_mul]
  all_goals try simp only [p100, p10000]
  all_goals ring


lemma initial0 : a 0 = 1 := by rfl
lemma initial1 : a 1 = 11 := by rfl
lemma initial2 : a 2 = 100 := by rfl
lemma initial3 : a 3 = 1101111 := by rfl
lemma initial4 : a 4 = 10000 := by rfl
lemma initial5 : a 5 = 11110111111 := by rfl
lemma initial6 : a 6 = 1000000 := by rfl
lemma initial7 : a 7 = 111111011111111 := by rfl

lemma claim1 : ∀ n : ℕ, 5 < n → (a n : ℤ) = 10101 * (a (n - 2) : ℤ) - 1010100 * (a (n - 4) : ℤ) + 1000000 * (a (n - 6) : ℤ) := by
  intro n hn
  suffices hq : (a n : ℚ) = 10101 * (a (n - 2) : ℚ) - 1010100 * (a (n - 4) : ℚ) + 1000000 * (a (n - 6) : ℚ) by exact_mod_cast hq
  by_cases small : n < 8
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 8 ∨ n = 2 * k + 9 := by
    exact ⟨(n - 8) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = 100 * (100 : ℚ) ^ (k + 3) := by
      rw [show n = 2 * (k + 3) + 2 by omega]
      exact value0 (k + 3)
    have v1 : (a (n - 6) : ℚ) = 100 * (100 : ℚ) ^ k := by
      rw [show n - 6 = 2 * k + 2 by omega]
      exact value0 k
    have v2 : (a (n - 2) : ℚ) = 100 * (100 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 2 * (k + 2) + 2 by omega]
      exact value0 (k + 2)
    have v3 : (a (n - 4) : ℚ) = 100 * (100 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 2 * (k + 1) + 2 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    have p100 : (100 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 2 := by
      calc _ = (((2 : ℚ) ^ 2) * (5 ^ 2)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
      calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [p100, p10000]
    all_goals ring
  · have v0 : (a n : ℚ) = (-1 / 9) + (-10000) * (100 : ℚ) ^ (k + 3) + (10000000 / 9) * (10000 : ℚ) ^ (k + 3) := by
      rw [show n = 2 * (k + 3) + 3 by omega]
      exact value1 (k + 3)
    have v1 : (a (n - 6) : ℚ) = (-1 / 9) + (-10000) * (100 : ℚ) ^ k + (10000000 / 9) * (10000 : ℚ) ^ k := by
      rw [show n - 6 = 2 * k + 3 by omega]
      exact value1 k
    have v2 : (a (n - 2) : ℚ) = (-1 / 9) + (-10000) * (100 : ℚ) ^ (k + 2) + (10000000 / 9) * (10000 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 2 * (k + 2) + 3 by omega]
      exact value1 (k + 2)
    have v3 : (a (n - 4) : ℚ) = (-1 / 9) + (-10000) * (100 : ℚ) ^ (k + 1) + (10000000 / 9) * (10000 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 2 * (k + 1) + 3 by omega]
      exact value1 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    have p100 : (100 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 2 := by
      calc _ = (((2 : ℚ) ^ 2) * (5 ^ 2)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
      calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [p100, p10000]
    all_goals ring

lemma claim2Tail : ∀ n : ℕ, 5 < n → (a n : ℚ) = -(-1000000 * (a (n - 6) : ℚ) + 1010100 * (a (n - 4) : ℚ) + -10101 * (a (n - 2) : ℚ)) := by
  intro n hn
  by_cases small : n < 8
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 8 ∨ n = 2 * k + 9 := by
    exact ⟨(n - 8) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = 100 * (100 : ℚ) ^ (k + 3) := by
      rw [show n = 2 * (k + 3) + 2 by omega]
      exact value0 (k + 3)
    have v1 : (a (n - 2) : ℚ) = 100 * (100 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 2 * (k + 2) + 2 by omega]
      exact value0 (k + 2)
    have v2 : (a (n - 6) : ℚ) = 100 * (100 : ℚ) ^ k := by
      rw [show n - 6 = 2 * k + 2 by omega]
      exact value0 k
    have v3 : (a (n - 4) : ℚ) = 100 * (100 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 2 * (k + 1) + 2 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    have p100 : (100 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 2 := by
      calc _ = (((2 : ℚ) ^ 2) * (5 ^ 2)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
      calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [p100, p10000]
    all_goals ring
  · have v0 : (a n : ℚ) = (-1 / 9) + (-10000) * (100 : ℚ) ^ (k + 3) + (10000000 / 9) * (10000 : ℚ) ^ (k + 3) := by
      rw [show n = 2 * (k + 3) + 3 by omega]
      exact value1 (k + 3)
    have v1 : (a (n - 2) : ℚ) = (-1 / 9) + (-10000) * (100 : ℚ) ^ (k + 2) + (10000000 / 9) * (10000 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 2 * (k + 2) + 3 by omega]
      exact value1 (k + 2)
    have v2 : (a (n - 6) : ℚ) = (-1 / 9) + (-10000) * (100 : ℚ) ^ k + (10000000 / 9) * (10000 : ℚ) ^ k := by
      rw [show n - 6 = 2 * k + 3 by omega]
      exact value1 k
    have v3 : (a (n - 4) : ℚ) = (-1 / 9) + (-10000) * (100 : ℚ) ^ (k + 1) + (10000000 / 9) * (10000 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 2 * (k + 1) + 3 by omega]
      exact value1 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    have p100 : (100 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 2 := by
      calc _ = (((2 : ℚ) ^ 2) * (5 ^ 2)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
      calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [p100, p10000]
    all_goals ring

open PowerSeries in
lemma claim2 : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X)) = 1 + 11 * X - 10001 * X ^ 2 + 990000 * X ^ 3 + 10000 * X ^ 4 - 1100000 * X ^ 5 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  have hd : s * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X)) = PowerSeries.C (1 : ℚ) * (s * X ^ 0) + PowerSeries.C (-10101 : ℚ) * (s * X ^ 2) + PowerSeries.C (1010100 : ℚ) * (s * X ^ 4) + PowerSeries.C (-1000000 : ℚ) * (s * X ^ 6) := by norm_num [map_ofNat] <;> ring
  have hn : 1 + 11 * X - 10001 * X ^ 2 + 990000 * X ^ 3 + 10000 * X ^ 4 - 1100000 * X ^ 5 = PowerSeries.C (1 : ℚ) * (X ^ 0 : PowerSeries ℚ) + PowerSeries.C (11 : ℚ) * (X ^ 1 : PowerSeries ℚ) + PowerSeries.C (-10001 : ℚ) * (X ^ 2 : PowerSeries ℚ) + PowerSeries.C (990000 : ℚ) * (X ^ 3 : PowerSeries ℚ) + PowerSeries.C (10000 : ℚ) * (X ^ 4 : PowerSeries ℚ) + PowerSeries.C (-1100000 : ℚ) * (X ^ 5 : PowerSeries ℚ) := by norm_num [map_ofNat] <;> ring
  rw [hd, hn]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_X_pow, coeff_mul_X_pow', s, coeff_mk]
  by_cases h : n ≤ 5
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3, initial4, initial5]
  · have hr := claim2Tail n (by omega)
    simp only [if_pos (show 6 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 0 ≤ n by omega), if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega), Nat.sub_zero]
    linarith

lemma claim3 : ∀ n : ℕ, Odd n → (a n : ℚ) = (10 * (100 ^ n - 9 * 10 ^ n) - 1) / 9 := by
  intro n hpar
  by_cases small : n < 2
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, initial0, initial1] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 2 ∨ n = 2 * k + 3 := by
    exact ⟨(n - 2) / 2, by omega⟩
  rcases hk with hk | hk
  · rw [Nat.odd_iff] at hpar
    omega
  · have v0 : (a n : ℚ) = (-1 / 9) + (-10000) * (100 : ℚ) ^ k + (10000000 / 9) * (10000 : ℚ) ^ k := by
      rw [show n = 2 * k + 3 by omega]
      exact value1 k
    have power1 : (100 : ℚ) ^ n = (10000 : ℚ) ^ k * (100 : ℚ) ^ 3 := by
      rw [show n = 2 * k + 3 by omega, pow_add, pow_mul]
      norm_num
    have power2 : (10 : ℚ) ^ n = (100 : ℚ) ^ k * (10 : ℚ) ^ 3 := by
      rw [show n = 2 * k + 3 by omega, pow_add, pow_mul]
      norm_num
    simp only [v0, power1, power2]
    try rw [hk]
    have p100 : (100 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 2 := by
      calc _ = (((2 : ℚ) ^ 2) * (5 ^ 2)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
      calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [p100, p10000]
    all_goals ring

lemma claim4 : ∀ n : ℕ, Even n → (a n : ℤ) = 10 ^ n := by
  intro n hpar
  suffices hq : (a n : ℚ) = 10 ^ n by exact_mod_cast hq
  by_cases small : n < 2
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, initial0, initial1] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 2 ∨ n = 2 * k + 3 := by
    exact ⟨(n - 2) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = 100 * (100 : ℚ) ^ k := by
      rw [show n = 2 * k + 2 by omega]
      exact value0 k
    have power1 : (10 : ℚ) ^ n = (100 : ℚ) ^ k * (10 : ℚ) ^ 2 := by
      rw [show n = 2 * k + 2 by omega, pow_add, pow_mul]
      norm_num
    simp only [v0, power1]
    try rw [hk]
    have p100 : (100 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 2 := by
      calc _ = (((2 : ℚ) ^ 2) * (5 ^ 2)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
      calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
           _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [p100, p10000]
    all_goals ring
  · rw [Nat.even_iff] at hpar
    omega


end Ours

section Helpers

open PowerSeries

lemma ps_eq_mul_inv {F N D : PowerSeries ℚ} (h : F * D = N) (hc : constantCoeff D ≠ 0) :
    F = N * D⁻¹ := by
  rw [← h, mul_assoc, PowerSeries.mul_inv_cancel D hc, mul_one]

lemma ps_int_of_rat {L R : PowerSeries ℤ}
    (h : PowerSeries.map (Int.castRingHom ℚ) L = PowerSeries.map (Int.castRingHom ℚ) R) :
    L = R := by
  ext n
  apply Int.cast_injective (α := ℚ)
  have hn := congr_arg (PowerSeries.coeff n) h
  simpa only [PowerSeries.coeff_map, Int.coe_castRingHom] using hn

lemma nat_div_of_floor {a X Y : ℕ} (hY : 0 < Y)
    (h : (a : ℤ) = ⌊(X : ℚ) / (Y : ℚ)⌋) : a = X / Y := by
  have hYq : (0 : ℚ) < (Y : ℚ) := by exact_mod_cast hY
  have hf := Int.floor_eq_iff.mp h.symm
  have h1 : (a : ℚ) * (Y : ℚ) ≤ (X : ℚ) := (le_div_iff₀ hYq).mp hf.1
  have h2 : (X : ℚ) < ((a : ℚ) + 1) * (Y : ℚ) := (div_lt_iff₀ hYq).mp hf.2
  have h1n : a * Y ≤ X := by exact_mod_cast h1
  have h2n : X < (a + 1) * Y := by exact_mod_cast h2
  have hle : a ≤ X / Y := (Nat.le_div_iff_mul_le hY).mpr h1n
  have hlt : X / Y < a + 1 := (Nat.div_lt_iff_lt_mul hY).mpr h2n
  omega

def seg (a : ℤ) : ℕ → (ℤ → Bool) → List Bool
  | 0, _ => []
  | m + 1, g => g a :: seg (a + 1) m g

lemma seg_snoc (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    seg a (m + 1) g = seg a m g ++ [g (a + m)] := by
  induction m generalizing a with
  | zero => simp [seg]
  | succ m ih =>
    rw [seg, ih (a + 1), seg, List.cons_append]
    congr 2
    push_cast
    ring

lemma seg_append_two (a : ℤ) (m : ℕ) (g : ℤ → Bool) (b : Bool)
    (h1 : g (a + m) = b) (h2 : g (a + m + 1) = b) :
    seg a m g ++ [b, b] = seg a (m + 2) g := by
  rw [seg_snoc a (m + 1) g, seg_snoc a m g, List.append_assoc]
  simp only [List.singleton_append, Nat.cast_add, Nat.cast_one, ← add_assoc, h1, h2]

lemma seg_getElem? (a : ℤ) (m : ℕ) (g : ℤ → Bool) (k : ℕ) (hk : k < m) :
    (seg a m g)[k]? = some (g (a + k)) := by
  induction m generalizing a k with
  | zero => omega
  | succ m ih =>
    cases k with
    | zero => simp [seg]
    | succ k =>
      simp only [seg, List.getElem?_cons_succ]
      rw [ih (a + 1) k (by omega)]
      congr 1
      push_cast
      ring

lemma seg_count (c : Bool) (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    (seg a m g).count c = ∑ k ∈ Finset.range m, if g (a + k) = c then 1 else 0 := by
  induction m generalizing a with
  | zero => simp [seg]
  | succ m ih =>
    rw [seg_snoc, List.count_append, ih a, Finset.sum_range_succ]
    simp [List.count_cons, beq_iff_eq]

lemma seg_count_icc (n : ℕ) (g : ℤ → Bool) :
    (seg (-(n : ℤ)) (2 * n + 1) g).count true =
      ((Finset.Icc (-(n : ℤ)) n).filter (fun i => g i)).card := by
  rw [seg_count, Finset.card_filter]
  refine Finset.sum_nbij (fun k : ℕ => (k : ℤ) - n) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k₁ _ k₂ _ h
    dsimp only at h
    omega
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    refine ⟨(i + n).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp only
    omega
  · intro k _
    have h1 : -(n : ℤ) + (k : ℤ) = (k : ℤ) - n := by ring
    rw [h1]

lemma seg_ofDigits (B : ℕ) (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    Nat.ofDigits B (((seg a m g).map Bool.toNat).reverse) =
      ∑ k ∈ Finset.range m, if g (a + k) then B ^ (m - 1 - k) else 0 := by
  induction m generalizing a with
  | zero => simp [seg]
  | succ m ih =>
    rw [seg_snoc, List.map_append, List.reverse_append, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      Nat.ofDigits_cons, ih a, Finset.sum_range_succ, Finset.mul_sum]
    simp only [Nat.add_sub_cancel]
    have hsum :
        (∑ x ∈ Finset.range m, B * (if g (a + x) then B ^ (m - 1 - x) else 0)) =
          ∑ x ∈ Finset.range m, if g (a + x) then B ^ (m - x) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx' := Finset.mem_range.mp hx
      split_ifs
      · rw [show m - x = (m - 1 - x) + 1 by omega, pow_succ']
      · simp
    rw [hsum]
    cases g (a + m) <;> simp [Nat.add_comm]

lemma seg_ofDigits_rev (B : ℕ) (n : ℕ) (g : ℤ → Bool) :
    Nat.ofDigits B (((seg (-(n : ℤ)) (2 * n + 1) g).map Bool.toNat).reverse) =
      ∑ i ∈ Finset.range (2 * n + 1), (g ((n : ℤ) - i)).toNat * B ^ i := by
  rw [seg_ofDigits, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hidx : -(n : ℤ) + ((2 * n + 1 - 1 - i : ℕ) : ℤ) = (n : ℤ) - i := by omega
  have hexp : 2 * n + 1 - 1 - (2 * n + 1 - 1 - i) = i := by omega
  rw [hidx, hexp]
  cases g ((n : ℤ) - i) <;> simp

end Helpers

namespace BridgeProof

lemma scan_seg_ours (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    Ours.scan (g (a - 2)) (g (a - 1)) (seg a m g) =
      seg (a - 1) m (fun i => Ours.update (g (i - 1)) (g i) (g (i + 1))) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    simp only [seg, Ours.scan]
    refine congrArg₂ List.cons ?_ ?_
    · congr 1 <;> ring
    · calc
        Ours.scan (g (a - 1)) (g a) (seg (a + 1) m g)
          = Ours.scan (g ((a + 1) - 2)) (g ((a + 1) - 1)) (seg (a + 1) m g) := by
              congr 1 <;> ring
        _ = seg ((a + 1) - 1) m (fun i => Ours.update (g (i - 1)) (g i) (g (i + 1))) := ih (a + 1)
        _ = seg ((a - 1) + 1) m (fun i => Ours.update (g (i - 1)) (g i) (g (i + 1))) := by
              congr 1; ring

lemma st_step (n : ℕ) (i : ℤ) :
    (OMA.S_oeis_a266515.state 29) (n + 1) i = Ours.update ((OMA.S_oeis_a266515.state 29) n (i - 1)) ((OMA.S_oeis_a266515.state 29) n i) ((OMA.S_oeis_a266515.state 29) n (i + 1)) := by
  rfl

lemma st_outside (n : ℕ) (i : ℤ) (hi : i < -(n : ℤ) ∨ (n : ℤ) < i) :
    (OMA.S_oeis_a266515.state 29) n i = Ours.background n := by
  induction n generalizing i with
  | zero =>
    have hne : i ≠ 0 := by omega
    simp [OMA.S_oeis_a266515.state, Ours.background, hne]
  | succ n ih =>
    rw [st_step, Ours.background]
    have h1 : (OMA.S_oeis_a266515.state 29) n (i - 1) = Ours.background n := ih (i - 1) (by omega)
    have h2 : (OMA.S_oeis_a266515.state 29) n i = Ours.background n := ih i (by omega)
    have h3 : (OMA.S_oeis_a266515.state 29) n (i + 1) = Ours.background n := ih (i + 1) (by omega)
    rw [h1, h2, h3]

lemma row_eq_seg (n : ℕ) :
    Ours.row n = seg (-(n : ℤ)) (2 * n + 1) ((OMA.S_oeis_a266515.state 29) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Ours.row, ih]
    have hr1 : (OMA.S_oeis_a266515.state 29) n (-(n : ℤ) + (2 * n + 1 : ℕ)) = Ours.background n :=
      st_outside n _ (by omega)
    have hr2 : (OMA.S_oeis_a266515.state 29) n (-(n : ℤ) + (2 * n + 1 : ℕ) + 1) = Ours.background n :=
      st_outside n _ (by omega)
    rw [seg_append_two (-(n : ℤ)) (2 * n + 1) ((OMA.S_oeis_a266515.state 29) n) (Ours.background n) hr1 hr2]
    have hl1 : Ours.background n = (OMA.S_oeis_a266515.state 29) n (-(n : ℤ) - 2) :=
      (st_outside n _ (by omega)).symm
    have hl2 : Ours.background n = (OMA.S_oeis_a266515.state 29) n (-(n : ℤ) - 1) :=
      (st_outside n _ (by omega)).symm
    conv_lhs =>
      arg 1; rw [hl1]
    conv_lhs =>
      arg 2; rw [hl2]
    rw [scan_seg_ours]
    have ha : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have hm : 2 * n + 1 + 2 = 2 * (n + 1) + 1 := by omega
    have hf : (fun i => Ours.update ((OMA.S_oeis_a266515.state 29) n (i - 1)) ((OMA.S_oeis_a266515.state 29) n i) ((OMA.S_oeis_a266515.state 29) n (i + 1))) =
        (OMA.S_oeis_a266515.state 29) (n + 1) := by
      funext i
      exact (st_step n i).symm
    rw [ha, hm, hf]


lemma a_eq (n : ℕ) : OMA.S_oeis_a266515.a n = Ours.a n := by
  rw [Ours.a, row_eq_seg, seg_ofDigits_rev, OMA.S_oeis_a266515.a, OMA.S_oeis_a266515.rowDigits]

lemma main_proof : type_of% @OMA.S_oeis_a266515.main := by
  have ha : OMA.S_oeis_a266515.a = Ours.a := funext a_eq
  dsimp only [OMA.S_oeis_a266515.A]
  rw [ha]
  refine ⟨Ours.claim1, ps_eq_mul_inv Ours.claim2 (by simp), Ours.claim3, ?_⟩
  intro n hn
  exact_mod_cast Ours.claim4 n hn

end BridgeProof

theorem OMA.solution : type_of% @OMA.S_oeis_a266515.main := BridgeProof.main_proof
