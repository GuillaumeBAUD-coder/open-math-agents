import OMAStatements.S_oeis_a136269
import Mathlib

/-!
Proof. Write c(N) = N^(1/3), h(x) = (3/4) x^4 + x/2 and S(N) = sum_{i ≤ N} c(i). By induction
h(c N) - 1/4 - (1/36)(1 - 1/c(N)^2) ≤ S(N) ≤ h(c N) - 1/4: with a = c(N+1), b = c(N), a^3 = b^3 + 1,
one has h(a) - h(b) - a = (a-b)^3 (a+b)/4, which is ≥ 0 and ≤ (1/36)(1/b^2 - 1/a^2) because
3ab(a-b) ≤ (a-b)(a^2+ab+b^2) = 1. For N = M^3 this pins the floor.
-/

namespace A136269Proof

noncomputable def c (N : ℕ) : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3)

noncomputable def S (N : ℕ) : ℝ := ∑ i ∈ Finset.Icc (1 : ℕ) N, (i : ℝ) ^ ((1 : ℝ) / 3)

lemma c_cube (N : ℕ) : c N ^ 3 = N := by
  unfold c
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  norm_num

lemma c_nonneg (N : ℕ) : 0 ≤ c N := Real.rpow_nonneg (Nat.cast_nonneg N) _

lemma c_one_le (N : ℕ) (hN : 1 ≤ N) : 1 ≤ c N := by
  unfold c
  exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)

lemma c_of_cube (M : ℕ) : c (M ^ 3) = M := by
  have h1 := c_cube (M ^ 3)
  have h2 := c_nonneg (M ^ 3)
  have h3 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  push_cast at h1
  exact (pow_left_inj₀ h2 h3 (by norm_num)).mp h1

lemma step (a b : ℝ) (hb : 1 ≤ b) (hab : a ^ 3 = b ^ 3 + 1) :
    0 ≤ 3 / 4 * (a ^ 4 - b ^ 4) + (a - b) / 2 - a ∧
    3 / 4 * (a ^ 4 - b ^ 4) + (a - b) / 2 - a ≤ 1 / 36 * (1 / b ^ 2 - 1 / a ^ 2) := by
  have hlt : b < a := by
    by_contra h
    push_neg at h
    have hb0 : (0 : ℝ) ≤ b := by linarith
    by_cases ha : 0 ≤ a
    · have := pow_le_pow_left₀ ha h 3
      linarith
    · push_neg at ha
      have h1 : a ^ 3 < 0 := Odd.pow_neg (by decide) ha
      have h2 : 0 ≤ b ^ 3 := by positivity
      linarith
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  have hd : 0 < a - b := by linarith
  have key : 3 / 4 * (a ^ 4 - b ^ 4) + (a - b) / 2 - a = (a - b) ^ 3 * (a + b) / 4 := by
    have : 3 / 4 * (a ^ 4 - b ^ 4) - (a + b) / 2 * (a ^ 3 - b ^ 3) = (a - b) ^ 3 * (a + b) / 4 := by
      ring
    have h1 : a ^ 3 - b ^ 3 = 1 := by linarith
    rw [h1] at this
    linarith
  rw [key]
  refine ⟨by positivity, ?_⟩
  have hq : (a - b) * (a ^ 2 + a * b + b ^ 2) = 1 := by
    have : (a - b) * (a ^ 2 + a * b + b ^ 2) = a ^ 3 - b ^ 3 := by ring
    linarith
  have h3 : 3 * (a * b * (a - b)) ≤ 1 := by
    have : (a - b) * (a ^ 2 + a * b + b ^ 2) - 3 * (a * b * (a - b)) = (a - b) ^ 3 := by ring
    have h' : 0 ≤ (a - b) ^ 3 := by positivity
    linarith
  have h30 : 0 ≤ 3 * (a * b * (a - b)) := by positivity
  have h4 : (3 * (a * b * (a - b))) ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ h30 h3 2
    simpa using this
  have e : 1 / 36 * (1 / b ^ 2 - 1 / a ^ 2) = (a - b) * (a + b) / (36 * (a ^ 2 * b ^ 2)) := by
    field_simp
    ring
  rw [e, le_div_iff₀ (by positivity)]
  have h5 : 0 ≤ (a - b) * (a + b) / 4 := by positivity
  have : (a - b) ^ 3 * (a + b) / 4 * (36 * (a ^ 2 * b ^ 2))
      = ((a - b) * (a + b) / 4) * (4 * (3 * (a * b * (a - b))) ^ 2) := by ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left h4 h5]

lemma bounds (N : ℕ) (hN : 1 ≤ N) :
    3 / 4 * c N ^ 4 + c N / 2 - 1 / 4 - 1 / 36 * (1 - 1 / c N ^ 2) ≤ S N ∧
    S N ≤ 3 / 4 * c N ^ 4 + c N / 2 - 1 / 4 := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h1 : c 1 = 1 := by simp [c]
    have h2 : S 1 = 1 := by simp [S]
    rw [h1, h2]
    norm_num
  | succ N hN ih =>
    have hS : S (N + 1) = S N + c (N + 1) := by
      unfold S c
      rw [Finset.sum_Icc_succ_top (by omega)]
    have hab : c (N + 1) ^ 3 = c N ^ 3 + 1 := by
      rw [c_cube, c_cube]
      push_cast
      ring
    obtain ⟨s1, s2⟩ := step (c (N + 1)) (c N) (c_one_le N hN) hab
    obtain ⟨i1, i2⟩ := ih
    rw [hS]
    constructor <;> linarith

theorem floor_formula (j : ℕ) :
    ⌊S (10 ^ (3 * (j + 1)))⌋ = 7500 * 10 ^ (4 * j) + 5 * 10 ^ j - 1 := by
  have hN : (10 : ℕ) ^ (3 * (j + 1)) = (10 ^ (j + 1)) ^ 3 := by
    rw [← pow_mul]
    congr 1
    ring
  rw [hN]
  have hc : c ((10 ^ (j + 1)) ^ 3) = 10 * 10 ^ j := by
    rw [c_of_cube]
    push_cast
    ring
  have hpos : 1 ≤ (10 ^ (j + 1)) ^ 3 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by norm_num))
  obtain ⟨b1, b2⟩ := bounds _ hpos
  rw [hc] at b1 b2
  have hx : (1 : ℝ) ≤ 10 ^ j := one_le_pow₀ (by norm_num)
  have hinv : 1 / (10 * (10 : ℝ) ^ j) ^ 2 ≥ 0 := by positivity
  have e4 : (10 * (10 : ℝ) ^ j) ^ 4 = 10000 * 10 ^ (4 * j) := by
    rw [mul_pow, ← pow_mul]
    congr 1
    · norm_num
    · congr 1
      ring
  rw [e4] at b1 b2
  rw [Int.floor_eq_iff]
  push_cast
  constructor <;> linarith

end A136269Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a136269.main := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := A136269Proof.floor_formula j
  have ha : OMA.S_oeis_a136269.a (3 * (j + 1)) = 7500 * 10 ^ (4 * j) + 5 * 10 ^ j - 1 := h
  rw [ha]
  have hj : j + 1 - 1 = j := by omega
  rw [hj]
  have : (10 : ℚ) ^ (4 * (j + 1)) = 10000 * 10 ^ (4 * j) := by
    rw [mul_add, pow_add]
    ring
  rw [this]
  push_cast
  ring
