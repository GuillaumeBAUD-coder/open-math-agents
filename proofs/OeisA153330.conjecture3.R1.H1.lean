import OMAReductions.R_OeisA153330_conjecture3_R1
import Mathlib

-- Step OeisA153330.conjecture3.R1.H1: hypothesis H1 of reduction OeisA153330.conjecture3.R1
-- Credit: @ivillar. Multiplying the bracket inequalities (and using 8(n+1) <= 9n) gives 2^(d+1) 3^a < 3^(c+1) 2^b < 2^(d+2) 3^a; splitting on the signs of c - a and d - b reduces to small power comparisons, settled by decide for differences below 28, and every m >= 28 is 5x + 8y.

/-! Step OeisA153330.conjecture3.R1.H1. -/

namespace P8A153330

/-- Numbers below 28 that are not of the form `5 x + 8 y`. -/
def S : Finset ℕ := {1, 2, 3, 4, 6, 7, 9, 11, 12, 14, 17, 19, 22, 27}

lemma rep_small : ∀ m < 28, m ∉ S → ∃ x < 6, ∃ y < 4, m = 5 * x + 8 * y := by decide

lemma rep_large (m : ℕ) (hm : 28 ≤ m) : ∃ x y : ℕ, m = 5 * x + 8 * y := by
  rcases (by omega : (m - 28) % 5 = 0 ∨ (m - 28) % 5 = 1 ∨ (m - 28) % 5 = 2 ∨
      (m - 28) % 5 = 3 ∨ (m - 28) % 5 = 4) with h | h | h | h | h
  · exact ⟨4 + (m - 28) / 5, 1, by omega⟩
  · exact ⟨1 + (m - 28) / 5, 3, by omega⟩
  · exact ⟨6 + (m - 28) / 5, 0, by omega⟩
  · exact ⟨3 + (m - 28) / 5, 2, by omega⟩
  · exact ⟨(m - 28) / 5, 4, by omega⟩

lemma rep_lt (m : ℕ) (h28 : m < 28) (hm : m ∉ S) : ∃ x y : ℕ, m = 5 * x + 8 * y := by
  obtain ⟨x, -, y, -, hxy⟩ := rep_small m h28 hm
  exact ⟨x, y, hxy⟩

/-- Same-sign case: `2^(v+1) < 3^(u+1) < 2^(v+2)`. -/
lemma table1 : ∀ u < 28, ∀ v < 28, 2 ^ (v + 1) < 3 ^ (u + 1) → 3 ^ (u + 1) < 2 ^ (v + 2) →
    (u + v = 3 ∨ u + v ∉ S) := by decide

/-- Both differences negative: `2 * 3^u < 3 * 2^v < 4 * 3^u`. -/
lemma table4 : ∀ u < 28, ∀ v < 28, 2 * 3 ^ u < 3 * 2 ^ v → 3 * 2 ^ v < 4 * 3 ^ u →
    u + v ∉ S := by decide

lemma case1 (u v : ℕ) (h1 : 2 ^ (v + 1) < 3 ^ (u + 1)) (h2 : 3 ^ (u + 1) < 2 ^ (v + 2)) :
    u + v = 3 ∨ ∃ x y : ℕ, u + v = 5 * x + 8 * y := by
  by_cases hs : 28 ≤ u + v
  · exact Or.inr (rep_large _ hs)
  · rcases table1 u (by omega) v (by omega) h1 h2 with h | h
    · exact Or.inl h
    · exact Or.inr (rep_lt _ (by omega) h)

lemma case4 (u v : ℕ) (h1 : 2 * 3 ^ u < 3 * 2 ^ v) (h2 : 3 * 2 ^ v < 4 * 3 ^ u) :
    ∃ x y : ℕ, u + v = 5 * x + 8 * y := by
  by_cases hs : 28 ≤ u + v
  · exact rep_large _ hs
  · exact rep_lt _ (by omega) (table4 u (by omega) v (by omega) h1 h2)

theorem a153330_h1 : ∀ a b c d n : ℕ, 8 ≤ n → 3 ^ a * n ≤ 2 ^ b → 3 * 2 ^ b < 4 * (3 ^ a * n) →
    3 ^ c * (n + 1) ≤ 2 ^ d → 3 * 2 ^ d < 4 * (3 ^ c * (n + 1)) →
    ((c + d : ℤ) - (a + b) = 1 ∨ (c + d : ℤ) - (a + b) = 3 ∨ (c + d : ℤ) - (a + b) = 6 ∨
      ∃ x y : ℕ, ((c + d : ℤ) - (a + b)).natAbs = 5 * x + 8 * y) := by
  intro a b c d n hn h1 h2 h3 h4
  have hX : 0 < 2 ^ b := by positivity
  have hY : 0 < 2 ^ d := by positivity
  have hZ : 0 < 3 ^ a := by positivity
  have hW : 0 < 3 ^ c := by positivity
  -- P2 : 3^(c+1) 2^b < 2^(d+2) 3^a
  have P2 : 3 ^ (c + 1) * 2 ^ b < 2 ^ (d + 2) * 3 ^ a := by
    have e1 : 3 ^ c * (n + 1) * (3 * 2 ^ b) ≤ 2 ^ d * (3 * 2 ^ b) := Nat.mul_le_mul_right _ h3
    have e2 : 2 ^ d * (3 * 2 ^ b) < 2 ^ d * (4 * (3 ^ a * n)) := Nat.mul_lt_mul_of_pos_left h2 hY
    have e3 : 2 ^ d * (4 * (3 ^ a * n)) ≤ 2 ^ d * (4 * (3 ^ a * (n + 1))) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      exact Nat.mul_le_mul_left _ (by omega)
    have e4 : (3 ^ (c + 1) * 2 ^ b) * (n + 1) < (2 ^ (d + 2) * 3 ^ a) * (n + 1) := by
      calc (3 ^ (c + 1) * 2 ^ b) * (n + 1) = 3 ^ c * (n + 1) * (3 * 2 ^ b) := by ring
        _ < 2 ^ d * (4 * (3 ^ a * (n + 1))) := lt_of_le_of_lt e1 (lt_of_lt_of_le e2 e3)
        _ = (2 ^ (d + 2) * 3 ^ a) * (n + 1) := by ring
    exact Nat.lt_of_mul_lt_mul_right e4
  -- P1 : 2^(d+1) 3^a < 3^(c+1) 2^b
  have P1 : 2 ^ (d + 1) * 3 ^ a < 3 ^ (c + 1) * 2 ^ b := by
    have e1 : 3 * 2 ^ d * (3 ^ a * n) < 4 * (3 ^ c * (n + 1)) * (3 ^ a * n) :=
      Nat.mul_lt_mul_of_pos_right h4 (by positivity)
    have e2 : 4 * (3 ^ c * (n + 1)) * (3 ^ a * n) ≤ 4 * (3 ^ c * (n + 1)) * 2 ^ b :=
      Nat.mul_le_mul_left _ h1
    have e3 : 8 * (n + 1) ≤ 9 * n := by omega
    have e4 : (2 ^ (d + 1) * 3 ^ a) * (12 * n) < (3 ^ (c + 1) * 2 ^ b) * (12 * n) := by
      have : 8 * (3 * 2 ^ d * (3 ^ a * n)) < 8 * (4 * (3 ^ c * (n + 1)) * 2 ^ b) := by
        have := lt_of_lt_of_le e1 e2
        omega
      have e5 : 8 * (4 * (3 ^ c * (n + 1)) * 2 ^ b) ≤ 36 * (3 ^ c * 2 ^ b) * n := by
        have : 8 * (4 * (3 ^ c * (n + 1)) * 2 ^ b) = 4 * (3 ^ c * 2 ^ b) * (8 * (n + 1)) := by ring
        rw [this]
        calc 4 * (3 ^ c * 2 ^ b) * (8 * (n + 1)) ≤ 4 * (3 ^ c * 2 ^ b) * (9 * n) :=
              Nat.mul_le_mul_left _ e3
          _ = 36 * (3 ^ c * 2 ^ b) * n := by ring
      calc (2 ^ (d + 1) * 3 ^ a) * (12 * n) = 8 * (3 * 2 ^ d * (3 ^ a * n)) := by ring
        _ < 8 * (4 * (3 ^ c * (n + 1)) * 2 ^ b) := this
        _ ≤ 36 * (3 ^ c * 2 ^ b) * n := e5
        _ = (3 ^ (c + 1) * 2 ^ b) * (12 * n) := by ring
    exact Nat.lt_of_mul_lt_mul_right e4
  rcases le_total a c with hac | hca <;> rcases le_total b d with hbd | hdb
  · -- c = a + u, d = b + v
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hac
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hbd
    have q1 : 2 ^ (v + 1) < 3 ^ (u + 1) := by
      have : 2 ^ (v + 1) * (2 ^ b * 3 ^ a) < 3 ^ (u + 1) * (2 ^ b * 3 ^ a) := by
        calc 2 ^ (v + 1) * (2 ^ b * 3 ^ a) = 2 ^ (b + v + 1) * 3 ^ a := by ring
          _ < 3 ^ (a + u + 1) * 2 ^ b := P1
          _ = 3 ^ (u + 1) * (2 ^ b * 3 ^ a) := by ring
      exact Nat.lt_of_mul_lt_mul_right this
    have q2 : 3 ^ (u + 1) < 2 ^ (v + 2) := by
      have : 3 ^ (u + 1) * (2 ^ b * 3 ^ a) < 2 ^ (v + 2) * (2 ^ b * 3 ^ a) := by
        calc 3 ^ (u + 1) * (2 ^ b * 3 ^ a) = 3 ^ (a + u + 1) * 2 ^ b := by ring
          _ < 2 ^ (b + v + 2) * 3 ^ a := P2
          _ = 2 ^ (v + 2) * (2 ^ b * 3 ^ a) := by ring
      exact Nat.lt_of_mul_lt_mul_right this
    have hD : ((a + u : ℕ) : ℤ) + ((b + v : ℕ) : ℤ) - ((a : ℤ) + (b : ℤ)) = ((u + v : ℕ) : ℤ) := by
      push_cast; ring
    rw [hD]
    rcases case1 u v q1 q2 with h | ⟨x, y, h⟩
    · right; left; exact_mod_cast h
    · right; right; right
      exact ⟨x, y, by rw [Int.natAbs_natCast]; exact h⟩
  · -- c = a + u, b = d + v : forces u = 0, v = 0
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hac
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hdb
    have q2 : 3 ^ (u + 1) * 2 ^ v < 4 := by
      have : 3 ^ (u + 1) * 2 ^ v * (2 ^ d * 3 ^ a) < 4 * (2 ^ d * 3 ^ a) := by
        calc 3 ^ (u + 1) * 2 ^ v * (2 ^ d * 3 ^ a) = 3 ^ (a + u + 1) * 2 ^ (d + v) := by ring
          _ < 2 ^ (d + 2) * 3 ^ a := P2
          _ = 4 * (2 ^ d * 3 ^ a) := by ring
      exact Nat.lt_of_mul_lt_mul_right this
    have hu : u = 0 := by
      by_contra hu
      have : 3 ^ 2 ≤ 3 ^ (u + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 1 ≤ 2 ^ v := Nat.one_le_two_pow
      nlinarith
    have hv : v = 0 := by
      by_contra hv
      have : 2 ^ 1 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 3 ^ 1 ≤ 3 ^ (u + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    subst hu hv
    right; right; right
    exact ⟨0, 0, by push_cast; ring_nf; simp⟩
  · -- a = c + u, d = b + v : forces u = 0, v = 0
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hca
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hbd
    have q1 : 2 ^ (v + 1) * 3 ^ u < 3 := by
      have : 2 ^ (v + 1) * 3 ^ u * (2 ^ b * 3 ^ c) < 3 * (2 ^ b * 3 ^ c) := by
        calc 2 ^ (v + 1) * 3 ^ u * (2 ^ b * 3 ^ c) = 2 ^ (b + v + 1) * 3 ^ (c + u) := by ring
          _ < 3 ^ (c + 1) * 2 ^ b := P1
          _ = 3 * (2 ^ b * 3 ^ c) := by ring
      exact Nat.lt_of_mul_lt_mul_right this
    have hu : u = 0 := by
      by_contra hu
      have : 3 ^ 1 ≤ 3 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ 1 ≤ 2 ^ (v + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    have hv : v = 0 := by
      by_contra hv
      have : 2 ^ 2 ≤ 2 ^ (v + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 1 ≤ 3 ^ u := Nat.one_le_pow _ _ (by norm_num)
      nlinarith
    subst hu hv
    right; right; right
    exact ⟨0, 0, by push_cast; ring_nf; simp⟩
  · -- a = c + u, b = d + v
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hca
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hdb
    have q1 : 2 * 3 ^ u < 3 * 2 ^ v := by
      have : 2 * 3 ^ u * (2 ^ d * 3 ^ c) < 3 * 2 ^ v * (2 ^ d * 3 ^ c) := by
        calc 2 * 3 ^ u * (2 ^ d * 3 ^ c) = 2 ^ (d + 1) * 3 ^ (c + u) := by ring
          _ < 3 ^ (c + 1) * 2 ^ (d + v) := P1
          _ = 3 * 2 ^ v * (2 ^ d * 3 ^ c) := by ring
      exact Nat.lt_of_mul_lt_mul_right this
    have q2 : 3 * 2 ^ v < 4 * 3 ^ u := by
      have : 3 * 2 ^ v * (2 ^ d * 3 ^ c) < 4 * 3 ^ u * (2 ^ d * 3 ^ c) := by
        calc 3 * 2 ^ v * (2 ^ d * 3 ^ c) = 3 ^ (c + 1) * 2 ^ (d + v) := by ring
          _ < 2 ^ (d + 2) * 3 ^ (c + u) := P2
          _ = 4 * 3 ^ u * (2 ^ d * 3 ^ c) := by ring
      exact Nat.lt_of_mul_lt_mul_right this
    obtain ⟨x, y, h⟩ := case4 u v q1 q2
    right; right; right
    refine ⟨x, y, ?_⟩
    have hD : (c : ℤ) + (d : ℤ) - (((c + u : ℕ) : ℤ) + ((d + v : ℕ) : ℤ)) = -((u + v : ℕ) : ℤ) := by
      push_cast; ring
    rw [hD, Int.natAbs_neg, Int.natAbs_natCast]
    exact h

end P8A153330

theorem OMA.solution : OMA.R_OeisA153330_conjecture3_R1.H1 :=
  P8A153330.a153330_h1
