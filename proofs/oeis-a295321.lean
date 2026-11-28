import OMAStatements.S_oeis_a295321

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: closed forms of 3a(n) as cubics in q for n = 4q+r (induction two terms at a time), giving
-- a(m+12) - 3a(m+8) + 3a(m+4) - a(m) = 16; the recurrence is the difference of two such identities.

open OMA.S_oeis_a295321

namespace P_oeis_a295321

def t (n i : ℕ) : ℕ := i * (n - i) * ((n - i + 1) % 2)

lemma icc_range (n M : ℕ) :
    ∑ i ∈ Finset.Icc 1 M, t n i = ∑ i ∈ Finset.range M, t n (i + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma a_eq (n : ℕ) : a n = ∑ i ∈ Finset.range ((n - 1) / 2), t n (i + 1) := by
  rw [← icc_range]; rfl

lemma even_sum (u p : ℕ) (hp : p ≤ u) :
    3 * ((∑ i ∈ Finset.range (2 * p), t (2 * u) (i + 1) : ℕ) : ℤ) =
      3 * p * 2 * (2 * u - 2) + 3 * (2 * u - 4) * p * (p - 1) - 2 * (p - 1) * p * (2 * p - 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have e : 2 * (p + 1) = 2 * p + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Nat.cast_add, Nat.cast_add, mul_add, mul_add, ih (by omega)]
    have h1 : (2 * u - (2 * p + 1) + 1) % 2 = 0 := by omega
    have h2 : (2 * u - (2 * p + 1 + 1) + 1) % 2 = 1 := by omega
    have h3 : ((2 * u - (2 * p + 1 + 1) : ℕ) : ℤ) = 2 * u - 2 * p - 2 := by omega
    simp only [t, h1, h2, mul_zero, mul_one, Nat.cast_zero, Nat.cast_mul, h3]
    push_cast
    ring

lemma odd_sum (u p : ℕ) (hp : p ≤ u) :
    3 * ((∑ i ∈ Finset.range (2 * p), t (2 * u + 1) (i + 1) : ℕ) : ℤ) =
      3 * p * (2 * u) + 3 * (2 * u - 1) * p * (p - 1) - 2 * (p - 1) * p * (2 * p - 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have e : 2 * (p + 1) = 2 * p + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Nat.cast_add, Nat.cast_add, mul_add, mul_add, ih (by omega)]
    have h1 : (2 * u + 1 - (2 * p + 1) + 1) % 2 = 1 := by omega
    have h2 : (2 * u + 1 - (2 * p + 1 + 1) + 1) % 2 = 0 := by omega
    have h3 : ((2 * u + 1 - (2 * p + 1) : ℕ) : ℤ) = 2 * u - 2 * p := by omega
    simp only [t, h1, h2, mul_zero, mul_one, Nat.cast_zero, Nat.cast_mul, h3]
    push_cast
    ring

lemma c1 (q : ℕ) : 3 * (a (4 * q + 1) : ℤ) =
    3 * q * 4 * q + 3 * (4 * q - 1) * q * (q - 1) - 2 * (q - 1) * q * (2 * q - 1) := by
  have hm : (4 * q + 1 - 1) / 2 = 2 * q := by omega
  have hn : 4 * q + 1 = 2 * (2 * q) + 1 := by ring
  rw [a_eq, hm, hn, odd_sum (2 * q) q (by omega)]
  push_cast; ring

lemma c2 (q : ℕ) : 3 * (a (4 * q + 2) : ℤ) =
    6 * q * 4 * q + 3 * (4 * q - 2) * q * (q - 1) - 2 * (q - 1) * q * (2 * q - 1) := by
  have hm : (4 * q + 2 - 1) / 2 = 2 * q := by omega
  have hn : 4 * q + 2 = 2 * (2 * q + 1) := by ring
  rw [a_eq, hm, hn, even_sum (2 * q + 1) q (by omega)]
  push_cast; ring

lemma c3 (q : ℕ) : 3 * (a (4 * q + 3) : ℤ) =
    3 * q * (4 * q + 2) + 3 * (4 * q + 1) * q * (q - 1) - 2 * (q - 1) * q * (2 * q - 1)
      + 3 * (2 * q + 1) * (2 * q + 2) := by
  have hm : (4 * q + 3 - 1) / 2 = 2 * q + 1 := by omega
  have hn : 4 * q + 3 = 2 * (2 * q + 1) + 1 := by ring
  rw [a_eq, hm, hn, Finset.sum_range_succ]
  rw [Nat.cast_add, mul_add, odd_sum (2 * q + 1) q (by omega)]
  have h1 : (2 * (2 * q + 1) + 1 - (2 * q + 1) + 1) % 2 = 1 := by omega
  have h3 : ((2 * (2 * q + 1) + 1 - (2 * q + 1) : ℕ) : ℤ) = 2 * q + 2 := by omega
  simp only [t, h1, mul_one, Nat.cast_mul, h3]
  push_cast; ring

lemma c4 (q : ℕ) : 3 * (a (4 * q + 4) : ℤ) =
    6 * q * (4 * q + 2) + 3 * 4 * q * q * (q - 1) - 2 * (q - 1) * q * (2 * q - 1) := by
  have hm : (4 * q + 4 - 1) / 2 = 2 * q + 1 := by omega
  have hn : 4 * q + 4 = 2 * (2 * q + 2) := by ring
  rw [a_eq, hm, hn, Finset.sum_range_succ]
  rw [Nat.cast_add, mul_add, even_sum (2 * q + 2) q (by omega)]
  have h1 : (2 * (2 * q + 2) - (2 * q + 1) + 1) % 2 = 0 := by omega
  simp only [t, h1, mul_zero, Nat.cast_zero]
  push_cast; ring

lemma diff16 (m : ℕ) (hm : 1 ≤ m) :
    (a (m + 12) : ℤ) - 3 * a (m + 8) + 3 * a (m + 4) - a m = 16 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ m = 4 * q + r + 1 :=
    ⟨(m - 1) / 4, (m - 1) % 4, by omega, by omega⟩
  interval_cases r
  · have e0 := c1 q; have e1 := c1 (q + 1); have e2 := c1 (q + 2); have e3 := c1 (q + 3)
    push_cast at e0 e1 e2 e3
    rw [show 4 * (q + 1) + 1 = 4 * q + 0 + 1 + 4 by ring] at e1
    rw [show 4 * (q + 2) + 1 = 4 * q + 0 + 1 + 8 by ring] at e2
    rw [show 4 * (q + 3) + 1 = 4 * q + 0 + 1 + 12 by ring] at e3
    rw [show 4 * q + 1 = 4 * q + 0 + 1 by ring] at e0
    linarith
  · have e0 := c2 q; have e1 := c2 (q + 1); have e2 := c2 (q + 2); have e3 := c2 (q + 3)
    push_cast at e0 e1 e2 e3
    rw [show 4 * (q + 1) + 2 = 4 * q + 1 + 1 + 4 by ring] at e1
    rw [show 4 * (q + 2) + 2 = 4 * q + 1 + 1 + 8 by ring] at e2
    rw [show 4 * (q + 3) + 2 = 4 * q + 1 + 1 + 12 by ring] at e3
    rw [show 4 * q + 2 = 4 * q + 1 + 1 by ring] at e0
    linarith
  · have e0 := c3 q; have e1 := c3 (q + 1); have e2 := c3 (q + 2); have e3 := c3 (q + 3)
    push_cast at e0 e1 e2 e3
    rw [show 4 * (q + 1) + 3 = 4 * q + 2 + 1 + 4 by ring] at e1
    rw [show 4 * (q + 2) + 3 = 4 * q + 2 + 1 + 8 by ring] at e2
    rw [show 4 * (q + 3) + 3 = 4 * q + 2 + 1 + 12 by ring] at e3
    rw [show 4 * q + 3 = 4 * q + 2 + 1 by ring] at e0
    linarith
  · have e0 := c4 q; have e1 := c4 (q + 1); have e2 := c4 (q + 2); have e3 := c4 (q + 3)
    push_cast at e0 e1 e2 e3
    rw [show 4 * (q + 1) + 4 = 4 * q + 3 + 1 + 4 by ring] at e1
    rw [show 4 * (q + 2) + 4 = 4 * q + 3 + 1 + 8 by ring] at e2
    rw [show 4 * (q + 3) + 4 = 4 * q + 3 + 1 + 12 by ring] at e3
    rw [show 4 * q + 4 = 4 * q + 3 + 1 by ring] at e0
    linarith

theorem main_proved : ∀ n : ℕ, 13 < n →
    (a n : ℤ) = a (n - 1) + 3 * a (n - 4) - 3 * a (n - 5) - 3 * a (n - 8) + 3 * a (n - 9) +
      a (n - 12) - a (n - 13) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 14 := ⟨n - 14, by omega⟩
  have d1 := diff16 (m + 1) (by omega)
  have d2 := diff16 (m + 2) (by omega)
  have e1 : m + 14 - 1 = m + 1 + 12 := by omega
  have e4 : m + 14 - 4 = m + 2 + 8 := by omega
  have e5 : m + 14 - 5 = m + 1 + 8 := by omega
  have e8 : m + 14 - 8 = m + 2 + 4 := by omega
  have e9 : m + 14 - 9 = m + 1 + 4 := by omega
  have e12 : m + 14 - 12 = m + 2 := by omega
  have e13 : m + 14 - 13 = m + 1 := by omega
  have e0 : m + 14 = m + 2 + 12 := by omega
  rw [e1, e4, e5, e8, e9, e12, e13, e0]
  linarith

end P_oeis_a295321

theorem OMA.solution : type_of% @OMA.S_oeis_a295321.main := P_oeis_a295321.main_proved
