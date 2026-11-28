import OMAStatements.S_oeis_a173693
import Mathlib

/-!
# A173693: the order 36 recurrence for a(n) = ceiling(A107293(n)/2)

Write b for A107293. The matrix definition gives b(n+5) = b(n+4) + b(n+3) - b(n+2) + b(n) with
b(0..4) = 0, 0, 0, 0, 1. The difference b(n+31) - b(n) satisfies the same recurrence and its
first five values are even, so the parity of b has period 31. For every integer z,
2 * ceiling(z/2) = z + (z mod 2), hence 2 a(n) = b(n) + (b(n) mod 2). The characteristic
polynomial of the claimed recurrence is (x^5 - x^4 - x^3 + x^2 - 1)(x^31 - 1): the sequence b
satisfies it because of the first factor, and the parity of b because of the second. Adding the
two and halving gives the recurrence for a.
-/

namespace OMA.P173693

open OMA.S_oeis_a173693

/-- The vector M^n v with v = (0, 0, 0, 0, 1). -/
def w (n : ℕ) : Fin 5 → ℤ := (M ^ n).mulVec ![0, 0, 0, 0, 1]

lemma w_succ (n : ℕ) : w (n + 1) = M.mulVec (w n) := by
  unfold w; rw [pow_succ', ← Matrix.mulVec_mulVec]

lemma M_apply (u : Fin 5 → ℤ) :
    M.mulVec u = ![u 1, u 2, u 3, u 4, u 0 - u 2 + u 3 + u 4] := by
  ext i
  fin_cases i <;> simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  ring

lemma b_def (n : ℕ) : b n = w n 0 := rfl

lemma sh0 (n : ℕ) : w (n + 1) 0 = w n 1 := by rw [w_succ, M_apply]; rfl
lemma sh1 (n : ℕ) : w (n + 1) 1 = w n 2 := by rw [w_succ, M_apply]; rfl
lemma sh2 (n : ℕ) : w (n + 1) 2 = w n 3 := by rw [w_succ, M_apply]; rfl
lemma sh3 (n : ℕ) : w (n + 1) 3 = w n 4 := by rw [w_succ, M_apply]; rfl
lemma sh4 (n : ℕ) : w (n + 1) 4 = w n 0 - w n 2 + w n 3 + w n 4 := by
  rw [w_succ, M_apply]; rfl

/-- The recurrence of A107293. -/
lemma b_rec (n : ℕ) : b (n + 5) = b (n + 4) + b (n + 3) - b (n + 2) + b n := by
  have e5 : b (n + 5) = w n 0 - w n 2 + w n 3 + w n 4 := by
    rw [b_def, show n + 5 = (n + 4) + 1 from rfl, sh0, show n + 4 = (n + 3) + 1 from rfl, sh1,
      show n + 3 = (n + 2) + 1 from rfl, sh2, show n + 2 = (n + 1) + 1 from rfl, sh3, sh4]
  have e4 : b (n + 4) = w n 4 := by
    rw [b_def, show n + 4 = (n + 3) + 1 from rfl, sh0, show n + 3 = (n + 2) + 1 from rfl, sh1,
      show n + 2 = (n + 1) + 1 from rfl, sh2, sh3]
  have e3 : b (n + 3) = w n 3 := by
    rw [b_def, show n + 3 = (n + 2) + 1 from rfl, sh0, show n + 2 = (n + 1) + 1 from rfl, sh1, sh2]
  have e2 : b (n + 2) = w n 2 := by
    rw [b_def, show n + 2 = (n + 1) + 1 from rfl, sh0, sh1]
  rw [e5, e4, e3, e2, b_def]; ring

lemma w0 : w 0 = ![0, 0, 0, 0, 1] := by simp [w]

/-- The first five terms of A107293. -/
lemma b_init : b 0 = 0 ∧ b 1 = 0 ∧ b 2 = 0 ∧ b 3 = 0 ∧ b 4 = 1 := by
  have h1 : w 1 = ![0, 0, 0, 1, 1] := by rw [w_succ, w0, M_apply]; simp
  have h2 : w 2 = ![0, 0, 1, 1, 2] := by rw [w_succ, h1, M_apply]; simp
  have h3 : w 3 = ![0, 1, 1, 2, 2] := by rw [w_succ, h2, M_apply]; simp
  have h4 : w 4 = ![1, 1, 2, 2, 3] := by rw [w_succ, h3, M_apply]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [b_def, w0]; rfl
  · rw [b_def, h1]; rfl
  · rw [b_def, h2]; rfl
  · rw [b_def, h3]; rfl
  · rw [b_def, h4]; rfl

/-- Five consecutive terms of the recurrence, computed by iteration. -/
def fb : ℕ → ℤ × ℤ × ℤ × ℤ × ℤ
  | 0 => (0, 0, 0, 0, 1)
  | n + 1 => ((fb n).2.1, (fb n).2.2.1, (fb n).2.2.2.1, (fb n).2.2.2.2,
      (fb n).2.2.2.2 + (fb n).2.2.2.1 - (fb n).2.2.1 + (fb n).1)

lemma fb_eq (n : ℕ) :
    fb n = (b n, b (n + 1), b (n + 2), b (n + 3), b (n + 4)) := by
  induction n with
  | zero => obtain ⟨h0, h1, h2, h3, h4⟩ := b_init; simp [fb, h0, h1, h2, h3, h4]
  | succ k ih => simp only [fb, ih]; rw [b_rec k]

lemma fb31 : fb 31 = (13802, 19920, 28750, 41494, 59887) := by decide +kernel

/-- The terms b(31), ..., b(35). -/
lemma b_31 : b 31 = 13802 ∧ b 32 = 19920 ∧ b 33 = 28750 ∧ b 34 = 41494 ∧ b 35 = 59887 := by
  have h := fb_eq 31
  rw [fb31] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨h0.symm, h1.symm, h2.symm, h3.symm, h4.symm⟩

/-- The parity of A107293 has period 31. -/
lemma par_aux (n : ℕ) :
    b (n + 31) % 2 = b n % 2 ∧ b (n + 32) % 2 = b (n + 1) % 2 ∧ b (n + 33) % 2 = b (n + 2) % 2 ∧
      b (n + 34) % 2 = b (n + 3) % 2 ∧ b (n + 35) % 2 = b (n + 4) % 2 := by
  induction n with
  | zero =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := b_init
    obtain ⟨g0, g1, g2, g3, g4⟩ := b_31
    simp only [Nat.zero_add]
    rw [h0, h1, h2, h3, h4, g0, g1, g2, g3, g4]
    decide
  | succ k ih =>
    obtain ⟨i0, i1, i2, i3, i4⟩ := ih
    have r1 := b_rec k
    have r2 := b_rec (k + 31)
    refine ⟨i1, i2, i3, i4, ?_⟩
    have e1 : k + 1 + 35 = k + 31 + 5 := by ring
    have e2 : k + 1 + 4 = k + 5 := by ring
    rw [e1, e2, r1, r2]
    have e3 : k + 31 + 4 = k + 35 := by ring
    have e4 : k + 31 + 3 = k + 34 := by ring
    have e5 : k + 31 + 2 = k + 33 := by ring
    rw [e3, e4, e5]
    omega

lemma par (n : ℕ) : b (n + 31) % 2 = b n % 2 := (par_aux n).1

/-- Twice the ceiling of z/2 is z plus the parity of z. -/
lemma two_ceil (z : ℤ) : 2 * ⌈(z : ℚ) / 2⌉ = z + z % 2 := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' z
  · have h : ⌈(z : ℚ) / 2⌉ = k := by
      rw [hk]; push_cast
      rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℚ) ≠ 0)]
      exact Int.ceil_intCast k
    rw [h]; omega
  · have h : ⌈(z : ℚ) / 2⌉ = k + 1 := by
      rw [Int.ceil_eq_iff, hk]; push_cast
      constructor <;> linarith
    rw [h]; omega

lemma two_a (n : ℕ) : 2 * a n = b n + b n % 2 := two_ceil (b n)

end OMA.P173693

open OMA.S_oeis_a173693 OMA.P173693 in
theorem OMA.solution : type_of% @OMA.S_oeis_a173693.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have s1 : m + 36 - 1 = m + 35 := by omega
  have s2 : m + 36 - 2 = m + 34 := by omega
  have s3 : m + 36 - 3 = m + 33 := by omega
  have s5 : m + 36 - 5 = m + 31 := by omega
  have s31 : m + 36 - 31 = m + 5 := by omega
  have s32 : m + 36 - 32 = m + 4 := by omega
  have s33 : m + 36 - 33 = m + 3 := by omega
  have s34 : m + 36 - 34 = m + 2 := by omega
  have s36 : m + 36 - 36 = m := by omega
  rw [s1, s2, s3, s5, s31, s32, s33, s34, s36]
  have r1 := b_rec m
  have r2 := b_rec (m + 31)
  have p0 := par m
  have p2 := par (m + 2)
  have p3 := par (m + 3)
  have p4 := par (m + 4)
  have p5 := par (m + 5)
  have e36 : m + 31 + 5 = m + 36 := by ring
  have e35 : m + 31 + 4 = m + 35 := by ring
  have e34 : m + 31 + 3 = m + 34 := by ring
  have e33 : m + 31 + 2 = m + 33 := by ring
  have f36 : m + 5 + 31 = m + 36 := by ring
  have f35 : m + 4 + 31 = m + 35 := by ring
  have f34 : m + 3 + 31 = m + 34 := by ring
  have f33 : m + 2 + 31 = m + 33 := by ring
  rw [e36, e35, e34, e33] at r2
  rw [f36] at p5
  rw [f35] at p4
  rw [f34] at p3
  rw [f33] at p2
  have t36 := two_a (m + 36)
  have t35 := two_a (m + 35)
  have t34 := two_a (m + 34)
  have t33 := two_a (m + 33)
  have t31 := two_a (m + 31)
  have t5 := two_a (m + 5)
  have t4 := two_a (m + 4)
  have t3 := two_a (m + 3)
  have t2 := two_a (m + 2)
  have t0 := two_a m
  linarith
