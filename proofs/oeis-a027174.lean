import OMAStatements.S_oeis_a027174
import Mathlib

namespace OMA.S_oeis_a027174

lemma ch (n k m : ℕ) (h : n = k + m) : (n.choose k : ℚ) = (n.factorial : ℚ) / ((k.factorial : ℚ) * (m.factorial : ℚ)) := by
  subst h
  rw [Nat.cast_choose ℚ (by omega), Nat.add_sub_cancel_left]

noncomputable def R (n : ℕ) : ℚ := 4 * (2 * n + 1) * (2 * n + 3) * (9 * n ^ 2 + 50 * n + 65) / ((n + 1) * (n + 3) * (n + 4) * (n + 5))

lemma cform (n : ℕ) : (a n : ℚ) + 4 = ((2 * n).choose n : ℚ) * R n := by
  unfold R
  unfold a
  push_cast
  rw [ch (2 * n + 6) (n + 1) (n + 5) (by omega), ch (2 * n + 5) n (n + 5) (by omega),
    ch (2 * n + 5) (n + 1) (n + 4) (by omega), ch (2 * n + 4) n (n + 4) (by omega),
    ch (2 * n) n n (by omega)]
  simp only [Nat.factorial_succ]
  push_cast
  have h1 : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

lemma cstep (n : ℕ) : ((2 * (n + 1)).choose (n + 1) : ℚ) * (n + 1) = ((2 * n).choose n : ℚ) * (2 * (2 * n + 1)) := by
  have := Nat.succ_mul_centralBinom_succ n
  simp only [Nat.centralBinom] at this
  have h : (((n + 1) * (2 * (n + 1)).choose (n + 1) : ℕ) : ℚ) = ((2 * (2 * n + 1) * (2 * n).choose n : ℕ) : ℚ) := by rw [this]
  push_cast at h
  linarith

end OMA.S_oeis_a027174

set_option maxRecDepth 100000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a027174.main := by
  intro n
  open OMA.S_oeis_a027174 in
  have h0 := cform n
  have h1 := cform (n + 1)
  have h2 := cform (n + 2)
  have s1 := cstep n
  have s2 := cstep (n + 1)
  have key : (-2 * (((n : ℚ) + 4) + 3) * (139 * ((n : ℚ) + 4) - 175) * (a (n + 2) : ℚ) +
      (1279 * ((n : ℚ) + 4) ^ 2 + 1334 * ((n : ℚ) + 4) - 1089) * (a (n + 1) : ℚ) -
      2 * (167 * ((n : ℚ) + 4) + 121) * (2 * ((n : ℚ) + 4) - 3) * (a n : ℚ) +
      12 * (111 * ((n : ℚ) + 4) ^ 2 + 456 * ((n : ℚ) + 4) + 229)) = 0 := by
    set c0 : ℚ := ((2 * n).choose n : ℚ)
    set c1 : ℚ := ((2 * (n + 1)).choose (n + 1) : ℚ)
    set c2 : ℚ := ((2 * (n + 2)).choose (n + 2) : ℚ)
    have e1 : c1 = c0 * (2 * (2 * n + 1)) / (n + 1) := by field_simp; linarith
    have s2' : c2 * ((n:ℚ) + 2) = c1 * (2 * (2 * (n:ℚ) + 3)) := by
      have := s2; push_cast at this ⊢; linarith
    have e2 : c2 = c1 * (2 * (2 * (n:ℚ) + 3)) / (n + 2) := by field_simp; linarith
    have ha0 : (a n : ℚ) = c0 * R n - 4 := by have := h0; linarith
    have ha1 : (a (n+1) : ℚ) = c1 * R (n+1) - 4 := by
      have := h1; push_cast at this; linarith
    have ha2 : (a (n+2) : ℚ) = c2 * R (n+2) - 4 := by
      have := h2; push_cast at this; linarith
    rw [ha0, ha1, ha2, e2, e1]
    simp only [R]
    push_cast
    have : (n:ℚ) + 1 ≠ 0 := by positivity
    have : (n:ℚ) + 2 ≠ 0 := by positivity
    have : (n:ℚ) + 3 ≠ 0 := by positivity
    have : (n:ℚ) + 4 ≠ 0 := by positivity
    have : (n:ℚ) + 5 ≠ 0 := by positivity
    have : (n:ℚ) + 6 ≠ 0 := by positivity
    have : (n:ℚ) + 7 ≠ 0 := by positivity
    field_simp
    ring
  dsimp only
  exact_mod_cast key
