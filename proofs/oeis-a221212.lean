import OMAStatements.S_oeis_a221212
import Mathlib

namespace OMA.A221212Proof

open OMA.S_oeis_a221212

lemma phi_bounds : (1.618:ℝ) < Real.goldenRatio ∧ Real.goldenRatio < 1.6181 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold Real.goldenRatio
  constructor <;> nlinarith

lemma x3 : x 3 = Real.goldenRatio + 2 := rfl
lemma x2 : x 2 = Real.goldenRatio + 1 := rfl

lemma x4 : x 4 = 3 * Real.goldenRatio + 2 := by
  show (if (0+4) % 2 = 0 then (Nat.fib (0+4) : ℝ) * Real.goldenRatio + Nat.fib (0+3) else x (0+3) + x (0+1)) = _
  norm_num [Nat.fib_add_two]

lemma x5 : x 5 = 4 * Real.goldenRatio + 3 := by
  show (if (1+4) % 2 = 0 then (Nat.fib (1+4) : ℝ) * Real.goldenRatio + Nat.fib (1+3) else x (1+3) + x (1+1)) = _
  rw [if_neg (by norm_num)]
  rw [show 1 + 3 = 4 from rfl, x4, show 1 + 1 = 2 from rfl, x2]; ring

lemma x6 : x 6 = 8 * Real.goldenRatio + 5 := by
  show (if (2+4) % 2 = 0 then (Nat.fib (2+4) : ℝ) * Real.goldenRatio + Nat.fib (2+3) else x (2+3) + x (2+1)) = _
  rw [if_pos (by norm_num)]
  norm_num [Nat.fib_add_two]

lemma x7 : x 7 = 11 * Real.goldenRatio + 7 := by
  show (if (3+4) % 2 = 0 then (Nat.fib (3+4) : ℝ) * Real.goldenRatio + Nat.fib (3+3) else x (3+3) + x (3+1)) = _
  rw [if_neg (by norm_num)]
  rw [show 3 + 3 = 6 from rfl, x6, show 3 + 1 = 4 from rfl, x4]; ring

lemma round_eq_of (y : ℝ) (k : ℤ) (h1 : (k:ℝ) - 1/2 ≤ y) (h2 : y < k + 1/2) : round y = k := by
  rw [round_eq, Int.floor_eq_iff]; constructor <;> push_cast <;> linarith

lemma a3 : a 3 = 4 := by
  obtain ⟨h1, h2⟩ := phi_bounds
  unfold a; rw [x3]; apply round_eq_of <;> push_cast <;> linarith

lemma a5 : a 5 = 9 := by
  obtain ⟨h1, h2⟩ := phi_bounds
  unfold a; rw [x5]; apply round_eq_of <;> push_cast <;> linarith

lemma a7 : a 7 = 25 := by
  obtain ⟨h1, h2⟩ := phi_bounds
  unfold a; rw [x7]; apply round_eq_of <;> push_cast <;> linarith

end OMA.A221212Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a221212.main) := by
  intro h
  have := h.1 7 (by norm_num)
  norm_num at this
  rw [OMA.A221212Proof.a7, OMA.A221212Proof.a5, OMA.A221212Proof.a3] at this
  norm_num at this

