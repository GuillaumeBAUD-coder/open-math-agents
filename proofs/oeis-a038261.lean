import OMAStatements.S_oeis_a038261
import Mathlib

def OMA.u : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 1, 1, 1, 1)
  | j+1 => ((u j).2.2.2.2, (u j).2.2.2.2 + (u j).2.2.2.1,
      (u j).2.2.2.2 + (u j).2.2.2.1 + (u j).2.2.1,
      (u j).2.2.2.2 + (u j).2.2.2.1 + (u j).2.2.1 + (u j).2.1,
      (u j).2.2.2.2 + (u j).2.2.2.1 + (u j).2.2.1 + (u j).2.1 + (u j).1)

open OMA OMA.S_oeis_a038261 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a038261.main := by
  have s (m : ℕ) : w (4*m+5) = w (4*m+4) + w (4*m+3) ∧ w (4*m+6) = w (4*m+5) + w (4*m+2) ∧
      w (4*m+7) = w (4*m+6) + w (4*m+1) ∧ w (4*m+8) = w (4*m+7) + w (4*m) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [w] <;> split_ifs <;> first | rfl | omega
  have K (j : ℕ) : w (4*j) = (u j).1 ∧ w (4*j+1) = (u j).2.1 ∧ w (4*j+2) = (u j).2.2.1 ∧
      w (4*j+3) = (u j).2.2.2.1 ∧ w (4*j+4) = (u j).2.2.2.2 := by
    induction j with
    | zero => refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [w] <;> simp [u]
    | succ j ih =>
      have := s j
      simp only [u, mul_add, mul_one, add_assoc, Nat.reduceAdd] at *
      omega
  have A (n : ℕ) : a n = (u (2*n)).1 := by
    rw [a, show 8*n = 4*(2*n) by ring]
    exact (K _).1
  have f (j : ℕ) : (u (j+1)).1 = (u j).2.2.2.2 ∧ (u (j+1)).2.1 = (u j).2.2.2.2 + (u j).2.2.2.1 ∧
      (u (j+1)).2.2.1 = (u j).2.2.2.2 + (u j).2.2.2.1 + (u j).2.2.1 ∧
      (u (j+1)).2.2.2.1 = (u j).2.2.2.2 + (u j).2.2.2.1 + (u j).2.2.1 + (u j).2.1 ∧
      (u (j+1)).2.2.2.2 = (u j).2.2.2.2 + (u j).2.2.2.1 + (u j).2.2.1 + (u j).2.1 + (u j).1 :=
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  have V (m : ℕ) : ((u (m+10)).1 : ℤ) = 15*(u (m+8)).1 - 35*(u (m+6)).1 + 28*(u (m+4)).1 - 9*(u (m+2)).1 + (u m).1 ∧
      ((u (m+10)).2.1 : ℤ) = 15*(u (m+8)).2.1 - 35*(u (m+6)).2.1 + 28*(u (m+4)).2.1 - 9*(u (m+2)).2.1 + (u m).2.1 ∧
      ((u (m+10)).2.2.1 : ℤ) = 15*(u (m+8)).2.2.1 - 35*(u (m+6)).2.2.1 + 28*(u (m+4)).2.2.1 - 9*(u (m+2)).2.2.1 + (u m).2.2.1 ∧
      ((u (m+10)).2.2.2.1 : ℤ) = 15*(u (m+8)).2.2.2.1 - 35*(u (m+6)).2.2.2.1 + 28*(u (m+4)).2.2.2.1 - 9*(u (m+2)).2.2.2.1 + (u m).2.2.2.1 ∧
      ((u (m+10)).2.2.2.2 : ℤ) = 15*(u (m+8)).2.2.2.2 - 35*(u (m+6)).2.2.2.2 + 28*(u (m+4)).2.2.2.2 - 9*(u (m+2)).2.2.2.2 + (u m).2.2.2.2 := by
    induction m with
    | zero => simp [u]
    | succ m ih =>
      have f0 := f m
      have f2 := f (m+2)
      have f4 := f (m+4)
      have f6 := f (m+6)
      have f8 := f (m+8)
      have f10 := f (m+10)
      simp only [add_assoc, Nat.reduceAdd] at f0 f2 f4 f6 f8 f10 ⊢
      omega
  have h (n : ℕ) : (a (n+5) : ℤ) = 15*a (n+4) - 35*a (n+3) + 28*a (n+2) - 9*a (n+1) + a n := by
    simp only [A, mul_add, Nat.reduceMul]
    exact (V (2*n)).1
  ext (_ | _ | _ | _ | _ | n) <;>
  simp [pow_succ, mul_sub, mul_add, sub_mul, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_mul_C,
    ← map_ofNat (C : ℤ →+* _), -eq_intCast] <;>
  first | linarith [h n] | simp [A, u]
