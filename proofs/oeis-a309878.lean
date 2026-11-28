import OMAStatements.S_oeis_a309878
import Mathlib

open OMA.S_oeis_a309878 Complex in
theorem OMA.solution : type_of% @OMA.S_oeis_a309878.main := by
  have h (n : ℕ) : b n = -2*I*(1+I)^n + (I-1)*n + 2*I := by
    induction n with
    | zero => simp [b]
    | succ n ih =>
      rw [b, ih, pow_succ]
      push_cast
      linear_combination ((n:ℂ)+2) * I_sq
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [a, h, pow_succ]
    ring
  · intro n
    have c : (1 - I)^n = starRingEnd ℂ ((1+I)^n) := by simp [sub_eq_add_neg]
    have c1 := congrArg re c
    have c2 := congrArg im c
    rw [conj_re] at c1
    rw [conj_im] at c2
    rw [a, h]
    apply Complex.ext <;> simp <;> linarith
