import OMAStatements.S_oeis_a235088
import Mathlib

open OMA.S_oeis_a235088 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a235088.main := by
  have D (n : ℕ) : (d n : ℤ) = 4*n + 1 + 2*(-1)^n := by
    induction n with
    | zero => simp [d]
    | succ n ih =>
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n <;>
      simp [d, pow_succ, pow_mul, show ∀ c, (2*k+c)%2 = c%2 by omega, add_assoc] at ih ⊢ <;>
      linarith
  have Q (n : ℕ) : (a n : ℤ) = 1 - (-1)^n - n + 2*n^2 := by
    induction n with
    | zero => simp [a]
    | succ n ih =>
      rcases n with _ | n
      · simp [a]
      · simp [a, D, pow_succ] at ih ⊢
        linarith
  have E (k : ℕ) : (a (2*k) : ℤ) = 8*k^2 - 2*k := by
    rw [Q]
    simp [pow_mul]
    ring
  have O (k : ℕ) : (a (2*k+1) : ℤ) = 8*k^2 + 6*k + 3 := by
    rw [Q]
    simp [pow_mul, pow_succ]
    ring
  have fl (q : ℚ) (x : ℤ) (h1 : (x:ℚ) ≤ q) (h2 : q < x+1) : ⌊q⌋ = x := Int.floor_eq_iff.2 ⟨h1, h2⟩
  have cl (q : ℚ) (x : ℤ) (h1 : (x:ℚ)-1 < q) (h2 : q ≤ x) : ⌈q⌉ = x := Int.ceil_eq_iff.2 ⟨h1, h2⟩
  refine ⟨fun n _ => ?_, fun n _ => Q n, fun n hn => ?_, ?_, fun n _ => ?_⟩
  · obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [E, fl ((((2*k:ℕ):ℚ)-1)^2/4) (k^2-k) (by push_cast; linarith) (by push_cast; linarith),
        cl (((2*k:ℕ):ℚ)^2/2) (2*k^2) (by push_cast; linarith) (by push_cast; linarith)]
      ring
    · rw [O, fl ((((2*k+1:ℕ):ℚ)-1)^2/4) (k^2) (by push_cast; linarith) (by push_cast; linarith),
        cl (((2*k+1:ℕ):ℚ)^2/2) (2*k^2+2*k+1) (by push_cast; linarith) (by push_cast; linarith)]
      ring
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [Q, pow_succ]
    ring
  · have Q' (n : ℕ) : (a n : ℚ) = 1 - (-1)^n - n + 2*n^2 := mod_cast Q n
    simp only [← map_ofNat (C (R := ℚ))]
    ext n
    rcases n with _ | _ | _ | _ | n <;>
    simp [pow_succ, mul_sub, sub_mul, mul_add, add_mul, ← mul_assoc, Q', coeff_X, coeff_one] <;> ring
  · obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [E, fl (((2*k:ℕ):ℚ)/2) k (by push_cast; linarith) (by push_cast; linarith)]
      push_cast
      ring
    · rw [O, fl (((2*k+1:ℕ):ℚ)/2) k (by push_cast; linarith) (by push_cast; linarith)]
      push_cast
      ring
