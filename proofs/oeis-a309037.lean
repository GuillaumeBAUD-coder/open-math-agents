import OMAStatements.S_oeis_a309037
import Mathlib

open OMA.S_oeis_a309037 PowerSeries Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a309037.main := by
  have s (n : ℕ) : (∑ k ∈ range n, 2^(k+1)*10^k : ℚ) = 2*(2^n*10^n-1)/19 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      ring
  have t (m : ℕ) : (∑ k ∈ range m, 2^(k+1)*10^(2*m-k) : ℚ) = 5*(10^m*10^m-2^m*10^m)/2 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, sum_congr (rfl : range m = _) fun k hk =>
        show (2:ℚ)^(k+1)*10^(2*(m+1)-k) = 100*(2^(k+1)*10^(2*m-k)) by
          rw [show 2*(m+1)-k = 2*m-k+2 by have := mem_range.1 hk; omega]
          ring,
        ← mul_sum, ih, show 2*(m+1)-m = m+2 by omega]
      ring
  have h (m : ℕ) : (a (m+1) : ℚ) = 2*(2^(m+1)*10^(m+1)-1)/19 + 5*(10^m*10^m-2^m*10^m)/2 := by
    simp [a, s, t, show ∀ k, 2*(m+1)-2-k = 2*m-k by omega]
  have g (k : ℕ) : (a (k+4) : ℚ) = 121*a (k+3) - 2120*a (k+2) + 2000*a (k+1) := by
    rw [h, h, h, h]
    ring
  refine ⟨?_, fun n hn => ?_, fun n hn => ?_⟩
  · ext (_ | _ | _ | _ | n) <;>
    simp [pow_succ, mul_sub, sub_mul, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, h, coeff_C,
      coeff_mul_C, ← map_ofNat (C : ℚ →+* _)] <;> ring
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have p : (4:ℚ)^m*5^m = 2^m*10^m := by
      rw [← mul_pow, ← mul_pow]
      norm_num
    have q : (100:ℚ)^m = 10^m*10^m := by
      rw [← mul_pow]
      norm_num
    rw [h]
    linear_combination (15/38)*p - (5/2)*q
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact_mod_cast g k
