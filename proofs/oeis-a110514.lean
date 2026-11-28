import OMAStatements.S_oeis_a110514
import Mathlib

-- Proof of the conjectured formula in OEIS A110514 (statement by @ivillar).
-- Idea: J(m) = Jacobi(2^m, 2m+1) = χ₈(2m+1)^m (second supplementary law) is 4-periodic:
-- 1, -1, 1, 1, ...; b(n) = Σ J(n-2k) satisfies b(n+2) = b(n) + J(n+2), hence
-- b(n) - b(n-2) - b(n-4) + b(n-6) = J(n) - J(n-4) = 0, which is the denominator of the g.f.

namespace OMAA110514Helpers

open PowerSeries OMA.S_oeis_a110514

def J (m : ℕ) : ℤ := jacobiSym ((2 : ℤ) ^ m) (2 * m + 1)

theorem Jval (m : ℕ) : J m = if m % 4 = 1 then -1 else 1 := by
  unfold J
  rw [jacobiSym.pow_left, jacobiSym.at_two (by exact ⟨m, by ring⟩), ZMod.χ₈_nat_eq_if_mod_eight]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ m = 4 * q + r := ⟨m / 4, m % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 4).symm⟩
  have h2 : (2 * (4 * q + r) + 1) % 2 = 1 := by omega
  have h8 : (2 * (4 * q + r) + 1) % 8 = 2 * r + 1 := by omega
  have h4 : (4 * q + r) % 4 = r := by omega
  rw [h4, if_neg (by omega), h8]
  interval_cases r <;> simp [pow_add, pow_mul]

theorem Jper (m : ℕ) : J (m + 4) = J m := by
  rw [Jval, Jval, show (m + 4) % 4 = m % 4 by omega]

def b (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n / 2 + 1), J (n - 2 * k)

theorem b_step (n : ℕ) : b (n + 2) = J (n + 2) + b n := by
  unfold b
  rw [show (n + 2) / 2 + 1 = n / 2 + 1 + 1 by omega, Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  omega

theorem b0 : b 0 = 1 := by simp [b, Jval]
theorem b1 : b 1 = -1 := by simp [b, Jval]

theorem key : mk (fun n => (b n : ℚ)) * (1 - X ^ 2 - X ^ 4 + X ^ 6) = 1 - X + X ^ 2 + X ^ 3 := by
  have e1 : mk (fun n => (b n : ℚ)) * (1 - X ^ 2 - X ^ 4 + X ^ 6) =
      mk (fun n => (b n : ℚ)) - X ^ 2 * mk (fun n => (b n : ℚ)) - X ^ 4 * mk (fun n => (b n : ℚ)) +
        X ^ 6 * mk (fun n => (b n : ℚ)) := by ring
  have e2 : (1 - X + X ^ 2 + X ^ 3 : ℚ⟦X⟧) = X ^ 0 - X ^ 1 + X ^ 2 + X ^ 3 := by ring
  rw [e1, e2]
  ext n
  simp only [map_add, map_sub, coeff_mk, coeff_X_pow_mul', coeff_X_pow]
  have B2 := b_step 0
  have B3 := b_step 1
  have B4 := b_step 2
  have B5 := b_step 3
  by_cases hn : n ≤ 5
  · interval_cases n <;> simp_all [Jval, b0, b1] <;> norm_num [Jval] at *
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have h1 := b_step (m + 4)
    have h2 := b_step m
    have hp := Jper (m + 2)
    simp only [show m + 4 + 2 = m + 6 by ring] at h1 hp
    simp [show ¬ (m + 6 = 1) by omega, show ¬ (m + 6 = 2) by omega, show ¬ (m + 6 = 3) by omega]
    have q1 : ((b (m + 6) : ℤ) : ℚ) = ((J (m + 6) + b (m + 4) : ℤ) : ℚ) := by rw [h1]
    have q2 : ((b (m + 2) : ℤ) : ℚ) = ((J (m + 2) + b m : ℤ) : ℚ) := by rw [h2]
    have q3 : ((J (m + 6) : ℤ) : ℚ) = ((J (m + 2) : ℤ) : ℚ) := by rw [hp]
    push_cast at q1 q2 q3
    linear_combination q1 - q2 + q3

end OMAA110514Helpers

open PowerSeries OMA.S_oeis_a110514 OMAA110514Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a110514.main := by
  intro n
  have hG : G = mk (fun n => (b n : ℚ)) := by
    rw [G, eq_comm, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), key]
  rw [a, hG, coeff_mk, b]
  push_cast
  rfl

