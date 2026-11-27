import OMAStatements.S_oeis_a053482
import Mathlib

-- Problem: A053482: Binomial transform of A029767.
-- Upstream: formal-conjectures statements/oeis-a053482.lean:0 (declaration OMA.S_oeis_a053482.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! With d(n,k) = C(n,k) k! = n (n-1) ... (n-k+1), let u(n) be the sum of d(n,k) 2^k and v(n) the
sum of d(n,k). Then a(n) = 2 u(n) - v(n), and d(n+1,k+1) = (n+1) d(n,k) gives
u(n+1) = 2 (n+1) u(n) + 1 and v(n+1) = (n+1) v(n) + 1. Substituting these three times turns the
recurrence into a polynomial identity. -/

namespace A053482Aux

open OMA.S_oeis_a053482

/-- u(n) = ∑_k d(n,k) 2^k. -/
def u (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (n.descFactorial k : ℤ) * 2 ^ k

/-- v(n) = ∑_k d(n,k). -/
def v (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (n.descFactorial k : ℤ)

theorem a_eq (n : ℕ) : a n = 2 * u n - v n := by
  unfold a u v
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

theorem u_succ (n : ℕ) : u (n + 1) = 2 * ((n : ℤ) + 1) * u n + 1 := by
  unfold u
  rw [Finset.sum_range_succ' (fun k => ((n + 1).descFactorial k : ℤ) * 2 ^ k), Finset.mul_sum]
  simp only [Nat.descFactorial_zero, Nat.cast_one, pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.succ_descFactorial_succ]
  push_cast
  ring

theorem v_succ (n : ℕ) : v (n + 1) = ((n : ℤ) + 1) * v n + 1 := by
  unfold v
  rw [Finset.sum_range_succ' (fun k => ((n + 1).descFactorial k : ℤ)), Finset.mul_sum]
  simp only [Nat.descFactorial_zero, Nat.cast_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.succ_descFactorial_succ]
  push_cast
  ring

theorem rec (m : ℕ) :
    a (m + 3) - (3 * ((m : ℤ) + 3) + 1) * a (m + 2) +
      (2 * ((m : ℤ) + 3) + 3) * ((m : ℤ) + 3 - 1) * a (m + 1) -
      2 * ((m : ℤ) + 3 - 1) * ((m : ℤ) + 3 - 2) * a m = 0 := by
  have hu1 := u_succ m
  have hu2 := u_succ (m + 1)
  have hu3 := u_succ (m + 2)
  have hv1 := v_succ m
  have hv2 := v_succ (m + 1)
  have hv3 := v_succ (m + 2)
  push_cast at hu2 hu3 hv2 hv3
  rw [a_eq, a_eq, a_eq, a_eq, hu3, hv3, hu2, hv2, hu1, hv1]
  ring

end A053482Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a053482.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  rw [e1, e2, Nat.add_sub_cancel]
  have h := A053482Aux.rec m
  push_cast
  exact h
