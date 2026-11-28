import OMAStatements.S_oeis_a383700
import Mathlib

-- Problem: A383700: Coefficient of x^2 in expansion of (x+1) * (x+5) * ... * (x+4*n-3).
-- Upstream: formal-conjectures statements/oeis-a383700.lean:0 (declaration OMA.S_oeis_a383700.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Let P(n) be the product and c_k(n) its coefficient of x^k. Since P(n+1) = P(n) (x + 4n + 1),
c_0(n+1) = (4n+1) c_0(n) and c_(k+1)(n+1) = c_k(n) + (4n+1) c_(k+1)(n). Expressing
c_2(m+3), c_2(m+2), c_2(m+1) through c_0(m), c_1(m), c_2(m) turns the recurrence into a
polynomial identity. -/

namespace A383700Aux

open Polynomial OMA.S_oeis_a383700

/-- The product (x+1)(x+5)...(x+4n-3). -/
noncomputable def P (n : ℕ) : ℤ[X] := ∏ j ∈ Finset.range n, (X + C (4 * (j : ℤ) + 1))

theorem P_succ (n : ℕ) : P (n + 1) = P n * (X + C (4 * (n : ℤ) + 1)) := by
  unfold P
  rw [Finset.prod_range_succ]

theorem c_succ (n k : ℕ) :
    (P (n + 1)).coeff (k + 1) = (P n).coeff k + (4 * (n : ℤ) + 1) * (P n).coeff (k + 1) := by
  rw [P_succ, mul_add, coeff_add, coeff_mul_X, coeff_mul_C]
  ring

theorem c_zero (n : ℕ) : (P (n + 1)).coeff 0 = (4 * (n : ℤ) + 1) * (P n).coeff 0 := by
  rw [P_succ, mul_add, coeff_add, coeff_mul_X_zero, coeff_mul_C]
  ring

theorem rec (m : ℕ) :
    (P (m + 3)).coeff 2 + 3 * (-4 * ((m : ℤ) + 3) + 7) * (P (m + 2)).coeff 2 +
      (48 * ((m : ℤ) + 3) ^ 2 - 216 * ((m : ℤ) + 3) + 247) * (P (m + 1)).coeff 2 -
      (4 * ((m : ℤ) + 3) - 11) ^ 3 * (P m).coeff 2 = 0 := by
  have a3 := c_succ (m + 2) 1
  have a2 := c_succ (m + 1) 1
  have a1 := c_succ m 1
  have b2 := c_succ (m + 1) 0
  have b1 := c_succ m 0
  have z1 := c_zero m
  push_cast at a3 a2 b2
  simp only [Nat.reduceAdd] at a3 a2 a1 b2 b1
  rw [a3, a2, b2, a1, b1, z1]
  ring

end A383700Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a383700.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  rw [e1, e2, Nat.add_sub_cancel]
  have h := A383700Aux.rec m
  unfold OMA.S_oeis_a383700.a
  push_cast
  exact h
