import OMAStatements.S_oeis_a097204
import Mathlib

-- Problem: A097204: Binomial transform of A033312.
-- Upstream: formal-conjectures statements/oeis-a097204.lean:0 (declaration OMA.S_oeis_a097204.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! With d(n,k) = C(n,k) k! and v(n) the sum of d(n,k) over k, a(n) = v(n) - 2^n. The shift
d(n+1,k+1) = (n+1) d(n,k) gives v(n+1) = (n+1) v(n) + 1, and substituting this four times turns the
recurrence into a polynomial identity. -/

namespace A097204Aux

open OMA.S_oeis_a097204

/-- v(n) = ∑_k d(n,k). -/
def v (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (n.descFactorial k : ℤ)

theorem a_eq (n : ℕ) : a n = v n - 2 ^ n := by
  have h2 : (2 : ℤ) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) := by
    have := Nat.sum_range_choose n
    exact_mod_cast this.symm
  unfold a v
  rw [h2, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.descFactorial_eq_factorial_mul_choose]
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
    a (m + 4) + (-((m : ℤ) + 4) - 5) * a (m + 3) + (5 * ((m : ℤ) + 4) + 3) * a (m + 2) +
      4 * (-2 * ((m : ℤ) + 4) + 3) * a (m + 1) + 4 * (((m : ℤ) + 4) - 3) * a m = 0 := by
  have h1 := v_succ m
  have h2 := v_succ (m + 1)
  have h3 := v_succ (m + 2)
  have h4 := v_succ (m + 3)
  push_cast at h2 h3 h4
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, h4, h3, h2, h1]
  ring

end A097204Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a097204.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e2 : m + 4 - 2 = m + 2 := by omega
  have e3 : m + 4 - 3 = m + 1 := by omega
  rw [e1, e2, e3, Nat.add_sub_cancel]
  have h := A097204Aux.rec m
  push_cast
  exact h
