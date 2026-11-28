import OMAStatements.S_oeis_a112001
import Mathlib

open OMA.S_oeis_a112001 in
theorem OMA.solution : type_of% @OMA.S_oeis_a112001.main := by
  have e0 (m : ℕ) : T (m+2) 0 = -(2*((m:ℤ)+2) - 1) * T (m+1) 0 := rfl
  have e (m k : ℕ) (h : k ≤ m) :
      T (m+2) (k+1) = -(2*m+2-k) * (T (m+1) (k+1) + T (m+1) k) := by
    rw [show T (m+2) (k+1) = if m + 2 < k + 2 then 0 else
      -(2 * ((m : ℤ) + 2) - ((k : ℤ) + 1) - 1) * (T (m + 1) (k + 1) + T (m + 1) k) from rfl,
      if_neg (by omega)]
    ring
  have L (m : ℕ) : 3*T (m+1) 1 = 2*m*T (m+1) 0 ∧ 9*T (m+2) 2 = -(m+1)*m*(4*m+5)*T (m+1) 0 ∧
      405*T (m+3) 3 = -2*(m+1)*m*(20*m^2+75*m+67)*T (m+2) 0 := by
    induction m with
    | zero => simp [T]
    | succ j ih =>
      obtain ⟨l1, l2, l3⟩ := ih
      have h1 := e j 0 (by omega)
      have h2 := e (j+1) 1 (by omega)
      have h3 := e (j+2) 2 (by omega)
      have z0 := e0 j
      have z1 := e0 (j+1)
      simp only [add_assoc, Nat.reduceAdd] at h1 h2 h3 z0 z1 ⊢
      push_cast at h1 h2 h3 z0 z1 ⊢
      have n1 : 3*T (j+2) 1 = 2*(j+1)*T (j+2) 0 := by
        linear_combination 3*h1 - (2*j+2)*l1 - (2*j+2)*z0
      have n2 : 9*T (j+3) 2 = -(j+2)*(j+1)*(4*j+9)*T (j+2) 0 := by
        linear_combination 9*h2 - (2*j+3)*l2 - 3*(2*j+3)*n1 + (j+1)*j*(4*j+5)*z0
      exact ⟨by linear_combination n1, by linear_combination n2, by
        linear_combination 405*h3 - (2*j+4)*l3 - 45*(2*j+4)*n2
          + 2*(j+2)*(j+1)*(20*j^2+115*j+162)*z1⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have qb := congrArg (Int.cast : ℤ → ℚ) (L (k+2)).2.2
  have qa := congrArg (Int.cast : ℤ → ℚ) (L (k+1)).2.2
  have q0 := congrArg (Int.cast : ℤ → ℚ) (e0 (k+2))
  simp only [a, add_assoc, Nat.reduceAdd, Nat.add_sub_cancel] at qb qa q0 ⊢
  push_cast at qb qa q0 ⊢
  linear_combination (1/1620 : ℚ) * ((k+1)*(20*(k+1)^2+75*(k+1)+67)*qb
    + (2*k+7)*(k+3)*(20*(k+2)^2+75*(k+2)+67)*qa
    - 2*(k+1)*(k+2)*(k+3)*(20*(k+1)^2+75*(k+1)+67)*(20*(k+2)^2+75*(k+2)+67)*q0)
