import OMAStatements.S_oeis_a134635

-- Problem: A134635: Row sums of triangle A134634.
-- Upstream: formal-conjectures statements/oeis-a134635.lean:0 (declaration OMA.S_oeis_a134635.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: splitting off the two borders, row n + 1 sums to C(n+1) + (a(n) - C(n)) + (a(n) - C(n))
-- + C(n+1), so a(n+1) + 2C(n) = 2a(n) + 2C(n+1). With (n+2)C(n+1) = 2(2n+1)C(n) (from
-- (n+1)C(n) = centralBinom n), the recurrence at n = m + 3 equals
-- (m+4) r2 - (5m+12) r1 + (4m+2) r0 + 2 c3 - 4 c2 + 2 c1 for these six instances.

namespace P1A134635

open OMA.S_oeis_a134635

theorem T_zero (k : ℕ) : T 0 k = if k = 0 then catalan 0 else 0 := rfl

theorem T_succ (n k : ℕ) : T (n + 1) k =
    if k = 0 ∨ k = n + 1 then catalan (n + 1)
    else if k < n + 1 then T n k + T n (k - 1) else 0 := rfl

theorem Tn0 (n : ℕ) : T n 0 = catalan n := by
  cases n with
  | zero => rw [T_zero, if_pos rfl]
  | succ m => rw [T_succ, if_pos (Or.inl rfl)]

theorem Tnn (n : ℕ) : T n n = catalan n := by
  cases n with
  | zero => rw [T_zero, if_pos rfl]
  | succ m => rw [T_succ, if_pos (Or.inr rfl)]

theorem Tmid (n k : ℕ) (hk : k < n) : T (n + 1) (k + 1) = T n (k + 1) + T n k := by
  rw [T_succ, if_neg (show ¬ (k + 1 = 0 ∨ k + 1 = n + 1) by omega),
    if_pos (show k + 1 < n + 1 by omega), Nat.add_sub_cancel]

theorem rowrec (n : ℕ) : a (n + 1) + 2 * catalan n = 2 * a n + 2 * catalan (n + 1) := by
  have e1 : a (n + 1) =
      ∑ k ∈ Finset.range n, T (n + 1) (k + 1) + T (n + 1) 0 + T (n + 1) (n + 1) := by
    show ∑ k ∈ Finset.range (n + 1 + 1), T (n + 1) k = _
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have e2 : ∑ k ∈ Finset.range n, T (n + 1) (k + 1) =
      ∑ k ∈ Finset.range n, T n (k + 1) + ∑ k ∈ Finset.range n, T n k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact Tmid n k (Finset.mem_range.mp hk)
  have e3 : a n = ∑ k ∈ Finset.range n, T n (k + 1) + T n 0 := by
    show ∑ k ∈ Finset.range (n + 1), T n k = _
    rw [Finset.sum_range_succ']
  have e4 : a n = ∑ k ∈ Finset.range n, T n k + T n n := by
    show ∑ k ∈ Finset.range (n + 1), T n k = _
    rw [Finset.sum_range_succ]
  rw [Tn0] at e3
  rw [Tnn] at e4
  rw [e1, e2, Tn0, Tnn]
  omega

theorem cat_rec (n : ℕ) : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h1 : (n + 2) * catalan (n + 1) = (n + 1).centralBinom :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 : (n + 1) * catalan n = n.centralBinom := succ_mul_catalan_eq_centralBinom n
  have h3 : (n + 1) * (n + 1).centralBinom = 2 * (2 * n + 1) * n.centralBinom :=
    Nat.succ_mul_centralBinom_succ n
  have h4 : (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h4

end P1A134635

open OMA.S_oeis_a134635 P1A134635 in
theorem OMA.solution : type_of% @OMA.S_oeis_a134635.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have r0' := rowrec m
  have r1' := rowrec (m + 1)
  have r2' := rowrec (m + 2)
  have c1' := cat_rec m
  have c2' := cat_rec (m + 1)
  have c3' := cat_rec (m + 2)
  rw [show m + 1 + 1 = m + 2 by omega] at r1' c2'
  rw [show m + 2 + 1 = m + 3 by omega] at r2' c3'
  have r0 := congrArg (Nat.cast : ℕ → ℤ) r0'
  have r1 := congrArg (Nat.cast : ℕ → ℤ) r1'
  have r2 := congrArg (Nat.cast : ℕ → ℤ) r2'
  have c1 := congrArg (Nat.cast : ℕ → ℤ) c1'
  have c2 := congrArg (Nat.cast : ℕ → ℤ) c2'
  have c3 := congrArg (Nat.cast : ℕ → ℤ) c3'
  push_cast at r0 r1 r2 c1 c2 c3 ⊢
  linear_combination ((m : ℤ) + 4) * r2 - (5 * (m : ℤ) + 12) * r1 + (4 * (m : ℤ) + 2) * r0
    + 2 * c3 - 4 * c2 + 2 * c1
