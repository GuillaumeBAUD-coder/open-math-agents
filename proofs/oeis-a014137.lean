import OMAStatements.S_oeis_a014137

-- Problem: A014137: Partial sums of Catalan numbers (A000108).
-- Credit: @MBimrose (the owner of the agent is credited as the solver)
-- Mathar's recurrence: (n+1)a(n) - (5n-1)a(n-1) + (4n-2)a(n-2) = 0 for n >= 2.
-- Since a(n) - a(n-1) = catalan n, the identity is equivalent to the Catalan recurrence
-- (n+1)C(n) = 2(2n-1)C(n-1), which is `cat_rec` below, derived from
-- (n+1)C(n) = centralBinom n and (n+1)centralBinom(n+1) = 2(2n+1)centralBinom n.

open OMA.S_oeis_a014137

/-- One term of the defining sum: `a (n+1) = a n + catalan (n+1)`. -/
lemma a_succ (n : ℕ) : a (n + 1) = a n + (catalan (n + 1) : ℤ) := by
  simp [OMA.S_oeis_a014137.a, Finset.sum_range_succ]

/-- The two-term Catalan recurrence: `(m+2) * catalan (m+1) = (4*m+2) * catalan m`. -/
lemma cat_rec (m : ℕ) : (m + 2) * catalan (m + 1) = (4 * m + 2) * catalan m := by
  have h1 : (m + 2) * catalan (m + 1) = Nat.centralBinom (m + 1) :=
    succ_mul_catalan_eq_centralBinom (m + 1)
  have h3 : (m + 1) * Nat.centralBinom (m + 1) = 2 * (2 * m + 1) * Nat.centralBinom m :=
    Nat.succ_mul_centralBinom_succ m
  have h4 : Nat.centralBinom m = (m + 1) * catalan m :=
    (succ_mul_catalan_eq_centralBinom m).symm
  have key : (m + 1) * ((m + 2) * catalan (m + 1)) = (m + 1) * ((4 * m + 2) * catalan m) := by
    rw [h1, h3, h4]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) key

theorem OMA.solution : type_of% @OMA.S_oeis_a014137.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : a (m + 2) = a (m + 1) + (catalan (m + 2) : ℤ) := a_succ (m + 1)
  have h2 : a (m + 1) = a m + (catalan (m + 1) : ℤ) := a_succ m
  have hc : ((m : ℤ) + 3) * (catalan (m + 2) : ℤ) =
      (4 * (m : ℤ) + 6) * (catalan (m + 1) : ℤ) := by
    have h := cat_rec (m + 1)
    have h' : (((m + 3) * catalan (m + 2) : ℕ) : ℤ) =
        (((4 * (m + 1) + 2) * catalan (m + 1) : ℕ) : ℤ) := by
      rw [h]
    push_cast at h' ⊢
    linarith
  have e1 : a (m + 2) = a m + (catalan (m + 1) : ℤ) + (catalan (m + 2) : ℤ) := by
    rw [h1, h2]
  have hidx1 : m + 2 - 1 = m + 1 := rfl
  have hidx2 : m + 2 - 2 = m := rfl
  rw [hidx1, hidx2, e1, h2]
  push_cast
  linear_combination hc
