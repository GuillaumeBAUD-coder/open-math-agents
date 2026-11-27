import OMAStatements.S_oeis_a159864
import Mathlib

-- Problem: A159864, difference array of the Fibonacci numbers; Mathar's row sums.
-- Upstream: formal-conjectures statements/oeis-a159864.lean (declaration OMA.S_oeis_a159864.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: telescoping the defining difference gives R(n) = F(n+1) - D(n+1, 0) for the row sum
-- R(n), and D(j, 0) = (-1)^(j+1) F(j) (Fibonacci numbers of negative index), so
-- R(n) = (1 - (-1)^n) F(n+1).

namespace OMA.P_oeis_a159864

open OMA.S_oeis_a159864

theorem D_succ (j i : ℕ) : D (j + 1) i = D j (i + 1) - D j i := rfl

/-- Closed form of the iterated differences (Fibonacci numbers of negative index included). -/
theorem D_closed : ∀ j i : ℕ, D j i =
    if j ≤ i then (Nat.fib (i - j) : ℤ) else (-1) ^ (j - i + 1) * (Nat.fib (j - i) : ℤ) := by
  intro j
  induction j with
  | zero => intro i; simp [D]
  | succ j ih =>
    intro i
    rw [D_succ, ih (i + 1), ih i]
    rcases Nat.lt_or_ge j i with h | h
    · -- j < i
      obtain ⟨t, rfl⟩ : ∃ t, i = j + 1 + t := ⟨i - (j + 1), by omega⟩
      rw [if_pos (show j ≤ j + 1 + t + 1 by omega), if_pos (show j ≤ j + 1 + t by omega),
        if_pos (show j + 1 ≤ j + 1 + t by omega)]
      rw [show j + 1 + t + 1 - j = t + 2 by omega, show j + 1 + t - j = t + 1 by omega,
        show j + 1 + t - (j + 1) = t by omega, Nat.fib_add_two]
      push_cast
      ring
    · rcases Nat.eq_or_lt_of_le h with h' | h'
      · -- j = i
        obtain rfl : j = i := h'.symm
        rw [if_pos (show j ≤ j + 1 by omega), if_pos (show j ≤ j by omega),
          if_neg (show ¬ (j + 1 ≤ j) by omega), show j + 1 - j = 1 by omega,
          show j - j = 0 by omega]
        simp
      · -- i < j
        obtain ⟨t, rfl⟩ : ∃ t, j = i + 1 + t := ⟨j - (i + 1), by omega⟩
        rw [if_neg (show ¬ (i + 1 + t ≤ i) by omega), if_neg (show ¬ (i + 1 + t + 1 ≤ i) by omega)]
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht
          rw [if_pos (show i + 1 + 0 ≤ i + 1 by omega), show i + 1 - (i + 1 + 0) = 0 by omega,
            show i + 1 + 0 - i = 1 by omega, show i + 1 + 0 + 1 - i = 2 by omega]
          norm_num
        · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
          rw [if_neg (show ¬ (i + 1 + (u + 1) ≤ i + 1) by omega),
            show i + 1 + (u + 1) - (i + 1) = u + 1 by omega,
            show i + 1 + (u + 1) - i = u + 2 by omega,
            show i + 1 + (u + 1) + 1 - i = u + 3 by omega,
            show (Nat.fib (u + 3) : ℤ) = Nat.fib (u + 1) + Nat.fib (u + 2) by
              rw [Nat.fib_add_two]; push_cast; ring]
          rw [pow_succ, pow_succ, pow_succ]
          ring

theorem D_zero (j : ℕ) : D j 0 = (-1) ^ (j + 1) * (Nat.fib j : ℤ) := by
  rw [D_closed]
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp
  · rw [if_neg (by omega), Nat.sub_zero]

/-- The row sum `R n = ∑_{k ≤ n} T n k`. -/
def R (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T n k

theorem R_eq (n : ℕ) : R n = (Nat.fib (n + 1) : ℤ) - D (n + 1) 0 := by
  have h1 : R (n + 1) = (Nat.fib (n + 1) : ℤ) +
      ∑ k ∈ Finset.range (n + 1), D (k + 1) (n - k) := by
    unfold R T
    rw [Finset.sum_range_succ']
    simp only [show n + 1 - 0 = n + 1 by omega]
    rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      rw [show n + 1 - (k + 1) = n - k by omega]
  have h2 : ∑ k ∈ Finset.range (n + 1), D (k + 1) (n - k) =
      (∑ k ∈ Finset.range (n + 1), D k (n + 1 - k)) - R n := by
    unfold R T
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [D_succ, show n - k + 1 = n + 1 - k by omega]
  have h3 : R (n + 1) = (∑ k ∈ Finset.range (n + 1), D k (n + 1 - k)) + D (n + 1) 0 := by
    unfold R T
    rw [Finset.sum_range_succ, Nat.sub_self]
  rw [h2] at h1
  linarith

theorem main' : ∀ n : ℕ,
    (∑ k ∈ Finset.range (2 * n + 1), T (2 * n) k = 0) ∧
    (∑ k ∈ Finset.range (2 * n + 2), T (2 * n + 1) k = 2 * (Nat.fib (2 * n + 2) : ℤ)) := by
  intro n
  constructor
  · have := R_eq (2 * n)
    unfold R at this
    rw [this, D_zero, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul]
    simp
  · have := R_eq (2 * n + 1)
    unfold R at this
    rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring] at this
    rw [this, D_zero, show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring, pow_succ, pow_mul]
    simp
    ring

end OMA.P_oeis_a159864

theorem OMA.solution : type_of% @OMA.S_oeis_a159864.main := OMA.P_oeis_a159864.main'
