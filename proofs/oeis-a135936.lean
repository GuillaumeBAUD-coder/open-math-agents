import OMAStatements.S_oeis_a135936
import Mathlib

/-!
Proof sketch. The coefficient of `x^(n - 2m)` in `B n` is computed by two-step induction on `n`
following the recurrence `B (n+3) = X * B (n+2) - B (n+1)`: the index `n + 3 - 2m` comes from
index `n + 2 - 2m` of `B (n+2)` and index `(n+1) - 2(m-1)` of `B (n+1)`, so only coefficients
of the same parity class are involved. Coefficients above the degree vanish (separate lemma).
The binomial recurrence is Pascal's rule. The second conjunct is then binomial algebra.
-/

namespace R135936
open OMA.S_oeis_a135936 Polynomial

/-- Closed form of the coefficient (the statement's right-hand side). -/
def g (n m : ℕ) : ℤ :=
  (-1 : ℤ) ^ m *
    ((Nat.choose (n - m) m : ℤ) - if m = 0 then 0 else 3 * (Nat.choose (n - m - 1) (m - 1) : ℤ))

/-- Value of `g` at `m = j + 1` with top binomial index `u + 1`. -/
def H (u j : ℕ) : ℤ :=
  (-1 : ℤ) ^ (j + 1) * (((u + 1).choose (j + 1) : ℤ) - 3 * (u.choose j : ℤ))

theorem g0 (n : ℕ) : g n 0 = 1 := by simp [g]

theorem gH (n j u : ℕ) (h : n = u + j + 2) : g n (j + 1) = H u j := by
  subst h
  unfold g H
  rw [if_neg (show j + 1 ≠ 0 by omega), show u + j + 2 - (j + 1) = u + 1 by omega,
    show u + 1 - 1 = u by omega, show j + 1 - 1 = j by omega]

theorem R0 (u : ℕ) : H (u + 1) 0 = H u 0 - 1 := by
  simp only [H, zero_add, pow_one, Nat.choose_one_right, Nat.choose_zero_right]
  push_cast
  ring

theorem R1 (u i : ℕ) : H (u + 1) (i + 1) = H u (i + 1) - H u i := by
  unfold H
  rw [Nat.choose_succ_succ' (u + 1) (i + 1), Nat.choose_succ_succ' u i]
  push_cast
  ring

theorem R2 (i : ℕ) : H (i + 1) (i + 1) = - H i i := by
  simp only [H, Nat.choose_self]
  push_cast
  ring

theorem hB (n : ℕ) : boubaker (n + 3) = X * boubaker (n + 2) - boubaker (n + 1) := by
  rw [boubaker]

theorem deg : ∀ n k : ℕ, n < k → (boubaker n).coeff k = 0
  | 0, k, h => by
    rw [boubaker, coeff_one, if_neg (show k ≠ 0 by omega)]
  | 1, k, h => by
    rw [boubaker, coeff_X, if_neg (show 1 ≠ k by omega)]
  | 2, k, h => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [boubaker, coeff_add, coeff_X_pow, if_neg (show k + 1 ≠ 2 by omega), coeff_ofNat_succ,
      add_zero]
  | n + 3, k, h => by
    have ih2 := deg (n + 2)
    have ih1 := deg (n + 1)
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hB, coeff_sub, coeff_X_mul, ih2 k (by omega), ih1 (k + 1) (by omega), sub_zero]

theorem formula : ∀ n m : ℕ, 2 * m ≤ n → (boubaker n).coeff (n - 2 * m) = g n m
  | 0, m, h => by
    obtain rfl : m = 0 := by omega
    simp [boubaker, g]
  | 1, m, h => by
    obtain rfl : m = 0 := by omega
    simp [boubaker, g]
  | 2, m, h => by
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · simp [boubaker, g, coeff_X_pow]
    · norm_num [boubaker, g, coeff_X_pow]
  | n + 3, m, h => by
    have ih2 := formula (n + 2)
    have ih1 := formula (n + 1)
    rw [hB, coeff_sub]
    by_cases hm : m = 0
    · subst hm
      have e : n + 3 - 2 * 0 = (n + 2) + 1 := by omega
      rw [e, coeff_X_mul, deg (n + 1) (n + 2 + 1) (by omega)]
      have h2 := ih2 0 (by omega)
      rw [show n + 2 - 2 * 0 = n + 2 by omega] at h2
      rw [h2, g0, g0, sub_zero]
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rcases (show 2 * (j + 1) ≤ n + 2 ∨ 2 * (j + 1) = n + 3 by omega) with hj | hj
      · have e : n + 3 - 2 * (j + 1) = (n + 2 - 2 * (j + 1)) + 1 := by omega
        rw [e, coeff_X_mul, ih2 (j + 1) hj]
        have e1 : n + 2 - 2 * (j + 1) + 1 = n + 1 - 2 * j := by omega
        rw [e1, ih1 j (by omega), gH (n + 3) j (n - j + 1) (by omega),
          gH (n + 2) j (n - j) (by omega)]
        by_cases hj0 : j = 0
        · subst hj0
          rw [g0]
          exact (R0 (n - 0)).symm
        · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          rw [gH (n + 1) i (n - (i + 1)) (by omega)]
          exact (R1 (n - (i + 1)) i).symm
      · have e : n + 3 - 2 * (j + 1) = 0 := by omega
        rw [e, coeff_X_mul_zero]
        have h1 := ih1 j (by omega)
        rw [show n + 1 - 2 * j = 0 by omega] at h1
        rw [h1]
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [gH (n + 3) (i + 1) (i + 1) (by omega), gH (n + 1) i i (by omega), R2, zero_sub]

end R135936

theorem OMA.solution : type_of% @OMA.S_oeis_a135936.main := by
  intro n m h
  have hf : OMA.S_oeis_a135936.a135936 n m = R135936.g n m := R135936.formula n m h
  refine ⟨hf, ?_⟩
  rw [hf]
  unfold R135936.g OMA.S_oeis_a135936.a115139 OMA.S_oeis_a135936.a132460
  rw [show n + 1 - 1 - m = n - m by omega]
  split_ifs <;> ring
