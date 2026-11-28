import OMAStatements.S_oeis_a296161
import Mathlib

/-!
# A296161: Barker's recurrence

The odd i ≤ m are 1, 3, ..., 2K − 1 with K = floor((m+1)/2), so
Σ_{i ≤ m} (n − i)(i mod 2) = K·n − K² (induction on m). Hence a(x) = k(x)·x − k(x)² with
k(x) = floor((floor(x/2) + 1)/2), and k(x + 4) = k(x) + 1. Substituting into the recurrence at
n = m + 9 leaves a polynomial identity in m, k(m) and k(m+1).
-/

namespace A296161Proof

theorem sumK (n m : ℕ) (hm : m ≤ n) :
    ((∑ i ∈ Finset.Icc 1 m, (n - i) * (i % 2) : ℕ) : ℤ) =
      (((m + 1) / 2 : ℕ) : ℤ) * n - (((m + 1) / 2 : ℕ) : ℤ) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ih (by omega), Nat.cast_mul,
      Nat.cast_sub (show m + 1 ≤ n by omega)]
    rcases Nat.mod_two_eq_zero_or_one (m + 1) with h | h
    · rw [h, show (m + 1 + 1) / 2 = (m + 1) / 2 by omega]
      generalize (m + 1) / 2 = K
      push_cast
      ring
    · have e2 : ((m : ℤ) + 1) = 2 * (((m + 1) / 2 : ℕ) : ℤ) + 1 := by
        have : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
        exact_mod_cast this
      rw [h, show (m + 1 + 1) / 2 = (m + 1) / 2 + 1 by omega]
      generalize (m + 1) / 2 = K at e2 ⊢
      push_cast
      linear_combination (-1 : ℤ) * e2

theorem closed (x : ℕ) :
    (OMA.S_oeis_a296161.a x : ℤ) =
      (((x / 2 + 1) / 2 : ℕ) : ℤ) * x - (((x / 2 + 1) / 2 : ℕ) : ℤ) ^ 2 := by
  unfold OMA.S_oeis_a296161.a
  exact sumK x (x / 2) (Nat.div_le_self x 2)

end A296161Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a296161.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 4 = m + 5 by omega,
    show m + 9 - 5 = m + 4 by omega, show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m by omega,
    A296161Proof.closed, A296161Proof.closed, A296161Proof.closed, A296161Proof.closed,
    A296161Proof.closed, A296161Proof.closed,
    show ((m + 9) / 2 + 1) / 2 = ((m + 1) / 2 + 1) / 2 + 2 by omega,
    show ((m + 8) / 2 + 1) / 2 = (m / 2 + 1) / 2 + 2 by omega,
    show ((m + 5) / 2 + 1) / 2 = ((m + 1) / 2 + 1) / 2 + 1 by omega,
    show ((m + 4) / 2 + 1) / 2 = (m / 2 + 1) / 2 + 1 by omega]
  generalize ((m + 1) / 2 + 1) / 2 = K1
  generalize (m / 2 + 1) / 2 = K0
  push_cast
  ring
