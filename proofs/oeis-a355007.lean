import OMAStatements.S_oeis_a355007
import Mathlib

/-!
For a fixed `c`, the coefficient of `y^i` in `Product_{j = 1..m} (j + c*y)` is
`c^i * |Stirling1(m+1, i+1)|`; this follows by induction on `m` from the recurrence
`s(m+2, i+1) = (m+1) s(m+1, i+1) + s(m+1, i)`. With `c = n`, `m = n - 1`, `i = k - 1`, the entry
of A056856 is `n^(k-1) * |Stirling1(n, k)|`, and multiplying by `n` gives `T(n, k)`.
-/

namespace R355007
open OMA.S_oeis_a355007 Polynomial

theorem coeff_prod (c : ℕ) : ∀ m i : ℕ,
    (∏ j ∈ Finset.Icc 1 m, (C (j : ℕ) + C c * X)).coeff i = c ^ i * Nat.stirlingFirst (m + 1) (i + 1) := by
  intro m
  induction m with
  | zero =>
    intro i
    rw [Finset.Icc_eq_empty (by norm_num), Finset.prod_empty, coeff_one]
    rcases i with _ | i
    · simp [Nat.stirlingFirst_self]
    · rw [if_neg (by omega), Nat.stirlingFirst_eq_zero_of_lt (by omega), Nat.mul_zero]
  | succ m ih =>
    intro i
    rw [Finset.prod_Icc_succ_top (by omega), mul_add, ← mul_assoc, coeff_add, coeff_mul_C]
    rcases i with _ | i
    · rw [coeff_mul_X_zero, ih, Nat.stirlingFirst_succ_succ (m + 1) 0,
        Nat.stirlingFirst_succ_zero]
      ring
    · rw [coeff_mul_X, coeff_mul_C, ih, ih, Nat.stirlingFirst_succ_succ (m + 1) (i + 1)]
      push_cast
      ring

end R355007

open OMA.S_oeis_a355007 R355007 in
theorem OMA.solution : type_of% @OMA.S_oeis_a355007.main := by
  intro n k hk hkn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  unfold T A056856
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, coeff_prod]
  ring
