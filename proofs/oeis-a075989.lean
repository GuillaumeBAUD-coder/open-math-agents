import OMAStatements.S_oeis_a075989
import Mathlib

/-!
Both sides count the `d ∈ [1, n-1]` with `d ≤ 2 (n mod d)`. On the left, `{n/d} = (n mod d)/d`,
and `d = n` never counts. On the right, put `d = n - k`: then `k ≡ n (mod d)`, so with
`r = n mod d` the condition reads `(2r) mod d ≠ 2r`, that is `d ≤ 2r`. The reflection
`k ↦ n - k` of `[1, n-1]` matches the two sums.
-/

namespace R075989
open OMA.S_oeis_a075989

/-- The common indicator. -/
def g (n d : ℕ) : ℕ := if d ≤ 2 * (n % d) then 1 else 0

theorem lhs_term (n d : ℕ) (hd : 0 < d) :
    (if (1 : ℚ) / 2 ≤ Int.fract ((n : ℚ) / d) then 1 else 0) = g n d := by
  unfold g
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have key : (1 : ℚ) / 2 ≤ ((n % d : ℕ) : ℚ) / d ↔ d ≤ 2 * (n % d) := by
    rw [le_div_iff₀ hdq]
    constructor
    · intro h
      have h' : (d : ℚ) ≤ 2 * ((n % d : ℕ) : ℚ) := by linarith
      exact_mod_cast h'
    · intro h
      have h' : (d : ℚ) ≤ 2 * ((n % d : ℕ) : ℚ) := by exact_mod_cast h
      linarith
  by_cases h : d ≤ 2 * (n % d)
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]

theorem f_term (k d : ℕ) (hd : 0 < d) :
    f ((k + d : ℕ) : ℤ) (k : ℤ) = g (k + d) d := by
  unfold f g
  have habs : |((k + d : ℕ) : ℤ) - (k : ℤ)| = ((d : ℕ) : ℤ) := by
    push_cast
    rw [show (k : ℤ) + d - k = d by ring]
    exact abs_of_nonneg (by positivity)
  rw [habs, show ((k + d : ℕ) : ℤ) + (k : ℤ) = ((k + d + k : ℕ) : ℤ) by push_cast; ring,
    ← Int.natCast_mod, ← Int.natCast_mod, ← Int.natCast_mod, ← Nat.cast_add]
  simp only [ne_eq, Nat.cast_inj]
  have e1 : (k + d) % d = k % d := Nat.add_mod_right k d
  have e2 : (k + d + k) % d = (k % d + k % d) % d := by
    rw [show k + d + k = k + k + d by ring, Nat.add_mod_right, Nat.add_mod]
  rw [e1, e2]
  have hr : k % d < d := Nat.mod_lt k hd
  by_cases h : d ≤ 2 * (k % d)
  · rw [if_pos h, if_pos]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg h, if_neg]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp

end R075989

open OMA.S_oeis_a075989 R075989 in
theorem OMA.solution : type_of% @OMA.S_oeis_a075989.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hl : a (m + 1) = ∑ d ∈ Finset.Ico 1 (m + 1), g (m + 1) d := by
    unfold a
    rw [Finset.card_filter, Finset.sum_Icc_succ_top (by omega)]
    have hlast : g (m + 1) (m + 1) = 0 := by
      unfold g
      rw [Nat.mod_self, if_neg (by omega)]
    rw [lhs_term _ _ (by omega), hlast, Nat.add_zero]
    rw [← Finset.Ico_add_one_right_eq_Icc]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_Ico] at hd
    exact lhs_term _ _ (by omega)
  have hr : ∑ k ∈ Finset.Ico 1 (m + 1), f ((m + 1 : ℕ) : ℤ) (k : ℤ) =
      ∑ k ∈ Finset.Ico 1 (m + 1), g (m + 1) ((m + 1) - k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Ico] at hk
    have := f_term k (m + 1 - k) (by omega)
    rwa [show k + (m + 1 - k) = m + 1 by omega] at this
  rw [hl, hr, Finset.sum_Ico_reflect (g (m + 1)) 1 (m := m + 1) (n := m + 1) (by omega)]
  rw [show m + 1 + 1 - (m + 1) = 1 by omega, show m + 1 + 1 - 1 = m + 1 by omega]
