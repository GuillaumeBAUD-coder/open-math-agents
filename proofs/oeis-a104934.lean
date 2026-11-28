import OMAStatements.S_oeis_a104934
import Mathlib

/-!
# A104934: `2 a(n) = b(n) + c(n - 1)`

All three sequences satisfy `u(n + 2) = 3 u(n + 1) + 2 u(n)`, so both sides of
`2 a(n + 1) = b(n + 1) + c(n)` satisfy the same recurrence in `n`; they agree for `n = 0`
(`4 = 3 + 1`) and `n = 1` (`16 = 11 + 5`).
-/

namespace OMA.S_oeis_a104934

/-- The shifted identity, by two-step induction. -/
lemma key (n : ℕ) : 2 * a (n + 1) = b (n + 1) + c n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    have ha : a (n + 3) = 3 * a (n + 2) + 2 * a (n + 1) := rfl
    have hb : b (n + 3) = 3 * b (n + 2) + 2 * b (n + 1) := rfl
    have hc : c (n + 2) = 3 * c (n + 1) + 2 * c n := rfl
    have ih2' : 2 * a (n + 2) = b (n + 2) + c (n + 1) := ih2
    show 2 * a (n + 3) = b (n + 3) + c (n + 2)
    omega

end OMA.S_oeis_a104934

open OMA.S_oeis_a104934 in
theorem OMA.solution : type_of% @OMA.S_oeis_a104934.main := by
  refine ⟨rfl, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact key m
