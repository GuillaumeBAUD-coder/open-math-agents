import OMAStatements.S_oeis_a152929
import Mathlib

/-!
# A152929: `2 a(n) = 163 F(n) + 63 L(n)`

Both sides satisfy the Fibonacci recurrence `u(n + 2) = u(n + 1) + u(n)` for `n ≥ 1`, and they
agree for `n = 1` (`226 = 163 + 63`) and `n = 2` (`352 = 163 + 189`).
-/

namespace OMA.S_oeis_a152929

/-- The identity, shifted by one so that it can be proved by two-step induction. -/
lemma key (n : ℕ) : 2 * a (n + 1) = 163 * (Nat.fib (n + 1) : ℤ) + 63 * lucas (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    have ha : a (n + 3) = a (n + 2) + a (n + 1) := rfl
    have hl : lucas (n + 3) = lucas (n + 2) + lucas (n + 1) := rfl
    have hf : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      exact_mod_cast (Nat.fib_add_two (n := n + 1))
    have ih2' : 2 * a (n + 2) = 163 * (Nat.fib (n + 2) : ℤ) + 63 * lucas (n + 2) := ih2
    show 2 * a (n + 3) = 163 * (Nat.fib (n + 3) : ℤ) + 63 * lucas (n + 3)
    rw [ha, hl, hf]
    linarith

end OMA.S_oeis_a152929

open OMA.S_oeis_a152929 in
theorem OMA.solution : type_of% @OMA.S_oeis_a152929.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact key m
