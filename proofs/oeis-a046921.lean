import OMAStatements.S_oeis_a046921
import Mathlib

/-!
# A046921: odd numbers as `p + 2 a ^ 2` — the statement is false

Stern's counterexample `5777 = 2 * 2888 + 1` survives even when `p = 1` is allowed:
for `a = 0, …, 53` none of the numbers `5777 - 2 a ^ 2` is `1` or a prime, and for `a ≥ 54`
already `2 a ^ 2 > 5777`.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a046921.main) := by
  intro h
  obtain ⟨p, a, hp, he⟩ := h 2888
  -- `a` is at most `53`, since `2 * 54 ^ 2 = 5832 > 5777`
  have ha : a < 54 := by
    by_contra hc
    have : 54 * 54 ≤ a * a := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  -- so `p = 5777 - 2 a ^ 2` is one of 54 explicit numbers, none of them `1` or prime
  have hp' : p = 5777 - 2 * a ^ 2 := by omega
  subst hp'
  interval_cases a <;> rcases hp with hp | hp <;> revert hp <;> norm_num
