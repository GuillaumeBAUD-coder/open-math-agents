import Mathlib

/-!
# A simple sum of powers conjecture: `∑_{i=1}^p a_i^p = u`

Source: https://math.stackexchange.com/questions/5150281

The source considers `∑_{i=1}^p a_i^p = u`, where the `a_i` are distinct integers with
`|a_i| > 1`, `p` is an odd prime, and `u ∈ {-1, 0, 1}`. The conjecture: "This Diophantine
equation is solvable for every odd prime `p`."

Reading choices (for the reviewer):
* "Solvable for every odd prime `p`" is read as: for every odd prime `p` there are some
  `u ∈ {-1, 0, 1}` and distinct integers `a_1, …, a_p` with `|a_i| > 1` and `∑ a_i^p = u`.
  The source's examples use different `u` for different `p` (`u = 1` for `p = 3`, `u = 0` for
  `p = 5`, `u = -1` for `p = 7`), so `u` may depend on `p`.
  The one answer on the page reads it with `u` fixed instead. For `u = 0` and `p = 3`, it
  notes that Fermat's Last Theorem rules this out. That reading is therefore false, and it is
  not the one stated here.
* The source notes the variant `u ∈ {0, 1}`. It is equivalent, because `p` is odd: negating
  every `a_i` negates `u`. The statement keeps `u ∈ {-1, 0, 1}`.
* "Distinct" is `Function.Injective a` for `a : Fin p → ℤ`.
* Already settled: the cases `p = 3, 5, 7` are solved by the source's own identities, which are
  checked below. The open content is every larger odd prime.

Numeric sanity checks (the `example`s below, checked by `decide`):
`(-12)^3 + 9^3 + 10^3 = 1`; `27^5 + 84^5 + 110^5 + 133^5 + (-144)^5 = 0`; and
`2816^7 + 1348^7 + 1146^7 - 2787^7 - 1951^7 - 1031^7 - 130^7 = -1`. In each, the entries are
distinct with absolute value above 1. Together they witness `main`'s body for `p = 3, 5, 7`.
-/

namespace OMA.S_mse_5150281

/-- `a : Fin p → ℤ` solves the source's equation with right-hand side `u`. -/
def Solves (p : ℕ) (u : ℤ) (a : Fin p → ℤ) : Prop :=
  Function.Injective a ∧ (∀ i, 1 < |a i|) ∧ ∑ i, a i ^ p = u

example : Solves 3 1 ![-12, 9, 10] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide
example : Solves 5 0 ![27, 84, 110, 133, -144] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide
example : Solves 7 (-1) ![2816, 1348, 1146, -2787, -1951, -1031, -130] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem main :
    ∀ p : ℕ, p.Prime → Odd p →
      ∃ u : ℤ, u ∈ ({-1, 0, 1} : Set ℤ) ∧ ∃ a : Fin p → ℤ, Solves p u a := by
  sorry

end OMA.S_mse_5150281
