import Mathlib

/-!
# Questions about density of `{(k + 1/2)^n}` in `[0,1]`

Source: https://math.stackexchange.com/questions/4447984
Credit: @JeremyDevs

Question (Math StackExchange 4447984, 2022). Here `{x}` denotes the fractional part of `x`.
Are there any known positive integers `k` for which the set `{ {(k + 1/2)^n} : n ∈ ℕ }` is known
to be dense in `[0,1]`? (The asker notes that this is an open problem for `k = 1` and suspects
it is open for every `k`.) If the answer to the first question is no, then is the set
`{ {(k + 1/2)^n} : n, k ∈ ℕ }` known to be dense in `[0,1]`?

The first question asks what is known (and is the open problem); the second question is a
mathematical statement, and the answer at the source proves it: yes, the set is dense. For
`n = 2m` and `k = 2^(m-1) t` all terms of the binomial expansion of `(k + 1/2)^n` of index at
least `2` are integers, so `{(k + 1/2)^n} = {2^(-2m) + m t 2^(-m+1)}`, and as `t` varies these
numbers come within `m 2^(-m+1)` of every point of `[0,1]`. `main` states this positive answer to
the second question.

Conventions:
* `n` and `k` range over the positive integers (`0 < n`, `0 < k` in `ℕ`), the smaller of the two
  usual readings of `ℕ`, which gives the stronger statement.
* The fractional part is `Int.fract` on `ℝ`.
* "Dense in `[0,1]`" is `Set.Icc 0 1 ⊆ closure S` (the set `S` itself lies in `[0,1)`).
-/

namespace OMA.S_mse_4447984

/-- The fractional parts of the numbers `(k + 1/2)^n`, over all positive integers `n` and `k`,
are dense in `[0,1]`. -/
theorem main :
    Set.Icc (0 : ℝ) 1 ⊆
      closure {x : ℝ | ∃ n k : ℕ, 0 < n ∧ 0 < k ∧ x = Int.fract (((k : ℝ) + 1 / 2) ^ n)} := by
  sorry

end OMA.S_mse_4447984
