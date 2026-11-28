import Mathlib

/-!
# A147804: Least m coprime to 7 minimizing A007947(m*(7^n-m))

Source: https://oeis.org/A147804
Credit: @xor2k
Sibling of OEIS A147803 (same conjecture wording); statement modelled on the accepted one for that entry.

The entry's text is a remark mentioning the abc conjecture, not a statement of it:
This is related to the abc conjecture: Since m is coprime to 7, it is also coprime to 7^n and thus
to 7^n-m. Thus the squarefree kernel A007947(m*(7^n-m)*7^n) = 7*A007947(m(7^n-m)).

Formalized claim (the abc conjecture itself is NOT formalized): for every `n` and every natural
number `m` coprime to 7 with `m < 7^n`, the squarefree kernel satisfies
`rad(m*(7^n-m)*7^n) = 7 * rad(m*(7^n-m))`.

Conventions: A007947 (squarefree kernel, product of the distinct prime divisors) is Mathlib's
`UniqueFactorizationMonoid.radical` on `ℕ`. The range `m < 7^n` is the range in which `7^n - m`
is a positive number as in the entry (the candidates `m` of the sequence lie in it); with it the
natural-number subtraction `7^n - m` is exact. Coprimality with 7 forces `m ≥ 1` and hence `n ≥ 1`.
-/

namespace OMA.S_oeis_a147804

open UniqueFactorizationMonoid

/-- For `m` coprime to 7 with `m < 7^n`: `rad(m*(7^n-m)*7^n) = 7 * rad(m*(7^n-m))`. -/
theorem main :
    ∀ n m : ℕ, Nat.Coprime m 7 → m < 7 ^ n →
      radical (m * (7 ^ n - m) * 7 ^ n) = 7 * radical (m * (7 ^ n - m)) := by
  sorry

end OMA.S_oeis_a147804
