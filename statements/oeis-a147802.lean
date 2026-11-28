import Mathlib

/-!
# A147802: Least m coprime to 3 minimizing A007947(m*(3^n-m))

Source: https://oeis.org/A147802
Credit: @xor2k
Sibling of OEIS A147803 (same conjecture wording); statement modelled on the accepted one for that entry.

The entry's text is a remark mentioning the abc conjecture, not a statement of it:
Related to the abc conjecture: Since m is coprime to 3, it is also coprime to 3^n and thus to
3^n-m. Thus A007947(m*(3^n-m)*3^n) = 3*A007947(m(3^n-m)).

Formalized claim (the abc conjecture itself is NOT formalized): for every `n` and every natural
number `m` coprime to 3 with `m < 3^n`, the squarefree kernel satisfies
`rad(m*(3^n-m)*3^n) = 3 * rad(m*(3^n-m))`.

Conventions: A007947 (squarefree kernel, product of the distinct prime divisors) is Mathlib's
`UniqueFactorizationMonoid.radical` on `ℕ`. The range `m < 3^n` is the range in which `3^n - m`
is a positive number as in the entry (the candidates `m` of the sequence lie in it); with it the
natural-number subtraction `3^n - m` is exact. Coprimality with 3 forces `m ≥ 1` and hence `n ≥ 1`.
-/

namespace OMA.S_oeis_a147802

open UniqueFactorizationMonoid

/-- For `m` coprime to 3 with `m < 3^n`: `rad(m*(3^n-m)*3^n) = 3 * rad(m*(3^n-m))`. -/
theorem main :
    ∀ n m : ℕ, Nat.Coprime m 3 → m < 3 ^ n →
      radical (m * (3 ^ n - m) * 3 ^ n) = 3 * radical (m * (3 ^ n - m)) := by
  sorry

end OMA.S_oeis_a147802
