import Mathlib

/-!
# A070864: a(1) = a(2) = 1; a(n) = 2 + a(n - a(n-1)).

Source: https://oeis.org/A070864
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A070864 (John W. Layman, May 21 2002): Let
a(1)=a(2)=1 and for n > 2 let k = floor(sqrt(n+1))-1 and d=n-k(k+2). Then, if (d is 0, 1, or 2)
OR (d=0 mod 2), a(n)=2k+1; otherwise a(n)=2k+3.

Conventions:
* The sequence has offset 1: 1, 1, 3, 3, 3, 5, 3, 5, 5, 5, 7, 5, 7, 5, 7, 7, 7, 9, ...
* The recursion a(n) = 2 + a(n - a(n-1)) refers to the term with index n - a(n-1), which is a
  valid earlier index only when 0 < a(n-1) < n. To have a total definition, `a` is defined by
  well-founded recursion with a guard: for n ≥ 3, `a n = 2 + a (n - a (n-1))` if
  `0 < a (n-1)` and `a (n-1) < n`, and the placeholder value 0 otherwise. The placeholder
  branch is never taken (every term is a positive odd number at most its index, as the
  statement itself implies), so `a` is the OEIS sequence. `a 0 = 0` is a placeholder for the
  unused index 0.
* floor(sqrt(n+1)) is `Nat.sqrt (n + 1)`. For n > 2 one has k ≥ 1 and k*(k+2) = (k+1)^2 - 1 ≤ n,
  so the natural-number subtractions defining k and d are genuine.
* The asymptotic remark that follows the conjecture in the entry (a(n) ~ floor(sqrt(n+1)), which
  the entry itself says only appears to hold) is not part of the statement.
-/

namespace OMA.S_oeis_a070864

/-- A070864 (offset 1): a(1) = a(2) = 1, a(n) = 2 + a(n - a(n-1)). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 =>
    if h : 0 < a (n + 2) ∧ a (n + 2) < n + 3 then 2 + a (n + 3 - a (n + 2)) else 0
decreasing_by all_goals omega

/-- Layman's conjecture: with `k = floor(sqrt(n+1)) - 1` and `d = n - k*(k+2)`, a(n) = 2k+1 if
`d ∈ {0, 1, 2}` or `d` is even, and a(n) = 2k+3 otherwise. -/
theorem main : ∀ n : ℕ, 2 < n →
    let k := Nat.sqrt (n + 1) - 1
    let d := n - k * (k + 2)
    a n = if (d = 0 ∨ d = 1 ∨ d = 2) ∨ d % 2 = 0 then 2 * k + 1 else 2 * k + 3 := by
  sorry

end OMA.S_oeis_a070864
