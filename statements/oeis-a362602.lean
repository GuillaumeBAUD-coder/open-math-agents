import Mathlib

/-!
# A362602: Integers in the interval [Pi*k - 1/k, Pi*k + 1/k] for some k > 0 that are numerators of convergents to 2*Pi

Source: https://oeis.org/A362602
Credit: @xor2k
Sibling of OEIS A265735 (same conjecture wording); statement modelled on the accepted one for that entry.

Conjecture (OEIS A362602): the sequence is infinite.

Conventions: the sequence is the set of integers `m` such that
* there exists a positive integer `k` with `m` in the closed interval
  `[pi * k - 1 / k, pi * k + 1 / k]` (exactly as in A265735: `k` ranges over positive natural
  numbers, encoded by `1 ≤ k`, and the endpoint condition is written as `|pi * k - m| ≤ 1 / k`), and
* `m` is the numerator of a convergent to `2 * pi`: there is `n` with
  `m = ((2 * pi).convergent n).num`. Here `Real.convergent ξ n : ℚ` is Mathlib's `n`-th
  convergent of the simple continued fraction of `ξ` (it agrees with
  `(GenContFract.of ξ).convs n`), and `Rat.num` is the numerator in lowest terms, which is the
  usual convergent numerator `p_n` since `p_n` and `q_n` are coprime.

The offset of the OEIS sequence is 1; the sequence lists this set in increasing order.
-/

namespace OMA.S_oeis_a362602

/-- `m` lies in `[pi * k - 1 / k, pi * k + 1 / k]` for some positive integer `k`, and `m` is the
numerator of a convergent to `2 * pi`. -/
def IsTerm (m : ℤ) : Prop :=
  (∃ k : ℕ, 1 ≤ k ∧ |Real.pi * (k : ℝ) - (m : ℝ)| ≤ 1 / (k : ℝ)) ∧
    ∃ n : ℕ, ((2 * Real.pi).convergent n).num = m

/-- The sequence of integers in `[pi * k - 1 / k, pi * k + 1 / k]`, for some `k > 0`, that are
numerators of convergents to `2 * pi`, is infinite. -/
theorem main : Set.Infinite {m : ℤ | IsTerm m} := by
  sorry

end OMA.S_oeis_a362602
