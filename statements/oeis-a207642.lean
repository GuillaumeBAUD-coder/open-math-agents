import Mathlib

/-!
# A207642: Expansion of g.f.: Sum_{n>=0} x^n * Product_{k=0..n-1} (1 + x^(n+k)).

Source: https://oeis.org/A207642
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

## The conjecture

OEIS A207642, offset 0, COMMENTS line:

> Conjecture: a(n) is the number of partitions p of n into distinct parts such that
> max(p) <= 1 + 2*min(p), for n >= 1 (as in the Mathematica program at A241061).
> - Clark Kimberling, Apr 16 2014

## Modelling choices

* `a n` is the coefficient of `x^n` in `Sum_{k>=0} x^k * Product_{j=0..k-1} (1 + x^(k+j))`.
  The summand with index `k` is `x^k` times a polynomial with constant term 1, so it has no
  monomial of degree `< k`. Therefore the coefficient of `x^n` in the full series equals the
  coefficient of `x^n` in the finite sum over `k = 0..n`, computed in `Polynomial ℕ`. This
  definition reproduces the DATA line (`1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 4, ...`).
* A partition of `n` into distinct parts is a `p : Nat.Partition n` with `p.parts.Nodup`.
  For `n ≥ 1` the partition is nonempty, and `max(p) <= 1 + 2*min(p)` is equivalent to
  `x ≤ 1 + 2*y` for all parts `x, y`, which is how it is written here (so that no
  `max`/`min` of a multiset needs to be defined).
* The identity is stated for every `n ≥ 1`, as in the source.
-/

namespace OMA.S_oeis_a207642

open Polynomial

/-- A207642: coefficient of `x^n` in `Sum_{k>=0} x^k * Product_{j=0..k-1} (1 + x^(k+j))`
(the summands with `k > n` do not contribute to this coefficient). -/
noncomputable def a (n : ℕ) : ℕ :=
  (∑ k ∈ Finset.range (n + 1), (X : ℕ[X]) ^ k * ∏ j ∈ Finset.range k, (1 + X ^ (k + j))).coeff n

/-- The number of partitions of `n` into distinct parts with `max ≤ 1 + 2 * min`. -/
def b (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n =>
    p.parts.Nodup ∧ ∀ x ∈ p.parts, ∀ y ∈ p.parts, x ≤ 1 + 2 * y)).card

/-- Clark Kimberling's conjecture (Apr 16 2014): `a(n) = b(n)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = b n := by
  sorry

end OMA.S_oeis_a207642
