import Mathlib

/-!
# OEIS A249709: Barker's recurrence and generating function

Source: https://oeis.org/A249709 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 04 2014), offset 1: Number of length 3+3 0..n arrays with every four
consecutive terms having the maximum of some two terms equal to the minimum of the remaining two
terms. Data: 20, 125, 440, 1153, 2524, 4893, 8688, 14433, 22756, 34397, ... The formula section
states: Empirical: a(n) = (1/15)*n^5 + 2*n^4 + 7*n^3 + 7*n^2 + (44/15)*n + 1. Conjectures from Colin
Barker, Nov 10 2018: (Start) G.f.: x*(20 + 5*x - 10*x^2 - 12*x^3 + 6*x^4 - x^5) / (1 - x)^6. a(n) =
6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* An array is a function x : Fin 6 → Fin (n + 1), the array x(0..5) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `split4` says that the maximum of some 2 of its 4 arguments equals the minimum of the other 2,
  written as one disjunct for each of the 6 choices of the 2 terms; `good x` requires it for each of
  the 3 windows of 4 consecutive terms, x(s..s+3) for s = 0..2.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^6 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..32), all the entry's listed terms.
-/

namespace OMA.S_oeis_a249709

open PowerSeries

/-- The maximum of some two of the four terms a, b, c, d equals the minimum of the other two: one
disjunct for each of the 6 choices of the two terms. -/
def split4 (a b c d : ℕ) : Prop :=
  max a b = min c d ∨ max a c = min b d ∨ max a d = min b c ∨ max b c = min a d ∨ max b d = min a c ∨
    max c d = min a b

/-- Each of the windows x(0..3), x(1..4) and x(2..5) has two terms whose maximum equals the minimum
of the remaining two. -/
def good (x : Fin 6 → ℕ) : Prop :=
  split4 (x 0) (x 1) (x 2) (x 3) ∧
    split4 (x 1) (x 2) (x 3) (x 4) ∧
    split4 (x 2) (x 3) (x 4) (x 5)

instance : DecidablePred good := fun x => by unfold good split4; infer_instance

/-- A249709(n): the number of 0..n arrays x(0..5) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 6 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (20 + 5 * X - 10 * X ^ 2 - 12 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  sorry

end OMA.S_oeis_a249709
