import Mathlib

/-!
# OEIS A250337: Barker's recurrence and generating function

Source: https://oeis.org/A250337 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 19 2014), offset 1: Number of length 1+5 0..n arrays with every six
consecutive terms having the maximum of some three terms equal to the minimum of the remaining three
terms. Data: 44, 429, 2056, 6785, 17796, 39949, 80144, 147681, 254620, 416141, ... The formula
section states: Empirical: a(n) = 3*n^5 + 10*n^4 + 15*n^3 + 11*n^2 + 4*n + 1. Conjectures from Colin
Barker, Nov 12 2018: (Start) G.f.: x*(44 + 165*x + 142*x^2 + 4*x^3 + 6*x^4 - x^5) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* An array is a function x : Fin 6 → Fin (n + 1), the array x(0..5) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `split33` says that the maximum of some 3 of its 6 arguments equals the minimum of the other 3,
  written as one disjunct for each of the 20 choices of the 3 terms; `good x` requires it for the
  whole array x(0..5).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^6 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..28), all the entry's listed terms.
-/

namespace OMA.S_oeis_a250337

open PowerSeries

/-- The maximum of some three of the six terms a, b, c, d, e, f equals the minimum of the other
three: one disjunct for each of the 20 choices of the three terms. -/
def split33 (a b c d e f : ℕ) : Prop :=
  max (max a b) c = min (min d e) f ∨ max (max a b) d = min (min c e) f ∨ max (max a b) e = min (min
    c d) f ∨ max (max a b) f = min (min c d) e ∨ max (max a c) d = min (min b e) f ∨ max (max a c)
    e = min (min b d) f ∨ max (max a c) f = min (min b d) e ∨ max (max a d) e = min (min b c) f ∨
    max (max a d) f = min (min b c) e ∨ max (max a e) f = min (min b c) d ∨ max (max b c) d = min
    (min a e) f ∨ max (max b c) e = min (min a d) f ∨ max (max b c) f = min (min a d) e ∨ max (max b
    d) e = min (min a c) f ∨ max (max b d) f = min (min a c) e ∨ max (max b e) f = min (min a c) d ∨
    max (max c d) e = min (min a b) f ∨ max (max c d) f = min (min a b) e ∨ max (max c e) f = min
    (min a b) d ∨ max (max d e) f = min (min a b) c

/-- Some three terms of x(0..5) have maximum equal to the minimum of the remaining three. -/
def good (x : Fin 6 → ℕ) : Prop :=
  split33 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

instance : DecidablePred good := fun x => by unfold good split33; infer_instance

/-- A250337(n): the number of 0..n arrays x(0..5) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 6 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (44 + 165 * X + 142 * X ^ 2 + 4 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  sorry

end OMA.S_oeis_a250337
