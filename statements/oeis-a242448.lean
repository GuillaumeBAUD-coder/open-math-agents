import Mathlib

/-!
# A242448: Distinct linear polynomials in a recursively generated array.

Source: https://oeis.org/A242448
Name: Number of distinct linear polynomials `b + c*x` in row `n` of the array
generated as in Comments.

Comments / Mathematica definition.  Put `f1(x) = 2*x`, `f2(x) = 1 - x`,
`f3(x) = 2 - x`, `g(1) = {x}`, and for `n > 1`

    b(n) = union(f1(g(n-1)), f2(g(n-1)), f3(g(n-1)))
    h(n) = union(h(n-1), g(n-1))
    g(n) = b(n) \ intersect(b(n), h(n))

where `h(1) = g(1)`; here `b(n) \ intersect(b(n), h(n))` is the set of new
polynomials produced at step `n`.  The sequence `a(n)` is the number of
elements of `g(n)`.  Row `n` of the array is then the elements of `g(n)`
arranged by the total order `<<` from the Comments (first by the coefficient
`c`, then by the constant `b`), so the ordering does not affect the count.

Conjecture (FORMULA): `a(n) = 2*a(n-1) - a(n-3)` for `n >= 6`.

Credit: @bear20252026 (agent: catpaw, model CatPaw)

Linear polynomials `b + c*x` are represented as the pair `(b, c) : Z × Z`.
The generation rule above was simulated independently and reproduces the
listed terms `1, 3, 6, 12, 22, ..., 635618` for `1 <= n <= 26`, and the
recurrence was checked for `6 <= n <= 26`.  The body stays `sorry`; a person
reviews the translation before merging.
-/

namespace OMA.S_oeis_a242448

/-- A linear polynomial `b + c * x`, represented by the pair `(b, c)`. -/
abbrev Poly := ℤ × ℤ

def f1 (p : Poly) : Poly := (2 * p.1, 2 * p.2)

def f2 (p : Poly) : Poly := (1 - p.1, -p.2)

def f3 (p : Poly) : Poly := (2 - p.1, -p.2)

/-- One step of the recursion: `b` is the set of all three images of the
previous row `g`, `h'` accumulates all rows seen so far, and the next row is
`b \ h'`, i.e. the newly produced polynomials. -/
def step (s : Finset Poly × Finset Poly) : Finset Poly × Finset Poly :=
  let g := s.1
  let h := s.2
  let b := (g.image f1) ∪ (g.image f2) ∪ (g.image f3)
  let h' := h ∪ g
  (b \ h', h')

/-- The initial state `(g(1), h(1)) = ({x}, {x})`. -/
def init : Finset Poly × Finset Poly := ({(0, 1)}, {(0, 1)})

/-- The `n`-th row `g(n)` of the array. -/
def row (n : ℕ) : Finset Poly :=
  (Function.iterate step (n - 1) init).1

/-- `a(n)`, the number of distinct linear polynomials in row `n`. -/
def a242448 (n : ℕ) : ℕ := (row n).card

theorem main :
    ∀ n : ℕ, 6 ≤ n →
      a242448 n = 2 * a242448 (n - 1) - a242448 (n - 3) := by
  sorry

end OMA.S_oeis_a242448
