import Mathlib

/-!
# A037084: Positive integers not going to 1 under iterations of the map in A001281: n->3n-1 if n odd, n->n/2 if n even.

Source: https://oeis.org/A037084
Credit: @luciusacarr

The entry's comments record two conjectures. `main` states both, as a conjunction, in the order
the source gives them.

Conjecture 1 (Benoit Cloitre, May 14 2002). For any x, the iterated process "x -> 3x-1 if x is
odd, x -> x/2 if x is even" leads to one of the following three cycles: (1, 2),
(5, 14, 7, 20, 10), (41, 122, 61, 182, 91, 272, 136, 68, 34, 17, 50, 25, 74, 37, 110, 55, 164, 82).
The source adds: up to at least 100000000, every number reaches 1, 5 or 17.

Conjecture 2 (M. F. Hasler, Nov 26 2007). The sequence is the complement (in N*) of A039500 and
the union of A039501 and A039502 (the union part is marked as conjectured).

Reading of the source:
* `f` is the map of A001281 on the natural numbers: `f n = n / 2` for even `n` and
  `f n = 3 * n - 1` for odd `n` (for odd `n ≥ 1`, `3 * n - 1` has no truncation).
* "for any x" ranges over the positive integers (the sequence and A039500-A039502 live in N*;
  `0` is a fixed point of `f` and is excluded).
* Each of the three cycles is closed under `f` and contains `1`, `5` or `17` respectively, so the
  orbit of `x` leads to one of them iff some iterate `f^[k] x` equals `1`, `5` or `17`.
* A039500, A039501, A039502 are the positive integers whose orbit reaches `1`, `5`, `17`
  respectively. The sequence A037084 itself is the set of positive integers whose orbit never
  reaches `1`. Its being the complement of A039500 holds by definition; the conjectured part is
  that every term lies in A039501 or A039502, i.e. that its orbit reaches `5` or `17`.
-/

namespace OMA.S_oeis_a037084

/-- The map of A001281: `n ↦ n / 2` if `n` is even, `n ↦ 3n - 1` if `n` is odd. -/
def f (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n - 1

/-- The orbit of `n` under `f` reaches `m`. -/
def Reaches (n m : ℕ) : Prop := ∃ k : ℕ, f^[k] n = m

theorem main :
    -- Conjecture 1: every positive integer reaches one of the cycles through 1, 5 and 17.
    (∀ x : ℕ, 0 < x → Reaches x 1 ∨ Reaches x 5 ∨ Reaches x 17) ∧
    -- Conjecture 2: every term of A037084 (a positive integer not reaching 1) lies in
    -- A039501 ∪ A039502 (reaches 5 or reaches 17).
    (∀ x : ℕ, 0 < x → ¬ Reaches x 1 → Reaches x 5 ∨ Reaches x 17) := by
  sorry

end OMA.S_oeis_a037084
