import Mathlib

/-!
# Erdős Problem 634

Source: https://www.erdosproblems.com/634
Credit: @OrangeHeadz

## The problem, as the source states it

Find all n such that there is at least one triangle which can be cut into n congruent triangles.

The source records: every square has the property (any triangle will do); Soifer showed that
2n^2, 3n^2, 6n^2 and n^2 + m^2 have it; Beeson showed that 7 and 11 do not. It then says that
it is possible that any prime of the form 4n+3 does not have this property, and that in
particular it is not known whether 19 has it.

## What `main` states, and why

The source asks for a set and gives no conjectured description of it, so the question as posed
is not a single closed proposition. The only conjecture the source itself puts forward is the one
about primes of the form 4n+3, and that is what `main` states: no prime p with p % 4 = 3,
other than p = 3, has the property. This is the open sub-question named by the source (it
contains the case 19), not the full classification.

The exception p = 3 is forced by the source itself. Read literally, the sentence covers 3,
which is a prime of the form 4n+3; but the same paragraph lists 3n^2 as having the property,
and n = 1 gives 3 (join the centre of an equilateral triangle to its three vertices). So the
literal sentence is false at 3 and the intended range is the primes 7, 11, 19, 23, ...

Literature: Beeson and Roşu, Tiling a triangle into a prime number of congruent triangles,
arXiv:2607.23453, claim that a prime N has the property exactly when N = 2, N = 3 or
N % 4 = 1, which would settle `main` positively. It is a preprint.

## Conventions

* The plane is `EuclideanSpace ℝ (Fin 2)`.
* A triangle is an `Affine.Triangle`: three affinely independent points, so it is not degenerate.
  The region it occupies is `Affine.Simplex.closedInterior` (barycentric weights in [0, 1], the
  closed triangle), and its inside is `Affine.Simplex.interior` (weights in (0, 1), the open
  triangle).
* Cut into n triangles means: n triangles whose closed regions cover the big closed triangle
  exactly and whose open insides are pairwise disjoint. The pieces need not meet edge to edge.
* Congruent is Mathlib's `Congruent` on the vertex families: all pairwise distances agree. This
  compares vertices in the order they are listed, but each piece is chosen existentially, so its
  vertices may be listed in whatever order makes the match; nothing is lost. Mirror images count
  as congruent, as usual (the altitude of an isosceles triangle cuts it into 2 congruent halves).
* `IsCuttable` is the definition of the same name in formal-conjectures, file
  FormalConjectures/ErdosProblems/633.lean (the neighbouring problem, same notion of cutting),
  with its notation unfolded.
* Sanity of the definition: n = 0 never has the property (an empty union is not a triangle) and
  n = 1 always has it (the triangle itself).
-/

namespace OMA.S_erdos_634

/-- The triangle `T` can be cut into `n` congruent triangles: there are `n` triangles in the
plane, any two of them congruent, with pairwise disjoint interiors, whose closed regions have
union exactly the closed region of `T`. -/
def IsCuttable (n : ℕ) (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ Ts : Fin n → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
    (∀ i j, Congruent (Ts i).points (Ts j).points) ∧
      Pairwise (fun i j ↦ Disjoint (Ts i).interior (Ts j).interior) ∧
      ⋃ i, (Ts i).closedInterior = T.closedInterior

/-- The property of Erdős Problem 634: there is at least one triangle which can be cut into
`n` congruent triangles. -/
def HasProperty (n : ℕ) : Prop :=
  ∃ T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), IsCuttable n T

/-- No prime of the form 4n+3 other than 3 has the property. -/
theorem main : ∀ p : ℕ, p.Prime → p % 4 = 3 → p ≠ 3 → ¬ HasProperty p := by
  sorry

end OMA.S_erdos_634
