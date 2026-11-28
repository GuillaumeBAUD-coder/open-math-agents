import FormalConjectures.ErdosProblems.«668»
import Mathlib

/-!
# Reduction of Erdős Problem 668, part (i): rigid vertices and the sliding (flex) lemma

The target asks: for every `m`, all sufficiently large `n` admit `m` pairwise non-congruent
`n`-point maximisers of the unit-distance count `unitDistNum`, the maximum being
`Erdos90.maxUnitDistances n = sSup (Erdos90.unitDistanceCounts n)` (Erdős 90, open).

This file splits the target into two independent statements.

* `H1` — the open core, a structural existence claim about a *single* maximiser: for all
  sufficiently large `n` some `n`-point maximiser contains a point `p` whose unique
  unit-distance partner inside the configuration is one point `q` (a rigid vertex of unit
  degree exactly `1`).  This is the only place where the unknown value `maxUnitDistances n` is
  used; it says one optimal configuration has a rigid vertex.

* `H2` — the flex (sliding) lemma, a purely geometric statement that never mentions
  `maxUnitDistances` or maximisers: if `A` is an `n`-point set and `p ∈ A` has the unique unit
  partner `q ∈ A`, with at least two points left after deleting `p`, then for every `m` there
  are `m` pairwise non-congruent `n`-point sets whose unit-distance count equals that of `A`.
  Reason: sliding `p` along the circle of radius `1` about `q` keeps `dist p q = 1` and leaves
  every other pair untouched, so the count cannot drop below that of `A`; applied to a
  maximiser it therefore cannot rise either, so every slid position is again a maximiser.
  Positions giving congruent sets are only finitely many, because an isometry of the plane is
  determined up to two choices by the images of two distinct points.

`main` assembles the two: every sufficiently large `n` that carries a rigid vertex has, for
every `m`, `m` pairwise non-congruent maximisers — exactly the target.

The file also proves, unconditionally, that `maxUnitDistances n` is attained by an `n`-point set
(`attainment`), so the target is not vacuous and its `m = 1` instance holds outright.
-/

open Filter
open scoped EuclideanGeometry

namespace OMA.R_Erdos668_erdos_668_parts_i_R1

open Erdos90

/-- There are `n`-point finsets in the plane: the points `k • (1, 0)`, `k < n`. -/
lemma exists_finset_card_eq (n : ℕ) : ∃ A : Finset ℝ², A.card = n := by
  refine ⟨(Finset.range n).image
    (fun k : ℕ => WithLp.toLp 2 (fun _ : Fin 2 => (k : ℝ))), ?_⟩
  rw [Finset.card_image_of_injective]
  · simp
  intro a b h
  have h2 : (fun _ : Fin 2 => ((a : ℝ))) = (fun _ : Fin 2 => ((b : ℝ))) :=
    WithLp.toLp_injective 2 h
  simpa using congrFun h2 (0 : Fin 2)

/-- The set of unit-distance counts of `n`-point sets is non-empty. -/
lemma unitDistanceCounts_nonempty (n : ℕ) : (unitDistanceCounts n).Nonempty := by
  obtain ⟨A, hA⟩ := exists_finset_card_eq n
  exact ⟨unitDistNum A, A, hA, rfl⟩

/-- **Attainment.**  For every `n` the maximal unit-distance count `maxUnitDistances n` is
realised by an `n`-point set: the counts are bounded above, so the supremum of the non-empty
set of counts is itself one of them. -/
lemma attainment (n : ℕ) :
    ∃ A : Finset ℝ², A.card = n ∧ unitDistNum A = maxUnitDistances n := by
  have h := Nat.sSup_mem (unitDistanceCounts_nonempty n) (unitDistanceCounts_BddAbove n)
  simpa [maxUnitDistances, unitDistanceCounts] using h

/-- `maxUnitDistances n` is an upper bound for the unit-distance count of `n`-point sets. -/
lemma unitDistNum_le_maxUnitDistances (A : Finset ℝ²) :
    unitDistNum A ≤ maxUnitDistances A.card :=
  le_csSup (unitDistanceCounts_BddAbove A.card) ⟨A, rfl, rfl⟩

/-- **H1 (open core).**  For all sufficiently large `n`, some `n`-point maximiser of the
unit-distance count has a vertex `p` whose only unit-distance partner inside the configuration
is a single point `q`.  Such a `p` can be slid around `q` (see `H2`). -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ A : Finset ℝ²,
    A.card = n ∧ unitDistNum A = maxUnitDistances n ∧
      ∃ p ∈ A, ∃! q, q ∈ A ∧ dist p q = 1

/-- **H2 (flex / sliding lemma).**  Let `A` be an `n`-point set and `p ∈ A` a point whose only
unit-distance partner inside `A` is `q ∈ A`, with at least two points left after deleting `p`.
Then for every `m` there are `m` pairwise non-congruent `n`-point sets whose unit-distance
count is exactly that of `A`.

The statement never mentions `maxUnitDistances`: applied to a maximiser it yields `m` pairwise
non-congruent maximisers, applied to any other set `m` pairwise non-congruent sets with the same
number of unit distances. -/
def H2 : Prop :=
  ∀ (m : ℕ) (n : ℕ) (A : Finset ℝ²) (p q : ℝ²), A.card = n → p ∈ A → q ∈ A →
    2 ≤ (A.erase p).card → dist p q = 1 →
    (∀ r ∈ A, r ≠ p → dist p r = 1 → r = q) →
      ∃ X : Fin m → Finset ℝ²,
        (∀ i, (X i).card = n ∧ unitDistNum (X i) = unitDistNum A) ∧
          ∀ i j, i ≠ j → ¬ ∃ f : ℝ² ≃ᵢ ℝ², f '' (X i) = X j

theorem main : H1 → H2 → type_of% @Erdos668.erdos_668.parts.i := by
  intro h1 h2 m
  filter_upwards [h1, eventually_ge_atTop (3 : ℕ)] with n hn hn3
  obtain ⟨A, hcard, hmax, p, hpA, q, hq, huniq⟩ := hn
  have huniq' : ∀ r ∈ A, r ≠ p → dist p r = 1 → r = q := fun r hr hrp hd =>
    huniq r ⟨hr, hd⟩
  have htwo : 2 ≤ (A.erase p).card := by
    rw [Finset.card_erase_of_mem hpA]
    omega
  obtain ⟨X, hX, hX'⟩ := h2 m n A p q hcard hpA hq.1 htwo hq.2 huniq'
  refine ⟨X, fun i => ⟨(hX i).1, (hX i).2.trans hmax⟩, ?_⟩
  exact fun i j hij hcong => hX' i j hij hcong

end OMA.R_Erdos668_erdos_668_parts_i_R1
