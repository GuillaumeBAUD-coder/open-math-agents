import OMAStatements.S_oeis_a000009

/-!
# Reduction oeis-a000009.R1 of A000009 (two conjectures of Zhi-Wei Sun)

Credit: @Jwolf52

The target is a conjunction of a representation conjecture and three non-divisibility
conjectures. This file splits it into four independent steps:

* `H1`: every positive integer is the sum of a finite *set* of strict partition numbers,
  pairwise non-dividing (the representation conjecture, restated with `Finset`, which is
  easier to work with than `Fin k → ℕ`).
* `H2`, `H3`, `H4`: for `n > 7`, `q(n)` does not divide `p(n)`, `p(n) - 1`, `p(n) + 1`.

Proved unconditionally here:
* `rep_of_finset`: a `Finset` representation gives a representation in the target's form.
* `extend_cover`: the greedy step behind the finite verification of note #43523. If the
  subset sums of `S` cover `[L, U]` and `a ∉ S` with `a ≤ U + 1 - L`, then the subset sums
  of `insert a S` cover `[L, U + a]`. (Adding the divisibility side conditions on `a` keeps
  the set an antichain, so a proof of `H1` reduces to an infinite supply of suitable `a`.)
-/

namespace OMA.R_oeis_a000009_R1

open OMA.S_oeis_a000009

/-- The representation conjecture, in `Finset` form. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → ∃ T : Finset ℕ,
    (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧
    (∑ x ∈ T, x) = n

/-- `q(n)` does not divide `p(n)` for `n > 7`. -/
def H2 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ strictPartitionCount n ∣ partitionCount n

/-- `q(n)` does not divide `p(n) - 1` for `n > 7`. -/
def H3 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ strictPartitionCount n ∣ partitionCount n - 1

/-- `q(n)` does not divide `p(n) + 1` for `n > 7`. -/
def H4 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ strictPartitionCount n ∣ partitionCount n + 1

/-- A finite antichain of strict partition numbers, listed as a `Fin k`-indexed family. -/
theorem rep_of_finset (T : Finset ℕ)
    (hq : ∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m)
    (hanti : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) :
    ∃ k : ℕ, ∃ terms : Fin k → ℕ,
      (∀ i, ∃ m : ℕ, 0 < m ∧ terms i = strictPartitionCount m) ∧
      (∑ i, terms i) = ∑ x ∈ T, x ∧
      (∀ i j, i ≠ j → ¬ terms i ∣ terms j) := by
  let e : T ≃ Fin T.card := T.equivFin
  refine ⟨T.card, fun i => (e.symm i : ℕ), ?_, ?_, ?_⟩
  · intro i
    exact hq _ (e.symm i).2
  · rw [Equiv.sum_comp e.symm (fun x : T => (x : ℕ))]
    exact Finset.sum_coe_sort T (fun x => x)
  · intro i j hij
    apply hanti _ (e.symm i).2 _ (e.symm j).2
    intro h
    exact hij (e.symm.injective (Subtype.ext h))

/-- The greedy extension step: adding a new element `a ≤ U + 1 - L` to a set whose subset
sums cover `[L, U]` yields a set whose subset sums cover `[L, U + a]`. -/
theorem extend_cover (S : Finset ℕ) (a L U : ℕ) (ha : a ∉ S)
    (hcov : ∀ n, L ≤ n → n ≤ U → ∃ T ⊆ S, (∑ x ∈ T, x) = n)
    (hle : a ≤ U + 1 - L) :
    ∀ n, L ≤ n → n ≤ U + a → ∃ T ⊆ insert a S, (∑ x ∈ T, x) = n := by
  intro n hLn hnU
  by_cases h : n ≤ U
  · obtain ⟨T, hT, hs⟩ := hcov n hLn h
    exact ⟨T, hT.trans (Finset.subset_insert a S), hs⟩
  · push_neg at h
    obtain ⟨T, hT, hs⟩ := hcov (n - a) (by omega) (by omega)
    have haT : a ∉ T := fun h' => ha (hT h')
    refine ⟨insert a T, Finset.insert_subset_insert a hT, ?_⟩
    rw [Finset.sum_insert haT, hs]
    omega

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a000009.main := by
  intro h1 h2 h3 h4
  refine ⟨?_, fun n hn => ⟨h2 n hn, h3 n hn, h4 n hn⟩⟩
  intro n hn
  obtain ⟨T, hq, hanti, hsum⟩ := h1 n hn
  obtain ⟨k, terms, hterms, hs, hdiv⟩ := rep_of_finset T hq hanti
  exact ⟨k, terms, hterms, hs.trans hsum, hdiv⟩

end OMA.R_oeis_a000009_R1
