import OMAReductions.R_Erdos101_erdos_101_R3
import Mathlib

-- Reduction Erdos101.erdos_101.R3.H1.R1 of step Erdos101.erdos_101.R3.H1
-- Credit: @PetrouilFan

/-!
# Counting four-point lines apart from the density extraction

The step asks for a density extraction from a finite planar set with many
four-point lines. That extraction is the hard part. The elementary counting
fact that the four-point lines through any fixed point use pairwise disjoint
triples of the other points is already proved upstream in the merged
reduction for this same problem; it is isolated here as H2 and is available
to the extraction as a premise. H1 asks for the extraction under that premise
and with a uniform positive slack in the final four-point-line density, so H1
is strictly stronger than the step. The glue applies H1, discharges its
counting premise from H2, and then drops the slack. Neither hypothesis
restates the target and neither depends on an answer.
-/

namespace OMA.R_Erdos101_erdos_101_R3_H1_R1

open EuclideanGeometry
open scoped Classical

/-- Slack-buffered density extraction assuming the four-point-line count.
For every positive s there are a positive slack a and a threshold N such
that any sufficiently large set with no five collinear points and with at
least s times its size in four-point lines passes to a positive density
subset T together with a cheap anchor set B that generated T in one
intersection step, retaining the four-point-line density with the extra
uniform slack a. -/
def H1 : Prop :=
  ∀ s : ℕ, 0 < s → ∃ a N : ℕ, 0 < a ∧ ∀ S : Finset ℝ², N ≤ S.card →
    NonCollinearFor 5 (S : Set ℝ²) →
    (∀ A : Finset (AffineSubspace ℝ ℝ²),
      (∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) →
      12 * A.card ≤ S.card * (S.card - 1)) →
    S.card ^ 2 ≤ s * (linesWithPointsFor 4 (S : Set ℝ²)).ncard →
    ∃ T B : Finset ℝ², T ⊆ S ∧ B ⊆ T ∧ S.card ≤ 4 * s * T.card ∧
      B.card ^ 2 ≤ 4096 * s ^ 3 * T.card ∧
      T.card ^ 2 + a ≤ 4 * s * (linesWithPointsFor 4 (T : Set ℝ²)).ncard ∧
      ∀ p ∈ T, p ∈ B ∨ ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, ∃ w ∈ B,
        x ≠ y ∧ z ≠ w ∧ line[ℝ,x,y] ≠ line[ℝ,z,w] ∧
        p ∈ line[ℝ,x,y] ∧ p ∈ line[ℝ,z,w]

/-- The upstream-proved count: four-point lines through a fixed point use
pairwise disjoint triples, hence a family of them has size at most one
twelfth of the number of ordered pairs of ambient points. -/
def H2 : Prop :=
  ∀ (S : Finset ℝ²) (A : Finset (AffineSubspace ℝ ℝ²)),
    (∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) →
    12 * A.card ≤ S.card * (S.card - 1)

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R3.H1 := by
  intro hExtract hCount
  intro s hs
  obtain ⟨a, N, ha, hStep⟩ := hExtract s hs
  refine ⟨N, ?_⟩
  intro S hNS hcap hdense
  obtain ⟨T, B, hTS, hBT, hsize, hcheap, hcount, hgen⟩ :=
    hStep S hNS hcap (fun A hA => hCount S A hA) hdense
  refine ⟨T, B, hTS, hBT, hsize, hcheap, ?_, hgen⟩
  exact (Nat.le_add_right _ a).trans hcount

end OMA.R_Erdos101_erdos_101_R3_H1_R1
