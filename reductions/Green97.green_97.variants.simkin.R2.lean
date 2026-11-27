import FormalConjectures.GreensOpenProblems.«97»

/-!
Reduction of Simkin's theorem following Simkin, Adv. Math. 427 (2023),
Theorems 1.1 and 2.24, Claim 3.4, Lemma 3.5, and Section 6.
S consists of the entropy scores of finite square step densities.
A is the density on each cell, rather than its mass. The two orientations
give complementary diagonal densities d at successive knots, interpolated
affinely between knots. The cancellation of the uniform reference terms
leaves the constant -3 in this normalization.

H1 is the variational counting principle without a numerical approximation.
H2 is a uniform upper certificate for all finite step densities, without
a board-counting assertion. H3 is a single finite lower witness, for which
the 12 by 12 matrix in Claim 6.2 suffices. R1 instead asks for direct bounds
on the numbers of placements. A numerical estimate with uncontrolled error
is insufficient for either strict inequality.
-/

namespace OMA.R_Green97_green_97_variants_simkin_R2
open Filter Topology

/-- The enumeration rate equals the supremum of the finite-grid entropy scores. -/
def H1 : Prop :=
  let S : Set ℝ := {r | ∃ N : ℕ, 0 < N ∧ ∃ A : Fin N → Fin N → ℝ,
    let f := fun x : ℝ ↦ x * Real.log x
    let d := fun (b : Bool) (k : ℕ) ↦ 1 - (∑ i : Fin N, ∑ j : Fin N,
      if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N
    (∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = N) ∧ (∀ j, ∑ i, A i j = N) ∧
    (∀ b (k : Fin (2*N+1)), 0 ≤ d b k.val) ∧ r = -3 - (∑ i, ∑ j, f (A i j)) / (N : ℝ)^2 -
      (∑ b : Bool, ∑ k : Fin (2*N), ∫ t in (0:ℝ)..1,
        f ((1-t) * d b k.val + t * d b (k.val+1))) / N}
  ∃ s : ℝ, IsLUB S s ∧
    Tendsto (fun n : ℕ ↦ (Green97.numQueens n : ℝ) ^ ((1 : ℝ) / n) / n)
      atTop (𝓝 (Real.exp s))

/-- Uniform upper certificate with a strict margin. -/
def H2 : Prop :=
  let S : Set ℝ := {r | ∃ N : ℕ, 0 < N ∧ ∃ A : Fin N → Fin N → ℝ,
    let f := fun x : ℝ ↦ x * Real.log x
    let d := fun (b : Bool) (k : ℕ) ↦ 1 - (∑ i : Fin N, ∑ j : Fin N,
      if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N
    (∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = N) ∧ (∀ j, ∑ i, A i j = N) ∧
    (∀ b (k : Fin (2*N+1)), 0 ≤ d b k.val) ∧ r = -3 - (∑ i, ∑ j, f (A i j)) / (N : ℝ)^2 -
      (∑ b : Bool, ∑ k : Fin (2*N), ∫ t in (0:ℝ)..1,
        f ((1-t) * d b k.val + t * d b (k.val+1))) / N}
  ∃ u : ℝ, u < -1.94 ∧ ∀ t ∈ S, t ≤ u

/-- A finite step density giving a strict lower certificate. -/
def H3 : Prop :=
  let S : Set ℝ := {r | ∃ N : ℕ, 0 < N ∧ ∃ A : Fin N → Fin N → ℝ,
    let f := fun x : ℝ ↦ x * Real.log x
    let d := fun (b : Bool) (k : ℕ) ↦ 1 - (∑ i : Fin N, ∑ j : Fin N,
      if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N
    (∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = N) ∧ (∀ j, ∑ i, A i j = N) ∧
    (∀ b (k : Fin (2*N+1)), 0 ≤ d b k.val) ∧ r = -3 - (∑ i, ∑ j, f (A i j)) / (N : ℝ)^2 -
      (∑ b : Bool, ∑ k : Fin (2*N), ∫ t in (0:ℝ)..1,
        f ((1-t) * d b k.val + t * d b (k.val+1))) / N}
  ∃ t ∈ S, -1.9449 < t

theorem main : H1 → H2 → H3 → type_of% @Green97.green_97.variants.simkin := by
  rintro ⟨s, hs, hlim⟩ ⟨u, hu, hupper⟩ ⟨t, ht, hlower⟩
  have hsu : s ≤ u := hs.2 hupper
  have hts : t ≤ s := hs.1 ht
  refine ⟨-s, by linarith, by linarith, ?_⟩
  simpa only [neg_neg] using hlim

end OMA.R_Green97_green_97_variants_simkin_R2
