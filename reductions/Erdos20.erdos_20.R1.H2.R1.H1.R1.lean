import OMAReductions.R_Erdos20_erdos_20_R1_H2_R1

-- Reduction Erdos20.erdos_20.R1.H2.R1.H1.R1 of step Erdos20.erdos_20.R1.H2.R1.H1
-- Credit: @JamesSlash

/-!
# The planar spectral point from a non-tree wire metric

Source: OpenAI, *Euclidean geometry in the asymptotic spectrum of tensors* and *An exponential bound for
sunflowers* (OpenAI Math Release, Nov 2026), formalized in Lean 4 in github.com/openai/math (Apache-2.0).
There the target is `OAI.Combinatorics.Sunflower.exists_planar_point`, proved from
`OAI.LinearAlgebra.SpectralBooks.matrix_spectral_plane`, which is
`exists_jointly_convex_spectral_plane (nonTreeWireMetric_every_field F)`: the spectral tree-or-plane
alternative. The split below follows that proof.

Tensors on a finite site type are encoded as in the parent step: `⟨d, T⟩` with local dimensions `d j`
and coefficients `T : (∀ j, Fin (d j)) → ℂ`; a spectral point is nonnegative, sends the unit to 1 and
zero tensors to 0, is monotone under restriction (one matrix per site), multiplicative under the
Kronecker product and additive under the direct sum. The wire distance `δ s t` of a spectral point is the
binary log-price of one shared bit (the 2-dimensional diagonal) between the sites `s` and `t`
(`OAI.LinearAlgebra.SpectralBooks.SiteTensor.rawWireDistance φ 1`).

- `H1` (algebraic side, `HasNonTreeWireMetric ℂ`): some spectral point on finitely many sites has a wire
  distance that violates the four-point condition of tree metrics. In OpenAI's proof this is the
  contrapositive of a border-complexity lower bound (`OAI.Computability.BorderVNP`).
- `H2` (geometric side, `exists_jointly_convex_spectral_plane` + `exists_planar_point`): a single
  four-point defect yields, through the CAT(0) geodesic realization of the spectrum, a Euclidean
  spectral plane, and on it every finite planar placement carries one spectral point whose one-bit
  prices are the normalized Gaussian mean widths.
-/

namespace OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (Φ : (Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ) → ℝ),
    ((∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧
      (∀ X : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ, (∀ z, X.2 z = 0) → Φ X = 0) ∧
      (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ,
        (∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
      (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ,
        Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) *
          Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y) ∧
      (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ,
        Φ ⟨fun j => X.1 j + Y.1 j, fun z =>
          if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩)
          else if h' : ∀ j, X.1 j ≤ z j then
            Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩)
          else 0⟩ = Φ X + Φ Y)) ∧
    ∃ a b c e : J,
      let δ := fun s t : J => Real.logb 2 (Φ ⟨fun j => if j = s ∨ j = t then 2 else 1,
        fun y => if (y s : ℕ) = y t then 1 else 0⟩);
      max (δ a c + δ b e) (δ a e + δ b c) < δ a b + δ c e

def H2 : Prop :=
  let P : ∀ (J : Type) [Fintype J] [DecidableEq J], ((Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ) → ℝ) → Prop :=
    fun J _ _ Φ => (∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧
      (∀ X : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ, (∀ z, X.2 z = 0) → Φ X = 0) ∧
      (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ,
        (∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
      (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ,
        Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) *
          Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y) ∧
      (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ,
        Φ ⟨fun j => X.1 j + Y.1 j, fun z =>
          if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩)
          else if h' : ∀ j, X.1 j ≤ z j then
            Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩)
          else 0⟩ = Φ X + Φ Y)
  ∀ (J : Type) [Fintype J] [DecidableEq J] (Φ : (Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ) → ℝ) (a b c e : J),
    P J Φ →
    (let δ := fun s t : J => Real.logb 2 (Φ ⟨fun j => if j = s ∨ j = t then 2 else 1,
        fun y => if (y s : ℕ) = y t then 1 else 0⟩);
      max (δ a c + δ b e) (δ a e + δ b c) < δ a b + δ c e) →
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nontrivial I] (x : I ↪ EuclideanSpace ℝ (Fin 2)),
      ∃ Ψ, P I Ψ ∧ ∀ (S : Finset I) (hS : S.Nonempty),
        Real.logb 2 (Ψ ⟨fun i => if i ∈ S then 2 else 1,
          fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩) =
        (∫ u, S.sup' hS (fun i => inner ℝ u (x i)) ∂ProbabilityTheory.stdGaussian _) /
          ∫ u, Finset.univ.sup' Finset.univ_nonempty (fun i => inner ℝ u (x i))
            ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))

theorem main : H1 → H2 → OMA.R_Erdos20_erdos_20_R1_H2_R1.H1 := by
  intro hA hB I _ _ _ x
  obtain ⟨J, _, _, Φ, hΦ, a, b, c, e, hv⟩ := hA
  obtain ⟨Ψ, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := hB J Φ a b c e hΦ hv I x
  exact ⟨Ψ, h1, h2, h3, h4, h5, h6, h7⟩

end OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1
