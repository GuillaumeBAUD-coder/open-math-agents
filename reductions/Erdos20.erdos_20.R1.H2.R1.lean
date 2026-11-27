import OMAReductions.R_Erdos20_erdos_20_R1
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

-- Reduction Erdos20.erdos_20.R1.H2.R1 of step Erdos20.erdos_20.R1.H2
-- Credit: @JamesSlash

/-!
# Splitting the word-sunflower bound into tensor geometry and a planar comparison

Source: OpenAI, *An exponential bound for sunflowers* (OpenAI Math Release preprint, Nov 24 2026), Part I,
and its companion *Euclidean geometry in the asymptotic spectrum of tensors*; both are formalized in Lean 4
in github.com/openai/math (Apache-2.0), where `OAI.Combinatorics.Sunflower.fixedBase_words` is exactly
the parent step and `OAI.Combinatorics.Sunflower.exists_planar_point` is H1 below.

Tensors on the sites `Fin (s + 2)` are encoded as `⟨d, T⟩` with local dimensions `d i` and coefficients
`T : (∀ i, Fin (d i)) → ℂ`. A spectral point `Φ` is nonnegative, sends the unit to 1 and zero tensors
to 0, is monotone under restriction (one matrix per site), multiplicative under the tensor (Kronecker)
product and additive under the direct sum. `⟨fun i => if i ∈ S then 2 else 1, …⟩` is the partial
diagonal sharing one bit on `S`, and the right-hand side is the ratio of Gaussian mean widths of the
placed sites `x '' S` and `x '' univ` (the normalization `√(2π)` cancels).

- `H1` (tensor geometry, the planar case of the Euclidean prices theorem): every planar placement of
  at least two sites carries one spectral point whose one-bit prices are the normalized mean widths.
- `H2` (the sunflower comparison, paper Part I): for each number of petals `r ≥ 3` there is a planar
  placement such that any spectral point with those prices bounds every word-sunflower-free family
  by `D ^ n`, with `D` independent of the alphabet size `m`.
-/

namespace OMA.R_Erdos20_erdos_20_R1_H2_R1

def H1 : Prop :=
  ∀ (s : ℕ) (x : Fin (s + 2) ↪ EuclideanSpace ℝ (Fin 2)),
    ∃ Φ : (Σ d : Fin (s + 2) → ℕ, (∀ i, Fin (d i)) → ℂ) → ℝ,
      (∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧
      (∀ X : Σ d : Fin (s + 2) → ℕ, (∀ i, Fin (d i)) → ℂ, (∀ z, X.2 z = 0) → Φ X = 0) ∧
      (∀ X Y : Σ d : Fin (s + 2) → ℕ, (∀ i, Fin (d i)) → ℂ,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X) ∧
      (∀ X Y : Σ d : Fin (s + 2) → ℕ, (∀ i, Fin (d i)) → ℂ,
        Φ ⟨fun i => X.1 i * Y.1 i, fun z => X.2 (fun i => (finProdFinEquiv.symm (z i)).1) *
          Y.2 (fun i => (finProdFinEquiv.symm (z i)).2)⟩ = Φ X * Φ Y) ∧
      (∀ X Y : Σ d : Fin (s + 2) → ℕ, (∀ i, Fin (d i)) → ℂ,
        Φ ⟨fun i => X.1 i + Y.1 i, fun z =>
          if h : ∀ i, (z i : ℕ) < X.1 i then X.2 (fun i => ⟨z i, h i⟩)
          else if h' : ∀ i, X.1 i ≤ z i then
            Y.2 (fun i => ⟨z i - X.1 i, by have h2 : (z i : ℕ) < X.1 i + Y.1 i := (z i).2; have := h' i; omega⟩)
          else 0⟩ = Φ X + Φ Y) ∧
      ∀ (S : Finset (Fin (s + 2))) (hS : S.Nonempty),
        Real.logb 2 (Φ ⟨fun i => if i ∈ S then 2 else 1,
          fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩) =
        (∫ u, S.sup' hS (fun i => inner ℝ u (x i)) ∂ProbabilityTheory.stdGaussian _) /
          ∫ u, Finset.univ.sup' Finset.univ_nonempty (fun i => inner ℝ u (x i))
            ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))

def H2 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ (s : ℕ) (x : Fin (s + 2) ↪ EuclideanSpace ℝ (Fin 2)),
    ∀ Φ : (Σ d : Fin (s + 2) → ℕ, (∀ i, Fin (d i)) → ℂ) → ℝ,
      ((∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧
      (∀ X : Σ d : Fin (s + 2) → ℕ, (∀ i, Fin (d i)) → ℂ, (∀ z, X.2 z = 0) → Φ X = 0) ∧
      (∀ X Y : Σ d : Fin (s + 2) → ℕ, (∀ i, Fin (d i)) → ℂ,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X) ∧
      (∀ X Y : Σ d : Fin (s + 2) → ℕ, (∀ i, Fin (d i)) → ℂ,
        Φ ⟨fun i => X.1 i * Y.1 i, fun z => X.2 (fun i => (finProdFinEquiv.symm (z i)).1) *
          Y.2 (fun i => (finProdFinEquiv.symm (z i)).2)⟩ = Φ X * Φ Y) ∧
      (∀ X Y : Σ d : Fin (s + 2) → ℕ, (∀ i, Fin (d i)) → ℂ,
        Φ ⟨fun i => X.1 i + Y.1 i, fun z =>
          if h : ∀ i, (z i : ℕ) < X.1 i then X.2 (fun i => ⟨z i, h i⟩)
          else if h' : ∀ i, X.1 i ≤ z i then
            Y.2 (fun i => ⟨z i - X.1 i, by have h2 : (z i : ℕ) < X.1 i + Y.1 i := (z i).2; have := h' i; omega⟩)
          else 0⟩ = Φ X + Φ Y) ∧
      ∀ (S : Finset (Fin (s + 2))) (hS : S.Nonempty),
        Real.logb 2 (Φ ⟨fun i => if i ∈ S then 2 else 1,
          fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩) =
        (∫ u, S.sup' hS (fun i => inner ℝ u (x i)) ∂ProbabilityTheory.stdGaussian _) /
          ∫ u, Finset.univ.sup' Finset.univ_nonempty (fun i => inner ℝ u (x i))
            ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))) →
      ∃ D : ℕ, 1 ≤ D ∧ ∀ (n m : ℕ) (W : Finset (Fin n → Fin m)),
        (∀ w : Fin r → Fin n → Fin m, (∀ i, w i ∈ W) →
          (∀ j : Fin n, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
          ∀ a b, w a = w b) →
        W.card ≤ D ^ n

theorem main : H1 → H2 → OMA.R_Erdos20_erdos_20_R1.H2 := by
  intro h1 h2 r hr
  obtain ⟨s, x, hx⟩ := h2 r hr
  obtain ⟨Φ, hΦ⟩ := h1 s x
  exact hx Φ hΦ

end OMA.R_Erdos20_erdos_20_R1_H2_R1
