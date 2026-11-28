import Mathlib

/-!
# Row-module membership for a polynomial matrix over a finite field

Source: spk, https://mathoverflow.net/questions/84148 (CC BY-SA 3.0).
Credit: @connoranderson (agent: Codex)

Algebraic multiplicity is the root multiplicity of the determinant after
base change to the algebraic closure. Geometric multiplicity is the dimension
of the kernel of the specialized matrix. The conclusion gives polynomial
coefficients over the original finite field.
-/

namespace OMA.S_mo_84148
open Polynomial

noncomputable def extendPoly {K : Type*} [Field K] (p : K[X]) : (AlgebraicClosure K)[X] :=
  p.map (algebraMap K (AlgebraicClosure K))

noncomputable def specialized {K : Type*} [Field K] {n : ℕ} (G : Matrix (Fin n) (Fin n) K[X])
    (z : AlgebraicClosure K) : Matrix (Fin n) (Fin n) (AlgebraicClosure K) :=
  Matrix.of fun i j => (extendPoly (G i j)).eval z

theorem main : ∀ (K : Type) [Field K] [Finite K] (n : ℕ)
    (G : Matrix (Fin n) (Fin n) K[X]) (r : Fin n → K[X]), G.det ≠ 0 →
    (∀ z : AlgebraicClosure K, (extendPoly G.det).IsRoot z →
      (extendPoly G.det).rootMultiplicity z =
        Module.finrank (AlgebraicClosure K) (LinearMap.ker (specialized G z).mulVecLin)) →
    (∀ z : AlgebraicClosure K, (extendPoly G.det).IsRoot z →
      ∀ v : Fin n → AlgebraicClosure K, (specialized G z).mulVec v=0 →
        dotProduct (fun i => (extendPoly (r i)).eval z) v=0) →
    ∃ b : Fin n → K[X], Matrix.vecMul b G = r := by
  sorry

end OMA.S_mo_84148
