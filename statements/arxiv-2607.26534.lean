import Mathlib

namespace OMA.S_arxiv_2607_26534

open scoped BigOperators

/-- A spectrum is an orthogonal family of characters of the same size as the set. -/
noncomputable def Spectral {N : ℕ} (A : Finset (ZMod N)) : Prop :=
  let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))
  A.Nonempty ∧ ∃ S : Finset (ZMod N),
    S.card = A.card ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      (∑ a ∈ A, ζ ^ (((x - y) * a).val)) = 0

/-- A translational tiling gives exactly one sum representation of each group element. -/
def Tiles {N : ℕ} (A : Finset (ZMod N)) : Prop :=
  ∃ B : Finset (ZMod N), ∀ x : ZMod N,
    ∃! ab : ↥A × ↥B, (ab.1 : ZMod N) + (ab.2 : ZMod N) = x

/-- Somlai's square-free cyclic case of Fuglede's conjecture, Theorem 1.2. -/
theorem main :
    ∀ (k : ℕ) (p : Fin k → ℕ),
      0 < k → Function.Injective p → (∀ i, (p i).Prime) →
      (∀ i : Fin k, 0 < i.val →
        (∏ j ∈ Finset.univ.filter (fun j : Fin k => j < i), p j) < p i) →
      ∀ A : Finset (ZMod (∏ i, p i)), Spectral A ↔ Tiles A := by
  sorry

end OMA.S_arxiv_2607_26534
