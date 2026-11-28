import Mathlib

/-!
# MathOverflow 159879

Source: https://mathoverflow.net/questions/159879
-/

namespace OMA.S_mo_159879

open Matrix

def sign : Bool → ℝ
  | false => -1
  | true => 1

def signVector {n : ℕ} (b : Fin n → Bool) : Fin n → ℝ := fun i => sign (b i)

noncomputable def coefficient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ b : Fin n → Bool,
    (signVector b ⬝ᵥ (A *ᵥ signVector b)) * ∏ i ∈ S, sign (b i)

theorem main : (¬ ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ), B.PosSemidef →
      ∀ S : Finset (Fin n), coefficient B S ≠ 0) ∧
    (¬ ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ), B.PosSemidef →
      ∀ S : Finset (Fin n), 0 ≤ coefficient B S) := by
  sorry

end OMA.S_mo_159879
