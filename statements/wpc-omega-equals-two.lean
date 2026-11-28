import Mathlib

/-!
# Is the square matrix multiplication exponent two?

Source: https://en.wikipedia.org/wiki/Computational_complexity_of_matrix_multiplication
Credit: @chuyeow (catalog statement)

We use the algebraic model over a fixed field. A division-free straight-line
program must compute the matrix entries as formal polynomials, including over
finite fields. Its cost counts scalar additions, subtractions and multiplications.

The question below retains the catalog's conjectured value. The November 24,
2026 preprint *The matrix multiplication exponent is nine fourths* reports a
different value for this model: https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/lean/docs/107.md
-/

namespace OMA.S_wpc_omega_equals_two

open MvPolynomial

/-- The two summands index entries of the left and right matrices. -/
abbrev Entry (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

abbrev Wire (F : Type*) [Field F] (n : ℕ) := MvPolynomial (Entry n) F

variable {F : Type*} [Field F] {n : ℕ}

/-- An operand can be a previously computed value, a scalar or an input entry. -/
def Available (prior : List (Wire F n)) (p : Wire F n) : Prop :=
  p ∈ prior ∨ (∃ c : F, p = C c) ∨ ∃ e : Entry n, p = X e

/-- Newest gate first. Each list element costs one operation and may be reused. -/
def ValidProgram : List (Wire F n) → Prop
  | [] => True
  | p :: prior =>
    ValidProgram prior ∧ ∃ x y : Wire F n, Available prior x ∧ Available prior y ∧
      (p = x + y ∨ p = x - y ∨ p = x * y)

/-- All output entries must be available from the same program. -/
def Multiplies (program : List (Wire F n)) : Prop :=
  ValidProgram program ∧ ∀ i k : Fin n, Available program
    (∑ j : Fin n, X (Sum.inl (i, j)) * X (Sum.inr (j, k)))

/-- Exponents for which size-n multiplication has arithmetic cost O(n^τ). -/
def Admissible (F : Type*) [Field F] (τ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∃ program : List (Wire F n),
    Multiplies program ∧ (program.length : ℝ) ≤ c * (n : ℝ) ^ τ

noncomputable def omega (F : Type*) [Field F] : ℝ :=
  sInf {τ : ℝ | Admissible F τ}

theorem main : ∀ (F : Type*) [Field F], omega F = 2 := by
  sorry

end OMA.S_wpc_omega_equals_two
