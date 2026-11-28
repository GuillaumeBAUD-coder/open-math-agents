import Mathlib

/-!
# The Williamson conjecture

Source: https://en.wikipedia.org/wiki/Williamson_conjecture
Credit: Sudharsan Rajendiran

Williamson matrices of order `n` are four `n × n` matrices `A, B, C, D` with entries `±1` that are
symmetric and circulant and satisfy `A² + B² + C² + D² = 4n I`. Williamson showed that they yield
a Hadamard matrix of order `4n`. The Williamson conjecture is that Williamson matrices of order
`n` exist for all positive integers `n`.

The conjecture is false: Đoković (1993) showed by an exhaustive computer search that there are no
Williamson matrices of order `35` (independently verified by Bright, Kotsireas and Ganesh with
SAT solvers, who also showed that `35` is the smallest such order). We state this known answer:
it is not the case that Williamson matrices exist in every positive order.

Conventions:
- Matrices are indexed by `Fin n` with integer entries; every entry is `1` or `-1`.
- Circulant: `A = Matrix.circulant a` for some `a : Fin n → ℤ`, i.e. `A i j = a (i - j)` with
  subtraction in `Fin n` (that is, modulo `n`).
- Symmetric: `Aᵀ = A`.
- `4n I` is `(4 * n : ℤ) • 1`.
-/

namespace OMA.S_wp_williamson_conjecture

/-- `A` is a symmetric circulant `±1` matrix of order `n`. -/
def IsSymCircPM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∃ a : Fin n → ℤ, A = Matrix.circulant a) ∧ A.transpose = A ∧
    ∀ i j, A i j = 1 ∨ A i j = -1

/-- `A, B, C, D` are Williamson matrices of order `n`. -/
def IsWilliamson {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsSymCircPM A ∧ IsSymCircPM B ∧ IsSymCircPM C ∧ IsSymCircPM D ∧
    A * A + B * B + C * C + D * D = ((4 * n : ℕ) : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)

/-- The Williamson conjecture is false: Williamson matrices do not exist in every positive
order (Đoković 1993: none of order `35`). -/
theorem main : ¬ ∀ n : ℕ, 0 < n →
    ∃ A B C D : Matrix (Fin n) (Fin n) ℤ, IsWilliamson A B C D := by
  sorry

end OMA.S_wp_williamson_conjecture
