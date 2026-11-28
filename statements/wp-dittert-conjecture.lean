import Mathlib

/-!
# Dittert conjecture (Dittert–Hajek conjecture)

Source: https://en.wikipedia.org/wiki/Dittert_conjecture
Credit: @joshuadc11

Let `A` be a real `n × n` matrix with nonnegative entries whose total sum is `n`.
Define
`ϕ(A) = ∏ᵢ (∑ⱼ Aᵢⱼ) + ∏ⱼ (∑ᵢ Aᵢⱼ) - per(A)`,
where `per(A) = ∑_{σ ∈ Sₙ} ∏ᵢ A_{i, σ(i)}` is the permanent of `A`.
The Dittert conjecture asserts that `ϕ(A)` is uniquely maximized at the uniform matrix
`A = (1/n) Jₙ` (all entries equal to `1/n`).
-/

namespace OMA.S_wp_dittert_conjecture

/-- The permanent of an `n × n` real matrix. -/
def permanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, A i (σ i)

/-- The Dittert functional `ϕ(A) = ∏ᵢ (∑ⱼ Aᵢⱼ) + ∏ⱼ (∑ᵢ Aᵢⱼ) - per(A)`. -/
def phi {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∏ i : Fin n, ∑ j : Fin n, A i j) +
  (∏ j : Fin n, ∑ i : Fin n, A i j) -
  permanent A

/-- The `n × n` uniform matrix `(1 / n) Jₙ`. -/
noncomputable def uniformMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun _ _ => (1 : ℝ) / (n : ℝ))

theorem main :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, 0 ≤ A i j) →
      (∑ i : Fin n, ∑ j : Fin n, A i j) = (n : ℝ) →
      phi A ≤ phi (uniformMatrix n) ∧
      (phi A = phi (uniformMatrix n) → A = uniformMatrix n) := by
  sorry

end OMA.S_wp_dittert_conjecture
