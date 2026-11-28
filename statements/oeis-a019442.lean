import Mathlib

/-!
# A019442: Numbers m such that a Hadamard matrix of order m exists.

Source: https://oeis.org/A019442
Credit: @its-shitzu

A019442 lists the `m` for which a Hadamard matrix of order `m` exists, that is, an `m × m` matrix
with entries `±1` whose rows are pairwise orthogonal. The entry conjectures that this list is
exactly `1`, `2` and the multiples of `4`: the sequence is `1, 2, 4, 8, 12, 16, 20, ...`, with
conjectured generating function `(2x³ + x² + 1)/(1 - x)²`.

We use Mathlib's `Matrix.IsHadamard`, which over `ℤ` says exactly that every entry is `±1`
(`Matrix.IsHadamard.apply_mem`, since `unitary ℤ = {1, -1}`) and `M * Mᵀ = m • 1`.

The necessary condition `m = 1 ∨ m = 2 ∨ 4 ∣ m` is a theorem; the converse is the conjecture.
-/

namespace OMA.S_oeis_a019442

/-- A Hadamard matrix of order `n` exists: an `n × n` matrix over `ℤ` with entries `±1` whose
rows are pairwise orthogonal. -/
def HasHadamardMatrix (n : ℕ) : Prop :=
  ∃ M : Matrix (Fin n) (Fin n) ℤ, M.IsHadamard

/-- OEIS A019442 (conjecture): the numbers `m ≥ 1` for which a Hadamard matrix of order `m`
exists are exactly `1`, `2` and the multiples of `4`. -/
theorem main : ∀ n : ℕ, 0 < n → (HasHadamardMatrix n ↔ n = 1 ∨ n = 2 ∨ 4 ∣ n) := by
  sorry

end OMA.S_oeis_a019442
