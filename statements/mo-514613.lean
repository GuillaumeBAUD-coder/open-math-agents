import Mathlib

/-!
# Are prime-difference matrices always nonsingular?

Source: https://mathoverflow.net/questions/514613 (CC BY-SA 4.0); conjectured by Zhi-Wei Sun in
2013, see OEIS A228638.

For `n ≥ 1` let `G_n` be the graph on the vertices `1, 2, …, n` in which distinct `i, j` are
joined when `|i - j|` is prime, and let `A_n` be its adjacency matrix. Question: is `A_n`
nonsingular for every `n ≥ 4`? (The asker checked `det A_n ≢ 0 (mod 65521)` for
`4 ≤ n ≤ 1500`.)

We state the affirmative answer.

Formalization notes:
* The vertices `1, …, n` are indexed by `Fin n` (`0, …, n-1`); only differences matter.
* `A n` has entry `1` when `|i - j|` is prime and `0` otherwise (the diagonal is `0`, as `0` is
  not prime). Nonsingular over `ℚ` means `det (A n) ≠ 0`.
* `n ≥ 4` is needed: `A_1`, `A_2`, `A_3` are singular. Checked numerically (determinant modulo a
  large prime): nonsingular for `4 ≤ n < 160`.
-/

namespace OMA.S_mo_514613

/-- The adjacency matrix of the graph on `n` vertices joining `i ≠ j` when `|i - j|` is prime. -/
def A (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => if (Int.natAbs ((i : ℤ) - (j : ℤ))).Prime then 1 else 0

/-- For every `n ≥ 4` the prime-difference matrix `A_n` is nonsingular. -/
theorem main : ∀ n : ℕ, 4 ≤ n → (A n).det ≠ 0 := by
  sorry

end OMA.S_mo_514613
