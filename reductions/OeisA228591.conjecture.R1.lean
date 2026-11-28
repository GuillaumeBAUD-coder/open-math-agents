import FormalConjectures.OEIS.«228591»

-- Reduction OeisA228591.conjecture.R1 of Determinant of odd composite sum indicator matrix
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
/-!
# Reduction of OEIS A228591 (determinant of the odd-composite sum indicator matrix)

Target: `∀ n > 15, a n ≠ 0`, where `a n` is the determinant of the `n × n` 0/1 matrix
`M i j = 1` iff `i + j + 2 = 2` or `i + j + 2` is an odd composite (`i, j : Fin n`).

The reduction uses the structure recorded by Zhi-Wei Sun for this family (OEIS A228591 comment):
entries with `i + j` even vanish except the single `(0,0)` entry, so the matrix splits into two
opposite-parity blocks and its determinant is a **square** of the determinant of one half-size block
(up to sign, and up to the `(0,0)` entry when `n` is odd — which is `1` here because `0 + 0 + 2 = 2`).

Concretely, with `hd n` the half-size determinant of the map
`(i, j) ↦ 0 if 2i+2j+3 is prime else 1` (n even) resp. `0 if 2i+2j+5 is prime else 1` (n odd),
both indexed by `Fin (n/2)` resp. `Fin ((n-1)/2)`, the two steps are

* **H1** (structure, a theorem of Sun, not yet in Mathlib): `a n = (hd n)^2 ∨ a n = -(hd n)^2` for
  every `n > 15`. Verified numerically for `n ≤ 50` with exact integer determinants, and it is the
  standard `(-1)^{n/2} det M = D(n)^2` / `(-1)^{(n-1)/2} det M = m_{1,1} D(n)^2` statement
  specialised to this matrix (`m_{1,1} = 1`).
* **H2** (the open core in half size): `hd n ≠ 0` for every `n > 15`.

H1 is a finite-linear-algebra theorem (block elimination on the parity split, using that the two
off-diagonal blocks are transposes). H2 is the remaining nonvanishing statement about a family of
Hankel-type determinants of the prime-complement indicator `[2s-1 composite]`; it is not known and it
is not reachable by a finite computation. Proving both closes the target, and the implication
`H1 ∧ H2 → target` below is unconditional.
-/

namespace OMA.R_OeisA228591_conjecture_R1

open Matrix

/-- Sun's square structure for the odd-composite sum indicator matrix: the determinant is `±(hd n)^2`. -/
def H1 : Prop := ∀ n : ℕ, 15 < n →
  let hd : ℤ := if n % 2 = 0 then
      Matrix.det (Matrix.of (fun i j : Fin (n / 2) =>
        if (2 * i.val + 2 * j.val + 3).Prime then (0 : ℤ) else 1))
    else
      Matrix.det (Matrix.of (fun i j : Fin ((n - 1) / 2) =>
        if (2 * i.val + 2 * j.val + 5).Prime then (0 : ℤ) else 1))
  OeisA228591.a n = hd ^ 2 ∨ OeisA228591.a n = -(hd ^ 2)

/-- The half-size determinants never vanish (the remaining open core). -/
def H2 : Prop := ∀ n : ℕ, 15 < n →
  let hd : ℤ := if n % 2 = 0 then
      Matrix.det (Matrix.of (fun i j : Fin (n / 2) =>
        if (2 * i.val + 2 * j.val + 3).Prime then (0 : ℤ) else 1))
    else
      Matrix.det (Matrix.of (fun i j : Fin ((n - 1) / 2) =>
        if (2 * i.val + 2 * j.val + 5).Prime then (0 : ℤ) else 1))
  hd ≠ 0

theorem main : H1 → H2 → type_of% @OeisA228591.conjecture := by
  intro h1 h2 n hn
  have h1n := h1 n hn
  have h2n := h2 n hn
  rcases h1n with h | h
  · rw [h]
    exact pow_ne_zero 2 h2n
  · rw [h]
    exact neg_ne_zero.mpr (pow_ne_zero 2 h2n)

end OMA.R_OeisA228591_conjecture_R1
