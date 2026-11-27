import FormalConjectures.ErdosProblems.«261»

-- Reduction Erdos261.erdos_261.parts.ii.R1 of Erdős Problem 261 — ii
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 261 (ii) as one deterministic integer orbit

For `n > 0`, every representation `n / 2^n = ∑ a / 2^a` with at least two distinct terms uses only
`a > n` (since `a / 2^a` is decreasing). Decide the integers `ℓ = n+1, n+2, …` one at a time and
keep the scaled residual `ρ = 2^ℓ · (n / 2^n - ∑_{taken a < ℓ} a / 2^a)`, an integer, starting
from `ρ = 2n` at `ℓ = n+1`. Taking `ℓ` sends `ρ ↦ 2(ρ - ℓ)`, skipping it sends `ρ ↦ 2ρ`; the
representation is finished when `ρ = ℓ` and `ℓ` is taken.

With `c = ρ - ℓ - 1` the moves are `c ↦ 2c ∓ ℓ`, and `|c|` evolves by `a ↦ |2a - ℓ|` whatever
the choices (a choice exists only when `c ∈ {-1, 0, 1}`). The map below fixes the canonical
choice: take `ℓ` exactly when `ρ > ℓ + 1`.

* `H1` (open): for every `n > 0` the canonical orbit started at `(n + 1, 2n)` reaches a state
  `(m, m)` after at least one step. Checked by computer for every `n ≤ 10000` (the worst case is
  `n = 10`, which needs 55317 steps), in line with Tengely–Ulas–Zygadło.
* `H2` (bookkeeping, provable): such a hit gives a representation: the levels taken along the way
  together with `m` itself. The invariant is `n / 2^n = ∑_{taken} a / 2^a + ρ / 2^ℓ`, and there are
  at least two terms because `n / 2^n ≠ m / 2^m` for `m ≥ n + 2`.
-/

namespace OMA.R_Erdos261_erdos_261_parts_ii_R1

/-- The canonical residual orbit of `n / 2^n` reaches the take-and-finish state `ρ = ℓ`. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → ∃ j : ℕ, 0 < j ∧
    ((fun p : ℕ × ℕ => (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1) else 2 * p.2))^[j]
      (n + 1, 2 * n)).2 = n + 1 + j

/-- A hit of the canonical residual orbit yields a representation with at least two terms. -/
def H2 : Prop := ∀ n j : ℕ, 0 < n → 0 < j →
    ((fun p : ℕ × ℕ => (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1) else 2 * p.2))^[j]
      (n + 1, 2 * n)).2 = n + 1 + j → Erdos261.Erdos261Prop n

theorem main : H1 → H2 → type_of% @Erdos261.erdos_261.parts.ii := by
  intro h1 h2 n hn
  obtain ⟨j, hj, h⟩ := h1 n hn
  exact h2 n j hn hj h

end OMA.R_Erdos261_erdos_261_parts_ii_R1
