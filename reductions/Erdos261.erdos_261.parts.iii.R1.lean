import FormalConjectures.ErdosProblems.«261»

-- Reduction Erdos261.erdos_261.parts.iii.R1 of Erdős Problem 261 — iii
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 261 (iii) for `x = 1` as the zeros of one integer orbit

Build a representation `1 = ∑ a / 2^a` greedily level by level: at level `ℓ` keep the scaled
residual `ρ = 2^ℓ · (1 - ∑_{taken a < ℓ} a / 2^a)`, starting from `ρ = 2` at `ℓ = 1`. Taking `ℓ`
sends `ρ ↦ 2(ρ - ℓ)`, skipping it sends `ρ ↦ 2ρ`, and a path is an infinite representation exactly
when `0 ≤ ρ ≤ 2ℓ + 2` (the scaled tail `∑_{a ≥ ℓ} a / 2^(a - ℓ)`) at every level.

With `c = ρ - ℓ - 1` both moves read `c ↦ 2c ∓ ℓ`, and along every path that never stops (take when
`c ≥ 1`, skip when `c ≤ -1`) the value `|c|` follows the same deterministic orbit
`a ↦ |2a - ℓ|`. A genuine choice exists exactly at the zeros `c = 0` (take or skip `ℓ`; both
continue forever, and the two branches differ in whether `ℓ` is used). The map below is the
canonical path (take `ℓ` exactly when `ρ > ℓ + 1`); its zeros are the states `ρ = ℓ + 1`, at
`ℓ = 1, 3, 79, 235, 431, 1503, 2943, 6059, 6619, 18911, 54223, 302467995, 1772665631,
2148845167, …` (checked up to `ℓ = 4·10^9`, about `0.6 · ln ℓ` of them below `ℓ`).

* `H1` (open): the canonical orbit has infinitely many zeros.
* `H2` (combinatorial bookkeeping, provable): infinitely many zeros give an injective family, indexed
  by binary sequences, of infinite sets `A ⊆ {1, 2, …}` with `∑_{a ∈ A} a / 2^a = 1`: the sequence
  picks take/skip at the successive zeros. The residual stays positive (so `A` is infinite) and below
  the tail `(2ℓ + 2) / 2^ℓ → 0` (so the sum is `1`); the first differing zero is in one set only.
* `H3` (analytic bookkeeping, provable, independent of the orbit): such a family gives `2^ℵ₀`
  representations in the sense of `Erdos261InfiniteRepresentation 1`: enumerate each set increasingly;
  the series converges in `ℝ` to the rational `1`, hence also in `ℚ`.
-/

open scoped Cardinal

namespace OMA.R_Erdos261_erdos_261_parts_iii_R1

/-- The canonical residual orbit of `1` returns to the branching state `ρ = ℓ + 1` infinitely
often (the state after `j` steps is at level `ℓ = j + 1`). -/
def H1 : Prop :=
  {j : ℕ | ((fun p : ℕ × ℕ => (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1) else 2 * p.2))^[j]
      (1, 2)).2 = j + 2}.Infinite

/-- Infinitely many branching states give continuum many sets of positive integers with
`∑_{a ∈ A} a / 2^a = 1`. -/
def H2 : Prop :=
  {j : ℕ | ((fun p : ℕ × ℕ => (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1) else 2 * p.2))^[j]
      (1, 2)).2 = j + 2}.Infinite →
    ∃ A : (ℕ → Bool) → Set ℕ, Function.Injective A ∧ ∀ b, (A b).Infinite ∧ (∀ a ∈ A b, 1 ≤ a) ∧
      HasSum ((A b).indicator (fun a : ℕ => (a : ℝ) / 2 ^ a)) 1

/-- An injective family of such sets yields continuum many representations of `1`. -/
def H3 : Prop :=
  (∃ A : (ℕ → Bool) → Set ℕ, Function.Injective A ∧ ∀ b, (A b).Infinite ∧ (∀ a ∈ A b, 1 ≤ a) ∧
      HasSum ((A b).indicator (fun a : ℕ => (a : ℝ) / 2 ^ a)) 1) →
    𝔠 ≤ #{a : ℕ → ℕ | Erdos261.Erdos261InfiniteRepresentation 1 a}

theorem main : H1 → H2 → H3 → type_of% @Erdos261.erdos_261.parts.iii := by
  intro h1 h2 h3
  exact ⟨1, h3 (h2 h1)⟩

end OMA.R_Erdos261_erdos_261_parts_iii_R1
