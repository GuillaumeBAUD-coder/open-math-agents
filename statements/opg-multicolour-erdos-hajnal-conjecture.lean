import Mathlib

/-!
# Multicolour Erdős--Hajnal Conjecture

Source: https://www.openproblemgarden.org/op/multicolour_erdos_hajnal_conjecture
Credit: @joshuadc11

Conjecture (Erdős–Hajnal): for every fixed `k ≥ 2`, `m ≥ 2`, and fixed `m`-colouring `χ` of
`E(K_k)`, there exists `ε > 0` such that every `m`-colouring of `E(K_n)` contains either `k`
vertices whose induced edge-colouring is isomorphic to `χ`, or at least `n ^ ε` vertices whose
edges use at most `m - 1` colours.

## Encoding

* An `m`-colouring of `E(K_n)` is a function `c : Sym2 (Fin n) → Fin m` (only values on off-diagonal
  pairs `s(u, v)` with `u ≠ v` are used).
* We assume `2 ≤ m` (the standard multicolour setting generalizing `m = 2`; for `m = 1` the
  `m - 1 = 0` colour alternative fails vacuously for `2 ≤ n < k`).
* Containing `k` vertices coloured according to `χ` is an embedding `f : Fin k ↪ Fin n` such that
  `c s(f i, f j) = χ s(i, j)` for all `i ≠ j`.
* Using at most `m - 1` colours on `S : Finset (Fin n)` is equivalent to omitting at least one
  colour `a : Fin m` on all edges `s(u, v)` with `u, v ∈ S`, `u ≠ v`.
-/

namespace OMA.S_opg_multicolour_erdos_hajnal_conjecture

/-- Multicolour Erdős–Hajnal conjecture: for every `k ≥ 2`, `m ≥ 2`, and `m`-colouring `χ` of
`E(K_k)`, there exists `ε > 0` such that every `m`-colouring of `E(K_n)` contains either a copy
of `(K_k, χ)` or a subset of at least `n ^ ε` vertices missing at least one colour. -/
theorem main : ∀ (k m : ℕ), 2 ≤ k → 2 ≤ m → ∀ χ : Sym2 (Fin k) → Fin m,
    ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (c : Sym2 (Fin n) → Fin m),
      (∃ f : Fin k ↪ Fin n, ∀ i j : Fin k, i ≠ j → c s(f i, f j) = χ s(i, j)) ∨
      (∃ S : Finset (Fin n), (n : ℝ) ^ ε ≤ (S.card : ℝ) ∧
        ∃ a : Fin m, ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ a) := by
  sorry

end OMA.S_opg_multicolour_erdos_hajnal_conjecture
