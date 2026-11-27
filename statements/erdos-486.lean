import Mathlib

/-!
# Erdős Problem 486

Source: https://www.erdosproblems.com/486
Credit: @SudharsanAnimations

Let `A ⊆ ℕ`, and for each `n ∈ A` choose some `X_n ⊆ ℤ/nℤ`. Let
`B = {m ∈ ℕ : m ∉ X_n (mod n) for all n ∈ A with m > n}`.
Must `B` have a logarithmic density, that is, does
`lim_{x → ∞} (1 / log x) ∑_{m ∈ B, m < x} 1 / m` exist?

We state the affirmative answer: for every such choice of `A` and `X`, the limit exists
(as a real number). The problem is open; a disproof is the negation of `main`.

Conventions:
- As on the source page, `ℕ` means the positive integers: elements of `A` are positive
  (so that `ℤ/nℤ` is a finite cyclic group), and `B` consists of positive integers.
- `X n` is only used for `n ∈ A`; its value at other `n` is irrelevant.
- `m ∉ X_n (mod n)` means that the residue class of `m` in `ZMod n` is not in `X n`.
- `x` ranges over the reals, and `m < x` is the strict inequality of the source. For a natural
  number `m` and a real `x`, `m < x` holds exactly when `m < ⌈x⌉₊`, so the partial sum is a sum
  over `Finset.range ⌈x⌉₊`.
- "The limit exists" means convergence to a finite real limit `L`.
-/

namespace OMA.S_erdos_486

open Filter Topology

/-- The set `B` determined by `A` and the residue sets `X n`. -/
def B (A : Set ℕ) (X : (n : ℕ) → Set (ZMod n)) : Set ℕ :=
  {m : ℕ | 0 < m ∧ ∀ n ∈ A, n < m → ((m : ZMod n) ∉ X n)}

open Classical in
/-- `∑_{m ∈ S, m < x} 1 / m`. -/
noncomputable def logSum (S : Set ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ (Finset.range ⌈x⌉₊).filter (· ∈ S), (1 : ℝ) / m

/-- Erdős Problem 486, affirmative form: `B` always has a logarithmic density. -/
theorem main : ∀ (A : Set ℕ), (∀ n ∈ A, 0 < n) → ∀ X : (n : ℕ) → Set (ZMod n),
    ∃ L : ℝ, Tendsto (fun x : ℝ => logSum (B A X) x / Real.log x) atTop (𝓝 L) := by
  sorry

end OMA.S_erdos_486
