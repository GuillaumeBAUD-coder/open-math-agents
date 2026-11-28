import Mathlib

/-!
# Erdős Problem 1220

Source: https://www.erdosproblems.com/1220
Credit: @Moti1125

Let `λ` be a singular cardinal such that both `λ` and `cf(λ)` are `ℵ₀`-inaccessible. Does
`λ → (λ, ℵ₁)²` hold?

A cardinal `κ` is `ℵ₀`-inaccessible if `μ ^ ℵ₀ < κ` for all `μ < κ` (definition from the source).

We state the affirmative answer.

Conventions:
- `κ → (μ, ν)²` is the usual partition relation: for every set `X` of cardinality `κ` and every
  colouring of the two-element subsets of `X` with two colours (red and blue), there is a red
  homogeneous set of cardinality `μ` or a blue homogeneous set of cardinality `ν`. A colouring of
  pairs is a symmetric map `X → X → Bool`; only its values on distinct elements matter. Here
  `false` is red and `true` is blue.
- A cardinal `λ` is singular if it is infinite and `cf(λ) < λ`, with `cf(λ) = λ.ord.cof`.
- Cardinals live in universe `0` (sets are types in `Type`).
- In the Lean statement the cardinal `λ` is written `κ`, since `λ` is a Lean keyword.
-/

namespace OMA.S_erdos_1220

open Cardinal

/-- The partition relation `κ → (μ, ν)²`. -/
def PartitionRel (κ μ ν : Cardinal.{0}) : Prop :=
  ∀ (X : Type), #X = κ → ∀ c : X → X → Bool, (∀ x y, c x y = c y x) →
    (∃ H : Set X, #H = μ ∧ ∀ x ∈ H, ∀ y ∈ H, x ≠ y → c x y = false) ∨
    (∃ H : Set X, #H = ν ∧ ∀ x ∈ H, ∀ y ∈ H, x ≠ y → c x y = true)

/-- `κ` is `ℵ₀`-inaccessible: `μ ^ ℵ₀ < κ` for every `μ < κ`. -/
def IsAleph0Inaccessible (κ : Cardinal.{0}) : Prop :=
  ∀ μ < κ, μ ^ ℵ₀ < κ

theorem main :
    ∀ κ : Cardinal.{0}, ℵ₀ ≤ κ → κ.ord.cof < κ →
      IsAleph0Inaccessible κ → IsAleph0Inaccessible κ.ord.cof →
        PartitionRel κ κ (aleph 1) := by
  sorry

end OMA.S_erdos_1220
