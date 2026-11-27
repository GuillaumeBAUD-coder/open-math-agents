import Mathlib

/-!
# Sunflower conjecture

Source: https://en.wikipedia.org/wiki/Sunflower_(mathematics)
Credit: @Bondyboy2001

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The definition of a sunflower used here follows the one in google-deepmind/formal-conjectures
(`FormalConjecturesForMathlib.Combinatorics.SetFamily.Sunflower`), and the threshold function
follows `Erdos20.f` from the same repository, with `k` the uniform set size and `r` the number
of petals.
-/

namespace OMA.S_wp_sunflower_conjecture

variable {α : Type}

/-- A sunflower `F` with kernel `S` is a collection of sets in which all possible distinct
pairs of sets share the same intersection `S`. -/
def IsSunflowerWithKernel (F : Set (Set α)) (S : Set α) : Prop :=
  F.Pairwise (fun A B => A ∩ B = S)

/-- A sunflower `F` is a collection of sets in which all possible distinct pairs of sets
share the same intersection. -/
def IsSunflower (F : Set (Set α)) : Prop :=
  ∃ S, IsSunflowerWithKernel F S

/-- `sunflowerThreshold k r` is the least number `m` such that every family `F` of `k`-element
sets with at least `m` members contains a sunflower with `r` petals. -/
noncomputable def sunflowerThreshold (k r : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ f ∈ F, f.ncard = k) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = r ∧ IsSunflower S}

/-- The sunflower conjecture: the number of `k`-element sets required for the existence of a
sunflower with `r` petals can be bounded by an exponential function in `k`, for every fixed
`r > 2` (with `k ≥ 1`; for `k = 0` no family can force an `r > 2`-sunflower, as there is only
one empty set). -/
theorem main :
    ∃ c : ℕ → ℕ, ∀ k r, 0 < k → 2 < r → sunflowerThreshold k r < c r ^ k := by
  sorry

end OMA.S_wp_sunflower_conjecture
