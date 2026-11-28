import Mathlib

namespace OMA.S_wp_leopoldt_s_conjecture

open NumberField IsDedekindDomain
open scoped BigOperators

/-- The finite places of a number field above the rational prime p. -/
abbrev PlaceAbove (K : Type*) [Field K] [NumberField K] (p : ℕ) :=
  {v : HeightOneSpectrum (𝓞 K) // (p : 𝓞 K) ∈ v.asIdeal}

/-- The logarithm of a global unit in a finite-place completion. Raising to the
residue-field order minus one puts the unit in the group of principal units. -/
noncomputable def localLog {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (u : (𝓞 K)ˣ) : v.adicCompletion K :=
  let q := Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
  let x := algebraMap K (v.adicCompletion K) ((↑u : 𝓞 K) : K)
  let z := x ^ (q - 1) - 1
  ((q - 1 : ℕ) : v.adicCompletion K)⁻¹ *
    ∑' k : ℕ, (-1 : v.adicCompletion K) ^ k * z ^ (k + 1) /
      ((k + 1 : ℕ) : v.adicCompletion K)

/-- Leopoldt's conjecture in the simultaneous local logarithm formulation. -/
theorem main :
    ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime],
      ∃ scalar : (v : PlaceAbove K p) → ℚ_[p] →+* v.val.adicCompletion K,
        (∀ v, Continuous (scalar v)) ∧
        ∀ (m : ℕ) (u : Fin m → (𝓞 K)ˣ),
          (∀ a : Fin m → ℤ, (∏ i, u i ^ a i) = 1 → ∀ i, a i = 0) →
          ∀ b : Fin m → ℚ_[p],
            (∀ v, ∑ i, scalar v (b i) * localLog v.val (u i) = 0) →
            ∀ i, b i = 0 := by
  sorry

end OMA.S_wp_leopoldt_s_conjecture
