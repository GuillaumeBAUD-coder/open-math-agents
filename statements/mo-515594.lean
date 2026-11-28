import Mathlib

/-!
# Hadamard powers of the Pascal matrix

Source: VSP, https://mathoverflow.net/questions/515594 (CC BY-SA 4.0).
Credit: @connoranderson.

The strict-positivity assertion for all positive exponents is false. A
three-by-three separated minor is negative at a positive exponent and
singular at another. For every separated three-by-three minor, positivity
does hold on the full range of exponents at least one.
-/

namespace OMA.S_mo_515594

noncomputable def minor {k : ℕ} (a b : Fin k → ℕ) (r : ℝ) : ℝ :=
  (Matrix.of (fun i j => ((a i).choose (b j) : ℝ)^r)).det

theorem main : (¬ ∀ (k : ℕ) (a b : Fin k → ℕ), StrictMono a → StrictMono b →
      (∀ i j, b j < a i) → ∀ r : ℝ, 0 < r → 0 < minor a b r) ∧
    (∃ r : ℝ, 0 < r ∧ r < 1 ∧ minor ![3,4,5] ![0,1,2] r < 0 ∧
      ∃ s ∈ Set.Ioo r 1, minor ![3,4,5] ![0,1,2] s = 0) ∧
    (∀ a b : Fin 3 → ℕ, StrictMono a → StrictMono b → (∀ i j, b j < a i) →
      ∀ r : ℝ, 1 ≤ r → 0 < minor a b r) ∧
    ∀ (k : ℕ) (a b : Fin k → ℕ), StrictMono a → StrictMono b → (∀ i j, b j < a i) →
      ∀ᶠ r : ℝ in Filter.atTop, 0 < minor a b r := by
  sorry

end OMA.S_mo_515594
