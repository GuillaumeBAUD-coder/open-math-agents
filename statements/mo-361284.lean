import Mathlib

/-!
# A sharp integral inequality from prefix bounds on the third moment

Source: Ivan, https://mathoverflow.net/questions/361284 (CC BY-SA 4.0).
Credit: @connoranderson.

Integrability of the cube on each finite interval expresses the finiteness of
the cubic integral in the source's hypothesis. Only nonnegative arguments of
the function matter.
-/

namespace OMA.S_mo_361284

open MeasureTheory

theorem main : ∀ f : ℝ → ℝ, (∀ x, 0 ≤ x → 0 ≤ f x) →
    (∀ t : ℝ, 0 < t → IntervalIntegrable f volume 0 t ∧
      IntervalIntegrable (fun x => (f x)^3) volume 0 t ∧
      (∫ x in (0:ℝ)..t, (f x)^3) ≤ (∫ x in (0:ℝ)..t, f x)^2) →
    ∀ γ : ℝ, γ ∈ Set.Icc 1 3 → ∀ t : ℝ, 0 < t →
      IntervalIntegrable (fun x => (f x)^γ) volume 0 t ∧
      (∫ x in (0:ℝ)..t, (f x)^γ) ≤ (2*(∫ x in (0:ℝ)..t, f x))^((γ+1)/2)/(γ+1) := by
  sorry

end OMA.S_mo_361284
