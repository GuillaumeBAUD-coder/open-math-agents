import OMAStatements.S_oeis_a108476

-- Problem: A108476: Expansion of (1-4*x)/(1-6*x-12*x^2+8*x^3).
-- Upstream: formal-conjectures statements/oeis-a108476.lean:0 (declaration OMA.S_oeis_a108476.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a108476

open OMA.S_oeis_a108476 PowerSeries

def c (n : ℕ) : ℤ := A002605 (n + 1) * A026150 n

lemma c_rec (n : ℕ) : c (n + 3) = 6 * c (n + 2) + 12 * c (n + 1) - 8 * c n := by
  simp only [c, A002605, A026150]
  ring

lemma key : mk (fun n => (c n : ℚ)) * (1 - 6 * X - 12 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ) =
    1 - 4 * X := by
  have r (k : ℕ) : (c (k + 3) : ℚ) = 6 * c (k + 2) + 12 * c (k + 1) - 8 * c k := by
    exact_mod_cast c_rec k
  ring_nf
  ext n
  rcases n with _ | _ | _ | n <;> simp [coeff_mul_X_pow', coeff_X, ← map_ofNat C,
    coeff_mul_C, r, show c 0 = 1 by decide, show c 1 = 2 by decide, show c 2 = 24 by decide] <;> ring

lemma solve : ∀ n : ℕ, a n = A002605 (n + 1) * A026150 n := by
  have hu : IsUnit (1 - 6 * X - 12 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ) := by
    rw [isUnit_iff_constantCoeff]
    simp
  have h : (1 - 4 * X : PowerSeries ℚ) * (1 - 6 * X - 12 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ)⁻¹ =
      mk (fun n => (c n : ℚ)) := by
    rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), mul_one]
  intro n
  unfold a
  rw [h, coeff_mk]
  simp [c]

end OMA.P_oeis_a108476

theorem OMA.solution : type_of% @OMA.S_oeis_a108476.main := OMA.P_oeis_a108476.solve
