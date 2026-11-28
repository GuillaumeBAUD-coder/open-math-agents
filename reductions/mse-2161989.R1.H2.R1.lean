import OMAReductions.R_mse_2161989_R1
import Mathlib

namespace OMA.R_mse_2161989_R1_H2_R1

open OMA.S_mse_2161989

-- The third power of the fundamental unit supplies a shorter denominator.
def H1 : Prop :=
  ∀ p t : ℕ, p.Prime →
    3 + 4 * p * (f p)^2 < t →
    t ∣ (3 + 4 * p * (f p)^2) * f p →
    f (p * t^2) < f p

-- Beyond the original two cases, also exclude the third-power descent.
def H2 : Prop :=
  ∀ s : ℕ, 46 < s → ¬ s.Prime → ¬ IsSquare s →
    (∀ p t : ℕ, p.Prime → 1 < t → s = p * t^2 →
      ¬ (t ∣ f p ∨ ∃ a : ℕ, p * (f p)^2 + 1 = a * a ∧
        2 * a < t ∧ t ∣ 2 * a * f p)) →
    (∀ p t : ℕ, p.Prime → s = p * t^2 →
      3 + 4 * p * (f p)^2 < t →
      ¬ t ∣ (3 + 4 * p * (f p)^2) * f p) →
    ∃ p : ℕ, p.Prime ∧ p < s ∧ f s < f p

theorem main : H1 → H2 → OMA.R_mse_2161989_R1.H2 := by
  classical
  intro cubic residual s hs hcomp hns hold
  by_cases hit : ∃ p t : ℕ, p.Prime ∧ s = p * t^2 ∧
      3 + 4 * p * (f p)^2 < t ∧ t ∣ (3 + 4 * p * (f p)^2) * f p
  · obtain ⟨p, t, hp, rfl, ht, hd⟩ := hit
    have ht1 : 1 < t := by omega
    have hsq : 1 < t^2 := by nlinarith
    have hp' : p < p * t^2 := by
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hsq hp.pos
    exact ⟨p, hp, hp', cubic p t hp ht hd⟩
  · exact residual s hs hcomp hns hold
      (fun p t hp he ht hd => hit ⟨p, t, hp, he, ht, hd⟩)

end OMA.R_mse_2161989_R1_H2_R1
