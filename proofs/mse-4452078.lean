import OMAStatements.S_mse_4452078
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-!
# Complete negative answer to the derivative-ratio existence question

Problem: https://lefttosolve.com/p/mse-4452078
Source question: Mathematics Stack Exchange 4452078, user1058535, 16 May 2022.

The main result proves impossibility under the weaker assumption that absolute
value is nondecreasing only on a tail. The reciprocal is bounded below there,
but its derivative would eventually be at most minus one. The mean value
inequality gives a contradiction. No sign restriction, derivative continuity,
or additional nonvanishing assumption is required.

This is an elementary calculus argument; no research-novelty claim is made.
-/

open Filter Set

namespace OMA.MSE4452078

lemma bounded_below_not_uniformly_negative_derivative
    {g : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x : ℝ, a < x → DifferentiableAt ℝ g x)
    (hb : ∀ x : ℝ, a < x → b ≤ g x)
    (hd : ∀ x : ℝ, a < x → deriv g x ≤ -1) : False := by
  have hgon : DifferentiableOn ℝ g (Ioi a) := fun z hz => (hg z hz).differentiableWithinAt
  have hm := (convex_Ioi a).image_sub_le_mul_sub_of_deriv_le hgon.continuousOn
    (by rwa [isOpen_Ioi.interior_eq]) (by simpa [isOpen_Ioi.interior_eq] using hd)
    (a + 1) (by simp) (a + 1 + (g (a + 1) - b) + 1) (by simp; linarith [hb (a + 1) (by simp)])
    (by linarith [hb (a + 1) (by simp)])
  linarith [hb (a + 1) (by simp), hb (a + 1 + (g (a + 1) - b) + 1) (by linarith [hb (a + 1) (by simp)])]

lemma inv_lower_bound_of_abs_le {u v : ℝ}
    (hv : v ≠ 0) (h : |v| ≤ |u|) :
    -|v|⁻¹ ≤ u⁻¹ := by
  have hinv : |u|⁻¹ ≤ |v|⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (abs_pos.mpr hv) h
  calc
    -|v|⁻¹ ≤ -|u|⁻¹ := neg_le_neg hinv
    _ = -|u⁻¹| := by rw [abs_inv]
    _ ≤ u⁻¹ := neg_abs_le _

theorem no_square_ratio_divergence
    {f : ℝ → ℝ} {x₀ : ℝ}
    (hdiff : ∀ x : ℝ, x₀ < x → DifferentiableAt ℝ f x)
    (hmono : MonotoneOn (fun x : ℝ => |f x|) (Ioi x₀)) :
    ¬ Tendsto (fun x : ℝ => deriv f x / (f x) ^ 2) atTop atTop := by
  intro hlim
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hlim.eventually (eventually_ge_atTop (1 : ℝ)))
  let t := max a x₀ + 1
  have hat : a ≤ t := by dsimp [t]; linarith [le_max_left a x₀]
  have hxt : x₀ < t := by dsimp [t]; linarith [le_max_right a x₀]
  have hnonzero : ∀ x : ℝ, t ≤ x → f x ≠ 0 := by
    intro x hx hzero
    have hratio := ha x (hat.trans hx)
    simp [hzero] at hratio
    linarith
  apply bounded_below_not_uniformly_negative_derivative
    (g := fun x : ℝ => (f x)⁻¹) (a := t) (b := -|f t|⁻¹)
  · intro x hx
    exact (hdiff x (hxt.trans hx)).inv (hnonzero x hx.le)
  · intro x hx
    exact inv_lower_bound_of_abs_le (hnonzero t le_rfl)
      (hmono hxt (hxt.trans hx) hx.le)
  · intro x hx
    rw [deriv_fun_inv'' (hdiff x (hxt.trans hx)) (hnonzero x hx.le), neg_div]
    have hratio := ha x (hat.trans hx.le)
    linarith

end OMA.MSE4452078

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_4452078.main) := by
  rintro ⟨f, x₀, hdiff, hmono, hlim⟩
  exact OMA.MSE4452078.no_square_ratio_divergence hdiff (hmono.monotoneOn _) hlim
