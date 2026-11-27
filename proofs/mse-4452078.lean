import OMAStatements.S_mse_4452078
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- Disproof. If f'/f^2 tends to infinity then g = -1/f has derivative at least 1 eventually,
-- so g is unbounded above; but |f| nondecreasing and eventually nonzero keeps |g| bounded.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_4452078.main) := by
  rintro ⟨f, x₀, hd, hmono, ht⟩
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop 1)
  set a := max A (x₀ + 1) with ha
  have hne : ∀ x, a ≤ x → f x ≠ 0 := by
    intro x hx h0
    have := hA x (le_trans (le_max_left _ _) hx)
    rw [h0] at this
    norm_num at this
  have hdiff : ∀ x, a ≤ x → DifferentiableAt ℝ f x := fun x hx =>
    hd x (by have := le_max_right A (x₀ + 1); linarith)
  have hder : ∀ x, a ≤ x →
      HasDerivAt (fun y => -(f y)⁻¹) (deriv f x / f x ^ 2) x := by
    intro x hx
    have h := (HasDerivAt.inv (hdiff x hx).hasDerivAt (hne x hx)).neg
    have e : -(-deriv f x / f x ^ 2) = deriv f x / f x ^ 2 := by ring
    rw [e] at h
    exact h
  have hcont : ContinuousOn (fun y => -(f y)⁻¹) (Set.Ici a) := fun x hx =>
    (hder x hx).continuousAt.continuousWithinAt
  have hdon : DifferentiableOn ℝ (fun y => -(f y)⁻¹) (interior (Set.Ici a)) := by
    rw [interior_Ici]
    intro x hx
    exact (hder x (le_of_lt hx)).differentiableAt.differentiableWithinAt
  have hge : ∀ x ∈ interior (Set.Ici a), (1 : ℝ) ≤ deriv (fun y => -(f y)⁻¹) x := by
    rw [interior_Ici]
    intro x hx
    rw [(hder x (le_of_lt hx)).deriv]
    exact hA x (le_trans (le_max_left _ _) (le_of_lt hx))
  have key := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Ici a) hcont hdon hge
  have hfa : 0 < |f a| := abs_pos.2 (hne a le_rfl)
  set x := a + 2 / |f a| + 1 with hx
  have hax : a ≤ x := by
    have : 0 < 2 / |f a| := by positivity
    linarith
  have h1 := key a (Set.mem_Ici.2 le_rfl) x (Set.mem_Ici.2 hax) hax
  have hbound : ∀ y, a ≤ y → |(f y)⁻¹| ≤ 1 / |f a| := by
    intro y hy
    rw [abs_inv, one_div]
    exact inv_anti₀ hfa (hmono hy)
  have b1 := hbound x hax
  have b2 := hbound a le_rfl
  have c1 := neg_le_abs ((f x)⁻¹)
  have c2 := le_abs_self ((f a)⁻¹)
  have : x - a = 2 / |f a| + 1 := by rw [hx]; ring
  rw [this] at h1
  have e : 2 / |f a| = 2 * (1 / |f a|) := by ring
  linarith
