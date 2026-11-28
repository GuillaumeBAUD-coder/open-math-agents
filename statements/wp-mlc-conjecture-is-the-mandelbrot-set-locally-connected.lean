import Mathlib

namespace OMA.S_wp_mlc_conjecture_is_the_mandelbrot_set_locally_connected

/-- The quadratic polynomial with complex parameter c. -/
def quadratic (c z : ℂ) : ℂ := z ^ 2 + c

/-- The parameters for which the forward orbit of the critical point is bounded. -/
def mandelbrot : Set ℂ :=
  {c | ∃ R : ℝ, ∀ n : ℕ, ‖(quadratic c)^[n] 0‖ ≤ R}

theorem main : LocallyConnectedSpace ↥mandelbrot := by
  sorry

end OMA.S_wp_mlc_conjecture_is_the_mandelbrot_set_locally_connected
