import Mathlib

/-!
# On finding simpler symmetries to differential equations
Source: https://mathoverflow.net/questions/262592
Credit: @IgnacioCorrecher

The source asks for a representation and an invariance, without defining an
ordering on special functions. We exhibit the orbital family and characterize
the time integral by the normalized local Heun equation in one variable.
The latter is stated after removing its leading power, on the elliptic
interval. Bounded behavior with value one at zero selects the regular
solution (the other local exponent is negative). The time prefactor is
constant with respect to the integration variable and is suppressed.
The orbital equation uses 37/26 exactly as printed.
-/

namespace OMA.S_mo_262592

def k : ℝ := 121 / 304
def a : ℝ := 24 / 19
def q : ℝ := 1181 / 2299

def slope (x y : ℝ) : ℝ :=
  (12 / 19 : ℝ) * y * (1 + 73 / 24 * x^2 + 37 / 26 * x^4) /
    (x * (1 + k * x^2))

def orbit (x : ℝ) : ℝ :=
  |x| ^ (12 / 19 : ℝ) * (1 + k * x^2) ^ (-2673170 / 3616327 : ℝ) *
    Real.exp (1776 / 1573 * x^2)

def decay (e : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..e, u ^ (29 / 19 : ℝ) * (1 + k * u^2) ^ q /
    (1 - u^2) ^ (3 / 2 : ℝ)

def regularHeun (w : ℝ → ℝ) : Prop :=
  w 0 = 1 ∧ ContinuousWithinAt w (Set.Ici 0) 0 ∧
  ∀ z ∈ Set.Ioo (0 : ℝ) 1,
    DifferentiableAt ℝ w z ∧ DifferentiableAt ℝ (deriv w) z ∧
    deriv (deriv w) z +
      ((1 + a) / z + (3 / 2 : ℝ) / (z - 1) - q / (z + 1 / k)) * deriv w z +
      (a * (3 / 2 - q) * z + a * (3 / (2 * k) + q)) /
        (z * (z - 1) * (z + 1 / k)) * w z = 0

theorem main :
    (∀ x c : ℝ, x ≠ 0 →
      HasDerivAt (fun t => c * orbit t) (slope x (c * orbit x)) x) ∧
    (∀ x y c : ℝ, slope (-x) (c * y) = -(c * slope x y)) ∧
    (∀ y : ℝ → ℝ, (∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt y (slope x (y x)) x) →
      ∃ c : ℝ, ∀ x ∈ Set.Ioi (0 : ℝ), y x = c * orbit x) ∧
    (∃ w : ℝ → ℝ, regularHeun w ∧
      (∀ e ∈ Set.Ico (0 : ℝ) 1, decay e = (e^2) ^ a / (2 * a) * w (e^2)) ∧
      ∀ v : ℝ → ℝ, regularHeun v → Set.EqOn v w (Set.Ico 0 1)) := by
  sorry

end OMA.S_mo_262592
