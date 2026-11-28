import FormalConjectures.Wikipedia.Bloch

-- Reduction Bloch.blochConstant_upper_bound.R1 of the Ahlfors-Grunsky upper bound for Bloch's constant
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The Ahlfors–Grunsky upper bound for Bloch's constant

Following L. V. Ahlfors and H. Grunsky, *Über die Blochsche Konstante*, Math. Z. 42 (1937),
671–673. Write `c = Γ(1/3) Γ(11/12) / (Γ(1/4) √(1 + √3))` and let `Λ_c` be the triangular lattice
whose points are the vertices of the tiling of the plane by equilateral triangles of circumradius
`c`, placed so that `0` is the centre of one triangle.

* `H1` (Ahlfors–Grunsky, the deep input): there is a holomorphic `f` on the unit disk with
  `f'(0) = 1` such that every point of the disk that `f` sends to `Λ_c` is a critical point
  of `f`. The function is the Schwarz triangle map from the hyperbolic equilateral triangle with
  angles `π/6` centred at `0` onto the Euclidean equilateral triangle centred at `0`, continued by
  reflection; angles double at the vertices, so every vertex is a simple critical point, and the
  normalisation `f'(0) = 1` makes the Euclidean circumradius equal to `c`.
* `H2` (covering radius of the triangular lattice, elementary plane geometry): for `c > 0`,
  every open disk of radius `r > c` contains a point of `Λ_c`.
* `H3` (a holomorphic function that is injective on an open set has nowhere vanishing derivative
  there; standard, absent from Mathlib in this form).

`main`: if `B > c` were admissible for the Bloch constant, `f` would have a schlicht disk
`f '' S = ball x B`; by `H2` it contains a lattice point `f z`, `z ∈ S`; by `H1` `f' z = 0`,
contradicting `H3`.
-/

namespace OMA.R_Bloch_blochConstant_upper_bound_R1

open Metric Set

/-- Ahlfors–Grunsky 1937: a holomorphic function on the unit disk with `f'(0) = 1`, all of whose
points over the triangular lattice of circumradius `Γ(1/3) Γ(11/12) / (Γ(1/4) √(1 + √3))` are
critical points. The lattice consists of the points `c (1 + m (ζ - 1) + n (ζ² - 1))` with
`m n : ℤ` and `ζ = e^(2πi/3) = -1/2 + (√3/2) i`; `0` is the centre of one of its triangles. -/
def H1 : Prop :=
  ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) ∧ deriv f 0 = 1 ∧
    ∀ z ∈ ball (0 : ℂ) 1,
      (∃ m n : ℤ, f z = ((Real.Gamma (1 / 3) * Real.Gamma (11 / 12) / (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3)) : ℝ) : ℂ) *
        (1 + (m : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 1) +
          (n : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 - 1))) →
      deriv f z = 0

/-- The triangular lattice of circumradius `c` has covering radius `c`: every open disk of
radius `r > c` contains a lattice point. -/
def H2 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (x : ℂ) (r : ℝ), c < r →
    ∃ w : ℂ, (∃ m n : ℤ, w = ((c : ℝ) : ℂ) *
        (1 + (m : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 1) +
          (n : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 - 1))) ∧
      w ∈ ball x r

/-- A holomorphic function that is injective on an open set has nonvanishing derivative there. -/
def H3 : Prop :=
  ∀ (f : ℂ → ℂ) (S : Set ℂ), IsOpen S → DifferentiableOn ℂ f S → InjOn f S →
    ∀ z ∈ S, deriv f z ≠ 0

theorem main : H1 → H2 → H3 → type_of% @Bloch.blochConstant_upper_bound := by
  intro h1 h2 h3
  obtain ⟨f, hf, hf0, hcrit⟩ := h1
  have hc : (0 : ℝ) < Real.Gamma (1 / 3) * Real.Gamma (11 / 12) /
      (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3)) := by
    have h1 : (0 : ℝ) < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
    have h2 : (0 : ℝ) < Real.Gamma (11 / 12) := Real.Gamma_pos_of_pos (by norm_num)
    have h3 : (0 : ℝ) < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
    have h4 : (0 : ℝ) < Real.sqrt (1 + Real.sqrt 3) :=
      Real.sqrt_pos.2 (by positivity)
    positivity
  unfold Bloch.blochConstant
  refine csSup_le ⟨0, fun g _ _ => ⟨∅, isOpen_empty, empty_subset _, 0, by simp⟩⟩ ?_
  intro B hB
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨S, hSo, hS, x, himg, hinj⟩ := hB f hf hf0
  obtain ⟨w, hwL, hwb⟩ := h2 _ hc x B hlt
  rw [← himg] at hwb
  obtain ⟨z, hz, rfl⟩ := hwb
  exact h3 f S hSo (hf.mono hS) hinj z hz (hcrit z (hS hz) hwL)

end OMA.R_Bloch_blochConstant_upper_bound_R1
