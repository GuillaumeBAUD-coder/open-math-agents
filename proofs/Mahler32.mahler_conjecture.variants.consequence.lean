import FormalConjectures.Wikipedia.Mahler32

-- Mahler's conjecture follows from the proposed bound on the width of limit points.
-- Credit: @harshshah1618

open Filter

theorem OMA.solution : type_of% @Mahler32.mahler_conjecture.variants.consequence := by
  intro H x hx
  let f : ℝ → ℕ → ℝ := fun θ n => Int.fract (θ * (3 / 2 : ℝ) ^ n)
  have hupper (θ : ℝ) : IsBoundedUnder (· ≤ ·) atTop (f θ) :=
    isBoundedUnder_of ⟨1, fun n => (Int.fract_lt_one (θ * (3 / 2 : ℝ) ^ n)).le⟩
  have hlower (θ : ℝ) : IsBoundedUnder (· ≥ ·) atTop (f θ) :=
    isBoundedUnder_of ⟨0, fun n => Int.fract_nonneg (θ * (3 / 2 : ℝ) ^ n)⟩
  have hwidth (θ : ℝ) : 0 ≤ limsup (f θ) atTop - liminf (f θ) atTop :=
    sub_nonneg.mpr (liminf_le_limsup (hupper θ) (hlower θ))
  have hΩ : Mahler32.Ω (3 / 2) ≤ limsup (f x) atTop - liminf (f x) atTop := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨θ, hθ, rfl⟩
      exact hwidth θ
    · exact ⟨x, hx.1, rfl⟩
  have hsup : limsup (f x) atTop ≤ 1 / 2 := by
    apply limsup_le_of_le (hlower x).isCoboundedUnder_le
    exact (eventually_ge_atTop 1).mono fun n hn => (hx.2 n hn).le
  have hinf : 0 ≤ liminf (f x) atTop :=
    le_liminf_of_le (hupper x).isCoboundedUnder_ge
      (Eventually.of_forall fun n => Int.fract_nonneg _)
  linarith
