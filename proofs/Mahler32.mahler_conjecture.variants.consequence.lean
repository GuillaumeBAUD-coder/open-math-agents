import FormalConjectures.Wikipedia.Mahler32

/-!
Mahler's 3/2 problem: if `1/2 < Ω(3/2)` then there are no Z-numbers.
For a Z-number `x`, take `θ = x`: every `{x (3/2)^n}` (n ≥ 1) lies in `[0, 1/2)`,
so `limsup ≤ 1/2` and `liminf ≥ 0`, hence `Ω(3/2) ≤ 1/2`.
-/

theorem OMA.solution : type_of% @Mahler32.mahler_conjecture.variants.consequence := by
  intro H x hx
  obtain ⟨hx0, hfr⟩ := hx
  have hb : BddBelow {Filter.atTop.limsup (fun n ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n))
      - Filter.atTop.liminf (fun n ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n)) |
        (θ : ℝ) (_ : 0 < θ)} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨θ, -, rfl⟩
    exact sub_nonneg.mpr (Filter.liminf_le_limsup
      (Filter.isBoundedUnder_of ⟨1, fun n ↦ (Int.fract_lt_one _).le⟩)
      (Filter.isBoundedUnder_of ⟨0, fun n ↦ Int.fract_nonneg _⟩))
  have hmem : Filter.atTop.limsup (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n))
      - Filter.atTop.liminf (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) ∈
      {Filter.atTop.limsup (fun n ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n))
        - Filter.atTop.liminf (fun n ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n)) |
          (θ : ℝ) (_ : 0 < θ)} :=
    ⟨x, hx0, rfl⟩
  have hsup : Filter.atTop.limsup (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) ≤ 1 / 2 := by
    refine Filter.limsup_le_of_le
      (Filter.isBoundedUnder_of ⟨0, fun n ↦ Int.fract_nonneg _⟩).isCoboundedUnder_le ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (hfr n hn).le
  have hinf : 0 ≤ Filter.atTop.liminf (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) :=
    Filter.le_liminf_of_le
      (Filter.isBoundedUnder_of ⟨1, fun n ↦ (Int.fract_lt_one _).le⟩).isCoboundedUnder_ge
      (Filter.Eventually.of_forall fun n ↦ Int.fract_nonneg _)
  have hle : Mahler32.Ω (3 / 2) ≤ 1 / 2 := (csInf_le hb hmem).trans (by linarith)
  linarith
