import OMAReductions.R_Erdos173_erdos_173_R1

-- Reduction adapted from the public proof by Jacob Parish (Plasma AI), Apache-2.0.
-- https://github.com/plasma-ai/erdos-173/tree/4a368a652753
-- TwoScale and Transfer.Exclusion separate the far-scale spectral estimate,
-- the measurable transfer at nearby scales, and the circle exclusion.
-- The normalization from the pinned plane to complex coordinates is supplied here.

namespace OMA.R_Erdos173_erdos_173_R1_H2_R1

open MeasureTheory

def H1 : Prop :=
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  let avoids (c : ℂ → Fin 2) (r : ℝ) := ∀ p u : ℂ, ‖u‖ = 1 →
    ¬ (c (p + u * r) = c p ∧ c (p + u * (r * ζ)) = c p)
  ∀ x : ℝ, 0 < x → (3 / 2 ≤ x ∨ x ≤ 2 / 3) →
    ∀ c : ℂ → Fin 2, avoids c 1 → avoids c x → False

def H2 : Prop :=
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  let avoids (c : ℂ → Fin 2) (r : ℝ) := ∀ p u : ℂ, ‖u‖ = 1 →
    ¬ (c (p + u * r) = c p ∧ c (p + u * (r * ζ)) = c p)
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let weak (c : ℂ → Fin 2) (r : ℝ) :=
    ∀ᵐ q : ℂ × AddCircle (2 * Real.pi) ∂(volume : Measure ℂ).prod AddCircle.haarAddCircle,
      let u : ℂ := AddCircle.toCircle q.2
      ¬ (c (q.1 + u * r) = c q.1 ∧ c (q.1 + u * (r * ζ)) = c q.1)
  ∀ x : ℝ, 2 / 3 < x → x < 3 / 2 → x ≠ 1 →
    ∀ c : ℂ → Fin 2, avoids c 1 → avoids c x →
      ∃ d : ℂ → Fin 2, Measurable d ∧ weak d 1 ∧ weak d x

def H3 : Prop :=
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let weak (c : ℂ → Fin 2) (r : ℝ) :=
    ∀ᵐ q : ℂ × AddCircle (2 * Real.pi) ∂(volume : Measure ℂ).prod AddCircle.haarAddCircle,
      let u : ℂ := AddCircle.toCircle q.2
      ¬ (c (q.1 + u * r) = c q.1 ∧ c (q.1 + u * (r * ζ)) = c q.1)
  ∀ x : ℝ, 2 / 3 < x → x < 3 / 2 → x ≠ 1 →
    ∀ d : ℂ → Fin 2, Measurable d → weak d 1 → weak d x → False

theorem main : H1 → H2 → H3 → OMA.R_Erdos173_erdos_173_R1.H2 := by
  intro far transfer circle c s t hs ht missS missT
  by_contra hst
  let x := t / s
  have hx : 0 < x := div_pos ht hs
  have hx1 : x ≠ 1 := by simpa [x, div_eq_one_iff_eq hs.ne'] using Ne.symm hst
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  have hζ : ‖ζ‖ = 1 := by
    rw [Complex.norm_def, Real.sqrt_eq_one]
    simp [ζ, Complex.normSq]
    ring_nf
    norm_num
  have hζ' : ‖1 - ζ‖ = 1 := by
    rw [Complex.norm_def, Real.sqrt_eq_one]
    simp [ζ, Complex.normSq]
    ring_nf
    norm_num
  let e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  let d (z : ℂ) := c (e ((s : ℂ) * z))
  have miss (r : ℝ) (hr : 0 < r)
      (h : ∀ v : Fin 3 → EuclideanSpace ℝ (Fin 2),
        (∀ i j, i ≠ j → dist (v i) (v j) = s*r) → ¬ ∃ k, ∀ i, c (v i) = k)
      (p u : ℂ) (hu : ‖u‖ = 1) :
      ¬ (d (p + u * r) = d p ∧ d (p + u * (r * ζ)) = d p) := by
    rintro ⟨h₁, h₂⟩
    let f (z : ℂ) := e ((s : ℂ) * (p + u * ((r : ℂ) * z)))
    have hf (a b : ℂ) : dist (f a) (f b) = s * r * ‖a - b‖ := by
      rw [LinearIsometryEquiv.dist_map, dist_eq_norm]
      simp only [← mul_sub, add_sub_add_left_eq_sub, norm_mul, hu, one_mul,
        Complex.norm_real, Real.norm_of_nonneg hs.le, Real.norm_of_nonneg hr.le]
      ring
    let v : Fin 3 → EuclideanSpace ℝ (Fin 2) := fun i => f (![0,1,ζ] i)
    apply h v
    · intro i j hij
      change dist (f _) (f _) = _
      rw [hf]
      fin_cases i <;> fin_cases j <;> simp_all [norm_sub_rev ζ 1]
    · refine ⟨d p, ?_⟩
      intro i
      fin_cases i
      · simp [v, f, d]
      · simpa [v, f, d] using h₁
      · simpa [v, f, d] using h₂
  have one := miss 1 zero_lt_one (by simpa using missS)
  have other := miss x hx (by simpa [x, mul_div_cancel₀ _ hs.ne'] using missT)
  by_cases hfar : 3/2 ≤ x ∨ x ≤ 2/3
  · exact far x hx hfar d one other
  push Not at hfar
  obtain ⟨d', hd, h₁, h₂⟩ := transfer x hfar.2 hfar.1 hx1 d one other
  exact circle x hfar.2 hfar.1 hx1 d' hd h₁ h₂
end OMA.R_Erdos173_erdos_173_R1_H2_R1
