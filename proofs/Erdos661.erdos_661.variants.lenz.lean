import FormalConjectures.ErdosProblems.«661»

/-!
# Lenz's construction in `ℝ⁴`

Take `x_t = (3/5) * (u t, w t, 0, 0)` and `y_t = (4/5) * (0, 0, u t, w t)`, where
`(u t, w t) = ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))` is the rational parametrisation of
the unit circle. Then `dist x_s y_t ^ 2 = 9/25 + 16/25 = 1`. The map `t ↦ u t` is injective on
`ℕ`, so the points are distinct, and no `x_s` equals a `y_t` because `(u s, w s) ≠ (0, 0)`.

(The radii `3/5` and `4/5` replace the two radii `1/√2` of the usual description, to keep every
coordinate rational.)
-/

namespace OMA.E661

noncomputable def u (t : ℕ) : ℝ := (1 - (t : ℝ) ^ 2) / (1 + (t : ℝ) ^ 2)

noncomputable def w (t : ℕ) : ℝ := 2 * (t : ℝ) / (1 + (t : ℝ) ^ 2)

lemma circle (t : ℕ) : u t ^ 2 + w t ^ 2 = 1 := by
  have h : (1 + (t : ℝ) ^ 2) ≠ 0 := by positivity
  unfold u w
  field_simp
  ring

lemma u_injective : Function.Injective u := by
  intro s t h
  unfold u at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have h2 : (s : ℝ) ^ 2 = (t : ℝ) ^ 2 := by linear_combination (-1 / 2) * h
  have h3 : s ^ 2 = t ^ 2 := by exact_mod_cast h2
  exact Nat.pow_left_injective (by norm_num) h3

noncomputable def pA (t : ℕ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[3 / 5 * u t, 3 / 5 * w t, 0, 0]

noncomputable def pB (t : ℕ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[0, 0, 4 / 5 * u t, 4 / 5 * w t]

lemma pA_injective : Function.Injective pA := by
  intro s t h
  have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 4) => p 0) h
  simp only [pA] at h0
  have h1 : u s = u t := by
    have : (3 / 5 : ℝ) * u s = 3 / 5 * u t := by simpa using h0
    linarith
  exact u_injective h1

lemma pB_injective : Function.Injective pB := by
  intro s t h
  have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 4) => p 2) h
  simp only [pB] at h0
  have h1 : u s = u t := by
    have : (4 / 5 : ℝ) * u s = 4 / 5 * u t := by simpa using h0
    linarith
  exact u_injective h1

lemma pA_ne_pB (s t : ℕ) : pA s ≠ pB t := by
  intro h
  have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 4) => p 0) h
  have h1 := congrArg (fun p : EuclideanSpace ℝ (Fin 4) => p 1) h
  simp only [pA, pB] at h0 h1
  have e0 : (3 / 5 : ℝ) * u s = 0 := by simpa using h0
  have e1 : (3 / 5 : ℝ) * w s = 0 := by simpa using h1
  have hu : u s = 0 := by linarith
  have hw : w s = 0 := by linarith
  have := circle s
  rw [hu, hw] at this
  norm_num at this

lemma dist_pA_pB (s t : ℕ) : dist (pA s) (pB t) = 1 := by
  rw [EuclideanSpace.dist_eq, Real.sqrt_eq_one, Fin.sum_univ_four]
  simp only [pA, pB, Real.dist_eq, sq_abs]
  have hs := circle s
  have ht := circle t
  simp
  linear_combination (9 / 25) * hs + (16 / 25) * ht

end OMA.E661

theorem OMA.solution : type_of% @Erdos661.erdos_661.variants.lenz := by
  intro n
  refine ⟨(Finset.range n).image OMA.E661.pA, (Finset.range n).image OMA.E661.pB, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ OMA.E661.pA_injective, Finset.card_range]
  · rw [Finset.card_image_of_injective _ OMA.E661.pB_injective, Finset.card_range]
  · rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨t, -, ht⟩ := Finset.mem_image.1 hy
    exact OMA.E661.pA_ne_pB s t ht.symm
  · intro x hx y hy
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hy
    exact OMA.E661.dist_pA_pB s t
