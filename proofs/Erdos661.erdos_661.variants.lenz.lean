import FormalConjectures.ErdosProblems.«661»

-- Problem: Erdős Problem 661 — lenz
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/661.lean:138 (declaration Erdos661.erdos_661.variants.lenz)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

/-- First coordinate of the `k`-th point on the circle. -/
noncomputable def cx (n k : ℕ) : ℝ := (k : ℝ) / (2 * n + 2)

/-- Second coordinate of the `k`-th point on the circle of radius `1 / √2`. -/
noncomputable def cy (n k : ℕ) : ℝ := Real.sqrt (1 / 2 - cx n k ^ 2)

lemma cx_nonneg (n k : ℕ) : 0 ≤ cx n k := by
  unfold cx; positivity

lemma cx_lt (n k : ℕ) (hk : k < n) : cx n k < 1 / 2 := by
  unfold cx
  rw [div_lt_iff₀ (by positivity)]
  have : (k : ℝ) < n := by exact_mod_cast hk
  linarith

lemma cx_sq_lt (n k : ℕ) (hk : k < n) : cx n k ^ 2 < 1 / 2 := by
  have h0 := cx_nonneg n k
  have h1 := cx_lt n k hk
  nlinarith

lemma cy_sq (n k : ℕ) (hk : k < n) : cy n k ^ 2 = 1 / 2 - cx n k ^ 2 := by
  unfold cy
  rw [Real.sq_sqrt (by linarith [cx_sq_lt n k hk])]

lemma cy_pos (n k : ℕ) (hk : k < n) : 0 < cy n k := by
  unfold cy
  exact Real.sqrt_pos.mpr (by linarith [cx_sq_lt n k hk])

lemma cx_injective (n : ℕ) : Function.Injective (cx n) := by
  intro a b h
  unfold cx at h
  have hpos : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
  rw [div_left_inj' hpos] at h
  exact_mod_cast h

/-- Points in the plane of the first two coordinates. -/
noncomputable def ptA (n k : ℕ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![cx n k, cy n k, 0, 0]

/-- Points in the plane of the last two coordinates. -/
noncomputable def ptB (n k : ℕ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![0, 0, cx n k, cy n k]

lemma ptA_injective (n : ℕ) : Function.Injective (ptA n) := by
  intro a b h
  have := congrArg (fun p : EuclideanSpace ℝ (Fin 4) => p 0) h
  simp [ptA] at this
  exact cx_injective n this

lemma ptB_injective (n : ℕ) : Function.Injective (ptB n) := by
  intro a b h
  have := congrArg (fun p : EuclideanSpace ℝ (Fin 4) => p 2) h
  simp [ptB] at this
  exact cx_injective n this

end OMA

theorem OMA.solution : type_of% @Erdos661.erdos_661.variants.lenz := by
  intro n
  refine ⟨(Finset.range n).image (OMA.ptA n), (Finset.range n).image (OMA.ptB n), ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (OMA.ptA_injective n), Finset.card_range]
  · rw [Finset.card_image_of_injective _ (OMA.ptB_injective n), Finset.card_range]
  · rw [Finset.disjoint_left]
    intro p hpA hpB
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hpA
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hpB
    have := congrArg (fun p : EuclideanSpace ℝ (Fin 4) => p 1) hji
    simp [OMA.ptA, OMA.ptB] at this
    exact (OMA.cy_pos n i (Finset.mem_range.mp hi)).ne this
  · intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_four]
    simp only [OMA.ptA, OMA.ptB, Real.dist_eq, sq_abs]
    simp
    have h1 := OMA.cy_sq n i hi'
    have h2 := OMA.cy_sq n j hj'
    rw [show (OMA.cx n i ^ 2 + OMA.cy n i ^ 2 + OMA.cx n j ^ 2 + OMA.cy n j ^ 2) = 1 by
      rw [h1, h2]; ring]
