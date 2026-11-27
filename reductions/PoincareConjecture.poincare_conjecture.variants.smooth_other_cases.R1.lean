import FormalConjectures.Millennium.Poincare

-- Reduction PoincareConjecture.poincare_conjecture.variants.smooth_other_cases.R1 of PoincareConjecture — smooth other cases
-- Credit: @STRML
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open scoped Manifold ContDiff EuclideanGeometry ContinuousMap

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_other_cases_R1

/-- Odd dimensions congruent to 3 mod 4 (n = 7, 11, 15, ...): the classical Kervaire-Milnor
bP_{4k} regime where exotic spheres arise from plumbing. -/
def H1 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ¬ PoincareConjecture.SmoothConjectureFor.{0} (4 * k - 1)

/-- Odd dimensions congruent to 1 mod 4 (n = 9, 13, 17, ..., excluding 5 and 61): the Kervaire
invariant one regime (Browder, Hill-Hopkins-Ravenel, Wang-Xu, Lin-Wang-Xu). -/
def H2 : Prop :=
  ∀ k : ℕ, 2 ≤ k → k ≠ 15 → ¬ PoincareConjecture.SmoothConjectureFor.{0} (4 * k + 1)

/-- Even dimensions n > 4 excluding 6, 12, and 56 (n = 8, 10, 14, ...): the open frontier of
Conjecture 1.17 in Wang-Xu (2017), where bP_{2k+1} = 0 and Theta_{2k} is controlled by coker J. -/
def H3 : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≠ 6 → k ≠ 28 → ¬ PoincareConjecture.SmoothConjectureFor.{0} (2 * k)

lemma smoothConjectureFor_down.{u} (n : ℕ)
    (h : PoincareConjecture.SmoothConjectureFor.{u} n) :
    PoincareConjecture.SmoothConjectureFor.{0} n := by
  intro M _ _ _ _ he
  let hU : OpenPartialHomeomorph (ULift.{u} M) M := Homeomorph.ulift.toOpenPartialHomeomorph
  letI : ChartedSpace (ℝ^n) (ULift.{u} M) :=
    { atlas := {e | ∃ e' ∈ atlas (ℝ^n) M, e = hU.trans e'}
      chartAt := fun x => hU.trans (chartAt (ℝ^n) x.down)
      mem_chart_source := fun x => by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨Set.mem_univ x, mem_chart_source (ℝ^n) x.down⟩
      chart_mem_atlas := fun x => ⟨chartAt (ℝ^n) x.down, chart_mem_atlas (ℝ^n) x.down, rfl⟩ }
  haveI : HasGroupoid (ULift.{u} M) (contDiffGroupoid ∞ (𝓡 n)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, rfl⟩
    have hEq : (hU.trans e₁).symm.trans (hU.trans e₂) = e₁.symm.trans e₂ := by
      refine OpenPartialHomeomorph.ext _ _ (fun _ => by simp [hU]) (fun _ => by simp [hU]) ?_
      ext y
      simp [hU, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        OpenPartialHomeomorph.trans_target]
    rw [hEq]
    exact HasGroupoid.compatible he₁ he₂
  haveI : IsManifold (𝓡 n) ∞ (ULift.{u} M) := IsManifold.mk' (𝓡 n) ∞ (ULift.{u} M)
  obtain ⟨φ⟩ := h (ULift.{u} M) (Homeomorph.ulift.toHomotopyEquiv.trans he)
  let d : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ (ULift.{u} M) :=
    { toEquiv := Equiv.ulift.symm
      contMDiff_toFun := by
        intro x
        rw [contMDiffAt_iff]
        refine ⟨continuous_uliftUp.continuousAt, ?_⟩
        refine contDiffWithinAt_id.congr_of_eventuallyEq ?_ ?_
        · have hmem : (chartAt (ℝ^n) x).target ∈ nhds ((chartAt (ℝ^n) x) x) :=
            (chartAt (ℝ^n) x).open_target.mem_nhds
              ((chartAt (ℝ^n) x).map_source (mem_chart_source (ℝ^n) x))
          filter_upwards [mem_nhdsWithin_of_mem_nhds hmem] with y hy
          exact (chartAt (ℝ^n) x).right_inv hy
        · exact (chartAt (ℝ^n) x).right_inv
            ((chartAt (ℝ^n) x).map_source (mem_chart_source (ℝ^n) x))
      contMDiff_invFun := by
        intro x
        rw [contMDiffAt_iff]
        refine ⟨continuous_uliftDown.continuousAt, ?_⟩
        refine contDiffWithinAt_id.congr_of_eventuallyEq ?_ ?_
        · have hmem : (chartAt (ℝ^n) x.down).target ∈ nhds ((chartAt (ℝ^n) x.down) x.down) :=
            (chartAt (ℝ^n) x.down).open_target.mem_nhds
              ((chartAt (ℝ^n) x.down).map_source (mem_chart_source (ℝ^n) x.down))
          filter_upwards [mem_nhdsWithin_of_mem_nhds hmem] with y hy
          exact (chartAt (ℝ^n) x.down).right_inv hy
        · exact (chartAt (ℝ^n) x.down).right_inv
            ((chartAt (ℝ^n) x.down).map_source (mem_chart_source (ℝ^n) x.down)) }
  exact ⟨d.trans φ⟩

theorem main : H1 → H2 → H3 → type_of% @PoincareConjecture.poincare_conjecture.variants.smooth_other_cases := by
  intro h1 h2 h3 n hn hn' hSmooth
  have h0 : PoincareConjecture.SmoothConjectureFor.{0} n := smoothConjectureFor_down n hSmooth
  have h5 : n ≠ 5 := fun h => hn' (by simp [h, PoincareConjecture.SmoothTrueValues])
  have h6 : n ≠ 6 := fun h => hn' (by simp [h, PoincareConjecture.SmoothTrueValues])
  have h12 : n ≠ 12 := fun h => hn' (by simp [h, PoincareConjecture.SmoothTrueValues])
  have h56 : n ≠ 56 := fun h => hn' (by simp [h, PoincareConjecture.SmoothTrueValues])
  have h61 : n ≠ 61 := fun h => hn' (by simp [h, PoincareConjecture.SmoothTrueValues])
  by_cases heven : n % 2 = 0
  · have hk : 2 * (n / 2) = n := by omega
    rw [← hk] at h0
    exact h3 (n / 2) (by omega) (by omega) (by omega) h0
  · by_cases hmod4 : n % 4 = 1
    · have hk : 4 * (n / 4) + 1 = n := by omega
      rw [← hk] at h0
      exact h2 (n / 4) (by omega) (by omega) h0
    · have hk : 4 * ((n + 1) / 4) - 1 = n := by omega
      rw [← hk] at h0
      exact h1 ((n + 1) / 4) (by omega) h0

end OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_other_cases_R1
