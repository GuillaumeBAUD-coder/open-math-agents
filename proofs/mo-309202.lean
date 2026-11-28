import OMAStatements.S_mo_309202

-- Problem: Does uniform continuity of bounded continuous functions implies the same for all continuous functions on a uniform space?
-- Upstream: formal-conjectures statements/mo-309202.lean:0 (declaration OMA.S_mo_309202.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Topology Set

namespace OMA.Aux309202

/-- The natural numbers with the coarsest uniformity making every bounded real function
uniformly continuous. -/
def N : Type := ℕ

def BF : Type := {f : N → ℝ // ∃ C : ℝ, ∀ x, |f x| ≤ C}

instance : Nonempty BF := ⟨⟨fun _ => 0, 0, fun _ => by simp⟩⟩

instance instU : UniformSpace N := ⨅ f : BF, UniformSpace.comap f.1 inferInstance

lemma uc_of_bounded (f : N → ℝ) (hf : ∃ C : ℝ, ∀ x, |f x| ≤ C) : UniformContinuous f := by
  have h : @UniformContinuous N ℝ (UniformSpace.comap f inferInstance) _ f :=
    uniformContinuous_comap
  exact uniformContinuous_iInf_dom (i := (⟨f, hf⟩ : BF)) h

def cast (n : N) : ℝ := ((show ℕ from n : ℕ) : ℝ)

lemma cast_inj {a b : N} (h : |cast a - cast b| < 1) : a = b := by
  unfold cast at h
  have a' : ℕ := a
  have h2 : |(((show ℕ from a : ℕ) : ℤ) - ((show ℕ from b : ℕ) : ℤ) : ℤ)| < 1 := by
    have : ((|(((show ℕ from a : ℕ) : ℤ) - ((show ℕ from b : ℕ) : ℤ) : ℤ)| : ℤ) : ℝ) < 1 := by
      push_cast
      exact h
    exact_mod_cast this
  have h3 := Int.abs_lt_one_iff.mp h2
  have h4 : ((show ℕ from a : ℕ) : ℤ) = ((show ℕ from b : ℕ) : ℤ) := by linarith
  exact Nat.cast_injective h4

lemma open_singleton (n : N) : IsOpen ({n} : Set N) := by
  classical
  let g : N → ℝ := fun m => if m = n then 1 else 0
  have hg : UniformContinuous g := by
    refine uc_of_bounded g ⟨1, fun x => ?_⟩
    by_cases hx : x = n <;> simp [g, hx]
  have : ({n} : Set N) = g ⁻¹' (Ioi (1 / 2)) := by
    ext m
    by_cases hm : m = n <;> simp [g, hm] <;> norm_num
  rw [this]
  exact isOpen_Ioi.preimage hg.continuous

lemma cont_cast : Continuous cast := by
  rw [continuous_def]
  intro s _
  have : cast ⁻¹' s = ⋃ n ∈ cast ⁻¹' s, ({n} : Set N) := by
    ext m; simp
  rw [this]
  exact isOpen_biUnion fun n _ => open_singleton n

lemma not_uc_cast : ¬ UniformContinuous cast := by
  intro huc
  let F : Ultrafilter N := (Filter.hyperfilter ℕ : Ultrafilter ℕ)
  have hF : Cauchy (F : Filter N) := by
    rw [show (instU : UniformSpace N) = ⨅ f : BF, UniformSpace.comap f.1 inferInstance from rfl]
    rw [cauchy_iInf_uniformSpace]
    intro f
    rw [cauchy_comap_uniformSpace]
    obtain ⟨C, hC⟩ := f.2
    have hmem : Icc (-C) C ∈ (F.map f.1 : Filter ℝ) := by
      refine Filter.mem_map.mpr (Filter.univ_mem' fun x => ?_)
      exact abs_le.mp (hC x)
    obtain ⟨x, _, hx⟩ := isCompact_Icc.ultrafilter_le_nhds (F.map f.1) (by
      rw [Filter.le_principal_iff]; exact hmem)
    have hne : (Filter.map f.1 (F : Filter N)).NeBot := (F.map f.1).neBot
    exact (cauchy_nhds (a := x)).mono' hne hx
  have hc : Cauchy (Filter.map cast (F : Filter N)) := hF.map huc
  obtain ⟨x, hx⟩ := CompleteSpace.complete hc
  have hb : cast ⁻¹' (Metric.ball x (1 / 2)) ∈ (F : Filter N) :=
    hx (Metric.ball_mem_nhds x (by norm_num))
  have hsub : (cast ⁻¹' (Metric.ball x (1 / 2))).Subsingleton := by
    intro a ha b hb'
    apply cast_inj
    have h1 : dist (cast a) x < 1 / 2 := ha
    have h2 : dist (cast b) x < 1 / 2 := hb'
    rw [Real.dist_eq] at h1 h2
    have := abs_sub_lt_iff.mp h1
    have := abs_sub_lt_iff.mp h2
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  have hfin : (cast ⁻¹' (Metric.ball x (1 / 2))).Finite := hsub.finite
  exact Filter.notMem_hyperfilter_of_finite (α := ℕ) hfin hb

end OMA.Aux309202

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_309202.main) := by
  intro h
  exact OMA.Aux309202.not_uc_cast
    (h OMA.Aux309202.N (fun f _ hb => OMA.Aux309202.uc_of_bounded f hb)
      OMA.Aux309202.cast OMA.Aux309202.cont_cast)
