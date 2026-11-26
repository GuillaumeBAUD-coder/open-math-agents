import FormalConjectures.ErdosProblems.«1119»

-- Problem: Erdős Problem 1119 — erdos wetzel
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1119.lean:105 (declaration Erdos1119.erdos_1119.variants.erdos_wetzel)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Cardinal Filter Set

/-! Erdős's argument. If the family were uncountable, pick `ℵ₁` of its members. Two distinct
entire functions agree only on a countable set (identity theorem: the coincidence set is closed and
discrete in `ℂ`). The union of these `ℵ₁ · ℵ₁` countable sets has size `≤ ℵ₁ < 𝔠`, so some `z₀`
avoids all of them, and then the chosen functions take `ℵ₁` distinct values at `z₀`. -/

/-- Two distinct entire functions agree on a countable set. -/
lemma coincidence_countable {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hne : f ≠ g) : {z | f z = g z}.Countable := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  rcases hfa.eqOn_or_eventually_ne_of_preconnected hga isPreconnected_univ with h | h
  · exact absurd (funext fun z => h (mem_univ z)) hne
  · have hmem : {z | f z ≠ g z} ∈ codiscrete ℂ := h
    rw [mem_codiscrete'] at hmem
    have hc : {z | f z ≠ g z}ᶜ = {z | f z = g z} := by ext z; simp
    rw [hc] at hmem
    exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hmem.2

theorem OMA.solution : type_of% @Erdos1119.erdos_1119.variants.erdos_wetzel := by
  intro h F hF hval
  by_contra hunc
  -- A subfamily of cardinality `ℵ₁`.
  have h0 : ℵ₀ < #F := by
    rw [← not_le, le_aleph0_iff_set_countable]; exact hunc
  have h1 : ℵ_ 1 ≤ #F := by
    rw [← succ_aleph0]; exact Order.succ_le_of_lt h0
  obtain ⟨G, hGF, hG⟩ := le_mk_iff_exists_subset.mp h1
  -- The union of all pairwise coincidence sets.
  let ι := {p : G × G // p.1 ≠ p.2}
  let E : ι → Set ℂ := fun p => {z | p.1.1.1 z = p.1.2.1 z}
  have hE : ∀ p, #(E p) ≤ ℵ₀ := fun p =>
    le_aleph0_iff_set_countable.mpr (coincidence_countable (hF _ (hGF p.1.1.2))
      (hF _ (hGF p.1.2.2)) fun heq => p.2 (Subtype.ext heq))
  have hι : #ι ≤ ℵ_ 1 := by
    calc #ι ≤ #(G × G) := mk_subtype_le _
      _ = #G * #G := by simp [mk_prod]
      _ = ℵ_ 1 := by rw [hG]; exact mul_eq_self (aleph0_le_aleph 1)
  have hU : #(⋃ p, E p) ≤ ℵ_ 1 := by
    calc #(⋃ p, E p) ≤ #ι * ⨆ p, #(E p) := mk_iUnion_le E
      _ ≤ ℵ_ 1 * ℵ₀ := mul_le_mul' hι (ciSup_le' hE)
      _ ≤ ℵ_ 1 * ℵ_ 1 := mul_le_mul' le_rfl (aleph0_le_aleph 1)
      _ = ℵ_ 1 := mul_eq_self (aleph0_le_aleph 1)
  -- Since `ℵ₁ < 𝔠 = #ℂ`, some point avoids every coincidence set.
  have hne : (⋃ p, E p) ≠ Set.univ := by
    intro hu
    rw [hu, mk_univ, mk_complex] at hU
    exact absurd h (not_lt.mpr (by simpa using (Cardinal.lift_le.{_, 0}).mpr hU))
  obtain ⟨z₀, hz₀⟩ := (ne_univ_iff_exists_notMem _).mp hne
  have hinj : InjOn (fun f : ℂ → ℂ => f z₀) G := by
    intro f hf g hg hfg
    by_contra hfg'
    apply hz₀
    exact mem_iUnion.mpr ⟨⟨(⟨f, hf⟩, ⟨g, hg⟩), fun h' => hfg' (congrArg Subtype.val h')⟩, hfg⟩
  -- So `ℵ₁` distinct values are taken at `z₀`, contradicting countability.
  have hsub : (fun f : ℂ → ℂ => f z₀) '' G ⊆ {y : ℂ | ∃ f ∈ F, f z₀ = y} := by
    rintro y ⟨f, hf, rfl⟩
    exact ⟨f, hGF hf, rfl⟩
  have hcnt := le_aleph0_iff_set_countable.mpr ((hval z₀).mono hsub)
  rw [mk_image_eq_of_injOn _ _ hinj, hG] at hcnt
  exact absurd hcnt (not_le.mpr (by simpa using aleph0_lt_aleph_one))
