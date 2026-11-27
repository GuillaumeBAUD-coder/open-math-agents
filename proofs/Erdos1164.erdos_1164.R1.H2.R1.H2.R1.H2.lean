import OMAReductions.R_Erdos1164_erdos_1164_R1_H2_R1_H2_R1

/-! # The counting identity

Fix the time `k` and call a site visited if the walk is there at some time `≤ k`. The event that
every site of `U` except `x` is visited is the disjoint union of the event `F` that all of `U` is
visited and the event `G x` that `x` is the only unvisited site of `U`. The events `G x` are
disjoint and their union is the event that exactly one site of `U` is unvisited.
-/

namespace OMA1164

open MeasureTheory

lemma counting {Ω ι : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    [DecidableEq ι] (U : Finset ι) (V : ι → Set Ω) (hV : ∀ x, MeasurableSet (V x)) :
    ∑ x ∈ U, (μ {ω | ∀ y ∈ U.erase x, ω ∈ V y}).toReal =
      U.card * (μ {ω | ∀ x ∈ U, ω ∈ V x}).toReal + (μ {ω | ∃! x, x ∈ U ∧ ω ∉ V x}).toReal := by
  set F : Set Ω := {ω | ∀ x ∈ U, ω ∈ V x} with hFdef
  set G : ι → Set Ω := fun x => {ω | ω ∉ V x ∧ ∀ y ∈ U.erase x, ω ∈ V y} with hGdef
  have hG : ∀ x, MeasurableSet (G x) := by
    intro x
    have h : G x = (V x)ᶜ ∩ ⋂ y ∈ U.erase x, V y := by
      ext ω
      simp [hGdef]
    rw [h]
    exact (hV x).compl.inter (Finset.measurableSet_biInter _ fun y _ => hV y)
  have hE : ∀ x ∈ U, {ω | ∀ y ∈ U.erase x, ω ∈ V y} = F ∪ G x := by
    intro x hx
    ext ω
    constructor
    · intro h
      by_cases hω : ω ∈ V x
      · left
        intro y hy
        by_cases hyx : y = x
        · rw [hyx]
          exact hω
        · exact h y (Finset.mem_erase.2 ⟨hyx, hy⟩)
      · right
        exact ⟨hω, h⟩
    · rintro (h | h)
      · intro y hy
        exact h y (Finset.mem_of_mem_erase hy)
      · exact h.2
  have hdisj : ∀ x ∈ U, Disjoint F (G x) := by
    intro x hx
    rw [Set.disjoint_left]
    intro ω hF hGx
    exact hGx.1 (hF x hx)
  have hEm : ∀ x ∈ U, (μ {ω | ∀ y ∈ U.erase x, ω ∈ V y}).toReal =
      (μ F).toReal + (μ (G x)).toReal := by
    intro x hx
    rw [hE x hx, measure_union (hdisj x hx) (hG x),
      ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  have hGs : {ω | ∃! x, x ∈ U ∧ ω ∉ V x} = ⋃ x ∈ U, G x := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨x, ⟨hxU, hx⟩, huniq⟩
      refine ⟨x, hxU, hx, fun y hy => ?_⟩
      by_contra hyV
      exact (Finset.ne_of_mem_erase hy) (huniq y ⟨Finset.mem_of_mem_erase hy, hyV⟩)
    · rintro ⟨x, hxU, hx, hall⟩
      refine ⟨x, ⟨hxU, hx⟩, ?_⟩
      rintro y ⟨hyU, hy⟩
      by_contra hne
      exact hy (hall y (Finset.mem_erase.2 ⟨hne, hyU⟩))
  have hpd : (↑U : Set ι).PairwiseDisjoint G := by
    intro x hx y hy hxy
    show Disjoint (G x) (G y)
    rw [Set.disjoint_left]
    intro ω hωx hωy
    exact hωx.1 (hωy.2 x (Finset.mem_erase.2 ⟨hxy, hx⟩))
  have hGm : (μ {ω | ∃! x, x ∈ U ∧ ω ∉ V x}).toReal = ∑ x ∈ U, (μ (G x)).toReal := by
    rw [hGs, measure_biUnion_finset hpd (fun x _ => hG x),
      ENNReal.toReal_sum (fun x _ => measure_ne_top μ _)]
  rw [Finset.sum_congr rfl hEm, Finset.sum_add_distrib, hGm, Finset.sum_const, nsmul_eq_mul]

end OMA1164

theorem OMA.solution : OMA.R_Erdos1164_erdos_1164_R1_H2_R1_H2_R1.H2 := by
  intro Ω _ _ X hX U k
  have hpos : ∀ j, Measurable (Erdos1165.position X j) := by
    intro j
    unfold Erdos1165.position
    exact Finset.measurable_sum _ (fun i _ => hX.measurable i)
  have hV : ∀ x : ℤ × ℤ, MeasurableSet {ω : Ω | ∃ j ≤ k, Erdos1165.position X j ω = x} := by
    intro x
    have h : {ω : Ω | ∃ j ≤ k, Erdos1165.position X j ω = x} =
        ⋃ j : ℕ, ⋃ (_ : j ≤ k), Erdos1165.position X j ⁻¹' {x} := by
      ext ω
      simp
    rw [h]
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
      hpos j (measurableSet_singleton x)
  exact OMA1164.counting MeasureTheory.volume U
    (fun x => {ω : Ω | ∃ j ≤ k, Erdos1165.position X j ω = x}) hV
