import OMAReductions.R_Erdos1164_erdos_1164_R1_H2_R1_H2_R1
import Mathlib

-- Step Erdos1164.erdos_1164.R1.H2.R1.H2.R1.H2: hypothesis H2 of reduction Erdos1164.erdos_1164.R1.H2.R1.H2.R1
-- Credit: @ivillar
-- H2: the fixed-time counting identity  sum_{x in U} A(U - x) = |U| A(U) + B(U).
-- Proof: with E = {all of U visited} and G x = {x is the only unvisited point of U},
-- the event {U - x visited} is the disjoint union of E and G x, and the event
-- {exactly one point of U unvisited} is the disjoint union of the G x over x in U.

open MeasureTheory Erdos1164 Erdos1165 Finset
open scoped ProbabilityTheory

theorem OMA.solution : OMA.R_Erdos1164_erdos_1164_R1_H2_R1_H2_R1.H2 := by
  unfold OMA.R_Erdos1164_erdos_1164_R1_H2_R1_H2_R1.H2
  intro Ω _ _ X hX U k
  dsimp only
  classical
  have hpos : ∀ j, Measurable (position X j) := fun j =>
    Finset.measurable_sum _ (fun i _ => hX.measurable i)
  let P : ℤ × ℤ → Ω → Prop := fun x ω => ∃ j ≤ k, position X j ω = x
  change ∑ x ∈ U, (ℙ {ω | ∀ y ∈ U.erase x, P y ω}).toReal =
    (U.card : ℝ) * (ℙ {ω | ∀ y ∈ U, P y ω}).toReal +
      (ℙ {ω | ∃! y : ℤ × ℤ, y ∈ U ∧ ¬ P y ω}).toReal
  have hV : ∀ x : ℤ × ℤ, MeasurableSet {ω | P x ω} := by
    intro x
    have e : {ω | P x ω} = ⋃ j ∈ Finset.range (k + 1), (position X j) ⁻¹' {x} := by
      ext ω
      simp [P, Nat.lt_add_one_iff]
    rw [e]
    exact Finset.measurableSet_biUnion _ (fun j _ => hpos j (measurableSet_singleton x))
  let E : Set Ω := {ω | ∀ y ∈ U, P y ω}
  let G : ℤ × ℤ → Set Ω := fun x => {ω | ¬ P x ω ∧ ∀ y ∈ U, y ≠ x → P y ω}
  have hG : ∀ x, MeasurableSet (G x) := by
    intro x
    have e : G x = {ω | P x ω}ᶜ ∩ ⋂ y ∈ U.erase x, {ω | P y ω} := by
      ext ω
      simp only [G, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iInter,
        Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun y hy => h2 y hy.2 hy.1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun y hy hyx => h2 y ⟨hyx, hy⟩⟩
    rw [e]
    exact (hV x).compl.inter (Finset.measurableSet_biInter _ (fun y _ => hV y))
  have hsplit : ∀ x ∈ U, {ω | ∀ y ∈ U.erase x, P y ω} = E ∪ G x := by
    intro x _
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, E, G, Finset.mem_erase]
    constructor
    · intro h
      by_cases hpx : P x ω
      · left
        intro y hy
        by_cases hyx : y = x
        · rw [hyx]
          exact hpx
        · exact h y ⟨hyx, hy⟩
      · right
        exact ⟨hpx, fun y hy hyx => h y ⟨hyx, hy⟩⟩
    · rintro (h | ⟨_, h⟩)
      · exact fun y hy => h y hy.2
      · exact fun y hy => h y hy.2 hy.1
  have hdisj : ∀ x ∈ U, Disjoint E (G x) := by
    intro x hx
    rw [Set.disjoint_left]
    intro ω hE' hG'
    exact hG'.1 (hE' x hx)
  have hunion : {ω | ∃! y : ℤ × ℤ, y ∈ U ∧ ¬ P y ω} = ⋃ x ∈ U, G x := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, G, exists_prop]
    constructor
    · rintro ⟨x, ⟨hxU, hnx⟩, huniq⟩
      refine ⟨x, hxU, hnx, fun y hy hyx => ?_⟩
      by_contra hny
      exact hyx (huniq y ⟨hy, hny⟩)
    · rintro ⟨x, hxU, hnx, hall⟩
      refine ⟨x, ⟨hxU, hnx⟩, fun y hy => ?_⟩
      by_contra hyx
      exact hy.2 (hall y hy.1 hyx)
  have hpd : (U : Set (ℤ × ℤ)).PairwiseDisjoint G := by
    intro x hx x' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    exact h1.1 (h2.2 x hx hne)
  have hterm : ∀ x ∈ U, (ℙ {ω | ∀ y ∈ U.erase x, P y ω}).toReal =
      (ℙ E).toReal + (ℙ (G x)).toReal := by
    intro x hx
    rw [hsplit x hx, measure_union (hdisj x hx) (hG x),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hunion,
    measure_biUnion_finset hpd (fun x _ => hG x),
    ENNReal.toReal_sum (fun x _ => measure_ne_top _ _)]
