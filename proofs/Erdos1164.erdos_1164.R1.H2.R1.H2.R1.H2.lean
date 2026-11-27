import OMAReductions.R_Erdos1164_erdos_1164_R1_H2_R1_H2_R1

open MeasureTheory Finset Erdos1165
open scoped ProbabilityTheory

/-! Partition the walks missing at most one site according to which site is missing. -/

theorem OMA.solution : OMA.R_Erdos1164_erdos_1164_R1_H2_R1_H2_R1.H2 := by
  intro Ω _ _ X hX U k
  classical
  let V (x : ℤ × ℤ) : Set Ω := {ω | ∃ j ≤ k, position X j ω = x}
  let C (W : Finset (ℤ × ℤ)) : Set Ω := {ω | ∀ x ∈ W, ω ∈ V x}
  let D (x : ℤ × ℤ) : Set Ω := C (U.erase x) ∩ (V x)ᶜ
  have vm (x : ℤ × ℤ) : MeasurableSet (V x) := by
    have hpos (j : ℕ) : Measurable (position X j) := (range j).measurable_fun_sum (fun i _ => hX.measurable i)
    have desc : V x = ⋃ j ∈ range (k+1), (position X j) ⁻¹' {x} := by
      ext ω
      simp [V]
    rw [desc]
    exact Finset.measurableSet_biUnion _ (fun j _ => (hpos j) (measurableSet_singleton x))
  have cm (W : Finset (ℤ × ℤ)) : MeasurableSet (C W) := by
    have e : C W = ⋂ x ∈ W, V x := by ext; simp [C]
    rw [e]
    exact Finset.measurableSet_biInter _ (fun x _ => vm x)
  have dm (x : ℤ × ℤ) : MeasurableSet (D x) := (cm _).inter (vm x).compl
  have split (x : ℤ × ℤ) (hx : x∈U) : C (U.erase x) = C U ∪ D x := by
    ext ω
    constructor
    · intro h
      by_cases hv : ω ∈ V x
      · left
        intro y hy
        by_cases he : y=x
        · simpa [he] using hv
        · exact h y (mem_erase.mpr ⟨he,hy⟩)
      · exact Or.inr ⟨h,hv⟩
    · rintro (h|h)
      · exact fun y hy => h y (mem_of_mem_erase hy)
      · exact h.1
  have separate (x : ℤ × ℤ) (hx : x∈U) : Disjoint (C U) (D x) :=
    Set.disjoint_left.mpr fun ω h d => d.2 (h x hx)
  have disj : Set.PairwiseDisjoint (↑U : Set (ℤ × ℤ)) D := by
    intro x hx y hy hxy
    exact Set.disjoint_left.mpr fun ω dx dy => dy.2 (dx.1 y (mem_erase.mpr ⟨hxy.symm, hy⟩))
  have one : {ω | ∃! x : ℤ × ℤ, x∈U ∧ ω ∉ V x} = ⋃ x ∈ U, D x := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x,⟨hx,hn⟩,uniq⟩
      refine ⟨x,hx,?_,hn⟩
      intro y hy
      by_contra miss
      exact (mem_erase.mp hy).1 (uniq y ⟨mem_of_mem_erase hy,miss⟩)
    · rintro ⟨x,hx,h,hn⟩
      refine ⟨x,⟨hx,hn⟩,?_⟩
      rintro y ⟨hy,miss⟩
      by_contra he
      exact miss (h y (mem_erase.mpr ⟨he,hy⟩))
  change (∑ x ∈ U, (ℙ : Measure Ω).real (C (U.erase x))) =
    U.card * (ℙ : Measure Ω).real (C U) + (ℙ : Measure Ω).real {ω | ∃! x : ℤ × ℤ, x ∈ U ∧ ω ∉ V x}
  rw [one, measureReal_biUnion_finset disj (fun x _ => dm x)]
  calc
    _ = ∑ x ∈ U, ((ℙ : Measure Ω).real (C U) + (ℙ : Measure Ω).real (D x)) := by
      apply sum_congr rfl
      intro x hx
      rw [split x hx, measureReal_union (separate x hx) (dm x)]
    _ = _ := by simp [sum_add_distrib]
