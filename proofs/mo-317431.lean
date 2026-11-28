import OMAStatements.S_mo_317431
import Mathlib

namespace OMA.S_mo_317431

def S : Set ℝ := {x | (∃ q : ℚ, (q : ℝ) = x) ∧ x ≤ 0}

theorem hyp : ∀ U : Set ℝ, IsOpen U → (U ∩ S).Nonempty → (U ∩ (closure S \ S)).Nonempty := by
  intro U hU ⟨q, hqU, ⟨r, hr⟩, hq0⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU q hqU
  obtain ⟨x, hxirr, hx1, hx2⟩ := exists_irrational_btwn (show q - ε < q by linarith)
  have hx0 : x < 0 := by linarith
  refine ⟨x, hball ?_, ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  · rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨y, hy1, hy2⟩ := exists_rat_btwn (show x - δ < x by linarith)
    refine ⟨(y : ℝ), ⟨⟨y, rfl⟩, by linarith⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  · rintro ⟨⟨y, hy⟩, _⟩
    exact hxirr ⟨y, hy⟩

end OMA.S_mo_317431

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_317431.main) := by
  intro h
  have hc := h ℝ OMA.S_mo_317431.S OMA.S_mo_317431.hyp
  have o1 : IsOpen (Set.Iio (0:ℝ)) := isOpen_Iio
  have o2 : IsOpen (Set.Ioi (0:ℝ)) := isOpen_Ioi
  letI : TopologicalSpace ℝ := TopologicalSpace.generateFrom ({U : Set ℝ | IsOpen U} ∪ {OMA.S_mo_317431.S})
  have hS : IsOpen OMA.S_mo_317431.S :=
    TopologicalSpace.isOpen_generateFrom_of_mem (Or.inr rfl)
  have hI : IsOpen (Set.Iio (0:ℝ)) :=
    TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl o1)
  have hP : IsOpen (Set.Ioi (0:ℝ)) :=
    TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl o2)
  have hA : IsOpen (Set.Iic (0:ℝ)) := by
    have : Set.Iic (0:ℝ) = Set.Iio 0 ∪ OMA.S_mo_317431.S := by
      ext x
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, OMA.S_mo_317431.S, Set.mem_setOf_eq]
      constructor
      · intro hx
        rcases hx.lt_or_eq with hx | hx
        · exact Or.inl hx
        · exact Or.inr ⟨⟨0, by simp [hx]⟩, hx.le⟩
      · rintro (hx | ⟨_, hx⟩) <;> linarith
    rw [this]; exact hI.union hS
  have hcl : IsClopen (Set.Iic (0:ℝ)) := by
    refine ⟨?_, hA⟩
    have : (Set.Iic (0:ℝ))ᶜ = Set.Ioi 0 := by ext; simp
    rw [← isOpen_compl_iff, this]; exact hP
  rcases isClopen_iff.mp hcl with h0 | h0
  · have : (0:ℝ) ∈ Set.Iic (0:ℝ) := Set.mem_Iic.mpr le_rfl
    rw [h0] at this; exact absurd this (Set.notMem_empty _)
  · have : (1:ℝ) ∈ (Set.univ : Set ℝ) := Set.mem_univ _
    rw [← h0] at this
    exact absurd (Set.mem_Iic.mp this) (by norm_num)
