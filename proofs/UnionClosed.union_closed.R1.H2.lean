import OMAReductions.R_UnionClosed_union_closed_R1
import Mathlib

-- Step UnionClosed.union_closed.R1.H2: hypothesis H2 of reduction UnionClosed.union_closed.R1
-- Credit: @ivillar. If {x, y} is a member, X -> X ∪ {x, y} injects the members avoiding both into the members containing both, so the counts for x and y sum to at least |A|.

/-! Step UnionClosed.union_closed.R1.H2. -/

theorem P8UnionClosed.uc_h2 : ∀ (m : ℕ) (A : Finset (Finset (Fin m))) (x y : Fin m), x ≠ y →
    UnionClosed.IsUnionClosed A → {x, y} ∈ A →
    (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => x ∈ X)).card ∨
      (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => y ∈ X)).card := by
  intro m A x y hxy hA hxyA
  have hinj : (A.filter (fun X => ¬ (x ∈ X ∨ y ∈ X))).card ≤
      (A.filter (fun X => x ∈ X ∧ y ∈ X)).card := by
    apply Finset.card_le_card_of_injOn (fun X => X ∪ {x, y})
    · intro X hX
      simp only [Finset.mem_coe, Finset.mem_filter] at hX ⊢
      refine ⟨hA X hX.1 _ hxyA, by simp, by simp⟩
    · intro X hX Y hY hXY
      simp only [Finset.mem_coe, Finset.mem_filter, not_or] at hX hY
      ext z
      have hz := congrArg (fun Z => z ∈ Z) hXY
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, eq_iff_iff] at hz
      by_cases hzx : z = x
      · subst hzx
        simp [hX.2.1, hY.2.1]
      · by_cases hzy : z = y
        · subst hzy
          simp [hX.2.2, hY.2.2]
        · simpa [hzx, hzy] using hz
  have h1 := Finset.card_filter_add_card_filter_not (s := A) (fun X => x ∈ X ∨ y ∈ X)
  have h2 : (A.filter (fun X => x ∈ X ∨ y ∈ X)).card + (A.filter (fun X => x ∈ X ∧ y ∈ X)).card
      = (A.filter (fun X => x ∈ X)).card + (A.filter (fun X => y ∈ X)).card := by
    rw [Finset.filter_or, Finset.filter_and, Finset.card_union_add_card_inter]
  have h3 : A.card ≤ (A.filter (fun X => x ∈ X)).card + (A.filter (fun X => y ∈ X)).card := by
    omega
  have h3' : (A.card : ℚ) ≤ (A.filter (fun X => x ∈ X)).card + (A.filter (fun X => y ∈ X)).card := by
    exact_mod_cast h3
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  obtain ⟨ha, hb⟩ := hcon
  linarith

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1.H2 :=
  P8UnionClosed.uc_h2
