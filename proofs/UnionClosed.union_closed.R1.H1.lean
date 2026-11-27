import OMAReductions.R_UnionClosed_union_closed_R1
import Mathlib

-- Step UnionClosed.union_closed.R1.H1: hypothesis H1 of reduction UnionClosed.union_closed.R1
-- Credit: @ivillar. If {x} is a member, X -> X ∪ {x} injects the members avoiding x into the members containing x.

/-! Step UnionClosed.union_closed.R1.H1. -/

theorem P8UnionClosed.uc_h1 : ∀ (m : ℕ) (A : Finset (Finset (Fin m))) (x : Fin m),
    UnionClosed.IsUnionClosed A → {x} ∈ A →
    (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => x ∈ X)).card := by
  intro m A x hA hx
  have hinj : (A.filter (fun X => ¬ x ∈ X)).card ≤ (A.filter (fun X => x ∈ X)).card := by
    apply Finset.card_le_card_of_injOn (fun X => insert x X)
    · intro X hX
      simp only [Finset.mem_coe, Finset.mem_filter] at hX ⊢
      refine ⟨?_, Finset.mem_insert_self x X⟩
      have := hA X hX.1 {x} hx
      rwa [Finset.union_comm, ← Finset.insert_eq] at this
    · intro X hX Y hY hXY
      simp only [Finset.mem_coe, Finset.mem_filter] at hX hY
      have := congrArg (fun Z => Z.erase x) hXY
      simpa [Finset.erase_insert hX.2, Finset.erase_insert hY.2] using this
  have hsum := Finset.card_filter_add_card_filter_not (s := A) (fun X => x ∈ X)
  have h2 : A.card ≤ 2 * (A.filter (fun X => x ∈ X)).card := by omega
  have h2' : (A.card : ℚ) ≤ 2 * (A.filter (fun X => x ∈ X)).card := by exact_mod_cast h2
  linarith

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1.H1 :=
  P8UnionClosed.uc_h1
