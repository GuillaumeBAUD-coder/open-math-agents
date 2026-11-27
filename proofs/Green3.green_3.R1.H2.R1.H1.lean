import OMAReductions.R_Green3_green_3_R1_H2_R1
import Mathlib

/-! On the common integer grid, the occupied cells of width N and their
dilates of width M are disjoint. Their union lies between mM and MN. -/
open Finset

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1.H1 := by
  classical
  intro N m M S hM hMN hlast hrange hfree
  let cell (w i : ℕ) := Ico (i*w) ((i+1)*w)
  let band (w : ℕ) := S.biUnion (cell w)
  have mass (w : ℕ) : (band w).card = S.card*w := by
    rw [show band w = S.biUnion (cell w) from rfl,card_biUnion]
    · simp [cell,Nat.card_Ico, Nat.add_mul]
    · intro i _ j _ hne
      apply disjoint_left.mpr
      intro a hai haj
      obtain ⟨hi,hi'⟩ := mem_Ico.mp hai
      obtain ⟨hj,hj'⟩ := mem_Ico.mp haj
      rcases lt_or_gt_of_ne hne with h|h
      · exact (hi'.not_ge ((Nat.mul_le_mul_right w h).trans hj))
      · exact (hj'.not_ge ((Nat.mul_le_mul_right w h).trans hi))
  have dis : Disjoint (band M) (band N) := by
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨i,hi,hcell⟩ := mem_biUnion.mp ha
    obtain ⟨l,hl,hcell'⟩ := mem_biUnion.mp hb
    obtain ⟨hi₀,hi₁⟩ := mem_Ico.mp hcell
    obtain ⟨hl₀,hl₁⟩ := mem_Ico.mp hcell'
    apply hfree i hi (M-1) hlast l hl
    refine ⟨((Nat.mul_le_mul_left i (Nat.sub_le M 1)).trans hi₀).trans_lt hl₁,?_⟩
    simpa [Nat.sub_add_cancel hM] using hl₀.trans_lt hi₁
  have inside (w : ℕ) (hw : M ≤ w) (hw' : w ≤ N) : band w ⊆ Ico (m*M) (M*N) := by
    intro a ha
    obtain ⟨i,hi,hcell⟩ := mem_biUnion.mp ha
    obtain ⟨lo,up⟩ := mem_Ico.mp hcell
    obtain ⟨hmi,hiM⟩ := hrange i hi
    exact mem_Ico.mpr ⟨(Nat.mul_le_mul hmi hw).trans lo,up.trans_le (Nat.mul_le_mul hiM hw')⟩
  have count := card_le_card (union_subset (inside M le_rfl hMN) (inside N hMN le_rfl))
  rw [card_union_of_disjoint dis,mass,mass,Nat.card_Ico] at count
  simpa [Nat.mul_sub,Nat.add_mul,Nat.mul_add,Nat.mul_comm,add_comm] using count
