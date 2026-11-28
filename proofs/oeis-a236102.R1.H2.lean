import OMAReductions.R_oeis_a236102_R1
import Mathlib

/-! Adjoining a part of size one gives a proper injection. -/

theorem OMA.solution : OMA.R_oeis_a236102_R1.H2 := by
  intro m hm
  let f (p : Nat.Partition m) : Nat.Partition (m+1) :=
    ⟨1 ::ₘ p.parts, by
      intro i hi
      rcases Multiset.mem_cons.mp hi with rfl | h
      · decide
      · exact p.parts_pos h, by simp [p.parts_sum, Nat.add_comm]⟩
  have hinj : Function.Injective f := by
    intro p q h
    exact Nat.Partition.ext ((Multiset.cons_inj_right 1).mp (congrArg Nat.Partition.parts h))
  apply Fintype.card_lt_of_injective_of_notMem f hinj (b := Nat.Partition.indiscrete (m+1))
  rintro ⟨p, hp⟩
  have h : 1 ∈ (f p).parts := Multiset.mem_cons_self _ _
  rw [hp, Nat.Partition.indiscrete_parts (by omega), Multiset.mem_singleton] at h
  omega