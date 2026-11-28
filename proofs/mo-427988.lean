import OMAStatements.S_mo_427988
import Mathlib

open Finset

open OMA.S_mo_427988

private def exampleSet : Finset ℤ := {0,1,3,5,8,20,23,25,27,28}

private theorem example_in_interval : exampleSet ⊆ Icc (0 : ℤ) 28 := by decide +kernel

private theorem example_covers_ends :
    Icc (0 : ℤ) 28 ∪ Icc 56 84 ⊆ TripleSumset exampleSet := by decide +kernel

private theorem example_misses_middle : (42 : ℤ) ∉ TripleSumset exampleSet := by decide +kernel

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_427988.main) := by
  intro h
  have he := h 28 (by norm_num) exampleSet example_in_interval (by
    norm_num
    exact example_covers_ends)
  have hMiddle : (42 : ℤ) ∈ Icc (0 : ℤ) (3*28) := by norm_num
  exact example_misses_middle (he.symm ▸ hMiddle)
