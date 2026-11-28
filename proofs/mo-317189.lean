import OMAStatements.S_mo_317189
import Mathlib

open OMA.S_mo_317189
open Pointwise

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_317189.main) := by
  intro h
  have h1 := h {0, 1, 3, 4} ⟨1, by decide, by decide⟩
  have h2 : (({0, 1, 3, 4} : Finset ℤ) + {0, 1, 3, 4}).card = 9 := by decide
  have h3 : (({0, 1, 3, 4} : Finset ℤ) + {0, 1, 3, 4} + {0, 1, 3, 4}).card = 13 := by decide
  have h4 : ({0, 1, 3, 4} : Finset ℤ).card = 4 := by decide
  rw [h2, h3, h4] at h1
  omega
