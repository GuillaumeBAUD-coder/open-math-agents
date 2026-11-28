import OMAStatements.S_mo_238897
import Mathlib

open OMA.S_mo_238897

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_238897.main) := by
  intro h
  obtain ⟨d, D, hD⟩ := h 2 (1 / 2) (by norm_num)
  have h1 := hD 1
  rw [map_one] at h1
  have hc : numCycles (1 : Equiv.Perm (Fin 2)) = 2 := by
    simp [numCycles, Equiv.Perm.partition]
  rw [hc] at h1
  simp only [Units.val_one, Matrix.trace_one, Fintype.card_fin] at h1
  have h2 := congrArg Complex.re h1
  simp at h2
  norm_num at h2
  have h3 : (4 : ℝ) * d = 1 := by rw [h2]; norm_num
  have h4 : 4 * d = 1 := by exact_mod_cast h3
  omega
