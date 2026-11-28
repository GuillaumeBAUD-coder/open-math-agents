import OMAStatements.S_mo_448750
import Mathlib
open OMA.S_mo_448750

theorem OMA.solution : type_of% @OMA.S_mo_448750.main := by
  intro 𝕜 _ H _ _ _ C hC
  have hcl : ∀ Z ∈ C, Zᗮᗮ = Z := by
    intro Z hZ
    rw [Submodule.orthogonal_orthogonal_eq_closure]
    exact IsClosed.submodule_topologicalClosure_eq (hC Z hZ)
  have key : (⨆ Z ∈ C, Zᗮ)ᗮ = sInf C := by
    apply le_antisymm
    · apply le_sInf
      intro Z hZ
      have h1 : Zᗮ ≤ ⨆ Z ∈ C, Zᗮ := le_iSup₂_of_le Z hZ le_rfl
      have h2 := Submodule.orthogonal_le h1
      rw [hcl Z hZ] at h2
      exact h2
    · intro x hx
      rw [Submodule.mem_orthogonal']
      intro y hy
      have hsub : (⨆ Z ∈ C, Zᗮ) ≤ (sInf C)ᗮ := by
        apply iSup₂_le
        intro Z hZ
        exact Submodule.orthogonal_le (sInf_le hZ)
      have := hsub hy
      rw [Submodule.mem_orthogonal'] at this
      rw [inner_eq_zero_symm]
      exact this x hx
  rw [← key, Submodule.orthogonal_orthogonal_eq_closure]
