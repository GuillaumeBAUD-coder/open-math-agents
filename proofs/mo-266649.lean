import OMAStatements.S_mo_266649
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_266649.main) := fun h => by
  obtain ⟨φ, h2, -⟩ := h Unit (fun p hp g e => by rw [orderOf_eq_one_iff.2 (Subsingleton.elim g 1)] at e; nlinarith [hp.two_le])
    (fun p hp e => by simp at e; exact hp.ne_one e.symm)
  simp [Subsingleton.elim φ 1] at h2
