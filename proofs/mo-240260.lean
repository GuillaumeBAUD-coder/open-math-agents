import OMAStatements.S_mo_240260
import Mathlib

-- Problem: mo-240260, the chromatic number of the graph of the permutahedron is 2 (n >= 2).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Adjacent permutations differ by a transposition, so they have opposite signs: colouring by
-- the sign is a proper 2-colouring. For n >= 2 the identity is adjacent to the transposition
-- of 0 and 1, so one colour is not enough.

open OMA.S_mo_240260 in
theorem OMA.solution : type_of% @OMA.S_mo_240260.main := by
  intro n hn
  have hsign : ∀ σ τ : Equiv.Perm (Fin n),
      (∃ a b : Fin n, b.val = a.val + 1 ∧ τ = Equiv.swap a b * σ) →
        Equiv.Perm.sign τ = -Equiv.Perm.sign σ := by
    rintro σ τ ⟨a, b, hab, rfl⟩
    have hne : a ≠ b := by
      intro h
      rw [h] at hab
      omega
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, neg_one_mul]
  have hm1 : (-1 : ℤˣ) ≠ 1 := by decide
  have hcol : ∀ σ τ : Equiv.Perm (Fin n), Equiv.Perm.sign τ = -Equiv.Perm.sign σ →
      (if Equiv.Perm.sign σ = 1 then (0 : Fin 2) else 1) ≠
        (if Equiv.Perm.sign τ = 1 then (0 : Fin 2) else 1) := by
    intro σ τ h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
    · rw [h, h1, if_pos rfl, if_neg hm1]
      exact Fin.zero_ne_one
    · rw [h, h1, neg_neg, if_neg hm1, if_pos rfl]
      exact Fin.zero_ne_one.symm
  apply le_antisymm
  · have hc : (permutahedronGraph n).Colorable 2 := by
      refine ⟨SimpleGraph.Coloring.mk
        (fun σ => if Equiv.Perm.sign σ = 1 then (0 : Fin 2) else 1) ?_⟩
      intro σ τ hadj
      have h' : σ ≠ τ ∧ ((∃ a b : Fin n, b.val = a.val + 1 ∧ τ = Equiv.swap a b * σ) ∨
          (∃ a b : Fin n, b.val = a.val + 1 ∧ σ = Equiv.swap a b * τ)) := hadj
      rcases h'.2 with h2 | h2
      · exact hcol σ τ (hsign σ τ h2)
      · exact (hcol τ σ (hsign τ σ h2)).symm
    exact hc.chromaticNumber_le
  · obtain ⟨a, ha⟩ : ∃ a : Fin n, a.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : Fin n, b.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
    have hne : a ≠ b := by
      intro h
      rw [h] at ha
      omega
    have hadj : (permutahedronGraph n).Adj 1 (Equiv.swap a b) := by
      show (1 : Equiv.Perm (Fin n)) ≠ Equiv.swap a b ∧
        ((∃ a' b' : Fin n, b'.val = a'.val + 1 ∧ Equiv.swap a b = Equiv.swap a' b' * 1) ∨
          (∃ a' b' : Fin n, b'.val = a'.val + 1 ∧ 1 = Equiv.swap a' b' * Equiv.swap a b))
      refine ⟨?_, Or.inl ⟨a, b, by omega, (mul_one _).symm⟩⟩
      intro h
      have h2 : (1 : Equiv.Perm (Fin n)) a = Equiv.swap a b a := by rw [← h]
      rw [Equiv.Perm.one_apply, Equiv.swap_apply_left] at h2
      exact hne h2
    exact SimpleGraph.two_le_chromaticNumber_of_adj hadj
