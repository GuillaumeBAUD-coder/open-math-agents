import OMAStatements.S_mo_240260
import Mathlib

open OMA.S_mo_240260

lemma mo240260_sign {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : ∃ a b : Fin n, b.val = a.val + 1 ∧ τ = Equiv.swap a b * σ) :
    Equiv.Perm.sign τ = - Equiv.Perm.sign σ := by
  obtain ⟨a, b, hab, rfl⟩ := h
  have hne : a ≠ b := by intro h; rw [h] at hab; omega
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]; simp

theorem OMA.solution : type_of% @OMA.S_mo_240260.main := by
  intro n hn
  apply le_antisymm
  · have hc : (permutahedronGraph n).Colorable 2 := by
      refine ⟨SimpleGraph.Coloring.mk
        (fun σ => if Equiv.Perm.sign σ = 1 then (0 : Fin 2) else 1) ?_⟩
      intro σ τ hadj
      simp only [permutahedronGraph, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨_, h | h⟩ := hadj
      · have := mo240260_sign h
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;>
          simp [this, h1]
      · have := mo240260_sign h
        rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h1 | h1 <;>
          simp [this, h1]
    exact hc.chromaticNumber_le
  · let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    have hadj : (permutahedronGraph n).Adj 1 (Equiv.swap a b * 1) := by
      simp only [permutahedronGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ⟨a, b, rfl, rfl⟩⟩
      intro h
      have h2 := congrArg (fun p : Equiv.Perm (Fin n) => p a) h
      simp [Equiv.swap_apply_left] at h2
      exact absurd (congrArg Fin.val h2) (by simp [a, b])
    exact SimpleGraph.two_le_chromaticNumber_of_adj hadj
