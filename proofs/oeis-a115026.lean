import OMAStatements.S_oeis_a115026
import Mathlib

theorem a115026_fix : OMA.S_oeis_a115026.f 371 = 371 := by
  norm_num [OMA.S_oeis_a115026.f]

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a115026.main) := by
  intro h
  have hfix : Function.IsFixedPt OMA.S_oeis_a115026.f 371 := a115026_fix
  have hset : {m : ℕ | (∃ k : ℕ, OMA.S_oeis_a115026.f^[k] 371 = m) ∧ m ∈ Function.periodicPts OMA.S_oeis_a115026.f} = {371} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨k, hk⟩, _⟩
      rw [← hk]
      exact Function.iterate_fixed hfix k
    · rintro rfl
      exact ⟨⟨0, rfl⟩, Function.mk_mem_periodicPts Nat.one_pos hfix⟩
  have h2 := h 371 (by norm_num)
  unfold OMA.S_oeis_a115026.a at h2
  rw [hset, csInf_singleton] at h2
  omega
