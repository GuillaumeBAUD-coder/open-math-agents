import OMAStatements.S_mo_266649
import Mathlib

-- Problem: mo-266649, does every finite group of non-prime order without elements of order
-- p^2 have an automorphism of order 2 moving some subgroup?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. In the cyclic group of order 6 every automorphism (and its inverse) is a power map
-- x -> x^m, so it maps every subgroup onto itself. Its element orders divide 6, so none is
-- p^2, and 6 is not a prime.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_266649.main) := by
  intro h
  have hcard : Nat.card (Multiplicative (ZMod 6)) = 6 := by
    first
      | simp
      | (rw [Nat.card_eq_fintype_card]; rfl)
  have hA : ∀ p : ℕ, p.Prime → ∀ g : Multiplicative (ZMod 6), orderOf g ≠ p ^ 2 := by
    intro p hp g hg
    have h1 := orderOf_dvd_natCard g
    rw [hcard, hg] at h1
    have hp2 := hp.two_le
    have h6 : p ^ 2 ≤ 6 := Nat.le_of_dvd (by norm_num) h1
    have hple : p ≤ 2 := by nlinarith
    have hpeq : p = 2 := by omega
    subst hpeq
    norm_num at h1
  have hB : ∀ p : ℕ, p.Prime → Nat.card (Multiplicative (ZMod 6)) ≠ p := by
    intro p hp hpc
    rw [hcard] at hpc
    rw [← hpc] at hp
    exact absurd hp (by norm_num)
  obtain ⟨φ, -, H, hH⟩ := h (Multiplicative (ZMod 6)) hA hB
  apply hH
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic
    (φ : Multiplicative (ZMod 6) ≃* Multiplicative (ZMod 6)).toMonoidHom
  obtain ⟨m', hm'⟩ := MonoidHom.map_cyclic
    (φ.symm : Multiplicative (ZMod 6) ≃* Multiplicative (ZMod 6)).toMonoidHom
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    have e : (φ : Multiplicative (ZMod 6) ≃* Multiplicative (ZMod 6)).toMonoidHom y = y ^ m :=
      hm y
    rw [e]
    exact H.zpow_mem hy m
  · intro x hx
    refine ⟨φ.symm x, ?_, φ.apply_symm_apply x⟩
    have e : φ.symm x = x ^ m' := hm' x
    rw [e]
    exact H.zpow_mem hx m'
