import OMAReductions.R_mo_368734_R1
import Mathlib

/-!
# Proof of `mo-368734.R1.H1`

For a prime `p` with `p % 5 ≠ 1`, the map `x ↦ x ^ 5` on `ZMod p` is injective: for `p = 2` by
evaluation, for `p = 5` it is the Frobenius `x ^ 5 = x`, and otherwise `5` is invertible modulo
`p - 1`, so `x ↦ x ^ e` is a left inverse by Fermat's little theorem. An injective self-map of a
finite type is bijective, and translating by `3` preserves this.
-/

namespace OMA.Mo368734H1

theorem pow_five_injective (p : ℕ) [hp : Fact p.Prime] (h5 : p % 5 ≠ 1) :
    Function.Injective (fun x : ZMod p => x ^ 5) := by
  have hp2 := hp.out.two_le
  by_cases hp5 : p = 5
  · subst hp5
    intro x y hxy
    simpa only [ZMod.pow_card] using hxy
  by_cases hp2' : p = 2
  · subst hp2'
    have h : ∀ x : ZMod 2, x ^ 5 = x := fun x => by
      have h2 := ZMod.pow_card x
      calc x ^ 5 = (x ^ 2) ^ 2 * x := by ring
        _ = x := by rw [h2, h2, ← sq, h2]
    intro x y hxy
    simpa only [h] using hxy
  have hcop : Nat.Coprime 5 (p - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    omega
  have : NeZero (p - 1) := ⟨by omega⟩
  obtain ⟨e, he⟩ : ∃ e, 5 * e % (p - 1) = 1 := by
    refine ⟨(((ZMod.unitOfCoprime 5 hcop)⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val, ?_⟩
    have h1 : ((5 * (((ZMod.unitOfCoprime 5 hcop)⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val : ℕ) :
        ZMod (p - 1)) = ((1 : ℕ) : ZMod (p - 1)) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
      have := Units.mul_inv (ZMod.unitOfCoprime 5 hcop)
      rw [ZMod.coe_unitOfCoprime] at this
      exact_mod_cast this
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    rw [h1, Nat.one_mod_eq_one.mpr (by omega)]
  have key : ∀ x : ZMod p, (x ^ 5) ^ e = x := by
    intro x
    rw [← pow_mul, ← Nat.div_add_mod (5 * e) (p - 1), he]
    by_cases hx : x = 0
    · subst hx
      simp
    · rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul, pow_one]
  intro x y hxy
  have h := congrArg (fun t : ZMod p => t ^ e) hxy
  simp only [key] at h
  exact h

end OMA.Mo368734H1

theorem OMA.solution : OMA.R_mo_368734_R1.H1 := by
  intro p hp h5
  have : Fact p.Prime := ⟨hp⟩
  rw [← Finite.injective_iff_bijective]
  intro x y hxy
  apply OMA.Mo368734H1.pow_five_injective p h5
  simpa using hxy
