import OMAReductions.R_mo_368734_R1
import Mathlib

/-! For a prime `p` with `p % 5 ≠ 1`, `5` is coprime to `p - 1`, so some power `z ↦ z ^ m` inverts
`z ↦ z ^ 5` on `ZMod p` (Fermat). Hence `x ↦ x ^ 5 + 3` is injective on a finite type, so bijective. -/

namespace OMA.Step_mo_368734_R1_H1

/-- For `p ∤ 5 - 1`-type primes, some power undoes the fifth power on `ZMod p`. -/
theorem exists_inv_pow (p : ℕ) (hp : p.Prime) (h5 : p % 5 ≠ 1) :
    ∃ m : ℕ, ∀ z : ZMod p, (z ^ 5) ^ m = z := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.lt_or_ge p 3 with hlt | hge
  · have hp2 : p = 2 := by have := hp.two_le; omega
    subst hp2
    exact ⟨1, by decide⟩
  · have hcop : Nat.Coprime 5 (p - 1) := by
      rw [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
      omega
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
    refine ⟨m, fun z => ?_⟩
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    rw [← pow_mul, ← Nat.div_add_mod (5 * m) (p - 1), hm, pow_add, pow_mul, pow_one]
    by_cases hz : z = 0
    · subst hz
      have : 0 < (p - 1) * (5 * m / (p - 1)) + 1 := by omega
      simp
    · rw [ZMod.pow_card_sub_one_eq_one hz, one_pow, one_mul]

theorem bij (p : ℕ) (hp : p.Prime) (h5 : p % 5 ≠ 1) :
    Function.Bijective (fun x : ZMod p => x ^ 5 + 3) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Finite.injective_iff_bijective]
  intro x y hxy
  have h : x ^ 5 = y ^ 5 := add_right_cancel hxy
  obtain ⟨m, hm⟩ := exists_inv_pow p hp h5
  calc x = (x ^ 5) ^ m := (hm x).symm
    _ = (y ^ 5) ^ m := by rw [h]
    _ = y := hm y

end OMA.Step_mo_368734_R1_H1

theorem OMA.solution : OMA.R_mo_368734_R1.H1 :=
  OMA.Step_mo_368734_R1_H1.bij
