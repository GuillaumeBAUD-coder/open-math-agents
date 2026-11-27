import OMAStatements.S_oeis_a135659
import Mathlib

-- Problem: oeis-a135659
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P135659
open OMA.S_oeis_a135659

theorem sol : type_of% @OMA.S_oeis_a135659.main := by
  rintro m hm ⟨p, rfl⟩ h3
  have hp3 : 3 ≤ p := by
    by_contra h
    interval_cases p <;> simp_all
  have h8 : 2 ^ p % 8 = 0 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
    rw [pow_add]; simp [Nat.mul_mod]
  have h3' : (2 ^ p - 1) % 3 ≠ 0 := by
    intro h
    have := (Nat.Prime.eq_one_or_self_of_dvd hm 3 (Nat.dvd_of_mod_eq_zero h))
    omega
  have hm3 : 2 ^ p % 3 = 1 ∨ 2 ^ p % 3 = 2 := by
    have : 2 ^ p % 3 ≠ 0 := by
      intro h
      have : 3 ∣ 2 ^ p := Nat.dvd_of_mod_eq_zero h
      have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) this)
      omega
    omega
  have hpos : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  refine ⟨(2 ^ p - 1) / 24, ?_⟩
  unfold a
  omega

end OMA.P135659

theorem OMA.solution : type_of% @OMA.S_oeis_a135659.main := OMA.P135659.sol
