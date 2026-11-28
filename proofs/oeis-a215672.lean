import OMAStatements.S_oeis_a215672
import Mathlib

open OMA.S_oeis_a215672

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a215672.main) := by
  intro h
  have hpoulet : IsPoulet 617093 := by
    refine ⟨by decide, ?_, ?_⟩
    · intro hp
      rcases (Nat.dvd_prime hp).mp (show 43 ∣ 617093 by decide) with h | h <;>
        norm_num at h
    · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
      reduce_mod_char
  have hFactors : (617093 : ℕ).primeFactors = {43, 113, 127} := by
    rw [show (617093 : ℕ) = 43 * 113 * 127 by decide,
      Nat.primeFactors_mul (by decide : 43 * 113 ≠ 0) (by decide : 127 ≠ 0),
      Nat.primeFactors_mul (by decide : 43 ≠ 0) (by decide : 113 ≠ 0),
      (show Nat.Prime 43 by decide).primeFactors, (show Nat.Prime 113 by decide).primeFactors,
      (show Nat.Prime 127 by decide).primeFactors]
    decide
  obtain ⟨q, hq, r, hr⟩ := h 617093 hpoulet (by rw [hFactors]; decide)
  simp only [hFactors, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl <;> omega
