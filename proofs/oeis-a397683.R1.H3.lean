import OMAReductions.R_oeis_a397683_R1
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: if x and x+1 are both units mod 3^k then x = 1 mod 3. By the lifting lemma
-- dvd_sub_pow_of_dvd_sub, x^(3^(k-1)) = 1 mod 3^k, so the order of x is a power of 3 (odd).
-- Reducing mod 3, x+1 = 2 and 2^d = 1 in ZMod 3 forces the order d of x+1 to be even.

namespace OMA.P_oeis_a397683_R1_H3
open OMA.S_oeis_a397683

theorem H3_proof : ∀ k : ℕ, 1 ≤ k → f (3 ^ k) = 0 := by
  intro k hk
  have h1 : 3 ^ k ≠ 1 := by
    have : 3 ≤ 3 ^ k := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  unfold f
  rw [if_neg h1, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨hx, hx1, hord⟩
  have h3 : (3 : ℕ) ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  have hx3 : ¬ 3 ∣ x := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      ((Nat.Coprime.coprime_dvd_right h3 hx).symm) h
  have hx13 : ¬ 3 ∣ x + 1 := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      ((Nat.Coprime.coprime_dvd_right h3 hx1).symm) h
  have hmod : x % 3 = 1 := by omega
  -- order of x is odd
  have hpow : ((x : ZMod (3 ^ k))) ^ (3 ^ (k - 1)) = 1 := by
    have hd : ((3 : ℕ) : ℤ) ∣ (x : ℤ) - 1 := by
      have : (3 : ℤ) ∣ (x : ℤ) - 1 := by omega
      exact_mod_cast this
    have := dvd_sub_pow_of_dvd_sub hd (k - 1)
    rw [one_pow, show k - 1 + 1 = k by omega] at this
    have hz : (((x : ℤ) ^ 3 ^ (k - 1) - 1 : ℤ) : ZMod (3 ^ k)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast this)
    push_cast at hz
    exact sub_eq_zero.mp hz
  have hodd : Odd (orderOf (x : ZMod (3 ^ k))) := by
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hi]
    exact Odd.pow (by decide)
  -- order of x+1 is even
  have heven : Even (orderOf (((x + 1 : ℕ)) : ZMod (3 ^ k))) := by
    have hp := pow_orderOf_eq_one (((x + 1 : ℕ)) : ZMod (3 ^ k))
    have hc := congrArg (ZMod.castHom h3 (ZMod 3)) hp
    rw [map_pow, map_one, map_natCast] at hc
    have h2 : ((x + 1 : ℕ) : ZMod 3) = 2 := by
      rw [ZMod.natCast_eq_iff]
      exact ⟨(x + 1) / 3, by simp [ZMod.val]; omega⟩
    rw [h2] at hc
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    obtain ⟨j, hj⟩ := hne
    rw [hj, pow_succ, pow_mul] at hc
    have : (2 : ZMod 3) ^ 2 = 1 := by decide
    rw [this, one_pow, one_mul] at hc
    exact absurd hc (by decide)
  rw [hord] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end OMA.P_oeis_a397683_R1_H3

theorem OMA.solution : OMA.R_oeis_a397683_R1.H3 := OMA.P_oeis_a397683_R1_H3.H3_proof
