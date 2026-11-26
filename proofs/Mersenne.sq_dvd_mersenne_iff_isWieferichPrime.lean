import FormalConjectures.Wikipedia.Mersenne
import Mathlib.NumberTheory.Multiplicity

/-! The order of 2 modulo a prime divisor of a prime-exponent Mersenne number
is the exponent. The converse uses the lifting argument in the merged
Rotkiewicz variant, formalized by Deldor14. -/

theorem OMA.solution : type_of% @Mersenne.sq_dvd_mersenne_iff_isWieferichPrime := by
  intro q p hq hp hdvd
  have hp2 : p ≠ 2 := by
    rintro rfl
    have htwo : 2 ∣ 2 ^ q := dvd_pow_self 2 hq.ne_zero
    unfold mersenne at hdvd
    have hpos : 0 < (2 : ℕ) ^ q := by positivity
    omega
  have hqmod : (2 : ℕ) ^ q ≡ 1 [MOD p] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow q 2 (by decide))).mpr hdvd).symm
  have hqpow : (2 : ZMod p) ^ q = 1 := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr hqmod
  have ht : orderOf (2 : ZMod p) = q := by
    rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one hqpow) with h | h
    · have heq : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp h
      have hm : (2 : ℕ) ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by exact_mod_cast heq)
      have hd : p ∣ 1 := by simpa using hm.symm.dvd'
      exact (hp.not_dvd_one hd).elim
    · exact h
  have : Fact p.Prime := ⟨hp⟩
  have hne : (2 : ZMod p) ≠ 0 := by
    intro h
    simp [h, hq.ne_zero] at hqpow
  have hqpred : q ∣ p - 1 := by
    rw [← ht]
    exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hne)
  constructor
  · intro h
    have hm : (2 : ℕ) ^ q ≡ 1 [MOD p ^ 2] :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow q 2 (by decide))).mpr h).symm
    obtain ⟨k, hk⟩ := hqpred
    apply IsWieferichPrimeBase.of_pow_modEq hp
    simpa [hk, pow_mul] using hm.pow k
  · intro hw
    have hnd : ¬ p ∣ 2 ^ q := fun h => hp2
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    have hpred : ¬ p ∣ p - 1 :=
      Nat.not_dvd_of_pos_of_lt (by have := hp.two_le; omega) (by have := hp.pos; omega)
    have lift := Nat.emultiplicity_pow_sub_pow hp (hp.odd_of_ne_two hp2)
      (y := 1) (x := 2 ^ q) hdvd hnd (p - 1)
    rw [one_pow, emultiplicity_eq_zero.mpr hpred, add_zero] at lift
    have raised := (hw.pow_modEq (by decide : 2 ≠ 0)).pow q
    rw [one_pow, ← pow_mul, Nat.mul_comm (p - 1) q, pow_mul] at raised
    have hsquare : p ^ 2 ∣ (2 ^ q) ^ (p - 1) - 1 := raised.symm.dvd'
    rwa [pow_dvd_iff_le_emultiplicity, lift, ← pow_dvd_iff_le_emultiplicity] at hsquare
