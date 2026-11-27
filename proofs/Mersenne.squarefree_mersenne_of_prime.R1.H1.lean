import OMAReductions.R_Mersenne_squarefree_mersenne_of_prime_R1
import Mathlib.FieldTheory.Finite.Basic

open OMA.R_Mersenne_squarefree_mersenne_of_prime_R1

theorem OMA.solution : OMA.R_Mersenne_squarefree_mersenne_of_prime_R1.H1 := by
  intro q p hq hp hsq
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ mersenne q := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hsq
  have horder := orderOf_two_eq hq hp hdvd
  have hnonzero : (2 : ZMod p) ≠ 0 := by
    have hpow := pow_orderOf_eq_one (2 : ZMod p)
    rw [horder] at hpow
    intro hz
    rw [hz, zero_pow hq.ne_zero] at hpow
    exact zero_ne_one hpow
  have hqdiv : q ∣ p - 1 := horder ▸ ZMod.orderOf_dvd_card_sub_one hnonzero
  obtain ⟨k, hk⟩ := hqdiv
  apply (isWieferichPrimeBase_iff_pow_modEq (by decide : (2 : ℕ) ≠ 0)).2
  refine ⟨hp, ?_⟩
  have hzero := (ZMod.natCast_eq_zero_iff (mersenne q) (p ^ 2)).2 hsq
  unfold mersenne at hzero
  rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    sub_eq_zero] at hzero
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hk, pow_mul,
    hzero, one_pow]
