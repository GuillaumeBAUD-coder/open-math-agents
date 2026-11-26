import FormalConjectures.Wikipedia.Mersenne

-- Problem: Conjectures about Mersenne primes — sq dvd mersenne iff isWieferichPrime
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/Mersenne.lean:190 (declaration Mersenne.sq_dvd_mersenne_iff_isWieferichPrime)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Mersenne.sq_dvd_mersenne_iff_isWieferichPrime := by
  intro q p hq hp hdvd
  have hdvd' : p ∣ 2 ^ q - 1 := hdvd
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hpow : 2 ^ q = 2 * 2 ^ (q - 1) := by
    conv_lhs => rw [show q = (q - 1) + 1 by omega, pow_succ]
    ring
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 1 ≤ 2 ^ (q - 1) := Nat.one_le_two_pow
    rw [hpow] at hdvd'
    omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  haveI := Fact.mk hp
  have h2 : (2 : ZMod p) ^ q = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (2 ^ q - 1) p).mpr hdvd'
    rw [Nat.cast_sub Nat.one_le_two_pow, sub_eq_zero] at h
    exact_mod_cast h
  have hne : (2 : ZMod p) ≠ 1 := by
    intro h
    have h3 : ((1 : ℕ) : ZMod p) = 0 := by
      have : (2 : ZMod p) - 1 = 0 := by rw [h]; ring
      norm_num at this
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h3 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hord : orderOf (2 : ZMod p) = q := by
    rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one h2) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h1
  have hqd : q ∣ p - 1 := by
    rw [← hord]
    exact ZMod.orderOf_dvd_card_sub_one h20
  obtain ⟨k, hk⟩ := hqd
  have hpk : ¬ p ∣ k := by
    intro h
    have h3 : p ∣ p - 1 := hk ▸ Dvd.dvd.mul_left h q
    have h4 := Nat.le_of_dvd (by have := hp.two_le; omega) h3
    have := hp.two_le
    omega
  have hx : ¬ p ∣ 2 ^ q := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have key := Nat.emultiplicity_pow_sub_pow hp hodd (x := 2 ^ q) (y := 1) hdvd' hx k
  rw [one_pow, ← pow_mul, ← hk, emultiplicity_eq_zero.mpr hpk, add_zero] at key
  constructor
  · intro h
    refine ⟨hp, ?_⟩
    rw [pow_dvd_iff_le_emultiplicity] at h ⊢
    rw [key]
    exact h
  · intro h
    have h5 := h.sq_dvd_pow_sub_one
    rw [pow_dvd_iff_le_emultiplicity] at h5 ⊢
    rw [key] at h5
    exact h5
