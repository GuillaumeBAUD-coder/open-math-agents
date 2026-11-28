import OMAReductions.R_oeis_a054723_R1

/-! Let q = 2p + 1 with p ≡ 3 (mod 4), so q ≡ 7 (mod 8).
(→) If q is prime, 2 is a square mod q (`ZMod.exists_sq_eq_two_iff`), so by Euler's criterion
2^p = 2^((q-1)/2) ≡ 1 (mod q).
(←) If q ∣ 2^p - 1, let r be the least prime factor of q. Then 2^p ≡ 1 (mod r) and 2 ≢ 1, so the
order of 2 mod r is p, hence p ∣ r - 1. As 3 ≤ r ≤ 2p + 1, r is p + 1 or 2p + 1. The first is
impossible since p + 1 cannot divide 2(p + 1) - 1, so r = q and q is prime. -/

theorem OMA.solution : OMA.R_oeis_a054723_R1.H1 := by
  intro p hp hp4
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  constructor
  · intro hq
    have := Fact.mk hq
    have hq2 : 2 * p + 1 ≠ 2 := by omega
    have hsq : IsSquare (2 : ZMod (2 * p + 1)) :=
      (ZMod.exists_sq_eq_two_iff (p := 2 * p + 1) hq2).2 (Or.inr (by omega))
    have h20 : (2 : ZMod (2 * p + 1)) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod (2 * p + 1)) = ((0 : ℕ) : ZMod (2 * p + 1)) := by exact_mod_cast h
      rw [ZMod.natCast_eq_natCast_iff'] at h'
      rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at h'
      omega
    have he := (ZMod.euler_criterion (2 * p + 1) h20).1 hsq
    rw [show (2 * p + 1) / 2 = p by omega] at he
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, he, sub_self]
  · intro hdvd
    have hq1 : 2 * p + 1 ≠ 1 := by omega
    have hrp : (2 * p + 1).minFac.Prime := Nat.minFac_prime hq1
    have hrq : (2 * p + 1).minFac ∣ 2 * p + 1 := Nat.minFac_dvd _
    obtain ⟨r, hr⟩ : ∃ r, r = (2 * p + 1).minFac := ⟨_, rfl⟩
    rw [← hr] at hrp hrq
    have := Fact.mk hrp
    have hr2 : r ≠ 2 := by
      rintro rfl
      omega
    have hr3 : 3 ≤ r := by have := hrp.two_le; omega
    have h2r : (2 : ZMod r) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod r) = ((0 : ℕ) : ZMod r) := by exact_mod_cast h
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at h'
      omega
    have hpow : (2 : ZMod r) ^ p = 1 := by
      have h1 : ((2 ^ p - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 (hrq.trans hdvd)
      rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
        sub_eq_zero] at h1
      exact h1
    have hord : orderOf (2 : ZMod r) = p := by
      rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow) with h | h
      · exfalso
        rw [orderOf_eq_one_iff] at h
        have h' : ((2 : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by exact_mod_cast h
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at h'
        omega
      · exact h
    have hdiv : p ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one h2r
    have hrle : r ≤ 2 * p + 1 := Nat.le_of_dvd (by omega) hrq
    obtain ⟨t, ht⟩ := hdiv
    have ht1 : 1 ≤ t := by
      rcases t with _ | t
      · rw [Nat.mul_zero] at ht
        omega
      · omega
    have ht2 : t ≤ 2 := by
      by_contra h
      push Not at h
      have := Nat.mul_le_mul_left p h
      omega
    interval_cases t
    · exfalso
      have hr' : r = p + 1 := by omega
      have h5 : r ∣ 2 * r - (2 * p + 1) := Nat.dvd_sub (dvd_mul_left r 2) hrq
      rw [show 2 * r - (2 * p + 1) = 1 by omega] at h5
      have := Nat.le_of_dvd (by norm_num) h5
      omega
    · have hrq' : r = 2 * p + 1 := by omega
      rw [← hrq']
      exact hrp
