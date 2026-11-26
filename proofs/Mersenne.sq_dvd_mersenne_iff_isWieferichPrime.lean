import FormalConjectures.Wikipedia.Mersenne

/-!
# `p ^ 2 ∣ 2 ^ q - 1` iff `p` is a Wieferich prime, for primes `p ∣ 2 ^ q - 1`

The order of `2` modulo `p` is the prime `q`, so `q ∣ p - 1`; write `p - 1 = q * m`.
If `2 ^ q ≡ 1 (mod p ^ 2)` then `2 ^ (p - 1) = (2 ^ q) ^ m ≡ 1 (mod p ^ 2)`.
Conversely, let `y = 2 ^ q` modulo `p ^ 2`. Then `y ^ m = 2 ^ (p - 1) = 1`, and `y ≡ 1 (mod p)`
gives `y ^ p = 1` (`dvd_sub_pow_of_dvd_sub`). Since `m < p`, `gcd m p = 1`, so `y = 1`.
-/

theorem OMA.solution : type_of% @Mersenne.sq_dvd_mersenne_iff_isWieferichPrime := by
  intro q p hq hp hdvd
  unfold mersenne at hdvd ⊢
  have h1 : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with hlt | hge
    · have hp2 : p = 2 := by omega
      subst hp2
      have : 2 ∣ 2 ^ q := dvd_pow_self 2 hq.ne_zero
      omega
    · exact hge
  have := Fact.mk hp
  have := Fact.mk hq
  have hz : (2 : ZMod p) ^ q = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff (2 ^ q) 1 p).2 ((Nat.modEq_iff_dvd' h1).2 hdvd).symm
    push_cast at h
    exact h
  have hne1 : (2 : ZMod p) ≠ 1 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h'
    omega
  have hne0 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hord : orderOf (2 : ZMod p) = q := orderOf_eq_prime hz hne1
  have hqdvd : q ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hne0
  obtain ⟨m, hm⟩ := hqdvd
  rw [IsWieferichPrime, isWieferichPrimeBase_iff_pow_modEq (by norm_num)]
  constructor
  · intro h2
    refine ⟨hp, ?_⟩
    have h3 : 2 ^ q ≡ 1 [MOD p ^ 2] := ((Nat.modEq_iff_dvd' h1).2 h2).symm
    rw [hm, pow_mul]
    simpa using h3.pow m
  · rintro ⟨-, hw⟩
    have : NeZero (p ^ 2) := ⟨by positivity⟩
    have hym : ((2 : ZMod (p ^ 2)) ^ q) ^ m = 1 := by
      have h := (ZMod.natCast_eq_natCast_iff (2 ^ (p - 1)) 1 (p ^ 2)).2 hw
      rw [hm, pow_mul] at h
      push_cast at h
      exact h
    have hyp : ((2 : ZMod (p ^ 2)) ^ q) ^ p = 1 := by
      have hint : (p : ℤ) ∣ (2 : ℤ) ^ q - 1 := by
        have h := Int.natCast_dvd_natCast.2 hdvd
        rw [Nat.cast_sub h1] at h
        push_cast at h
        exact h
      have h2 := dvd_sub_pow_of_dvd_sub (R := ℤ) (p := p) (a := (2 : ℤ) ^ q) (b := 1) hint 1
      simp only [pow_one, one_pow] at h2
      have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd (((2 : ℤ) ^ q) ^ p - 1) (p ^ 2)).2
        (by exact_mod_cast h2)
      push_cast at h3
      exact sub_eq_zero.1 h3
    have hcop : Nat.Coprime m p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hpm
      have hm0 : m ≠ 0 := by
        rintro rfl
        omega
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hpm
      have hmle : m ≤ p - 1 := by
        rw [hm]
        exact Nat.le_mul_of_pos_left m hq.pos
      omega
    have hord1 : orderOf ((2 : ZMod (p ^ 2)) ^ q) ∣ 1 := by
      have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hym) (orderOf_dvd_of_pow_eq_one hyp)
      rwa [Nat.Coprime.gcd_eq_one hcop] at h
    have hy1 : (2 : ZMod (p ^ 2)) ^ q = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord1)
    have h4 : ((2 ^ q : ℕ) : ZMod (p ^ 2)) = ((1 : ℕ) : ZMod (p ^ 2)) := by
      push_cast
      exact hy1
    rw [ZMod.natCast_eq_natCast_iff] at h4
    exact (Nat.modEq_iff_dvd' h1).1 h4.symm
