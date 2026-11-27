import OMAReductions.R_Mersenne_squarefree_mersenne_of_prime_R1

/-!
# Step H1: a square prime factor of `M_q` (`q` prime) is a Wieferich prime

Let `p` be prime with `p ^ 2 ∣ 2 ^ q - 1`. Then `p` is odd and `p ∣ 2 ^ q - 1`, so the order of `2`
modulo `p` is the prime `q`, hence `q ∣ p - 1`. Writing `p - 1 = q * m`,
`2 ^ (p - 1) = (2 ^ q) ^ m ≡ 1 (mod p ^ 2)`, which is the Wieferich condition.
-/

theorem OMA.solution : OMA.R_Mersenne_squarefree_mersenne_of_prime_R1.H1 := by
  intro q p hq hp hsq
  have hdvd : p ∣ mersenne q := (dvd_pow_self p two_ne_zero).trans hsq
  unfold mersenne at hdvd hsq
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
  refine ⟨hp, ?_⟩
  have h3 : 2 ^ q ≡ 1 [MOD p ^ 2] := ((Nat.modEq_iff_dvd' h1).2 hsq).symm
  rw [hm, pow_mul]
  simpa using h3.pow m
