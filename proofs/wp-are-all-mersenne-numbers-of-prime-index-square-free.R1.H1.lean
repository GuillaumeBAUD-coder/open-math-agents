import OMAReductions.R_wp_are_all_mersenne_numbers_of_prime_index_square_free_R1

-- Step wp-are-all-mersenne-numbers-of-prime-index-square-free.R1.H1: hypothesis H1 of reduction
-- wp-are-all-mersenne-numbers-of-prime-index-square-free.R1
-- Credit: @sovrana

def okq (q : ℕ) : Bool := decide (q < 2) || (2 ^ (q - 1) % q ^ 2 != 1) || q == 1093 || q == 3511

theorem okq_all : (List.range 100001).all okq = true := by decide +kernel

theorem fin1093 : ∀ p : ℕ, p.Prime → p ∣ 1092 → ¬ (1093 ^ 2 ∣ 2 ^ p - 1) := by
  intro p hp hdv
  have hm : p ∈ Nat.primeFactors 1092 := Nat.mem_primeFactors.2 ⟨hp, hdv, by norm_num⟩
  have hs : Nat.primeFactors 1092 = {2, 3, 7, 13} := by decide +kernel
  rw [hs] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> norm_num

theorem fin3511 : ∀ p : ℕ, p.Prime → p ∣ 3510 → ¬ (3511 ^ 2 ∣ 2 ^ p - 1) := by
  intro p hp hdv
  have hm : p ∈ Nat.primeFactors 3510 := Nat.mem_primeFactors.2 ⟨hp, hdv, by norm_num⟩
  have hs : Nat.primeFactors 3510 = {2, 3, 5, 13} := by decide +kernel
  rw [hs] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> norm_num

theorem sol : ∀ p q : ℕ, p.Prime → q.Prime → q ^ 2 ∣ 2 ^ p - 1 →
    2 ^ (q - 1) % q ^ 2 = 1 ∧ q % (2 * p) = 1 ∧ 100000 < q := by
  intro p q hp hq hd
  have hp1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ p := dvd_pow_self 2 hp.ne_zero
    omega
  have hqd : q ∣ 2 ^ p - 1 := dvd_trans (dvd_pow_self q two_ne_zero) hd
  haveI : Fact q.Prime := ⟨hq⟩
  have h1 : (2 : ZMod q) ^ p = 1 := by
    have := (ZMod.natCast_eq_zero_iff (2 ^ p - 1) q).2 hqd
    rw [Nat.cast_sub hp1, Nat.cast_pow] at this
    simpa [sub_eq_zero] using this
  have hne : (2 : ZMod q) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 q).1 (by exact_mod_cast h)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this)
  have hord : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one h1
  have hord_ne : orderOf (2 : ZMod q) ≠ 1 := by
    intro h
    rw [orderOf_eq_one_iff] at h
    have e : (2 : ZMod q) = 1 + 1 := by norm_num
    rw [e] at h
    have : (1 : ZMod q) = 0 := by simpa using h
    exact one_ne_zero this
  have hord_p : orderOf (2 : ZMod q) = p := by
    rcases (Nat.dvd_prime hp).1 hord with h | h
    · exact absurd h hord_ne
    · exact h
  have hdv : p ∣ q - 1 := hord_p ▸ ZMod.orderOf_dvd_card_sub_one hne
  have hq3 := hq.two_le
  -- p is odd
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h3 : q ^ 2 ∣ 3 := by simpa using hd
    have := Nat.le_of_dvd (by norm_num) h3
    nlinarith
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have h2dvd : 2 ∣ q - 1 := by
    obtain ⟨t, ht⟩ := hqodd
    omega
  have hcop : Nat.Coprime 2 p := (Nat.coprime_two_left).2 hpodd
  have h2p : 2 * p ∣ q - 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2dvd hdv
  have hmod : q % (2 * p) = 1 := by
    obtain ⟨c, hc⟩ := h2p
    have hq' : q = 1 + (2 * p) * c := by
      have : q - 1 + 1 = q := by omega
      rw [← this, hc]; ring
    rw [hq', Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by have := hp.two_le; omega)
  have hwief : 2 ^ (q - 1) % q ^ 2 = 1 := by
    obtain ⟨e, he⟩ := hdv
    have hm : 1 ≡ 2 ^ p [MOD q ^ 2] := (Nat.modEq_iff_dvd' hp1).2 hd
    have h4 : (2 ^ p) ^ e ≡ 1 ^ e [MOD q ^ 2] := hm.symm.pow e
    rw [one_pow, ← pow_mul, ← he] at h4
    have hq2' : 1 < q ^ 2 := by nlinarith
    rw [h4]
    exact Nat.mod_eq_of_lt hq2'
  refine ⟨hwief, hmod, ?_⟩
  by_contra hlt
  push Not at hlt
  have hok := List.all_eq_true.1 okq_all q (List.mem_range.2 (by omega))
  simp only [okq, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq, not_not] at hok
  rcases hok with ((h | h) | h) | h
  · omega
  · exact h hwief
  · subst h
    exact fin1093 p hp hdv hd
  · subst h
    exact fin3511 p hp hdv hd

theorem OMA.solution : OMA.R_wp_are_all_mersenne_numbers_of_prime_index_square_free_R1.H1 := sol
