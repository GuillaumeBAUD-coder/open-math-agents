import FormalConjectures.Wikipedia.ProthPrime

-- Problem: Proth's primality theorem
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/ProthPrime.lean:91 (declaration ProthPrime.proth_primality_criterion)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @ProthPrime.proth_primality_criterion := by
  rintro N ⟨k, n, hk, hn, hkn, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hk1 : 1 ≤ k := hk.pos
  have hpm : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hexp : k * 2 ^ (m + 1) = 2 * (k * 2 ^ m) := by rw [pow_succ]; ring
  have ht1 : 1 ≤ k * 2 ^ m := Nat.mul_pos hk1 hpm
  have hhalf : (k * 2 ^ (m + 1) + 1 - 1) / 2 = k * 2 ^ m := by
    rw [hexp]; omega
  rw [hhalf]
  generalize hN : k * 2 ^ (m + 1) + 1 = N
  have hNodd : N = 2 * (k * 2 ^ m) + 1 := by rw [← hN, hexp]
  constructor
  · intro hp
    haveI := Fact.mk hp
    have hN2 : N ≠ 2 := by omega
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod N)
      (by rw [ZMod.ringChar_zmod_n]; exact hN2)
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (IsSquare.zero)
    have hdiv : N / 2 = k * 2 ^ m := by omega
    have h := ZMod.pow_div_two_eq_neg_one_or_one N ha0
    have h' : ¬ a ^ (N / 2) = 1 := fun h1 => ha ((ZMod.euler_criterion N ha0).mpr h1)
    rw [hdiv] at h h'
    exact ⟨a, by tauto⟩
  · rintro ⟨a, ha⟩
    by_contra hnp
    have hNpos : 0 < N := by omega
    have hN1 : N ≠ 1 := by omega
    have hq : (N.minFac).Prime := Nat.minFac_prime hN1
    have hqd : N.minFac ∣ N := Nat.minFac_dvd N
    have hsq : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self hNpos hnp
    generalize N.minFac = q at hq hqd hsq
    haveI := Fact.mk hq
    have hb : (ZMod.castHom hqd (ZMod q) a) ^ (k * 2 ^ m) = -1 := by
      have h1 := congrArg (ZMod.castHom hqd (ZMod q)) ha
      rw [map_pow, map_neg, map_one] at h1
      exact h1
    generalize ZMod.castHom hqd (ZMod q) a = b at hb
    have hc1 : (b ^ k) ^ (2 ^ m) = -1 := by rw [← pow_mul]; exact hb
    have hq2 : q ≠ 2 := by
      rintro rfl
      obtain ⟨c, hc⟩ := hqd
      omega
    have hneg : (-1 : ZMod q) ≠ 1 := by
      intro h
      have h2 : ((2 : ℕ) : ZMod q) = 0 := by
        push_cast
        linear_combination (-1 : ZMod q) * h
      rw [ZMod.natCast_eq_zero_iff] at h2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
    have hord : orderOf (b ^ k) = 2 ^ (m + 1) := by
      apply orderOf_eq_prime_pow
      · rw [hc1]; exact hneg
      · rw [pow_succ, pow_mul, hc1]; norm_num
    have hc0 : b ^ k ≠ 0 := by
      intro h
      rw [h, zero_pow (by positivity)] at hc1
      exact (neg_ne_zero.mpr one_ne_zero) hc1.symm
    have hdvd : 2 ^ (m + 1) ∣ q - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hc0
    have hle : 2 ^ (m + 1) ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) hdvd
    have h3 : (2 ^ (m + 1) + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
