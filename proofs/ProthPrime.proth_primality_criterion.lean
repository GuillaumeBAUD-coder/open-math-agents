import FormalConjectures.Wikipedia.ProthPrime

-- Problem: Proth's primality theorem
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/ProthPrime.lean:91 (declaration ProthPrime.proth_primality_criterion)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @ProthPrime.proth_primality_criterion := by
  rintro N ⟨k, n, hk, hn, hkn, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hexp : k * 2 ^ (m + 1) = 2 * (k * 2 ^ m) := by rw [pow_succ]; ring
  have ht1 : 0 < k * 2 ^ m := Nat.mul_pos hk.pos (by positivity)
  rw [show (k * 2 ^ (m + 1) + 1 - 1) / 2 = k * 2 ^ m by rw [hexp]; omega]
  generalize hN : k * 2 ^ (m + 1) + 1 = N
  have hNodd : N = 2 * (k * 2 ^ m) + 1 := by rw [← hN, hexp]
  constructor
  · intro hp
    haveI := Fact.mk hp
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod N)
      (by rw [ZMod.ringChar_zmod_n]; omega)
    have ha0 : a ≠ 0 := by rintro rfl; exact ha IsSquare.zero
    have h := ZMod.pow_div_two_eq_neg_one_or_one N ha0
    have h' : ¬ a ^ (N / 2) = 1 := fun h1 => ha ((ZMod.euler_criterion N ha0).mpr h1)
    rw [show N / 2 = k * 2 ^ m by omega] at h h'
    exact ⟨a, by tauto⟩
  · rintro ⟨a, ha⟩
    by_contra hnp
    have hq : N.minFac.Prime := Nat.minFac_prime (by omega)
    have hqd := Nat.minFac_dvd N
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < N) hnp
    generalize N.minFac = q at hq hqd hsq
    haveI := Fact.mk hq
    have hb : (ZMod.castHom hqd (ZMod q) a) ^ (k * 2 ^ m) = -1 := by
      simpa only [map_pow, map_neg, map_one] using congrArg (ZMod.castHom hqd (ZMod q)) ha
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
      rintro h
      simp [h, zero_pow (by positivity : 2 ^ m ≠ 0)] at hc1
    have hdvd : 2 ^ (m + 1) ∣ q - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hc0
    have hle : 2 ^ (m + 1) ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) hdvd
    have h3 : (2 ^ (m + 1) + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
