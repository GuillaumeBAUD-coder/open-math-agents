import OMAStatements.S_oeis_a094076

-- Disproof at the prime p = 271129 (OEIS A094076, comment of Bruno Mishutka: k = 271129 is a
-- counterexample, gcd(k + 2^n, 2^24 - 1) > 1 always, by a covering with the moduli of
-- 1 mod 2, 0 mod 4, 2 mod 8, 6 mod 24, 14 mod 24, 22 mod 24). Every 271129 + 2^k has one of
-- the factors 3, 5, 7, 13, 17, 241, all dividing M = 5592405 = 3 * 5 * 7 * 13 * 17 * 241, and
-- 2^24 = 1 (mod M), so the factor only depends on k mod 24.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a094076.main) := by
  intro h
  obtain ⟨k, hk⟩ := h 271129 (by norm_num)
  have h24 : 2 ^ 24 ≡ 1 [MOD 5592405] := by decide
  have hmod : 2 ^ k ≡ 2 ^ (k % 24) [MOD 5592405] := by
    have hk' : 2 ^ k = (2 ^ 24) ^ (k / 24) * 2 ^ (k % 24) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hk']
    calc (2 ^ 24) ^ (k / 24) * 2 ^ (k % 24) ≡ 1 ^ (k / 24) * 2 ^ (k % 24) [MOD 5592405] :=
          Nat.ModEq.mul_right _ (Nat.ModEq.pow _ h24)
      _ = 2 ^ (k % 24) := by rw [one_pow, one_mul]
  have hN : 271129 + 2 ^ k ≡ 271129 + 2 ^ (k % 24) [MOD 5592405] := Nat.ModEq.add_left _ hmod
  have cover : ∀ r < 24, ∃ q, q ∣ 5592405 ∧ q ∣ 271129 + 2 ^ r ∧ 2 ≤ q ∧ q ≤ 241 := by
    intro r hr
    interval_cases r
    · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨241, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  obtain ⟨q, hqM, hqr, hq2, hq241⟩ := cover (k % 24) (Nat.mod_lt _ (by norm_num))
  have hqN : q ∣ 271129 + 2 ^ k := (hN.dvd_iff hqM).mpr hqr
  have hpow : 0 < 2 ^ k := by positivity
  rcases hk.eq_one_or_self_of_dvd q hqN with h1 | h1
  · omega
  · omega
