import OMAStatements.S_oeis_a155559

lemma three_pow_two_pow (m : ℕ) : ∃ u, Odd u ∧ 3 ^ (2 ^ (m + 1)) = 1 + 2 ^ (m + 3) * u := by
  induction m with
  | zero => exact ⟨1, odd_one, by norm_num⟩
  | succ k ih =>
    obtain ⟨u, hu, h⟩ := ih
    refine ⟨u + 2 ^ (k + 2) * u ^ 2, ?_, ?_⟩
    · have he : Even (2 ^ (k + 2) * u ^ 2) := ⟨2 ^ (k + 1) * u ^ 2, by ring⟩
      exact hu.add_even he
    · rw [pow_succ 2 (k + 1), pow_mul, h]
      ring

lemma zmod_eq_one_iff (N x : ℕ) : ((x : ZMod N) = 1) ↔ x ≡ 1 [MOD N] := by
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]

lemma order_three (m : ℕ) : orderOf (3 : ZMod (2 ^ (m + 3))) = 2 ^ (m + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : ∀ k : ℕ, (3 : ZMod (2 ^ (m + 3))) ^ k = ((3 ^ k : ℕ) : ZMod (2 ^ (m + 3))) := by
    intro k; push_cast; rfl
  apply orderOf_eq_prime_pow
  · rw [h3, zmod_eq_one_iff]
    intro hc
    cases m with
    | zero =>
      norm_num [Nat.ModEq] at hc
    | succ k =>
      obtain ⟨u, hu, h⟩ := three_pow_two_pow k
      rw [h] at hc
      have hd : 2 ^ (k + 1 + 3) ∣ 2 ^ (k + 3) * u := by
        have := (Nat.modEq_iff_dvd' (by omega)).mp hc.symm
        simpa using this
      rw [show k + 1 + 3 = (k + 3) + 1 by ring, pow_succ] at hd
      have := Nat.dvd_of_mul_dvd_mul_left (by positivity) hd
      rw [← even_iff_two_dvd] at this
      exact (Nat.not_even_iff_odd.mpr hu) this
  · rw [h3, zmod_eq_one_iff]
    obtain ⟨u, hu, h⟩ := three_pow_two_pow m
    rw [h]
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]

theorem OMA.solution : type_of% @OMA.S_oeis_a155559.main := by
  intro n
  unfold OMA.S_oeis_a155559.a OMA.S_oeis_a155559.A131577 OMA.S_oeis_a155559.A090129
  cases n with
  | zero =>
    have h2 : orderOf (3 : ZMod (2 ^ (0 + 2))) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := orderOf_eq_prime_pow (p := 2) (n := 0) (x := (3 : ZMod 4)) (by decide) (by decide)
      simpa using this
    rw [h2, order_three 0]
    norm_num
  | succ m =>
    rw [show m + 1 + 3 = (m + 1) + 3 by rfl, order_three (m + 1),
      show m + 1 + 2 = m + 3 by ring, order_three m]
    simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero m)]
    rw [pow_succ 2 (m + 1)]
    have : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    omega
