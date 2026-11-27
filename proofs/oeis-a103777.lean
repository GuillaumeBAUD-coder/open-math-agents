import OMAStatements.S_oeis_a103777

lemma OMA.a103777_not_prime (k : ℕ) (h : k % 5 = 3 ∨ k % 5 = 4) :
    ¬ Nat.Prime (OMA.S_oeis_a103777.f k) := by
  intro hp
  have hdvd : 5 ∣ OMA.S_oeis_a103777.f k := by
    unfold OMA.S_oeis_a103777.f
    rw [Nat.dvd_iff_mod_eq_zero]
    rcases h with h | h <;> simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h]
  have hk : 3 ≤ k := by omega
  have hbig : 5 < OMA.S_oeis_a103777.f k := by
    unfold OMA.S_oeis_a103777.f
    nlinarith
  rcases hp.eq_one_or_self_of_dvd 5 hdvd with h1 | h1 <;> omega

theorem OMA.solution : type_of% @OMA.S_oeis_a103777.main := by
  intro k ⟨h0, h1, h2, h3⟩
  have : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases hk : k % 5
  · exact OMA.a103777_not_prime (k + 3) (by omega) h3
  · exact OMA.a103777_not_prime (k + 2) (by omega) h2
  · exact OMA.a103777_not_prime (k + 1) (by omega) h1
  · exact OMA.a103777_not_prime k (by omega) h0
  · exact OMA.a103777_not_prime k (by omega) h0
