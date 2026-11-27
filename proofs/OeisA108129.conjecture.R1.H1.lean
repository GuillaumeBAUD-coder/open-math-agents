import OMAReductions.R_OeisA108129_conjecture_R1

-- Step OeisA108129.conjecture.R1.H1: hypothesis H1 of reduction OeisA108129.conjecture.R1
-- Credit: @YourFriendPollux

open OeisA108129

/-- The covering congruence: `p ∣ 2 ^ 24 - 1` and `p ∣ 509203 * 2 ^ r - 1` give
`p ∣ 509203 * 2 ^ (24 * q + r) - 1`. -/
private lemma rickOneLe (r : ℕ) : 1 ≤ 509203 * 2 ^ r :=
  Nat.succ_le_of_lt (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) r))

private lemma key (p q r : ℕ) (hp : p ∣ 2 ^ 24 - 1) (hr : p ∣ 509203 * 2 ^ r - 1)
    (hpos : 0 < 509203 * 2 ^ (24 * q + r)) :
    p ∣ 509203 * 2 ^ (24 * q + r) - 1 := by
  have h2 : (2 : ℕ) ^ 24 ≡ 1 [MOD p] :=
    ((Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2 ^ 24)).mpr hp).symm
  have hr' : 509203 * 2 ^ r ≡ 1 [MOD p] :=
    ((Nat.modEq_iff_dvd' (rickOneLe r)).mpr hr).symm
  have hq : (2 : ℕ) ^ (24 * q) ≡ 1 [MOD p] := by
    have h24 : (2 : ℕ) ^ (24 * q) = (2 ^ 24) ^ q := by rw [pow_mul]
    rw [h24]
    simpa using h2.pow q
  have hm : (2 : ℕ) ^ (24 * q + r) ≡ 2 ^ r [MOD p] := by
    rw [pow_add]
    simpa using hq.mul (Nat.ModEq.refl (2 ^ r))
  exact (Nat.modEq_iff_dvd' (rickOneLe (24 * q + r))).mp
    ((hm.mul_left 509203).trans hr').symm

/-- The residues modulo `24` are covered by `3, 5, 7, 13, 17, 241`, all divisors of
`2 ^ 24 - 1`. -/
private lemma cover24 : ∀ r < 24, ∃ p : ℕ, p.Prime ∧ 1 < p ∧ p ≤ 241 ∧
    p ∣ 2 ^ 24 - 1 ∧ p ∣ 509203 * 2 ^ r - 1 := by
  intro r hr
  interval_cases r
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨241, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `509203 * 2 ^ m - 1` is never prime. -/
private lemma not_prime (m : ℕ) : ¬ (509203 * 2 ^ m - 1).Prime := by
  obtain ⟨q, r, hr, hm⟩ : ∃ q r : ℕ, r < 24 ∧ m = 24 * q + r :=
    ⟨m / 24, m % 24, Nat.mod_lt _ (by norm_num), by omega⟩
  obtain ⟨p, hpp, hp1, hp241, hp24, hpdiv⟩ := cover24 r hr
  intro hprime
  have hdvd : p ∣ 509203 * 2 ^ m - 1 := by
    rw [hm]
    exact key p q r hp24 hpdiv (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _))
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · omega
  · have hbig : 241 < 509203 * 2 ^ m - 1 := by
      have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have h3 : 509203 ≤ 509203 * 2 ^ m :=
        Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) m)
      omega
    omega

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  have hnoprime : ¬ ∃ m : ℕ, m ≠ 0 ∧ ((2 * 254602 - 1) * 2 ^ m - 1).Prime := by
    rintro ⟨m, -, hpr⟩
    have he : (2 * 254602 - 1) * 2 ^ m - 1 = 509203 * 2 ^ m - 1 := by norm_num
    rw [he] at hpr
    exact not_prime m hpr
  unfold OMA.R_OeisA108129_conjecture_R1.H1 OeisA108129.a
  rw [if_neg (by norm_num : (254602 : ℕ) ≠ 0), dif_neg hnoprime]
