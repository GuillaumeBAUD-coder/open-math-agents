import OMAReductions.R_mo_332147_R1

/-! If `2n = r * r` then `r = 2k`, `n = 2k²`, and any prime `p ∈ (n, 2n)` is coprime to `2k`
(it exceeds `2k`), so `(2n/p) = (2k/p)² = 1`. Bertrand's postulate supplies `p`. -/

theorem OMA.solution : OMA.R_mo_332147_R1.H1 := by
  intro n hn hsq
  obtain ⟨r, hr⟩ := hsq
  have hr2 : 2 ∣ r := by
    have : 2 ∣ r * r := ⟨n, hr.symm⟩
    exact (Nat.Prime.dvd_mul Nat.prime_two).1 this |>.elim id id
  obtain ⟨k, rfl⟩ := hr2
  have hn' : n = 2 * k * k := by nlinarith
  subst hn'
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * k * k) (by omega)
  have hk : 2 ≤ k := by
    by_contra h
    interval_cases k <;> omega
  have hp2 : p ≠ 2 * (2 * k * k) := by
    intro h
    have := hp.eq_one_or_self_of_dvd 2 (by rw [h]; exact dvd_mul_right 2 _)
    rcases this with h' | h'
    · omega
    · omega
  refine ⟨p, hp, h1, by omega, ?_⟩
  have hcop : (2 * (k : ℤ)).gcd p = 1 := by
    have hpk : ¬ p ∣ 2 * k := fun h => by
      have := Nat.le_of_dvd (by omega) h
      nlinarith [Nat.mul_le_mul hk hk]
    have : Nat.Coprime p (2 * k) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpk
    have e : (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) := by push_cast; ring
    rw [e, Int.gcd_natCast_natCast]
    exact this.symm
  have hsq := jacobiSym.sq_one' hcop
  have : (2 * ((2 * k * k : ℕ) : ℤ)) = (2 * k) * (2 * k) := by push_cast; ring
  rw [this, ← sq]
  exact hsq
