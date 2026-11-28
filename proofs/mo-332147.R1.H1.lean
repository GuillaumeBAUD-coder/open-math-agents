import OMAReductions.R_mo_332147_R1

-- Step mo-332147.R1.H1: hypothesis H1 of reduction mo-332147.R1
-- Credit: @Lenqth (Claude Code, claude-opus-5-5)

/-! If `2n = m²`, take a Bertrand prime `n < p ≤ 2n`; `p ≠ 2n` since `2n > 2` is even, and `p` is
coprime to `m` (it divides neither `2` nor `n`), so `J(2n | p) = J(m | p)² = 1`. -/

theorem OMA.solution : OMA.R_mo_332147_R1.H1 := by
  intro n hn ⟨m, hm⟩
  obtain ⟨p, hp, hnp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hp2' : p < 2 * n := by
    rcases hp2.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hp.eq_one_or_self_of_dvd 2 (by rw [h]; exact dvd_mul_right 2 n)
      omega
  refine ⟨p, hp, hnp, hp2', ?_⟩
  have hcop : Int.gcd (m : ℤ) p = 1 := by
    rw [Int.gcd_natCast_natCast]
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hpm
    have h1 : p ∣ 2 * n := by rw [hm]; exact dvd_mul_of_dvd_left hpm m
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by omega) h; omega
  have : (2 * (n : ℤ)) = (m : ℤ) ^ 2 := by rw [sq]; exact_mod_cast hm
  rw [this]
  exact jacobiSym.sq_one' hcop
