import OMAReductions.R_oeis_a024206_R1

-- Step oeis-a024206.R1.H1: hypothesis H1 of reduction oeis-a024206.R1
-- Credit: @sovrana

theorem primorial_sqfree (p : ℕ) : Squarefree (primorial p) := by
  rw [primorial_eq_prod_primesLE]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    have hi' := (Nat.mem_primesLE.1 hi).2
    have hj' := (Nat.mem_primesLE.1 hj).2
    exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes hi' hj').2 hij)
  · intro i hi
    exact (Nat.mem_primesLE.1 hi).2.squarefree

theorem sol : ∀ n p : ℕ, 1 ≤ n → p.Prime → OMA.S_oeis_a024206.a n + 1 = primorial p →
    Odd (n + 1) ∧ (n + 1) ^ 2 = 4 * primorial p + 1 ∧ ∀ r : ℕ, r.Prime → r ∣ n + 1 → p < r := by
  intro n p hn hp h
  have hP2 : 2 ≤ primorial p := by
    have h1 : p ∣ primorial p := (Nat.Prime.dvd_primorial_iff hp).2 le_rfl
    have h2 := Nat.le_of_dvd (primorial_pos p) h1
    have := hp.two_le
    omega
  have hq4 : 1 ≤ (n + 1) ^ 2 / 4 := by
    have : 4 ≤ (n + 1) ^ 2 := by nlinarith
    omega
  have hfl : (n + 1) ^ 2 / 4 = primorial p := by
    simp only [OMA.S_oeis_a024206.a] at h
    omega
  have hodd : Odd (n + 1) := by
    rcases Nat.even_or_odd (n + 1) with ⟨t, ht⟩ | ho
    · exfalso
      have : (n + 1) ^ 2 = 4 * (t * t) := by rw [ht]; ring
      have h4 : (n + 1) ^ 2 / 4 = t * t := by omega
      rw [h4] at hfl
      have hsq := primorial_sqfree p
      rw [← hfl] at hsq
      have hu := hsq t ⟨1, by ring⟩
      have : t = 1 := Nat.isUnit_iff.1 hu
      subst this
      omega
    · exact ho
  have hq : (n + 1) ^ 2 = 4 * primorial p + 1 := by
    obtain ⟨t, ht⟩ := hodd
    have e : (n + 1) ^ 2 = 4 * (t * t + t) + 1 := by rw [ht]; ring
    have h4 : (n + 1) ^ 2 / 4 = t * t + t := by omega
    omega
  refine ⟨hodd, hq, ?_⟩
  intro r hr hrd
  by_contra hle
  push Not at hle
  have h1 : r ∣ primorial p := (Nat.Prime.dvd_primorial_iff hr).2 hle
  have h2 : r ∣ (n + 1) ^ 2 := Dvd.dvd.pow hrd (by norm_num)
  have h3 : r ∣ 1 := by
    have := (Nat.dvd_add_right (Dvd.dvd.mul_left h1 4)).1 (hq ▸ h2)
    exact this
  exact hr.one_lt.ne' (Nat.dvd_one.1 h3)

theorem OMA.solution : OMA.R_oeis_a024206_R1.H1 := sol
