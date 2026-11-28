import OMAStatements.S_oeis_a217448

/-!
Explicit witness `k = p!`, where `p` is the smallest prime factor of `1 + n^2` (in the explicit
witness style of the accepted proof of the template entry OEIS A262965). Every prime `q ≤ p`
divides `k`, so `q ∣ 1 + (n+k)^2 ↔ q ∣ 1 + n^2`; hence `p` divides `1 + (n+k)^2` and no smaller
prime does.
-/

namespace OMA.P_oeis_a217448

/-- If `q ∣ k` then `q ∣ 1 + (n+k)^2 ↔ q ∣ 1 + n^2`. -/
lemma dvd_shift_iff (q n k : ℕ) (hq : q ∣ k) : q ∣ 1 + (n + k) ^ 2 ↔ q ∣ 1 + n ^ 2 := by
  obtain ⟨t, rfl⟩ := hq
  have e : 1 + (n + q * t) ^ 2 = 1 + n ^ 2 + q * (2 * n * t + q * t ^ 2) := by ring
  rw [e, Nat.dvd_add_left (dvd_mul_right _ _)]

end OMA.P_oeis_a217448

theorem OMA.solution : type_of% @OMA.S_oeis_a217448.main := by
  intro n hn
  set p := Nat.minFac (1 + n ^ 2) with hp
  have hN : 1 + n ^ 2 ≠ 1 := by have := pow_pos hn 2; omega
  have hpp : p.Prime := Nat.minFac_prime hN
  refine ⟨p.factorial, Nat.factorial_pos p, ?_⟩
  have hM : 1 + (n + p.factorial) ^ 2 ≠ 1 := by
    have := pow_pos (Nat.add_pos_left hn p.factorial) 2; omega
  have hpM : p ∣ 1 + (n + p.factorial) ^ 2 :=
    (OMA.P_oeis_a217448.dvd_shift_iff p n _ (Nat.dvd_factorial hpp.pos le_rfl)).mpr
      (Nat.minFac_dvd _)
  set q := Nat.minFac (1 + (n + p.factorial) ^ 2) with hq
  have hqp : q ≤ p := Nat.minFac_le_of_dvd hpp.two_le hpM
  have hqq : q.Prime := Nat.minFac_prime hM
  have hqN : q ∣ 1 + n ^ 2 :=
    (OMA.P_oeis_a217448.dvd_shift_iff q n _ (Nat.dvd_factorial hqq.pos hqp)).mp
      (Nat.minFac_dvd _)
  have : p ≤ q := Nat.minFac_le_of_dvd hqq.two_le hqN
  omega
