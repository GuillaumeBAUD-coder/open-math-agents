import OMAStatements.S_oeis_a090520

-- Proof: by Bertrand's postulate there is a prime p with 10^n/4 < p <= 2*(10^n/4), and then
-- floor(10^n/p) is 2 or 3, so the set defining A090519(n) is nonempty and its infimum is a member.
-- The argument follows the accepted proof of the template entry OEIS A090526 (sInf membership).

namespace OMA.P_a090520

/-- Bertrand: for `N ≥ 4` some prime `p` in `(N/4, N/2]` gives `N / p ∈ {2, 3}`. -/
lemma exists_prime_quot (N : ℕ) (hN : 4 ≤ N) : ∃ p : ℕ, p.Prime ∧ (N / p).Prime := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 4) (by omega)
  refine ⟨p, hp, ?_⟩
  have h2 : 2 ≤ N / p := (Nat.le_div_iff_mul_le hp.pos).2 (by omega)
  have h4 : N / p < 4 := (Nat.div_lt_iff_lt_mul hp.pos).2 (by omega)
  interval_cases h : N / p
  · exact Nat.prime_two
  · exact Nat.prime_three

end OMA.P_a090520

theorem OMA.solution : type_of% @OMA.S_oeis_a090520.main := by
  intro n hn
  have hN : 4 ≤ 10 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  obtain ⟨p, hp, hq⟩ := OMA.P_a090520.exists_prime_quot _ hN
  have h : (OMA.S_oeis_a090520.a090519 n).Prime ∧
      (10 ^ n / OMA.S_oeis_a090520.a090519 n).Prime :=
    Nat.sInf_mem (s := {p | p.Prime ∧ (10 ^ n / p).Prime}) ⟨p, hp, hq⟩
  rw [OMA.S_oeis_a090520.a, if_neg h.1.ne_zero]
  exact h.2.ne_zero
