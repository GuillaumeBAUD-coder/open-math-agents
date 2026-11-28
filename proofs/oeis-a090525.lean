import OMAStatements.S_oeis_a090525

-- Problem: A090525, no term is zero.
-- Credit: @bnb9001

open OMA.S_oeis_a090525 in
theorem OMA.solution : type_of% @OMA.S_oeis_a090525.main := by
  intro n hn
  have hp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
  have hdvd : Nat.minFac n ∣ n ^ n := dvd_pow (Nat.minFac_dvd n) (by omega)
  have hne : (n ^ n) ≠ 0 := pow_ne_zero _ (by omega)
  have hmem : n ^ n / Nat.minFac n ∈ {k : ℕ | (n ^ n / k).Prime} := by
    show (n ^ n / (n ^ n / Nat.minFac n)).Prime
    rw [Nat.div_div_self hdvd hne]
    exact hp
  intro h0
  have hs := Nat.sInf_mem ⟨_, hmem⟩
  unfold a at h0
  rw [h0] at hs
  exact Nat.not_prime_zero (by simpa using hs)
